-- Prove2me | Definitions.Def_LeanPool_CencovPetz_RationalDensity
-- name    : LeanPool_CencovPetz_RationalDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:59.980495+00:00
-- url     : https://prove2.me/theorems/7425f26b-2d4e-4f89-ac0c-646f75b14d45
-- title:
--   Rational Density
-- statement:
--   Definitions and structural lemmas for Rational Density, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/RationalDensity.lean

module
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
namespace Simplex
open Filter Topology
variable {α : Type*} [Fintype α]
noncomputable section
def approxWeight (p : Simplex α) (n : ℕ) (a : α) : ℕ :=
  Nat.floor (p.p a * (n + 1)) + 1
def approxDenom (p : Simplex α) (n : ℕ) : ℕ :=
  ∑ a : α, approxWeight (p := p) n a
lemma approxWeight_pos (p : Simplex α) (n : ℕ) (a : α) :
    0 < approxWeight (p := p) n a := by
  simp [approxWeight]
variable [Nonempty α]
lemma approxDenom_pos (p : Simplex α) (n : ℕ) :
    0 < approxDenom (p := p) n := by
  classical
  have : 0 < ∑ a : α, approxWeight (p := p) n a := by
    simpa using
      (Finset.sum_pos (s := (Finset.univ : Finset α))
        (f := fun a => approxWeight (p := p) n a)
        (by intro a ha; exact approxWeight_pos (p := p) n a)
        (Finset.univ_nonempty))
  simpa [approxDenom] using this
def approx (p : Simplex α) (n : ℕ) : Simplex α where
  p := fun a => (approxWeight (p := p) n a : ℝ) / (approxDenom (p := p) n : ℝ)
  pos := by
    intro a
    have hw : 0 < (approxWeight (p := p) n a : ℝ) := by
      exact_mod_cast approxWeight_pos (p := p) n a
    have hD : 0 < (approxDenom (p := p) n : ℝ) := by
      exact_mod_cast approxDenom_pos (p := p) n
    exact div_pos hw hD
  sum_eq_one := by
    classical
    let D : ℕ := approxDenom (p := p) n
    have hDpos : 0 < D := by
      simpa [D] using approxDenom_pos (p := p) n
    have hDne : (D : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hDpos)
    calc
      (∑ a : α, (approxWeight (p := p) n a : ℝ) / (D : ℝ))
          = (∑ a : α, (approxWeight (p := p) n a : ℝ)) / (D : ℝ) := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = (D : ℝ) / (D : ℝ) := by
            simp [D, approxDenom]
      _ = 1 := by
            field_simp [hDne]
end
end Simplex
end LeanPool.CencovPetz


