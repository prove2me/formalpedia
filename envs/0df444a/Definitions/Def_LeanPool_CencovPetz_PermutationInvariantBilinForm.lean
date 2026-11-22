-- Prove2me | Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
-- name    : LeanPool_CencovPetz_PermutationInvariantBilinForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:52.492588+00:00
-- url     : https://prove2.me/theorems/83ab1801-3769-4ddc-9950-db8a4e04ea2d
-- title:
--   Permutation Invariant Bilin Form
-- statement:
--   Definitions and structural lemmas for Permutation Invariant Bilin Form, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean

module
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentSpace_mem_iff
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply
attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {n : ℕ}
namespace TangentFin
abbrev V (n : ℕ) : Type := tangentSpace (α := Fin n)
namespace Basis
noncomputable def e (i : Fin n) : Fin n → ℝ := Pi.single i (1 : ℝ)
lemma sum_sub_e (i j : Fin n) : (∑ k : Fin n, (e (n := n) i k - e (n := n) j k)) = 0 := by
  classical
  simp [e]
noncomputable def dij (i j : Fin n) : V n :=
  ⟨fun k => e (n := n) i k - e (n := n) j k, by
    -- Membership in `tangentSpace` is `∑ = 0`.
    exact (tangentSpace.mem_iff (α := Fin n)
      (u := fun k => e (n := n) i k - e (n := n) j k)).2 (sum_sub_e (n := n) i j)⟩
end Basis
namespace Perm
open _root_.LeanPool.CencovPetz.TangentFin.Basis
noncomputable abbrev κ (σ : Equiv.Perm (Fin n)) : MarkovMorphism (Fin n) (Fin n) :=
  MarkovMorphism.deterministic (α := Fin n) (β := Fin n) (g := (σ : Fin n → Fin n)) σ.surjective
end Perm
namespace Bilin
open _root_.LeanPool.CencovPetz.TangentFin.Basis
open Perm
variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]
noncomputable abbrev B : LinearMap.BilinForm ℝ (V n) :=
  G.g (α := Fin n) (Simplex.uniform (α := Fin n))
end Bilin
end TangentFin
end LeanPool.CencovPetz


