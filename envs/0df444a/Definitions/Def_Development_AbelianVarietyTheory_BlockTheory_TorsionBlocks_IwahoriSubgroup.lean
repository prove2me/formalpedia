-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_IwahoriSubgroup
-- name    : Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_IwahoriSubgroup
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-27T05:46:30.335476+00:00
-- url     : https://prove2.me/theorems/676dbdce-351e-4954-b8d1-4ac8b1133798
-- title:
--   Iwahori Subgroup
-- statement:
--   Definitions and structural lemmas for Iwahori Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/IwahoriSubgroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup
section Defs
variable (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))]
abbrev Int : Subring F := (Valued.v (R := F) (Γ₀ := WithZero (Multiplicative ℤ))).integer
def upperBorel (r : ℕ) (k : Type) [CommRing k] : Subgroup (GL (Fin r) k) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) k).BlockTriangular id}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun {g} hg => by
    have := g.invertible
    have h := Matrix.blockTriangular_inv_of_blockTriangular hg
    simpa [Matrix.coe_units_inv] using h
def maxId : Ideal (Int F) where
  carrier := {x | Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ))}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simpa using Valuation.map_add_lt _ ha hb
  smul_mem' := fun c x hx => by
    have hc : Valued.v (c : F) ≤ (1 : WithZero (Multiplicative ℤ)) := c.2
    have hx' : Valued.v (x : F) < (1 : WithZero (Multiplicative ℤ)) := hx
    show Valued.v ((c * x : Int F) : F) < (1 : WithZero (Multiplicative ℤ))
    rw [Subring.coe_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx'
def iwahoriInt (r : ℕ) : Subgroup (GL (Fin r) (Int F)) :=
  (upperBorel r (Int F ⧸ maxId F)).comap
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maxId F)))
def iwahori (r : ℕ) : Subgroup (GL (Fin r) F) :=
  (iwahoriInt F r).map (Matrix.GeneralLinearGroup.map (Int F).subtype)
variable {F}
def diagPow {r : ℕ} (ϖ : F) (a : Fin r → ℤ) : Matrix (Fin r) (Fin r) F :=
  Matrix.diagonal fun i => ϖ ^ a i
def iwahoriDoubleCoset {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : Set (Matrix (Fin r) (Fin r) F) :=
  {g | ∃ i₁ ∈ iwahori F r, ∃ i₂ ∈ iwahori F r,
    g = (i₁ : Matrix (Fin r) (Fin r) F) * t * (i₂ : Matrix (Fin r) (Fin r) F)}
end Defs
def IwahoriEigenvalues : Prop :=
  ∀ (F : Type) [Field F] [Valued F (WithZero (Multiplicative ℤ))] [CompleteSpace F]
    (ϖ : F), Valued.v ϖ = WithZero.exp (-1 : ℤ) →
    ∀ (r : ℕ) (a : Fin r → ℤ), StrictAnti a →
    ∀ g ∈ iwahoriDoubleCoset (diagPow ϖ a),
      (∃ x : Fin r → F, Function.Injective x ∧
        g.charpoly = ∏ i, (X - C (x i)) ∧
        ∀ i, Valued.v (x i) = WithZero.exp (-(a i))) ∧
      g.charpoly.Separable
theorem self_mem_iwahoriDoubleCoset {F : Type} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    {r : ℕ} (t : Matrix (Fin r) (Fin r) F) : t ∈ iwahoriDoubleCoset t :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩
example (h : IwahoriEigenvalues) (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (r : ℕ) (a : Fin r → ℤ)
    (ha : StrictAnti a) : (diagPow ϖ a).charpoly.Separable :=
  (h _ ϖ hϖ r a ha _ (self_mem_iwahoriDoubleCoset _)).2
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup


