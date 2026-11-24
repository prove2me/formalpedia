-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:04:25.050891+00:00
-- url     : https://prove2.me/theorems/00951ff7-e945-49bb-8246-76214b761b45
-- title:
--   Row Block Indicator From Lt Iff
-- statement:
--   Definitions and structural lemmas for Row Block Indicator From Lt Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RowBlockIndicatorFromLtIff.lean

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
namespace GlobalTheory.StdLoc
def rowBlockIndicatorFrom (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0
def blockPar (R : Type) [CommRing R] (a d : ℕ) : Subgroup (GL (Fin d) R) where
  carrier := {g | (g : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)}
  mul_mem' := fun {x y} hx hy => by
    show ((x * y : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_mul]; exact hx.mul hy
  one_mem' := by
    show ((1 : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_one]; exact Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    show ((x⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    letI : Invertible (x : Matrix (Fin d) (Fin d) R) := Units.invertible x
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx
def glVol (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)
def blockIdx (q : ℝ) (c a a' : ℕ) : ℝ := q ^ (c * a * a') * glVol q (a + a') / (glVol q a * glVol q a')
end GlobalTheory.StdLoc


