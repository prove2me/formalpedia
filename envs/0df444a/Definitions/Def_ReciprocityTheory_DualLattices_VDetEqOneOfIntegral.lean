-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
-- name    : ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:51.379463+00:00
-- url     : https://prove2.me/theorems/0cfedb4b-dc9b-443e-a012-4971c0fcc1eb
-- title:
--   VDet Eq One Of Integral
-- statement:
--   Definitions and structural lemmas for VDet Eq One Of Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open Matrix
section
variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]
def IsIntegralMat (U : Matrix ι ι K) : Prop := ∀ i j, v (U i j) ≤ 1
def IsIntegralVec (c : ι → K) : Prop := ∀ j, v (c j) ≤ 1
variable {v}
end
structure Lat {K : Type} [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι]
    [DecidableEq ι] where

  B : Matrix ι ι K
  det_ne : B.det ≠ 0
namespace Lat
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
def pts (L : Lat v ι) : Set (ι → K) := {x | ∃ c, IsIntegralVec v c ∧ x = L.B *ᵥ c}
def std (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι] : Lat v ι :=
  ⟨1, by simp⟩
def mulRight (L : Lat v ι) (U : Matrix ι ι K) (hU : U.det ≠ 0) : Lat v ι :=
  ⟨L.B * U, by rw [Matrix.det_mul]; exact mul_ne_zero L.det_ne hU⟩
noncomputable def dual (L : Lat v ι) : Lat v ι :=
  ⟨(L.Bᵀ)⁻¹, by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_transpose]
    exact inv_ne_zero L.det_ne⟩
end Lat
section colen
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def colen (L' L : Lat v ι) : NNReal := v L'.B.det / v L.B.det
end colen
end ReciprocityTheory.PGsh


