-- Prove2me | Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
-- name    : ReciprocityTheory_ReducedBases_TBInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:36.222304+00:00
-- url     : https://prove2.me/theorems/5a1bbdcb-44ab-479a-ab36-c5ae5bcd8a03
-- title:
--   TBInjective
-- statement:
--   Definitions and structural lemmas for TBInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/TBInjective.lean

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace Matrix
variable {d : ℕ}
def fB (B : Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (B *ᵥ toReal x)
  map_add' x y := by
    have : toReal (x + y) = toReal x + toReal y := by funext i; simp [toReal]
    rw [this, mulVec_add]; rfl
  map_smul' n x := by
    have : toReal (n • x) = (n : ℝ) • toReal x := by funext i; simp [toReal]
    rw [this, mulVec_smul]
    ext i
    simp
def TB (B : Matrix (Fin d) (Fin d) ℝ) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun v := WithLp.toLp 2 (B *ᵥ WithLp.ofLp v)
  map_add' u v := by ext i; simp [mulVec_add]
  map_smul' r v := by ext i; simp [mulVec_smul]
end ReciprocityTheory.ReducedBases.T2
end


