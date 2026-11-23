-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:02:31.266807+00:00
-- url     : https://prove2.me/theorems/9892acb4-4328-4c68-98b8-0a7d1978ef61
-- title:
--   Periodic Bounded Gaussian Summable Cm Type
-- statement:
--   Definitions and structural lemmas for Periodic Bounded Gaussian Summable Cm Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
namespace GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
def embHom (φ : I → K →+* ℂ) : 𝓞 K →+ (I → ℂ) where
  toFun α := GlobalTheory.HeckeTheta.emb φ (α : K)
  map_zero' := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by funext i; simp [GlobalTheory.HeckeTheta.emb]
def embLat (φ : I → K →+* ℂ) : Submodule ℤ (I → ℂ) := LinearMap.range (embHom φ).toIntLinearMap
end GlobalTheory.HeckeLat


