-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:41.327447+00:00
-- url     : https://prove2.me/theorems/fb2c52e5-614f-429e-9c14-7c269787cfac
-- title:
--   Foldr Hol DEq Iterated FDeriv
-- statement:
--   Definitions and structural lemmas for Foldr Hol DEq Iterated FDeriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
namespace GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
noncomputable def holD (v : W) (Φ : W → ℂ) (z : W) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))
variable {σ : Type} (u : σ → W)
end GlobalTheory.Ker.CreOp


