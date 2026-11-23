-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:24.390875+00:00
-- url     : https://prove2.me/theorems/2aab580c-f037-4be6-8590-18fe5e911253
-- title:
--   Siegel Theta Transformation Siegel Parabolic
-- statement:
--   Definitions and structural lemmas for Siegel Theta Transformation Siegel Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
noncomputable def parChar {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (x : Matrix κ ι ℚ) : ℂ :=
  cexp (-(Real.pi * I * ((∑ k, x k ⬝ᵥ S *ᵥ x k : ℚ) : ℂ)))
end GlobalTheory.SW.Parab


