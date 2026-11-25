-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesLeafMainTermCurveSystem
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesLeafMainTermCurveSystem
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:54.915803+00:00
-- url     : https://prove2.me/theorems/3764bcec-b94a-4797-b303-821201ba8530
-- title:
--   Zeta Series Leaf Main Term Curve System
-- statement:
--   Definitions and structural lemmas for Zeta Series Leaf Main Term Curve System, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ZetaSeriesLeafMainTermCurveSystem.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesCoeffMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
namespace GlobalTheory.MainTerm
open Formalism.BaseCaseIdentities (Data Kn s0)
end GlobalTheory.MainTerm


