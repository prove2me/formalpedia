-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlock
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:15.786641+00:00
-- url     : https://prove2.me/theorems/69018cc8-9052-440e-b18d-fd15daf68cbd
-- title:
--   Exists Weil Rep SL2 Gl Bordered Block
-- statement:
--   Definitions and structural lemmas for Exists Weil Rep SL2 Gl Bordered Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWeilRepSL2GlBorderedBlock.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourierStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.WeilMix
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]
end GlobalTheory.JR.WeilMix


