-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:59.859321+00:00
-- url     : https://prove2.me/theorems/7edbd380-1230-4327-9ea0-82c032d98371
-- title:
--   Leaf Coordinate Weight Nonneg Of Adapted Chain Data
-- statement:
--   Definitions and structural lemmas for Leaf Coordinate Weight Nonneg Of Adapted Chain Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeafCoordinateWeightNonnegOfAdaptedChainData.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
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
open Formalism.BaseCaseIdentities (Data Kn s0)
open ReciprocityTheory.PGsh (OrdGe lgSum)
namespace GlobalTheory.LeafCoordWeight
end GlobalTheory.LeafCoordWeight


