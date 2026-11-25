-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap
-- name    : Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:03:33.236498+00:00
-- url     : https://prove2.me/theorems/bfa42bec-3a85-48a5-aeb7-119cd2c71f3e
-- title:
--   Top Of Map
-- statement:
--   Definitions and structural lemmas for Top Of Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocallyConstantCoinvariants/TopOfMap.lean

import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end PositivityTheory.KCo


