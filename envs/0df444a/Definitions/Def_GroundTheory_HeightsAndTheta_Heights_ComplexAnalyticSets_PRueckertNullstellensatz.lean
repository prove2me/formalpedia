-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRueckertNullstellensatz
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRueckertNullstellensatz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:00.154444+00:00
-- url     : https://prove2.me/theorems/b8d87cfa-d058-42b9-8c2e-be18cbab315e
-- title:
--   PRueckert Nullstellensatz
-- statement:
--   Definitions and structural lemmas for PRueckert Nullstellensatz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRueckertNullstellensatz.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
namespace RueckertNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}
end RueckertNullstellensatz
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


