-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:01:58.251685+00:00
-- url     : https://prove2.me/theorems/f97f4eef-7423-5174-b013-3922c17e30a2
-- title:
--   Orbit Stabilizer Mass Eq Weighted Sum Fibres
-- statement:
--   Definitions and structural lemmas for Orbit Stabilizer Mass Eq Weighted Sum Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.OrbFib
section
variable {G γ : Type} [Group G] [MulAction G γ]
end
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
end GlobalTheory.Mass.OrbFib
namespace GlobalTheory.Mass
end GlobalTheory.Mass


