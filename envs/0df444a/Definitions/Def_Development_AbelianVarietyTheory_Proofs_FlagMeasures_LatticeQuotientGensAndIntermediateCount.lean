-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:08:07.537821+00:00
-- url     : https://prove2.me/theorems/09a025e4-837f-4d4f-850b-55f0a43b581d
-- title:
--   Lattice Quotient Gens And Intermediate Count
-- statement:
--   Definitions and structural lemmas for Lattice Quotient Gens And Intermediate Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeQuotientGensAndIntermediateCount.lean

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
namespace GlobalTheory.Mass.LatticeGens
section Dedekind
variable {R V : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]
end Dedekind
section Count
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
end Count
end GlobalTheory.Mass.LatticeGens


