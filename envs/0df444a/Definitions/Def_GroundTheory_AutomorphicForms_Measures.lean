-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_Measures
-- name    : GroundTheory_AutomorphicForms_Measures
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:41.963928+00:00
-- url     : https://prove2.me/theorems/922e43b5-b691-4102-9135-061d2b5ea94e
-- title:
--   Measures
-- statement:
--   Definitions and structural lemmas for Measures, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Measures.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
namespace Measures
section General
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (K : Subgroup G)
def IsSmallNormal (N : Subgroup G) : Prop :=
  IsOpen (N : Set G) ∧ N ≤ K ∧ ∀ k ∈ K, ∀ y ∈ N, k * y * k⁻¹ ∈ N
def smallCosets : Set (Set G) :=
  {s | ∃ x : G, ∃ N : Subgroup G, IsSmallNormal K N ∧ s = x • (N : Set G)}
variable {K}
end General
section GeneralLinear
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] {β : Fin n → α}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
end GeneralLinear
end Measures
end GroundTheory.Automorphic


