-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:42.281393+00:00
-- url     : https://prove2.me/theorems/ddee0bec-75c7-4e49-9df1-6e1b12f2a7da
-- title:
--   Is Semisimple Of Locally Finite Compact Group
-- statement:
--   Definitions and structural lemmas for Is Semisimple Of Locally Finite Compact Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LocFinSemisimple
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
def ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U) : Subrepresentation ρ :=
  ⟨U, fun k _ hu => hU k _ hu⟩
variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
end GlobalTheory.LocFinSemisimple


