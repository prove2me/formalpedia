-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ReferenceLatticeMemOfMemInnerSpan
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ReferenceLatticeMemOfMemInnerSpan
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:49.09614+00:00
-- url     : https://prove2.me/theorems/747e6bfe-c527-529a-a9df-f2bc8da046c0
-- title:
--   Reference Lattice Mem Of Mem Inner Span
-- statement:
--   Definitions and structural lemmas for Reference Lattice Mem Of Mem Inner Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ReferenceLatticeMemOfMemInnerSpan.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open Formalism.HermitianLatticeCounting.P
noncomputable section
namespace GlobalTheory.DegCnt.ReflectionLatticeMembership
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
def Sg : Submodule K V := N.F.X ⊔ N.F'.X ⊔ N.Ist
end GlobalTheory.DegCnt.ReflectionLatticeMembership
namespace GlobalTheory.DegCnt
end GlobalTheory.DegCnt


