-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:00.613173+00:00
-- url     : https://prove2.me/theorems/a046efc7-e8ba-5cc9-a98e-f1b703c0a8f6
-- title:
--   Embedded Datum Invariant Under Unipotent
-- statement:
--   Definitions and structural lemmas for Embedded Datum Invariant Under Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.DatMove
open AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
def push (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (F : FlagD H r) : FlagD H r where
  e a := s (F.e a)
  T := F.T
  indep := F.indep.map' (s : V →ₗ[K] V) s.ker
  iso a b := by rw [hs]; exact F.iso a b
  zperp a := by rw [hs]; exact F.zperp a
  zz := by rw [hs]; exact F.zz
  hT := F.hT
variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
end GlobalTheory.DegAsm.DatMove
namespace GlobalTheory.DegAsm
open AdaptInv DatMove
end GlobalTheory.DegAsm


