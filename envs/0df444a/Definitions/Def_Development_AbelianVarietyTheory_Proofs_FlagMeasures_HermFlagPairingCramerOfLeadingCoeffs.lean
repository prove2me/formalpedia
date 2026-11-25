-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:19.825807+00:00
-- url     : https://prove2.me/theorems/9461d6fc-fcef-420c-8cd7-4a06adecfa17
-- title:
--   Herm Flag Pairing Cramer Of Leading Coeffs
-- statement:
--   Definitions and structural lemmas for Herm Flag Pairing Cramer Of Leading Coeffs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.MainNotions.S.Loc
namespace GlobalTheory.DegCnt.BlockMinor
variable {K : Type} [Field K]
def minor (bs : List (Kˣ × ℕ+)) (m : ℕ) : K := (Matrix.of fun a b : Fin m => ptEntryL bs a b).det
end GlobalTheory.DegCnt.BlockMinor
namespace GlobalTheory.DegCnt.FrameCramer
open Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end GlobalTheory.DegCnt.FrameCramer
namespace GlobalTheory.DegCnt.Monomial
open GlobalTheory.DegCnt.IdealPow GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V}
end GlobalTheory.DegCnt.Monomial


