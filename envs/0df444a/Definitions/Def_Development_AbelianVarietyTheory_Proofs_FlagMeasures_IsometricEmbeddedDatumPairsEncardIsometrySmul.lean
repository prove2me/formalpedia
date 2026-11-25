-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:26.54244+00:00
-- url     : https://prove2.me/theorems/42e421d4-dbf5-5e19-8e5d-f73b31042dde
-- title:
--   Isometric Embedded Datum Pairs Encard Isometry Smul
-- statement:
--   Definitions and structural lemmas for Isometric Embedded Datum Pairs Encard Isometry Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometricEmbeddedDatumPairsEncardIsometrySmul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
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
noncomputable section
namespace GlobalTheory.TripInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
abbrev lin (s : V ≃ₗ[K] V) : V →ₗ[𝓞 K] V := (s : V →ₗ[K] V).restrictScalars (𝓞 K)
def pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) : Submodule (𝓞 K) (V × V) :=
  Γ.map ((lin s).prodMap (lin s))
variable {H : HermSpace K V}
def tr (s : V ≃ₗ[K] V)
    (p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :
    (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) :=
  ((Formalism.HermitianLatticesTheory.gmap s p.1.1, pmap s p.1.2), (Formalism.HermitianLatticesTheory.gmap s p.2.1.1, pmap s p.2.1.2), s * p.2.2 * s⁻¹)
end GlobalTheory.TripInv


