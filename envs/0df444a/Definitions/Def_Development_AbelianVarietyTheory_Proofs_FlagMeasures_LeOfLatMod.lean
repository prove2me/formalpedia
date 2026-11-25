-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:24.046072+00:00
-- url     : https://prove2.me/theorems/eba5cc66-f955-4f94-9fed-2ef5b61a6753
-- title:
--   Le Of Lat Mod
-- statement:
--   Definitions and structural lemmas for Le Of Lat Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfLatMod.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
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
namespace GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
section General
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
end General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
section Nondeg
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn
end Nondeg
section Compl
variable {S I C : Submodule K V} (p : V →ₗ[K] V) (hCS : C ≤ S) (hpC : ∀ x ∈ S, p x ∈ C)
  (hpI : ∀ x, x - p x ∈ I) (hI : ∀ x ∈ I, p x = 0) (hC : ∀ x ∈ C, p x = x)
end Compl
end GlobalTheory.DegCnt.DelScale


