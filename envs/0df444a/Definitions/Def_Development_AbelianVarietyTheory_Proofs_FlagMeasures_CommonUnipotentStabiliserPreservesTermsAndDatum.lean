-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:10:30.33985+00:00
-- url     : https://prove2.me/theorems/c7b2832d-02ef-4866-ad61-f3b0cedcb51b
-- title:
--   Common Unipotent Stabiliser Preserves Terms And Datum
-- statement:
--   Definitions and structural lemmas for Common Unipotent Stabiliser Preserves Terms And Datum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonUnipotentStabiliserPreservesTermsAndDatum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
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
namespace GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
structure Keeps (F : FlagD H r) (s : V ≃ₗ[K] V) : Prop where
  iso : ∀ x y, H.B (s x) (s y) = H.B x y
  flag : ∀ (a : ℕ) (x : V), s x ∈ F.Xa a ↔ x ∈ F.Xa a
  vec : ∀ a : Fin (r + 1), s (F.e a) - F.e a ∈ F.Xa a.val
  mid : ∀ y : V, (∀ x ∈ F.X, H.B y x = 0) → s y - y ∈ F.X
section Group
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Group
end GlobalTheory.DegCnt.StabInv


