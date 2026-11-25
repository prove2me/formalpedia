-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisSide
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisSide
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:01:09.97505+00:00
-- url     : https://prove2.me/theorems/851e8ffe-3c1e-41a1-8917-13b3c4211aef
-- title:
--   Imports Bis Side
-- statement:
--   Definitions and structural lemmas for Imports Bis Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsBisSide.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordAssocVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ExSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair assocDeg assocVar ptCoord noCoord ptFlagModel
  stdE cE unif unif_frac_ne isPull_frame_of_one ptCoord_eq)
def FlagPairJoinLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V,
      IsPull O x (joinCoord z w) E EB → IsPull O x (joinCoord z w) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord z w)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => assocDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => assocDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (assocVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (assocVar ι₂) (φ.g i))
end GroundTheory.Heights₂.Heights.NumbersDVR


