-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:05.496282+00:00
-- url     : https://prove2.me/theorems/eb25f907-7799-4660-a5f2-df118b442d2b
-- title:
--   Has Deriv At Matrix Exp Zero
-- statement:
--   Definitions and structural lemmas for Has Deriv At Matrix Exp Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/OrbitDerivatives/HasDerivAtMatrixExpZero.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
namespace CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
def nu (σ : Mat n → (H →L[ℂ] H)) (Ws : List (List (Mat n))) (v : H) : ℝ := (Ws.map fun W => ‖dsW σ W v‖).sum
def Bdd (G : Set (Mat n)) (L : Mat n → Prop) (σ : Mat n → (H →L[ℂ] H)) {E : Type} [NormedAddCommGroup E]
    (T : H → E) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mat n))), (∀ W ∈ Ws, ∀ X ∈ W, L X) ∧ ∀ v, IsSm G σ v → ‖T v‖ ≤ C * nu σ Ws v
def Lin (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (T : H → H') : Prop :=
  (∀ v w, IsSm G σ v → IsSm G σ w → T (v + w) = T v + T w) ∧ ∀ (a : ℂ) v, IsSm G σ v → T (a • v) = a • T v
variable {L : Mat n → Prop}
section Lift
variable [CompleteSpace H] [CompleteSpace H']
structure TwInt (G : Set (Mat n)) (L : Mat n → Prop) (σ : Mat n → (H →L[ℂ] H)) (τ : Mat n → (H' →L[ℂ] H'))
    {ι : Type} [Fintype ι] (M : Mat n → ι → ι → ℂ) (T : ι → H → H') : Prop where
  lin : ∀ c, Lin G σ (T c)
  bdd : ∀ c, Bdd G L σ (T c)
  eqv : ∀ g ∈ G, ∀ c v, IsSm G σ v → τ g (T c v) = ∑ d, M g c d • T d (σ g v)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → ι → ι → ℂ} {T : ι → H → H'}
end Lift
end CompanionTheory.D.gk.FinalFormK


