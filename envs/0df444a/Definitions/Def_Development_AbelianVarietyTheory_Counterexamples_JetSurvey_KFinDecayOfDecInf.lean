-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
-- name    : Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:44:30.485925+00:00
-- url     : https://prove2.me/theorems/f88f4482-9fa0-43be-83c8-ab3dda3c80c5
-- title:
--   KFin Decay Of Dec Inf
-- statement:
--   Definitions and structural lemmas for KFin Decay Of Dec Inf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.ThreeDimData
namespace GlobalTheory.GapSizeCheck
open scoped InnerProductSpace in

def KFinDecay {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ u v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ u → PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
    ∃ C : ℝ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ x u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a)
def KFinDecayOfGap : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h → KFinDecay (k := k) (r := r) σ (aOf r h)
open scoped InnerProductSpace in

def SmoothDecayOfKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (a : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → KFinDecay (k := k) (r := r) σ a →
    ∀ v0 : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v0 →
      ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
        ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          ‖⟪v0, σ x w⟫_ℂ‖ ≤
            C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a)
end GlobalTheory.GapSizeCheck


