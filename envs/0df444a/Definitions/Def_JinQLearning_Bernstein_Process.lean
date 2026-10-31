-- Prove2me | Definitions.Def_JinQLearning_Bernstein_Process
-- name    : JinQLearning_Bernstein_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:35:02.950214+00:00
-- url     : https://prove2.me/theorems/b6b77678-2e39-4293-8389-adfce1d6c494
-- title:
--   Adaptive episode probability law and pseudo-regret
-- statement:
--   A start rule maps each completed history to a probability mass function on the finite state set. A tie rule maps that history, the new initial state and the current tables to a probability mass function on deterministic Markov policies, supported on policies greedy at every stage and state. Each episode's probability is its start mass times its policy mass times the product of its H transition probabilities. Full-path mass is the product of these conditional episode masses; an event's probability is their finite sum. Arbitrary real probabilities and all nonanticipating randomized starts are covered. Randomized tie kernels generalize deterministic selections, which are point masses. Policy selection occurs before that episode's fresh transitions. Regret is the sum of optimal initial-state value minus the selected policy's initial-state value, not realized reward regret. GreedyPath is only the operational greedy condition on replayed tables and contains no optimism, concentration or regret assumption.
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, pp. 4–5, §2 and regret definition; p. 16, Algorithm 2.

import Definitions.Def_JinQLearning_Bernstein_Tables

open scoped BigOperators
noncomputable section

namespace JinQLearning.Bernstein

variable {S A H : ℕ} [NeZero A]

/-- An arbitrary nonanticipating randomized choice of the next initial state. -/
abbrev StartRule (S A H : ℕ) := List (Episode S A H) → PMF (Fin S)

/-- Every greedy Markov-policy tie selection is allowed, including randomized choices
conditioned on the previous history and the new initial state, before fresh transitions. -/
structure TieRule (S A H : ℕ) where
  law : List (Episode S A H) → Fin S → Tables S A H → PMF (Policy S A H)
  greedy : ∀ past x q π, law past x q π ≠ 0 →
    ∀ h s a, q.Q h s a ≤ q.Q h s (π h s)

/-- The finite-history probability product, including the conditional start and policy laws. -/
def pathMass {K : ℕ} (M : Model S A H) (c₁ c₂ ℓ : ℝ)
    (start : StartRule S A H) (tie : TieRule S A H) (ω : Path S A H K) : ℝ :=
  ∏ k : Fin K,
    (start (pastEpisodes ω k.val) ((ω k).2 0)).toReal *
    (tie.law (pastEpisodes ω k.val) ((ω k).2 0) (snapshot M c₁ c₂ ℓ ω k.val) (ω k).1).toReal *
    ∏ h : Fin H, transition M h ((ω k).2 h.castSucc) (episodeAction (ω k) h) ((ω k).2 h.succ)

/-- Probability of an event, summing the genuine finite-history product over its paths. -/
def probability {K : ℕ} (M : Model S A H) (c₁ c₂ ℓ : ℝ)
    (start : StartRule S A H) (tie : TieRule S A H) (E : Path S A H K → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then pathMass M c₁ c₂ ℓ start tie ω else 0

/-- Pseudo-regret: values of the realized episode's played policy at its initial state. -/
def regret {K : ℕ} (M : Model S A H) (ω : Path S A H K) : ℝ :=
  ∑ k, (optimalValue M 0 ((ω k).2 0) - policyValue M (ω k).1 0 ((ω k).2 0))

/-- The purely operational greedy condition on a replayed path, without probability bounds. -/
def GreedyPath {K : ℕ} (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K) : Prop :=
  ∀ (k : Fin K) h x a,
    (snapshot M c₁ c₂ ℓ ω k.val).Q h x a ≤
      (snapshot M c₁ c₂ ℓ ω k.val).Q h x ((ω k).1 h x)

end JinQLearning.Bernstein


