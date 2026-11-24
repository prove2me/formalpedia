-- Prove2me | Definitions.Def_InterpOptStop_SAA_Supplement_MarkovLaw
-- name    : InterpOptStop_SAA_Supplement_MarkovLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:44:28.018801+00:00
-- url     : https://prove2.me/theorems/364e2d55-743e-4cbb-bb23-af4ca421f193
-- title:
--   Finite-horizon Markov law with specified transition kernels
-- statement:
--   For a path law $\mu$ on a finite sequence in any measurable state space and measurable transition kernels $K_t$, the Markov-law predicate specifies the conditional law of the next state given the whole past. If $A$ is a measurable event determined by the states through period $t$ and $B$ is a measurable next-state event, then
--   $$\Pr(A\cap\{x(t+1)\in B\})=\int_A K_t(x(t),B)\,d\mu.$$
--   The predicate is separate from the stopping model and from the assertion that each kernel is a probability kernel. It applies only when a next period exists. This gives a definite kernel version of the source conditional probabilities without imposing a density on the initial state.
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Assumption EC.2, p. ec24

import Mathlib

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

/-- The entire past through k, including the current state. -/
def history {α : Type*} {T : ℕ} (k : Fin T) (p : Fin T → α) : Fin (k.val + 1) → α :=
  fun i => p ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩

/-- Generic finite-horizon Markov law, unbundled from the stopping model.
The identity specifies the next-state conditional distribution given the whole past. -/
def MarkovLaw {α : Type*} [MeasurableSpace α] {T : ℕ}
    (μ : Measure (Fin T → α)) (K : Fin T → Kernel α α) : Prop :=
  ∀ (k : Fin T) (hk : k.val + 1 < T)
    (A : Set (Fin (k.val + 1) → α)), MeasurableSet A →
    ∀ B : Set α, MeasurableSet B →
      μ {p | history k p ∈ A ∧ p ⟨k.val + 1, hk⟩ ∈ B} =
        ∫⁻ p in {p | history k p ∈ A}, K k (p k) B ∂μ

end InterpOptStop.SAA.Supplement


