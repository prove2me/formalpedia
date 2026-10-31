-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_IsEmpiricalMinimizer
-- name    : FoundationsRL_EluderUCB_IsEmpiricalMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:41.715804+00:00
-- url     : https://prove2.me/theorems/08f17671-ee36-48e7-bdfd-8c4247de6fd6
-- title:
--   (4.4): the empirical minimizer of round $t$
-- statement:
--   On a sample path $(\pi^i,r^i)$, a function $\hat f^t$ is an empirical minimizer at round $t$ if
--
--   $$
--   \hat f^t\in\arg\min_{f\in\mathcal F}\sum_{i=1}^{t-1}\bigl(f(\pi^i)-r^i\bigr)^2.
--   $$
--
--   **Formalization Note** The predicate allows any minimizer, so every tie-breaking rule is covered.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.4), p. 58

import Mathlib

namespace FoundationsRL.EluderUCB

/-- **The empirical minimizer of round `t`.** Foster & Rakhlin, arXiv:2312.16730v1, (4.4), p. 58:
`f̂ᵗ = argmin_{f ∈ F} ∑_{i=1}^{t-1} (f(πⁱ) - rⁱ)²`.

**Formalization Note.** `fhat` is any minimizer, so every tie-breaking rule is allowed. Rounds are
indexed from `1`; `Finset.Ico 1 t` is `{1, …, t - 1}`. -/
def IsEmpiricalMinimizer {Act : Type*} (F : Set (Act → ℝ)) (π : ℕ → Act) (r : ℕ → ℝ) (t : ℕ)
    (fhat : Act → ℝ) : Prop :=
  fhat ∈ F ∧ ∀ f ∈ F,
    ∑ i ∈ Finset.Ico 1 t, (fhat (π i) - r i) ^ 2 ≤ ∑ i ∈ Finset.Ico 1 t, (f (π i) - r i) ^ 2

end FoundationsRL.EluderUCB


