-- Prove2me | Definitions.Def_CalibeatBandit_IsProbVec
-- name    : CalibeatBandit_IsProbVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:26.610134+00:00
-- url     : https://prove2.me/theorems/d9994492-d0a7-42bc-9c76-c71c352173c1
-- title:
--   Probability vectors $\Delta(\mathcal A)$ on $K$ actions
-- statement:
--   Let $\mathcal A=[K]$ be a finite set of $K$ actions. A vector $p\in\mathbb R^K$ is a **probability vector**, written $p\in\Delta(\mathcal A)$, if
--   $$p(i)\ge 0\ \text{ for every } i\in\mathcal A,\qquad \sum_{i\in\mathcal A}p(i)=1 .$$
--   Mixed strategies of the learner and of the recommendation, and the post-processing distributions of the internal learners, are probability vectors.
--
--   **Formalization Note** Actions are `Fin K`; a distribution is identified with its vector of point masses.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2 (Notation), p.7 (PDF 7)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **Probability vector on `[K]`.** A vector `p : Fin K → ℝ` is a (discrete) probability
distribution over the action set `𝒜 = [K]`, i.e. an element of `Δ(𝒜)`: all entries are
nonnegative and they sum to one.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2 Notation,
p.7: "For a finite set S, ∆(S) denotes the set of (discrete) probability distributions over S."

**Formalization Note.** The action set `[K] = {1, …, K}` is `Fin K = {0, …, K − 1}`; a
distribution is its vector of point masses. -/
def IsProbVec {K : ℕ} (p : Fin K → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

end CalibeatBandit


