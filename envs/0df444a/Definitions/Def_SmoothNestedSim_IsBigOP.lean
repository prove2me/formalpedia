-- Prove2me | Definitions.Def_SmoothNestedSim_IsBigOP
-- name    : SmoothNestedSim_IsBigOP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:18.729983+00:00
-- url     : https://prove2.me/theorems/7e9b3e0d-225a-46e5-91a2-dca90b8f8f3c
-- title:
--   Stochastic order $a_k = O_{\mathbb P}(b_k)$
-- statement:
--   Let $(S_k,P_k)_{k\ge 0}$ be probability spaces, $a_k:S_k\to\mathbb R$ random variables and $(b_k)$ a real sequence. We write $a_k = O_{\mathbb P}(b_k)$ if for every $\varepsilon>0$ there is a constant $C>0$ such that
--
--   $$
--   P_k\bigl(a_k > C\,b_k\bigr) < \varepsilon \qquad\text{for all $k$ large enough.}
--   $$
--
--   This is the paper's notion of convergence rate in probability: every rate statement of the mission (Propositions 1–2, Lemma EC.2, (EC.6.3), (EC.6.7), Theorem 1) is of this form.
--
--   **Formalization Note** Each index may carry its own probability space; a sequence on one space is the constant family. The inequality $<\varepsilon$ is strict, as printed. The probability of a non-measurable event is its outer measure.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §1.3, p.8 (definition of O_P)

import Mathlib

open MeasureTheory Filter

namespace SmoothNestedSim

/-- **Stochastic order `a_k = O_ℙ(b_k)`** (Wang, Wang, Zhang, *Smooth Nested Simulation*,
arXiv:2201.02958v6, §1.3, p.8): "`a_n = O_ℙ(b_n)` means that for any `ε > 0`, there exists
`C > 0` such that `ℙ(a_n > C b_n) < ε` for all `n` large enough."

Here `a k : S k → ℝ` is a random variable on the probability space `(S k, P k)` of index `k`
and `b : ℕ → ℝ` is a deterministic sequence.

**Formalization Note.** The index `k` of the asymptotics may carry its own sample space `S k`
and law `P k` (only the law at each `k` enters the definition); a sequence on one fixed space is
the special case of a constant family. The inequality `< ε` is strict, as printed. The
probability of an event that is not measurable is its outer measure. -/
def IsBigOP {S : ℕ → Type*} [∀ k, MeasurableSpace (S k)] (P : ∀ k, Measure (S k))
    (a : ∀ k, S k → ℝ) (b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k in atTop, P k {ω | C * b k < a k ω} < ENNReal.ofReal ε

end SmoothNestedSim


