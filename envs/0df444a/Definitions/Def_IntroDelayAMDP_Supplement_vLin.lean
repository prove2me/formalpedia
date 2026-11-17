-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_vLin
-- name    : IntroDelayAMDP_Supplement_vLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:45:28.234375+00:00
-- url     : https://prove2.me/theorems/8181b224-3854-4614-bf41-ba347cf8c97e
-- title:
--   V-function on a general state space
-- statement:
--   For a loss $\ell:\mathcal S\times\mathcal A\to\mathbb R$, a policy $\pi$ and $n$ remaining steps, define
--   $$V_0(s)=0,\qquad V_{n+1}(s)=\sum_{a}\pi(a\mid s)\Bigl(\ell(s,a)+\mathbf 1[h(s)+1<H]\int V_n\,dP(\cdot\mid s,a)\Bigr).$$
--   For $s\in\mathcal S_h$, $V_{H-h}(s)$ is the V-function $V^\pi(s)$ of Eq. (12) (with $V=0$ on the terminal layer), and in particular $V^\pi(s_0)=V_H(s_0)$. This is the expected loss of $\pi$ from $s$ to the end of the episode, with the sums over states of the tabular case replaced by integrals.
--
--
--   **Formalization Note** The integral is the Bochner integral; for a measurable policy and a measurable loss in $[0,1]$ the integrand is measurable and bounded, so it is the true expectation.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (12), p.13; Definition 2.1, p.13

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace

namespace IntroDelayAMDP.Supplement

open MeasureTheory ProbabilityTheory

/-- **V-function on a general state space** (Eq. (12), printed p.13, PDF p.15, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530); with "Sums over states then become integrals", Definition 2.1, printed p.13).
Printed p.13: "`Q^π_k(s, a) ≜ ℓ_k(s, a) + E_{s′∼P(·|s,a)}[V^π_k(s′)]`, `V^π_k(s) ≜ E_{a∼π(·|s)}[Q^π_k(s, a)]`",
with `V^π_k = 0` on the terminal layer `S_H`.

For a loss `ℓ`, a policy `π` and `n` remaining steps, `vLin L P ℓ π 0 s = 0` and
`vLin L P ℓ π (n + 1) s = ∑_a π(a | s) (ℓ(s, a) + ∫ vLin L P ℓ π n dP(· | s, a))`, the integral being dropped
for a last-layer state (its successor is terminal, where `V = 0`). For `s ∈ S_h`, `vLin … (H − h) s` is
`V^π(s)`, so `V^π(s₀) = vLin L P ℓ π H L.s0`.

**Formalization Note.** The integral is the Bochner integral; for a measurable policy and a measurable loss
in `[0, 1]` the integrand is measurable and bounded by `n`, so it is the true expectation. -/
noncomputable def vLin {X A : Type} [MeasurableSpace X] [Fintype A] {H : ℕ} (L : LayeredSpace X H)
    (P : A → Kernel X X) (ℓ : X → A → ℝ) (π : X → A → ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | n + 1, s => ∑ a, π s a *
      (ℓ s a + if L.layer s + 1 < H then ∫ x, vLin L P ℓ π n x ∂(P a s) else 0)

end IntroDelayAMDP.Supplement


