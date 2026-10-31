-- Prove2me | Definitions.Def_AdaDiscRL_polValue
-- name    : AdaDiscRL_polValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:44.159702+00:00
-- url     : https://prove2.me/theorems/86acc545-8853-4ef3-8202-b358d9721be9
-- title:
--   Policy value function $V^\pi_h$
-- statement:
--   A **policy** $\pi=(\pi_h)_{h\in[H]}$ maps each state $x$ to a distribution $\pi_h(x)$ over actions. Its **value function** is the expected sum of rewards from step $h$ on, given by the Bellman equations
--   $$
--   V^\pi_h(x)=\mathbb E_{a\sim\pi_h(x)}\Big[r_h(x,a)+\mathbb E_{Y\sim T_h(\cdot\mid x,a)}\big[V^\pi_{h+1}(Y)\big]\Big],\qquad V^\pi_{H+1}\equiv 0 .
--   $$
--   The regret compares $V^{\pi^k}_1$ with $V^\star_1$.
--
--   **Formalization Note** `polVRem M π m` is $V^\pi$ with $m$ steps remaining, so `polVRem M π H` is $V^\pi_1$. Policies are functions `Fin H → S → Measure A`, so the algorithms' greedy policies are policies without a measurability proof inside the definition.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Definition 2.2 and Eq. (1)–(3), p.9

import Mathlib
import Definitions.Def_AdaDiscRL_EpisodicMDP

open MeasureTheory ProbabilityTheory

namespace AdaDiscRL

/-- **Policy value function** (arXiv:2110.15843v3, Definition 2.2, Eq. (1)–(3), p.9).

A policy is `π : Fin H → S → Measure A`, `π h x` the action distribution at step `h + 1` in state
`x` (p.9: "`π_h : S → Δ(A)`"). `polVRem M π m x` is `V^π` at the step with `m` steps remaining,
by the Bellman equations (3): `V^π_h(x) = 𝔼_{a∼π_h(x)}[r_h(x,a) + 𝔼_{Y∼T_h(·|x,a)}[V^π_{h+1}(Y)]]`,
`V^π_{H+1} ≡ 0`. So `polVRem M π H` is `V^π_1`.

**Formalization Note.** Policies are plain functions to measures, so that the algorithms' greedy
policies (built from finitely many measurable regions) are policies without a measurability proof
in the definition. -/
noncomputable def polVRem {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Fin H → S → Measure A) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | m + 1 => fun x =>
      if hm : m < H then
        ∫ a, (M.meanReward ⟨H - 1 - m, by omega⟩ (x, a) +
          ∫ y, polVRem M π m y ∂(M.T ⟨H - 1 - m, by omega⟩ (x, a))) ∂(π ⟨H - 1 - m, by omega⟩ x)
      else 0

end AdaDiscRL


