-- Prove2me | Definitions.Def_AdaDiscRL_optValue
-- name    : AdaDiscRL_optValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:40.030008+00:00
-- url     : https://prove2.me/theorems/9d13f42e-dcbf-44e9-8352-1df1809c0a7e
-- title:
--   Optimal value functions $Q^\star_h$, $V^\star_h$ by the Bellman equations
-- statement:
--   For an episodic MDP the **optimal value functions** are defined backward from $V^\star_{H+1}\equiv 0$ by the Bellman equations
--   $$
--   Q^\star_h(x,a)=r_h(x,a)+\mathbb E_{Y\sim T_h(\cdot\mid x,a)}\big[V^\star_{h+1}(Y)\big],\qquad V^\star_h(x)=\sup_{a\in\mathcal A}Q^\star_h(x,a).
--   $$
--   The paper states that $V^\star_h=\sup_\pi V^\pi_h$ and that a deterministic optimal policy exists under suitable assumptions; the recursion above is the form used throughout its analysis.
--
--   **Formalization Note** `optVRem M m` is $V^\star$ at the step with $m$ steps remaining (`optVRem M 0` $=0$, `optVRem M H` $=V^\star_1$); `optQ M h` and `optV M h` are $Q^\star_h$, $V^\star_h$ for the 0-based step `h : Fin H`. The supremum over actions is a real supremum; under Assumption 1 or 2 the functions are bounded and Lipschitz, so all expectations are genuine.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §2.2, p.9, Eq. (3)

import Mathlib
import Definitions.Def_AdaDiscRL_EpisodicMDP

open MeasureTheory ProbabilityTheory

namespace AdaDiscRL

/-- **Optimal value functions** `V⋆`, `Q⋆` (arXiv:2110.15843v3, §2.2, p.9, Bellman equations (3)
and "`V⋆_h(x) = max_{a∈A} Q⋆_h(x, a)`").

`optVRem M m x` is `V⋆` at the step with `m` steps remaining (so `optVRem M 0 = 0` is
`V⋆_{H+1} ≡ 0`, and `optVRem M H` is `V⋆_1`); `optQ M h` is `Q⋆_h` and `optV M h` is `V⋆_h` for
`h : Fin H` (paper step `h+1`):
`Q⋆_h(x,a) = r_h(x,a) + 𝔼_{Y∼T_h(·|x,a)}[V⋆_{h+1}(Y)]`, `V⋆_h(x) = sup_a Q⋆_h(x,a)`.

**Formalization Note.** `V⋆` is defined by this backward recursion rather than as
`sup_π V^π`; the paper states the two agree (p.9). The supremum over the compact action space is
a real `⨆`. -/
noncomputable def optVRem {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | m + 1 => fun x =>
      if hm : m < H then
        ⨆ a : A, (M.meanReward ⟨H - 1 - m, by omega⟩ (x, a) +
          ∫ y, optVRem M m y ∂(M.T ⟨H - 1 - m, by omega⟩ (x, a)))
      else 0

/-- `Q⋆_h(x, a) = r_h(x, a) + 𝔼_{Y ∼ T_h(·|x,a)}[V⋆_{h+1}(Y)]` (Eq. (3), p.9); `h : Fin H` is the
paper's step `h + 1`, and `V⋆_{h+1}` is `optVRem M (H - 1 - h)`. -/
noncomputable def optQ {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (h : Fin H) (p : S × A) : ℝ :=
  M.meanReward h p + ∫ y, optVRem M (H - 1 - h.val) y ∂(M.T h p)

/-- `V⋆_h(x) = max_a Q⋆_h(x, a)` (p.9) for `h : Fin H` (paper step `h + 1`). -/
noncomputable def optV {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {H : ℕ}
    (M : EpisodicMDP S A H) (h : Fin H) (x : S) : ℝ :=
  optVRem M (H - h.val) x

end AdaDiscRL


