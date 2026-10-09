-- Prove2me | Definitions.Def_RobustPoA_Repeated_Regret
-- name    : RobustPoA_Repeated_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:58.363441+00:00
-- url     : https://prove2.me/theorems/a03a21bd-46c7-4f25-a57f-37805e89c0d2
-- title:
--   Equations (22), (24), pp. 13–14 — deviation improvement and vanishing average regret
-- statement:
--   For a comparison outcome $s'$ and a played outcome $s$, player $i$'s hypothetical cost improvement is
--
--   $$\delta_i(s;s')=C_i(s)-C_i(s'_i,s_{-i}).$$
--
--   A sequence $s^1,s^2,\ldots$ has **vanishing average external regret** if, for every player $i$, there is a function $\varepsilon_i(T)\to0$ such that, for every horizon $T\geq1$ and every fixed strategy $a_i\in S_i$,
--
--   $$\frac1T\sum_{t=1}^{T}C_i(s^t)\leq\frac1T\sum_{t=1}^{T}C_i(a_i,s^t_{-i})+\varepsilon_i(T).$$
--
--   The condition compares each player's realized cost with every time-invariant alternative; the error need not have a specified rate.
--
--   **Formalization Note** The sequence is infinite and its prefixes are used at each horizon. Time starts at 1, so the value at index 0 is unused. The universal comparison with every $a_i$ also covers strategy sets where a minimizing strategy is not attained.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), (22), p. 13 and (24), p. 14

import Mathlib
import Definitions.Def_RobustPoA_Static_Game

namespace RobustPoA.Repeated

/-- Equation (22), relative to a fixed comparison outcome. -/
def delta {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (s' s : ∀ i, S i) (i : ι) : ℝ :=
  C i s - C i (Function.update s i (s' i))

/-- Equation (24): each player has a vanishing average external-regret bound. -/
def VanishingRegret {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (seq : ℕ → ∀ i, S i) : Prop :=
  ∀ i, ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ T : ℕ, 1 ≤ T → ∀ t' : S i,
      (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, C i (seq t) ≤
        (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          C i (Function.update (seq t) i t') + ε T

end RobustPoA.Repeated


