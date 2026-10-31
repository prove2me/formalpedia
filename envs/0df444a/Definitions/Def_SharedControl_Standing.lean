-- Prove2me | Definitions.Def_SharedControl_Standing
-- name    : SharedControl_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:52.725519+00:00
-- url     : https://prove2.me/theorems/b6272bb2-9419-4f33-97df-c396fd41ff00
-- title:
--   Standing assumptions: $\pi_g > 0 \ge \pi_b$, $q\in[0,1]$, $r$ continuous with support $[r_l, r_h]$, $0 \le r_l < r_h$
-- statement:
--   A model $(\Omega, P, r, \pi_g, \pi_b, q, r_l, r_h)$ satisfies the **standing assumptions** of the paper when
--
--   1. $P$ is a probability measure and $r$ is a random variable (measurable);
--   2. $r$ has a continuous distribution: $\Pr[r = x] = 0$ for every $x \in \mathbb R$;
--   3. $r \in [r_l, r_h]$ almost surely, and $r_l$ and $r_h$ are the minimum and maximum of the support: $\Pr[r < r_l + \varepsilon] > 0$ and $\Pr[r > r_h - \varepsilon] > 0$ for every $\varepsilon > 0$;
--   4. $\pi_g > 0$, $\pi_b \le 0$, $0 \le q \le 1$ and $0 \le r_l < r_h$.
--
--   These are the paper's assumptions "$\pi_g > 0$ and $\pi_b \le 0$", "$r$ has a continuous distribution with support on $[r_l, r_h]$, where $0 \le r_l < r_h < \infty$", and "$r_l$ is the minimum value of the support of $r$". Every theorem of the mission assumes them.
--
--   **Formalization Note** "Continuous" is read as atomless; no density is assumed. Item 3 consists of consequences of $\operatorname{supp}(\text{law of } r) = [r_l, r_h]$ and also allows gaps inside $(r_l, r_h)$, so it is slightly more general than a support equal to the interval.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2, p.3; §2.1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model

open MeasureTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2, p.3 (PDF p.4), and §2.1, p.4 (PDF p.5): the standing
assumptions of the model. "With probability q, the state is “good” … where πg > 0 and πb ≤ 0.
… We assume that r has a continuous distribution with support on [rl, rh], where
0 ≤ rl < rh < ∞." and (p.4) "Recall that rl is the minimum value of the support of r".

**Formalization Note.** `P` is a probability measure and `r` is measurable (the standing
convention that a random variable is measurable). "Continuous distribution" is read as an
atomless law, `NullSingletonClass (P.map r)` (every singleton has probability zero; Mathlib's
former `NoAtoms`); no density is assumed. "Support on `[rl, rh]`" is encoded by
three consequences of `supp(law r) = [rl, rh]`: `r ∈ [rl, rh]` almost surely, and `rl`, `rh` are
the essential infimum and supremum of `r` (every one-sided neighbourhood
`{r < rl + ε}`, `{rh − ε < r}` has positive probability). This is more general than the
support being exactly `[rl, rh]`: gaps inside `(rl, rh)` are allowed. `q` is a probability,
`0 ≤ q ≤ 1`. -/
structure Standing {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure M.P
  measurable_r : Measurable M.r
  nullSingleton : NullSingletonClass (M.P.map M.r)
  ae_mem_Icc : ∀ᵐ ω ∂M.P, M.r ω ∈ Set.Icc M.rl M.rh
  rl_min_support : ∀ ε > 0, 0 < M.P {ω | M.r ω < M.rl + ε}
  rh_max_support : ∀ ε > 0, 0 < M.P {ω | M.rh - ε < M.r ω}
  πg_pos : 0 < M.πg
  πb_nonpos : M.πb ≤ 0
  q_nonneg : 0 ≤ M.q
  q_le_one : M.q ≤ 1
  rl_nonneg : 0 ≤ M.rl
  rl_lt_rh : M.rl < M.rh

end SharedControl


