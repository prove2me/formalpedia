-- Prove2me | Definitions.Def_LearnCollude_Schedule
-- name    : LearnCollude_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:20.763037+00:00
-- url     : https://prove2.me/theorems/2ab9cf51-3845-4973-9cba-23f55dfec9e9
-- title:
--   The cycle schedule of the Composite SPSA policy
-- statement:
--   A **schedule** is given by integers $v\ge1$, $w\ge0$, with nominal cycle lengths $N_c=vc+w$. With $\alpha=3/5$ put
--   $$
--   f_c=\lfloor N_c^{\alpha}\rfloor,\qquad L_c=\max(N_c,8f_c),\qquad s_c=\sum_{1\le l<c}L_l.
--   $$
--   Period $t\ge1$ lies in the unique cycle $c\ge1$ with $s_c<t\le s_c+L_c$, at position $\tau=t-s_c$. The five phases are: collusive exploration, $\tau\in[1,2f_c]$; collusive estimation, $\tau\in[2f_c+1,4f_c]$; competitive exploration, $\tau\in[4f_c+1,6f_c]$; competitive estimation, $\tau\in[6f_c+1,8f_c]$; exploitation, $\tau\in[8f_c+1,L_c]$.
--
--   **Formalization Note** The paper's $t_c=\sum_{i\le c}N_i$ overlaps when $8f_c>N_c$. Its proof says that the fifth phase then has length zero (p. 43), which is the reading $L_c=\max(N_c,8f_c)$. It affects finitely many cycles.
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), §3.1, p. 12; policy (10), p. 14; Theorem 3, p. 19; p. 43

import Mathlib
import Definitions.Def_LearnCollude_Randomness

namespace LearnCollude

/-- **The cycle schedule** `N_c = vc + w`, for integers `v ≥ 1`, `w ≥ 0`, Meylahn–den Boer,
SSRN:3741385 (PDF of 2021-12-06), Theorem 3, p. 19. -/
structure Schedule where
  /-- The slope `v`. -/
  v : ℕ
  /-- The offset `w`. -/
  w : ℕ
  one_le_v : 1 ≤ v

namespace Schedule

variable (S : Schedule)

/-- The nominal cycle length `N_c = vc + w`. -/
def N (c : ℕ) : ℕ := S.v * c + S.w

/-- Half the length of each of the first four phases: `f_c = ⌊N_c^α⌋` for `α = 3/5`. -/
noncomputable def f (c : ℕ) : ℕ := ⌊(S.N c : ℝ) ^ (3 / 5 : ℝ)⌋₊

/-- The length of cycle `c`, `L_c = max(N_c, 8⌊N_c^α⌋)`.

**Formalization Note** The paper's `t_c = Σ_{i ≤ c} N_i` (p. 12) with four phases of total length
`8⌊N_c^α⌋` overlaps when `8⌊N_c^α⌋ > N_c`, e.g. `v = 1, w = 0, c = 1`. The paper's proof says the fifth
phase then has length zero (p. 43), which is this reading. It affects finitely many cycles. -/
noncomputable def L (c : ℕ) : ℕ := max (S.N c) (8 * S.f c)

/-- The number of periods before cycle `c`, `s_c = Σ_{1 ≤ l < c} L_l`. -/
noncomputable def s (c : ℕ) : ℕ := ∑ l ∈ Finset.Ico 1 c, S.L l

/-- The cycle containing period `t`: the `c ≥ 1` with `s_c < t ≤ s_c + L_c`. -/
noncomputable def cycleOf (t : ℕ) : ℕ := sInf {c | 1 ≤ c ∧ t ≤ S.s (c + 1)}

/-- The position `τ = t − s_c` of period `t` in its cycle `c`. -/
noncomputable def tau (t : ℕ) : ℕ := t - S.s (S.cycleOf t)

end Schedule

/-- The five phases of a cycle of policy (10), Meylahn–den Boer, SSRN:3741385 (PDF of 2021-12-06),
p. 14: exploration and estimation of an arm, and exploitation. -/
inductive Phase
  | explore (a : Arm)
  | estimate (a : Arm)
  | exploit
  deriving DecidableEq

/-- The phase of period `t`, by `τ = tau t` and `f = f_c`: collusive exploration for `τ ∈ [1, 2f]`,
collusive estimation for `τ ∈ [2f + 1, 4f]`, competitive exploration for `τ ∈ [4f + 1, 6f]`,
competitive estimation for `τ ∈ [6f + 1, 8f]`, and exploitation afterwards. -/
noncomputable def Schedule.phaseOf (S : Schedule) (t : ℕ) : Phase :=
  let τ := S.tau t
  let f := S.f (S.cycleOf t)
  if τ ≤ 2 * f then Phase.explore Arm.col
  else if τ ≤ 4 * f then Phase.estimate Arm.col
  else if τ ≤ 6 * f then Phase.explore Arm.com
  else if τ ≤ 8 * f then Phase.estimate Arm.com
  else Phase.exploit

end LearnCollude


