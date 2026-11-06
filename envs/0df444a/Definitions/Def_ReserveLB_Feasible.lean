-- Prove2me | Definitions.Def_ReserveLB_Feasible
-- name    : ReserveLB_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:35.958684+00:00
-- url     : https://prove2.me/theorems/1d577cfc-9e1e-463a-96cf-21fd445c6263
-- title:
--   The system $\mathcal F_k(T)$ (4)
-- statement:
--   Given coefficients $\mu_{jqh}$, $v_{jq}$, $w_{jqrh}$, $c_{jq}$ indexed by jobs $j$, patterns $q$ and classes, a point $x = (x_{jq})$ is **feasible** for (4) if $x \ge 0$, $\sum_q x_{jq} = 1$ for every job $j$, and
--   $$
--   \sum_{j,q}\mu_{jqh}x_{jq} \le a_\mu(N_h)N_h,\qquad \sum_{j,\ q:\ f(q)=h} v_{jq}x_{jq} \le a_1(N_h)N_h,
--   $$
--   $$
--   \sum_{j,q} w_{jqrh}x_{jq} \le a_p N_h\ (r < h),\qquad \sum_{j,q} c_{jq}x_{jq} \le a_e,
--   $$
--   for every class $h$ (and every $r < h$), with $a_p = 11447/2025$ and $a_e = 11513/5000$. An **integral** point is the indicator of one pattern per job.
--
--   The paper's $\mathcal F_k(T)$ is this system with the exact $\mu, c$ and lower enclosures $\underline v, \underline w$ of the risk coefficients.
--
--   **Formalization Note** The coefficient families are parameters, so the same definition gives the system with true coefficients (Lemmas 3.1, the certificate) and with lower enclosures (Lemma 4.1).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, (4), p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_Pattern
import Definitions.Def_ReserveLB_firstActive
import Definitions.Def_ReserveLB_aMu
import Definitions.Def_ReserveLB_aOne

namespace ReserveLB

/-- **The system `F_k(T)` (4).**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, (4), p.5: "Σ_q xjq = 1, xjq ≥ 0, Σ_(j,q) µjqh xjq ≤ aµ(Nh)Nh,
Σ_(j,q: f(q)=h) v̲jq xjq ≤ a1(Nh)Nh, Σ_(j,q) w̲jqrh xjq ≤ apNh (r < h), Σ_(j,q) cjq xjq ≤ ae",
with `a_p = 11447/2025`, `a_e = 11513/5000`.

For coefficient families `µ`, `v`, `w`, `c` indexed by job and pattern, `Feasible C k n µ v w c x`
says that `x ≥ 0`, `Σ_q x_jq = 1` for every job `j`, and
1. `Σ_(j,q) µ_jqh x_jq ≤ a_µ(N_h) N_h` for every class `h`;
2. `Σ_(j, q : f(q) = h) v_jq x_jq ≤ a_1(N_h) N_h` for every class `h`;
3. `Σ_(j,q) w_jqrh x_jq ≤ (11447/2025) N_h` for every `r < h`;
4. `Σ_(j,q) c_jq x_jq ≤ 11513/5000`.

**Formalization Note.** The coefficients are parameters, so that the system can be read with the
true coefficients or with lower enclosures (the paper's `F_k(T)` uses lower enclosures of `v` and
`w`). An integral point is the indicator of a choice of one pattern per job. -/
def Feasible (C : ClassStr) (k n : ℕ) (mu : Fin n → Pattern C k → Fin C.L → ℝ)
    (v : Fin n → Pattern C k → ℝ) (w : Fin n → Pattern C k → Fin C.L → Fin C.L → ℝ)
    (c : Fin n → Pattern C k → ℝ) (x : Fin n → Pattern C k → ℝ) : Prop :=
  (∀ j q, 0 ≤ x j q) ∧ (∀ j, ∑ q, x j q = 1) ∧
  (∀ h, ∑ j, ∑ q, mu j q h * x j q ≤ aMu (C.N h) * C.N h) ∧
  (∀ h, ∑ j, ∑ q ∈ Finset.univ.filter (fun q : Pattern C k => firstActive q.1 = some h),
      v j q * x j q ≤ aOne (C.N h) * C.N h) ∧
  (∀ r h, r < h → ∑ j, ∑ q, w j q r h * x j q ≤ 11447 / 2025 * C.N h) ∧
  ∑ j, ∑ q, c j q * x j q ≤ 11513 / 5000

end ReserveLB


