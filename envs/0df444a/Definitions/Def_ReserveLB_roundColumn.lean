-- Prove2me | Definitions.Def_ReserveLB_roundColumn
-- name    : ReserveLB_roundColumn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:49.375707+00:00
-- url     : https://prove2.me/theorems/cb23fd33-253d-4adc-b900-42ed90980dc7
-- title:
--   Weighted column of an original and a pattern
-- statement:
--   For the rounding, the class rows of (4) are divided by $N_h$ and weighted: means weight $1$, first risks weight $\min\{N_h, 7\}$ when $N_h \ge 2$ (else $0$), prefix risks weight $13$ when $\lambda_{rh} \ge 16$ (else $0$). The **weighted column** of job $j$ and pattern $q$ is
--   $$
--   \sum_h \frac{\mu_{jqh}}{N_h} + \omega_1(N_{f(q)})\frac{v_{jq}}{N_{f(q)}} + \sum_{r < h}\omega_p(\lambda_{rh})\frac{w_{jqrh}}{N_h} .
--   $$
--   The exception row is the objective of the rounding, not a row.
--
--   **Formalization Note** Written with the true coefficients $v, w$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 4.1, p.7 (rounding weights)

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_coefMu
import Definitions.Def_ReserveLB_coefV
import Definitions.Def_ReserveLB_coefW
import Definitions.Def_ReserveLB_firstActive
import Definitions.Def_ReserveLB_lam

namespace ReserveLB

/-- **Weighted column of one original and one pattern.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 4.1, p.7: "Normalize the class rows of (4) by Nh. For rounding only, give means
weight one, first risks weight min{Nh, 7} when Nh ≥ 2, and prefix risks weight thirteen when
λrh ≥ 16. Give the other risk rows weight zero".

For the law `μ` of `X_j` and a pattern `q`, `roundColumn C T μ q` is the sum, over the rows of (4)
divided by `N_h`, of the weighted coefficients of the column `(j, q)`:
`Σ_h µ_jqh / N_h + ω_1(N_f) v_jq / N_f + Σ_(r<h) ω_p(λ_rh) w_jqrh / N_h`, where `f = f(q)`,
`ω_1(N) = min{N, 7}` if `N ≥ 2` and `0` otherwise, and `ω_p(λ) = 13` if `λ ≥ 16` and `0` otherwise.

**Formalization Note.** Written with the true coefficients `v`, `w`; the exception row is the
objective, not a row. -/
noncomputable def roundColumn (C : ClassStr) (T : ℝ) (μ : List (ℚ × ℚ)) (q : Fin C.L → Fin 3) : ℝ :=
  (∑ h, coefMu C T μ q h / C.N h) +
  (match firstActive q with
    | some f => (if 2 ≤ C.N f then (min (C.N f) 7 : ℕ) else 0 : ℝ) * coefV C T μ q / C.N f
    | none => 0) +
  ∑ r, ∑ h, (if r < h ∧ 16 ≤ lam C r h then 13 * coefW C T μ q r h / C.N h else 0)

end ReserveLB


