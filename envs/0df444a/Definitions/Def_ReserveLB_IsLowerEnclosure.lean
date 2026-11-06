-- Prove2me | Definitions.Def_ReserveLB_IsLowerEnclosure
-- name    : ReserveLB_IsLowerEnclosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:27.055879+00:00
-- url     : https://prove2.me/theorems/cfd1ef8b-32f5-4772-b52a-3bc9adaf42b8
-- title:
--   Lower enclosures $\underline v,\underline w$ of width $\eta$
-- statement:
--   Families $\underline v_{jq}$ and $\underline w_{jqrh}$ are **lower enclosures of width $\eta$** of the risk coefficients if for every job $j$, pattern $q$ and classes $r, h$,
--   $$
--   0 \le \underline v_{jq},\quad v_{jq} - \eta \le \underline v_{jq} \le v_{jq},\qquad 0 \le \underline w_{jqrh},\quad w_{jqrh} - \eta \le \underline w_{jqrh} \le w_{jqrh},
--   $$
--   with equality in the exact cases (base one or zero coefficient). Then $\underline v + \eta$ (resp. $\underline v$ in an exact case) is an **upper enclosure**.
--
--   **Formalization Note** The enclosures are real numbers (the paper's are rational) and nonnegative, as lower enclosures of the nonnegative effective sizes.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_Pattern
import Definitions.Def_ReserveLB_coefV
import Definitions.Def_ReserveLB_coefW
import Definitions.Def_ReserveLB_vExact
import Definitions.Def_ReserveLB_wExact

namespace ReserveLB

/-- **Lower enclosures of the risk coefficients.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: "Use rational lower enclosures of width η = 1/(16(n + 1)), denoted by
underlines. Base-one and zero cases are exact; elsewhere lower plus η is an upper enclosure."

`IsLowerEnclosure C k T η law vL wL` says that for every job `j` and pattern `q`,
`v_jq − η ≤ v̲_jq ≤ v_jq` with `v̲_jq ≥ 0`, and `v̲_jq = v_jq` in the exact cases; and likewise for
every `r, h`, `w_jqrh − η ≤ w̲_jqrh ≤ w_jqrh`, `w̲ ≥ 0`, exact in the exact cases. Here `v`, `w` are
the true coefficients of `X_j` with law `law j`.

**Formalization Note.** The enclosures are real numbers (the paper's are rational); they are
nonnegative, as lower enclosures of the nonnegative coefficients. -/
def IsLowerEnclosure (C : ClassStr) (k : ℕ) (T η : ℝ) {n : ℕ} (law : Fin n → List (ℚ × ℚ))
    (vL : Fin n → Pattern C k → ℝ) (wL : Fin n → Pattern C k → Fin C.L → Fin C.L → ℝ) : Prop :=
  (∀ j (q : Pattern C k), 0 ≤ vL j q ∧ coefV C T (law j) q.1 - η ≤ vL j q ∧
      vL j q ≤ coefV C T (law j) q.1 ∧ (vExact C T (law j) q.1 → vL j q = coefV C T (law j) q.1)) ∧
  (∀ j (q : Pattern C k) r h, 0 ≤ wL j q r h ∧ coefW C T (law j) q.1 r h - η ≤ wL j q r h ∧
      wL j q r h ≤ coefW C T (law j) q.1 r h ∧
      (wExact C T (law j) q.1 r h → wL j q r h = coefW C T (law j) q.1 r h))

end ReserveLB


