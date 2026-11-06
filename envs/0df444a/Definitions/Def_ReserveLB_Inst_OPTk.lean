-- Prove2me | Definitions.Def_ReserveLB_Inst_OPTk
-- name    : ReserveLB_Inst_OPTk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:12.818544+00:00
-- url     : https://prove2.me/theorems/08d4ae30-f9e6-4637-abf5-3ec9d6ead87b
-- title:
--   $\mathrm{OPT}_k$ of a rational instance
-- statement:
--   For an instance with speeds $s_i$, laws of $X_1, \dots, X_n$ and cap $k$,
--   $$
--   \mathrm{OPT}_k = \min_{\sigma:\ 1 \le |\sigma(j)| \le k}\ \mathbb E\, T_\sigma(X),
--   $$
--   computed with the speeds and laws of the instance read as real numbers.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_OPTk

namespace ReserveLB

/-- **`OPT_k` of a rational instance.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "OPTk = min_(σ: |σ(j)|≤k) E Tσ(X)".

`I.OPTk` is `OPTk` for the speeds, laws and cap `k` of the instance, read through the casts
`ℚ → ℝ`.

**Formalization Note.** Machine `i` has speed `speeds[i]`, job `j` has law `laws[j]`. -/
noncomputable def Inst.OPTk (I : Inst) : ℝ :=
  ReserveLB.OPTk I.k (fun i : Fin I.speeds.length => ((I.speeds.get i : ℚ) : ℝ))
    (fun j : Fin I.laws.length => I.laws.get j)

end ReserveLB


