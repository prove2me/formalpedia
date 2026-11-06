-- Prove2me | Definitions.Def_ReserveLB_ClassStr_Smooth1
-- name    : ReserveLB_ClassStr_Smooth1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:10.888124+00:00
-- url     : https://prove2.me/theorems/696dbdb0-a7c4-4e38-b411-19d38c3b48ab
-- title:
--   Smoothness conditions (1)
-- statement:
--   A class structure is **smooth** if, for all valid indices,
--   $$
--   S_{h+1} \le S_h/2,\qquad P_h \ge A_{h-1},\qquad A_h \le 2P_h,\qquad N_h \ge 2^h,\qquad P_h/P_f \ge 2^{h-f-1}\ (f < h),
--   $$
--   with $A_{-1} = 0$.
--
--   These are the conditions (1) produced by the reservation-preserving smoothing of Lemma 2.2; Lemmas 3.1 and 4.1 use them.
--
--   **Formalization Note** The condition $P_h \ge A_{h-1}$ is stated for $h \ge 1$ (at $h = 0$ it reads $P_0 \ge 0$).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, (1), p.3

import Mathlib
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_P
import Definitions.Def_ReserveLB_ClassStr_A

namespace ReserveLB

/-- **The smoothness conditions (1).**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, (1), p.3: "Sh+1 ≤ Sh/2, Ph ≥ Ah−1, Ah ≤ 2Ph, Nh ≥ 2^h,
Ph/Pf ≥ 2^(h−f−1) (f < h)."

`C.Smooth1` is the conjunction, for all valid indices, of
1. `S_(h+1) ≤ S_h / 2`;
2. `P_(h+1) ≥ A_h` (that is, `P_h ≥ A_(h−1)` for `h ≥ 1`; for `h = 0`, `A_(−1) = 0`);
3. `A_h ≤ 2 P_h`;
4. `N_h ≥ 2^h`;
5. `P_h / P_f ≥ 2^(h−f−1)` for `f < h`.

**Formalization Note.** Positivity of the speeds is a separate hypothesis wherever this is used;
the exponent `h − f − 1` is a natural number since `f < h`. -/
def ClassStr.Smooth1 (C : ClassStr) : Prop :=
  (∀ h h' : Fin C.L, h'.val = h.val + 1 → C.S h' ≤ C.S h / 2) ∧
  (∀ h h' : Fin C.L, h'.val = h.val + 1 → C.A h ≤ C.P h') ∧
  (∀ h, C.A h ≤ 2 * C.P h) ∧
  (∀ h, 2 ^ h.val ≤ C.N h) ∧
  (∀ f h : Fin C.L, f < h → (2 : ℝ) ^ (h.val - f.val - 1) ≤ C.P h / C.P f)

end ReserveLB


