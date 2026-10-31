-- Prove2me | Definitions.Def_MultiServerAppt_Y
-- name    : MultiServerAppt_Y
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:07.391612+00:00
-- url     : https://prove2.me/theorems/172309ea-610f-4c5c-b885-c4a6fad65747
-- title:
--   The number $Y_c(u)$ of clients present
-- statement:
--   The number of the first $c$ clients still in the system $u$ after the arrival of client $c$:
--
--   $$Y_c(u)=\#\{d\le c:\mathrm{dep}_d>t_c+u\}.$$
--
--   **Formalization Note** Later clients are not counted, since under first-come first-served they do not affect the first $c$. It is defined for all $u\ge 0$, not only before the next arrival: the recursion reads it at $u=x_{c+1}$, and the laws of $W$ and $M$ read it for all $u$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §3.3, pp.9-10, and §4.1, p.11

import Mathlib
import Definitions.Def_MultiServerAppt_dep

namespace MultiServerAppt

/-- The number `Y_c(u)` of the first `c` clients still in the system `u` time units after the arrival
of client `c`. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §3.3, p.9-10
and §4.1, p.11.

**Formalization Note** Later clients are not counted: by first-come first-served they do not affect
the first `c`. It is defined for all `u ≥ 0`, not only before the next arrival, as the page needs: the
recursion reads it at `u = x_{c+1}`, and `F_W`, `F_M` read it for all `u`. -/
noncomputable def Y (s : ℕ) (x b : ℕ → ℝ) (c : ℕ) (u : ℝ) : ℕ :=
  ((Finset.Icc 1 c).filter (fun d => arr s x c + u < dep s x b d)).card

end MultiServerAppt


