-- Prove2me | Definitions.Def_MultiServerAppt_M
-- name    : MultiServerAppt_M
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:16.68747+00:00
-- url     : https://prove2.me/theorems/7651b4e1-8c98-4928-8050-c2838495c695
-- title:
--   The makespan $M_c$
-- statement:
--   The makespan of the first $c$ clients, measured from $t_c$:
--
--   $$M_c=\max_{d\le c}\mathrm{dep}_d-t_c.$$
--
--   So $t_n+M_n$ is the end of the session.
--
--   **Formalization Note** The supremum runs over a finite set, nonempty in every use, so it is a maximum.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.2, p.14

import Mathlib
import Definitions.Def_MultiServerAppt_dep

namespace MultiServerAppt

/-- The makespan `M_c` of the first `c` clients, measured from `t_c`: the last of their departure
epochs minus `t_c`. So `t_n + M_n` is the end of the session. Kuiper–Lee, Appointment Scheduling for
Multiple Servers, SSRN 3975471, §4.2, p.14.

**Formalization Note** The supremum runs over a finite set, which is nonempty in every use (`1 ≤ c`),
so it is a maximum and the junk value of a real `⨆` never occurs. -/
noncomputable def M (s : ℕ) (x b : ℕ → ℝ) (c : ℕ) : ℝ :=
  (⨆ d : Finset.Icc 1 c, dep s x b d) - arr s x c

end MultiServerAppt


