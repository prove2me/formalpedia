-- Prove2me | Definitions.Def_MultiServerAppt_W
-- name    : MultiServerAppt_W
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:23.334841+00:00
-- url     : https://prove2.me/theorems/c26aa2f1-18b5-4c3b-83cb-8461c504d034
-- title:
--   The waiting time $W_c$
-- statement:
--   The waiting time of client $c$: $W_c=\mathrm{start}_c-t_c$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §1, p.2

import Mathlib
import Definitions.Def_MultiServerAppt_start

namespace MultiServerAppt

/-- The waiting time `W_c` of client `c`: its service start minus its arrival epoch. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, §1, p.2. -/
noncomputable def W (s : ℕ) (x b : ℕ → ℝ) (c : ℕ) : ℝ :=
  start s x b c - arr s x c

end MultiServerAppt


