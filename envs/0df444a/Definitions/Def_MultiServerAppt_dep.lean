-- Prove2me | Definitions.Def_MultiServerAppt_dep
-- name    : MultiServerAppt_dep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:15.557079+00:00
-- url     : https://prove2.me/theorems/cf97112d-8e7f-4df6-9d66-4b96e5b26ae8
-- title:
--   Departure epochs
-- statement:
--   The departure epoch of client $d$ is its service start plus its service time: $\mathrm{dep}_d=\mathrm{start}_d+b_d$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §3, p.8

import Mathlib
import Definitions.Def_MultiServerAppt_start

namespace MultiServerAppt

/-- The departure epoch of client `d`: service start plus service time; there is no pre-emption and
no sharing of servers. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §3,
p.8. -/
noncomputable def dep (s : ℕ) (x b : ℕ → ℝ) (d : ℕ) : ℝ :=
  start s x b d + b d

end MultiServerAppt


