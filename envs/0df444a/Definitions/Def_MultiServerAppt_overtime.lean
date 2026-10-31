-- Prove2me | Definitions.Def_MultiServerAppt_overtime
-- name    : MultiServerAppt_overtime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:34.102348+00:00
-- url     : https://prove2.me/theorems/63a8e4de-605f-4691-9cb7-463d7afbc981
-- title:
--   The overtime $O^{(s)}$
-- statement:
--   The overtime, incurred by all $s$ servers, for a targeted session end $T$:
--
--   $$O^{(s)}=s\max\{t_n+M_n-T,\ 0\}.$$
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (3), p.8, and §4.2, p.15

import Mathlib
import Definitions.Def_MultiServerAppt_M

namespace MultiServerAppt

/-- The overtime `O^(s) = s · max{t_n + M_n - T, 0}`, incurred by all `s` servers, for the targeted
session end `T`. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (3), p.8
and §4.2, p.15. -/
noncomputable def overtime (s : ℕ) (x b : ℕ → ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  (s : ℝ) * max (arr s x n + M s x b n - T) 0

end MultiServerAppt


