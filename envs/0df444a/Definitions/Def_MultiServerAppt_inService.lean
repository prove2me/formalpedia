-- Prove2me | Definitions.Def_MultiServerAppt_inService
-- name    : MultiServerAppt_inService
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:11.327425+00:00
-- url     : https://prove2.me/theorems/27191e8f-818b-4464-86ed-93bd3e45c33f
-- title:
--   Clients in service
-- statement:
--   The set of clients among the first $c$ in service $u$ after the arrival of client $c$: those $d\le c$ with $\mathrm{start}_d\le t_c+u<\mathrm{dep}_d$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §3.3, p.10, and §4.1, p.11

import Mathlib
import Definitions.Def_MultiServerAppt_dep

namespace MultiServerAppt

/-- The clients among the first `c` in service `u` time units after the arrival of client `c`: they
have started and have not left. Kuiper–Lee, Appointment Scheduling for Multiple Servers,
SSRN 3975471, §3.3, p.10 and §4.1, p.11 (the clients whose phases `Z` records). -/
noncomputable def inService (s : ℕ) (x b : ℕ → ℝ) (c : ℕ) (u : ℝ) : Finset ℕ :=
  (Finset.Icc 1 c).filter
    (fun d => start s x b d ≤ arr s x c + u ∧ arr s x c + u < dep s x b d)

end MultiServerAppt


