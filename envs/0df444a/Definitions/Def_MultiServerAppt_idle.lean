-- Prove2me | Definitions.Def_MultiServerAppt_idle
-- name    : MultiServerAppt_idle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:53.438458+00:00
-- url     : https://prove2.me/theorems/fd326839-04eb-400a-97b7-6d09effdb933
-- title:
--   The idle time $I^{(s)}$
-- statement:
--   The total server idle time of a session of $n$ clients is
--
--   $$I^{(s)}=\int_0^{t_n+M_n}\big(s-\#\{d\le n:\mathrm{start}_d\le\tau<\mathrm{dep}_d\}\big)\,\mathrm d\tau.$$
--
--   All servers count as available until the last server finishes the last client.
--
--   **Formalization Note** This is the integral of idle servers and not the right side of Eq. (18), so that Eq. (18) is a statement and not a definition.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.2, p.15

import Mathlib
import Definitions.Def_MultiServerAppt_M

namespace MultiServerAppt

/-- The total server idle time `I^(s)` of the session of `n` clients: the integral, up to the session
end `t_n + M_n`, of the number of servers not serving a client. Kuiper–Lee, Appointment Scheduling
for Multiple Servers, SSRN 3975471, §4.2, p.15 ("idle time and overtime are incurred by all servers
until the last server finishes the last client").

**Formalization Note** This is the integral of idle servers and not the right side of Eq. (18), so
that Eq. (18) is a statement: "the total time available in the system minus time spent in service". -/
noncomputable def idle (s : ℕ) (x b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∫ τ in (0 : ℝ)..(arr s x n + M s x b n),
    ((s : ℝ) -
      (((Finset.Icc 1 n).filter
        (fun d => start s x b d ≤ τ ∧ τ < dep s x b d)).card : ℝ))

end MultiServerAppt


