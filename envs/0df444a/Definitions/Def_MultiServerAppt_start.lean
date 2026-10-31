-- Prove2me | Definitions.Def_MultiServerAppt_start
-- name    : MultiServerAppt_start
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:09.685241+00:00
-- url     : https://prove2.me/theorems/b08fa797-d95a-4afa-aedf-12e4fe5a814b
-- title:
--   First-come first-served service start
-- statement:
--   Let $b_d$ be the service time of client $d$, and $\mathrm{dep}_d$ its departure epoch. The first $s$ clients start at $0$. For $c>s$,
--
--   $$\mathrm{start}_c=\max\Big\{t_c,\ \inf\big\{\tau:\#\{d<c:\mathrm{dep}_d>\tau\}<s\big\}\Big\}.$$
--
--   Client $c$ starts at the first moment at or after its arrival at which fewer than $s$ earlier clients remain, which is first-come first-served with $s$ servers, no pre-emption and no sharing.
--
--   **Formalization Note** Clients overtake one another, so this is not a Lindley recursion. For $c>s\ge 1$ the set in the infimum is nonempty and bounded below; both facts and the form displayed above are proved in the verification file, as is the Lindley recursion at $s=1$. The `attach` in the Lean code only records $d<c$ for termination.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §1, p.2, §3, p.8, §3.2, p.8

import Mathlib
import Definitions.Def_MultiServerAppt_arr

namespace MultiServerAppt

/-- The service start of client `c` under first-come first-served with `s` servers and service times
`b`. Each of the first `s` clients starts at `0`; a later client starts at the first time at or after
its arrival at which fewer than `s` earlier clients remain in the system. Kuiper–Lee, Appointment
Scheduling for Multiple Servers, SSRN 3975471, §1 p.2, §3 p.8, §3.2 p.8.

**Formalization Note** Clients overtake one another, so this is not a Lindley recursion. For `c > s`
the set in the `sInf` is nonempty and bounded below, since `c - 1 ≥ s ≥ 1`; both facts, and the form
of this definition with `attach` removed, are proved in
`Solutions/verification/MultiServerAppt_Sanity.lean`. `attach` only records `d < c` for termination.
At `s = 0` the set is empty and the junk value of `sInf` is irrelevant, as `1 ≤ s` throughout. -/
noncomputable def start (s : ℕ) (x b : ℕ → ℝ) (c : ℕ) : ℝ :=
  if c ≤ s then 0
  else
    max (arr s x c)
      (sInf {τ : ℝ |
        ((Finset.Icc 1 (c - 1)).attach.filter
          (fun d => τ < start s x b d.1 + b d.1)).card < s})
termination_by c
decreasing_by
  · have := Finset.mem_Icc.1 d.2
    omega
  · have := Finset.mem_Icc.1 a.2
    omega

end MultiServerAppt


