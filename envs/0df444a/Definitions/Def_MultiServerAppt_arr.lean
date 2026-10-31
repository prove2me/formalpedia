-- Prove2me | Definitions.Def_MultiServerAppt_arr
-- name    : MultiServerAppt_arr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:16.61558+00:00
-- url     : https://prove2.me/theorems/a091e5d8-1f89-4642-badf-6594f0f10950
-- title:
--   Arrival epochs $t_c$
-- statement:
--   The arrival epoch of client $c$ from the inter-arrival times:
--
--   $$t_c=\sum_{l=1}^{c-s}x_{s+l},$$
--
--   which is $0$ for $c\le s$, so that $t_1=\dots=t_s=0$.
--
--   **Formalization Note** Clients are 1-based natural numbers. The truncated subtraction $c-s$ is intended and gives the empty sum for $c\le s$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §1, p.2, and §5, p.17

import Mathlib

namespace MultiServerAppt

/-- The arrival epoch `t_c` of client `c` from the inter-arrival times: `t_c = ∑_{l=1}^{c-s} x_{s+l}`,
which is `0` for the first `s` clients. Kuiper–Lee, Appointment Scheduling for Multiple Servers,
SSRN 3975471, §1, p.2 and §5, p.17.

**Formalization Note** Clients are 1-based natural numbers, as on the page. The truncated subtraction
`c - s` is intended: it gives the empty sum, so `t_1 = ⋯ = t_s = 0`. -/
def arr (s : ℕ) (x : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (c - s), x (s + l)

end MultiServerAppt


