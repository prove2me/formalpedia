-- Prove2me | Definitions.Def_MultiServerAppt_UnsatState
-- name    : MultiServerAppt_UnsatState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:11.918365+00:00
-- url     : https://prove2.me/theorems/45b3f679-8914-4b9a-9c57-67617add949d
-- title:
--   Unsaturated nonempty states of the system
-- statement:
--   An unsaturated state is a pair $(\xi,m)$ with $\xi\in\{0,\dots,s-1\}$ and $m:\{1,\dots,\xi+1\}\to\iota$. It stands for $j=\xi+1\le s$ clients in the system, all in service, in phases $m$. These are the blocks $j=s,\dots,1$ of Eqs. (8) and (11).
--
--   **Formalization Note** The empty system $j=0$ is the absorbing state of the chain and not a state of the matrix, as on p.13.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11

import Mathlib

namespace MultiServerAppt

/-- The nonempty unsaturated states: `⟨ξ, m⟩` means `j = ξ + 1 ≤ s` clients are in the system, all
in service, and `m` lists their phases. These are the blocks `j = s, …, 1` of Eqs. (8), (11).
Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11, with
`min{j, s} = j`.

**Formalization Note** The empty system `j = 0` is the absorbing state, not a state of the matrix,
as on p.13. -/
abbrev UnsatState (ι : Type*) (s : ℕ) : Type _ := Σ ξ : Fin s, (Fin (ξ + 1) → ι)

end MultiServerAppt


