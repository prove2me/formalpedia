-- Prove2me | Definitions.Def_MultiServerAppt_State
-- name    : MultiServerAppt_State
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:55.604867+00:00
-- url     : https://prove2.me/theorems/a4f06ce1-2b34-4aea-ad06-52150660d17e
-- title:
--   The transient state space after client $s+i$
-- statement:
--   The transient states after client $s+i$ are the pairs $(j,m)$ with $1\le j\le s+i$ and $m:\{1,\dots,\min\{j,s\}\}\to\iota$. They split into the saturated states ($j>s$) and the unsaturated ones ($j\le s$).
--
--   **Formalization Note** The sum type replaces the dependent pairs of the page and is exactly the block decomposition of Eq. (14). The order of blocks on the page plays no role: vectors and matrices are functions of states.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11, and Eq. (12), p.12

import Mathlib
import Definitions.Def_MultiServerAppt_SatState
import Definitions.Def_MultiServerAppt_UnsatState

namespace MultiServerAppt

/-- The transient states `(j, m)`, `1 ≤ j ≤ s + i`, `m : Fin (min j s) → ι`, of the system after
client `s + i` has arrived: saturated states (`j > s`) on the left, unsaturated ones (`j ≤ s`) on the
right. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11 and
Eq. (12), p.12.

**Formalization Note** The sum type replaces the dependent pairs of the page and is the block
decomposition of Eq. (14). Block order is immaterial for a statement on a type: vectors and matrices
are functions of states, not positions. -/
abbrev State (ι : Type*) (s i : ℕ) : Type _ := SatState ι s i ⊕ UnsatState ι s

end MultiServerAppt


