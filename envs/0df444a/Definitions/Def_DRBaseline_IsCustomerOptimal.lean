-- Prove2me | Definitions.Def_DRBaseline_IsCustomerOptimal
-- name    : DRBaseline_IsCustomerOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:24.951519+00:00
-- url     : https://prove2.me/theorems/624cc636-d02c-4c88-bd3c-4643ee0763cc
-- title:
--   Customer's problem $\max_{s\le\omega}C_c(s)$
-- statement:
--   A shift $s$ **solves the customer's problem** at baseline $b$, rebate $r$ and demand $\omega$ if
--
--   1. $s\le\omega$ (a customer cannot reduce its demand by more than its realization), and
--   2. $C_c(s')\le C_c(s)$ for every $s'\le\omega$.
--
--   The paper writes $s^*(b,r\mid\omega)=\arg\max_{s\le\omega}C_c(s)$ and $S^*=S(s^*)$.
--
--   **Formalization Note** The feasible set is exactly $s\le\omega$, as printed, with no lower bound. The maximizer is not always unique (there are ties at isolated values of $\omega$), so optimality is a predicate on $s$.
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, §3.3, p.9

import Mathlib
import Definitions.Def_DRBaseline_customerObj

namespace DRBaseline

/-- **`s` solves the customer's problem `max_{s ≤ ω} C_c(s)`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, §3.3, p.9: "max_{s≤ω} C_c(s) … The constraint s ≤ ω states that a customer cannot reduce
its demand by more than its realization. Finally, let s∗(b,r|ω) .= arg max_{s≤ω} C_c(s)".

`IsCustomerOptimal cs b r ω s` says that `s ≤ ω` and `C_c(s') ≤ C_c(s)` for every `s' ≤ ω`.

**Formalization Note** The feasible set is exactly `s ≤ ω`, as printed, with no lower bound.
The maximizer is not always unique (ties at `ω = ω_A`, `ω = ω_B`), so this is a predicate on
`s`, not a function. -/
def IsCustomerOptimal (cs b r ω s : ℝ) : Prop :=
  s ≤ ω ∧ ∀ s' : ℝ, s' ≤ ω → customerObj cs b r ω s' ≤ customerObj cs b r ω s

end DRBaseline


