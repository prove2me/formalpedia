-- Prove2me | Definitions.Def_CloudCostOpt_State
-- name    : CloudCostOpt_State
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:11.495898+00:00
-- url     : https://prove2.me/theorems/d9f03d45-c9a4-4106-95ce-089d95f79e49
-- title:
--   System state $x_t=(x_{i,t}(s,l))$
-- statement:
--   The **system state** at the beginning of a period is the array of counts $x_{i}(s,l)\in\mathbb N$: the number of type-$i$ orders that arrived $s+1$ periods earlier and have completed $l$ steps (the orders in **order-state** $(s,l)$).
--
--   **Formalization Note** The state is a function on all triples $(i,s,l)$. Along every trajectory it vanishes outside the paper's index set $l\le s\le t-2$, $0\le l\le L_i-1$.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.4 (State of the System)

import Mathlib
import Definitions.Def_CloudCostOpt_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **System state** `x_t = (x_{i,t}(s, l))` (p.4): `x i s l` is the number of type-`i` orders in
order-state `(s, l)`, i.e. that arrived `s + 1` periods earlier and have completed `l` steps.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.4 ("State of the System").

Formalization Note: the state is a function on all of `Fin I × ℕ × ℕ`; along every trajectory it
vanishes off the paper's index set `l ≤ s ≤ t − 2`, `l ≤ Lᵢ − 1` (see `history`). -/
abbrev State (S : System) : Type := Fin S.I → ℕ → ℕ → ℕ

end CloudCostOpt


