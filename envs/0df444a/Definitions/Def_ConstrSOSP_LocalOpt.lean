-- Prove2me | Definitions.Def_ConstrSOSP_LocalOpt
-- name    : ConstrSOSP_LocalOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:55.999204+00:00
-- url     : https://prove2.me/theorems/11b02be7-328e-421c-940e-851629317414
-- title:
--   LocalOpt (Definition 4.1)
-- statement:
--   **LocalOpt.** *Input:* Boolean circuits $p,g:[2^n]\to[2^n]$ ($p$ is the potential and $g$ the neighbour function). *Goal:* find $v\in[2^n]$ with
--   $$
--   p(g(v))\ \ge\ p(v).
--   $$
--   The paper defines PLS as the class of TFNP problems that reduce to LocalOpt (p.17).
--
--   **Formalization Note** An instance is the code of two well-formed circuits with the same $n$; an answer is an $n$-bit string naming $v$. The search problem is the public `TetrisHard.Rows.SearchProblem`.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.1, p.17

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_app
import Definitions.Def_ConstrSOSP_encCircuit

namespace ConstrSOSP

/-- **LocalOpt** (arXiv:2604.02285, 2 Nov 2026, Definition 4.1, p.17): "Input: Boolean circuits
p, g : [2^n] → [2^n]. (p is the potential function and g is the neighbor function) Goal: Find
v ∈ [2^n] such that p(g(v)) ≥ p(v)." PLS is "the complexity class which contains all TFNP
problems that reduce to the PLS-complete Localopt problem" (p.17).

* An instance is the code `encCircuit p ++ encCircuit g` of two well-formed circuits with the same
  number `n` of inputs.
* An answer is an `n`-bit string `t`, naming the node `v = nodeOf t`, with `p(g(v)) ≥ p(v)` as
  integers.

**Formalization Note** `[2ⁿ] = {1, …, 2ⁿ}` with `n`-bit strings read as `1 + binary value`
(`nodeOf`). The search problem is the public `TetrisHard.Rows.SearchProblem`. -/
def LocalOpt : TetrisHard.Rows.SearchProblem where
  valid s := ∃ p g : Circuit, p.WF ∧ g.WF ∧ p.n = g.n ∧ s = encCircuit p ++ encCircuit g
  answer s t := ∃ p g : Circuit, p.WF ∧ g.WF ∧ p.n = g.n ∧ s = encCircuit p ++ encCircuit g ∧
    t.length = p.n ∧ p.app (nodeOf t) ≤ p.app (g.app (nodeOf t))

end ConstrSOSP


