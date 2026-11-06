-- Prove2me | Definitions.Def_ConstrSOSP_Iter
-- name    : ConstrSOSP_Iter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:56.981454+00:00
-- url     : https://prove2.me/theorems/c0a90b1f-062c-459b-98db-7c88b5a94840
-- title:
--   Iter (Definition 4.2)
-- statement:
--   **Iter.** *Input:* a Boolean circuit $C:[2^n]\to[2^n]$ with $C(1)>1$. *Goal:* find $v\in[2^n]$ such that either
--
--   1. $C(v)<v$, or
--   2. $C(v)>v$ and $C(C(v))=C(v)$.
--
--   Iter is the PLS-complete problem from which the paper's hardness reduction starts.
--
--   **Formalization Note** An instance is the code of a well-formed circuit with $C(1)>1$; an answer is an $n$-bit string naming $v$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.2, p.18

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_app
import Definitions.Def_ConstrSOSP_encCircuit

namespace ConstrSOSP

/-- **Iter** (arXiv:2604.02285, 2 Nov 2026, Definition 4.2, p.18): "Input: Boolean circuit
C : [2^n] → [2^n] with C(1) > 1. Goal: Find v ∈ [2^n] such that either • C(v) < v, or
• C(v) > v and C(C(v)) = C(v)."

* An instance is the code `encCircuit C` of a well-formed circuit with `C(1) > 1`.
* An answer is an `n`-bit string `t`, naming the node `v = nodeOf t`, with `C(v) < v`, or
  `C(v) > v` and `C(C(v)) = C(v)`.

**Formalization Note** `[2ⁿ] = {1, …, 2ⁿ}` with `n`-bit strings read as `1 + binary value`
(`nodeOf`); `C(1) > 1` forces `n ≥ 1`. -/
def Iter : TetrisHard.Rows.SearchProblem where
  valid s := ∃ C : Circuit, C.WF ∧ s = encCircuit C ∧ 1 < C.app 1
  answer s t := ∃ C : Circuit, C.WF ∧ s = encCircuit C ∧ t.length = C.n ∧
    (C.app (nodeOf t) < nodeOf t ∨
      (nodeOf t < C.app (nodeOf t) ∧ C.app (C.app (nodeOf t)) = C.app (nodeOf t)))

end ConstrSOSP


