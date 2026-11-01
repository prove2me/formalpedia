-- Prove2me | Definitions.Def_XOSMax_growClique
-- name    : XOSMax_growClique
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:31.670521+00:00
-- url     : https://prove2.me/theorems/d0ae0acb-d81c-4a41-bf5a-a1a2d5676004
-- title:
--   Growing a set from one element (Lines 4–6 of Algorithm 4)
-- statement:
--   This program implements the inner loop shared by Algorithms 3 and 4. Given the ground list $L$ and an element $v$, it sets $V'\leftarrow\{v\}$ and scans every $u\in V-v$ in the order of $L$, performing
--   $$
--   \text{if } f(V'+u)=f(V')+f(u)\text{ then } V'\leftarrow V'+u ,
--   $$
--   with the current $V'$ at each test. It returns the final $V'$.
--
--   The scan covers all of $V-v$, including elements that lie in earlier cliques: cliques overlap.
--
--   **Formalization Note** The equality is tested from three oracle answers, as a comparison of real numbers (unit-cost real model). Charges per element: a step for the loop, a step for forming $V'+u$, three oracle calls, a step for the arithmetic and the comparison, and a step for an insertion.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 4, Lines 4–6, p.7; Algorithm 3, Lines 1–3 and 5–7, p.6

import Mathlib
import Definitions.Def_XOSMax_OracleProg

namespace XOSMax

open OracleProg

variable {E : Type} [DecidableEq E]

/-- One iteration of Lines 6 and 3/7: the element `u` of the scan `foreach u ∈ V − v`, on the current
set `V'`. The test is `f(V' + u) = f(V') + f(u)`, evaluated from three oracle answers, with the
current `V'` (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Algorithm 4, Line 6, p.7).

**Formalization Note** Charges: one step for the loop iteration and the test `u ≠ v`, one step for
forming `V' + u`, three oracle calls, one step for adding and comparing the answers, and one step for
the insertion when the test passes. -/
noncomputable def growStep (v : E) (V' : Finset E) (u : E) : OracleProg E (Finset E) := do
  tick
  if u = v then
    pure V'
  else
    tick
    let a ← ask (insert u V')
    let b ← ask V'
    let c ← ask {u}
    tick
    if a = b + c then
      tick
      pure (insert u V')
    else
      pure V'

/-- Lines 4–6 of Algorithm 4 (and Lines 1–3, 5–7 of Algorithm 3), once `v` is picked: start from
`{v}` and scan **all** of `V − v` in the order of `L`, adding `u` whenever
`f(V' + u) = f(V') + f(u)` (arXiv:1811.09045v3, Algorithm 4, p.7; Algorithm 3, p.6).

**Formalization Note** The ground set is the list `L`, and "foreach" is the order of `L`. The scan
does not skip elements that earlier cliques cover. -/
noncomputable def growClique (L : List E) (v : E) : OracleProg E (Finset E) := do
  tick
  L.foldlM (growStep v) {v}

end XOSMax


