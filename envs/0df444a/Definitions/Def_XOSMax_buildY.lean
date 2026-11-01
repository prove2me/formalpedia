-- Prove2me | Definitions.Def_XOSMax_buildY
-- name    : XOSMax_buildY
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:23.385285+00:00
-- url     : https://prove2.me/theorems/9664f038-b30b-4afc-ade1-abd4c4c9d45c
-- title:
--   The candidate $Y_i$ (Line 7 of Algorithm 4)
-- statement:
--   Given the ground list and a set $V'$, this program computes
--   $$
--   Y\leftarrow V'\cup\{\,v\in V\setminus V'\ :\ f(V'+v)>f(V')\,\},
--   $$
--   with a strict inequality. This is Line 7 of Algorithm 4 and Line 8 of Algorithm 3: it adds to a clique all the elements with an additional positive contribution.
--
--   **Formalization Note** Charges: $n$ steps to copy $V'$, one oracle call for $f(V')$, and per element a step for the membership test and, outside $V'$, a step for $V'+v$, an oracle call, a step for the comparison and a step for an insertion. The value $f(V')$ is stored once.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 4, Line 7, p.7; Algorithm 3, Line 8, p.6

import Mathlib
import Definitions.Def_XOSMax_OracleProg

namespace XOSMax

open OracleProg

variable {E : Type} [DecidableEq E]

/-- One element `v` of the scan of `buildY`, where `b` is the stored value `f(V')`: the elements of
`V \ V'` with `f(V' + v) > f(V')` are added to the set `Y'` being built. -/
noncomputable def buildYStep (V' : Finset E) (b : ℝ) (Y' : Finset E) (v : E) :
    OracleProg E (Finset E) := do
  tick
  if v ∈ V' then
    pure Y'
  else
    tick
    let a ← ask (insert v V')
    tick
    if b < a then
      tick
      pure (insert v Y')
    else
      pure Y'

/-- Line 7 of Algorithm 4 and Line 8 of Algorithm 3:
`Y ← V' ∪ { v ∈ V \ V' | f(V' + v) > f(V') }`, with a **strict** inequality
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Algorithm 4, p.7; Algorithm 3, p.6).

**Formalization Note** Charges: `n` steps to copy `V'`, one oracle call for `f(V')`, and for each
element a step for the loop and the membership test, then a step for `V' + v`, an oracle call, a step
for the comparison, and a step for the insertion when it succeeds. This is the "O(n) time (including
O(n) value oracle calls) for each i" of the proof of Lemma 11, p.7. -/
noncomputable def buildY (L : List E) (V' : Finset E) : OracleProg E (Finset E) := do
  ticks L.length
  let b ← ask V'
  L.foldlM (buildYStep V' b) V'

end XOSMax


