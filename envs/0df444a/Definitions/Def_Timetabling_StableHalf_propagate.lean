-- Prove2me | Definitions.Def_Timetabling_StableHalf_propagate
-- name    : Timetabling_StableHalf_propagate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:03.303197+00:00
-- url     : https://prove2.me/theorems/43b7c863-25a4-4286-ba9e-d4216cf302d3
-- title:
--   Propagation of a decision, run to completion
-- statement:
--   Given a partial assignment $a$ and a node $v = (j, b)$ of an open pair, the **propagation of the decision** $v$ chooses $v$ (sets $a_j := b$), pushes $v$, and iterates the scan step $\mathsf{propStep}$ until the trial ends. It returns the final assignment $a'$ if the trial is done, and *failure* if it fails.
--
--   This is the operation the proof of Proposition 2.4 calls taking a decision and then considering "all the implications of this choice". The milestone *implications are forced* states what it computes.
--
--   **Formalization Note** The result is `Option (Fin n → Option Bool)` (`none` = failure). The iteration is bounded by the fuel $(n+1)(2n+2)$. At most $n$ nodes are ever pushed (each one is the chosen node of a pair that was open), each costing $2n + 1$ steps, plus one final step, so the fuel is never exhausted.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "Initially one arbitrary selects a schedule for some teacher (this is a decision); then one considers all the implications of this choice". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_propStep

namespace Timetabling.StableHalf

/-- **The propagation of one decision, run to its end.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4, p. 155:
"Initially one arbitrary selects a schedule for some teacher (this is a decision); then one
considers all the implications of this choice."

From the partial assignment `a`, the decision `v = (j, b)` chooses node `v` (sets `a j := some b`)
and pushes it; `propStep` is then iterated. The result is `some a'` when the trial ends `done a'`
(all implications taken into account) and `none` when it fails.

**Formalization Note.** The iteration is bounded by the fuel `(n + 1) * (2n + 2)`. Every node
pushed is the chosen node of a pair that was open, so at most `n` nodes are pushed, each costing
`2n + 1` steps, plus one final step: the fuel is never exhausted. Running out of fuel would also
return `none`. -/
def propagate {n : ℕ} (adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool)
    (a : Fin n → Option Bool) (v : Fin n × Bool) : StateM ℕ (Option (Fin n → Option Bool)) :=
  go ((n + 1) * (2 * n + 2)) (.running (Function.update a v.1 (some v.2)) [v] 0)
where
  /-- Iterate `propStep` with fuel. -/
  go : ℕ → Trial n → StateM ℕ (Option (Fin n → Option Bool))
    | _, .done a' => pure (some a')
    | _, .failed => pure none
    | 0, .running _ _ _ => pure none
    | f + 1, t@(.running _ _ _) => do
      let t' ← propStep adj t
      go f t'

end Timetabling.StableHalf


