-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_loopStep
-- name    : ConsensusHalvingItems_Additive_loopStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:31:43.818685+00:00
-- url     : https://prove2.me/theorems/3644829b-2a06-4b0c-be3c-057240219594
-- title:
--   One iteration of Step 3
-- statement:
--   One iteration of the while loop of Step 3 of the algorithm. It runs Step 3's test; if no solution $y \ne x$ of $S \cup T$ exists, the loop ends. Otherwise, with the returned $y$:
--
--   1. (Step 3a) for every item $j$ with $y_j \ne x_j$ it computes
--   $$
--   \gamma_j = \begin{cases} \dfrac{1 - x_j}{y_j - x_j} & \text{if } y_j > x_j, \\[2mm] \dfrac{x_j}{x_j - y_j} & \text{if } y_j < x_j; \end{cases}
--   $$
--   2. (Step 3b) $j^*$ is an index with the least $\gamma_j$, ties going to the lowest index;
--   3. (Step 3c) every $x_j$ is replaced by $s_j = (1 - \gamma_{j^*}) x_j + \gamma_{j^*} y_j$;
--   4. (Step 3d) $j^*$ is added to $T$.
--
--   All rational operations are charged by the cost model.
--
--   **Formalization Note** The result is `none` when the loop ends, and `some (T ∪ {j*}, s)` otherwise.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, Step 3, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_qadd
import Definitions.Def_ConsensusHalvingItems_Additive_qsub
import Definitions.Def_ConsensusHalvingItems_Additive_qmul
import Definitions.Def_ConsensusHalvingItems_Additive_qdiv
import Definitions.Def_ConsensusHalvingItems_Additive_qlt
import Definitions.Def_ConsensusHalvingItems_Additive_qeq
import Definitions.Def_ConsensusHalvingItems_Additive_findSolution

namespace ConsensusHalvingItems.Additive

/-- **One iteration of the while loop (Step 3).**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, Step 3, p. 5:

"3. While there exists a solution (y1, . . . , ym) ≠ (x1, . . . , xm) to S ∪ T, do the following:
(a) For every j ∈ M such that yj ≠ xj, compute γj := (1 − xj)/(yj − xj) if yj > xj;
xj/(xj − yj) if yj < xj.
(b) Let j∗ = argmin_{j∈M, yj≠xj} γj.
(c) For every j ∈ M, let sj := (1 − γj∗) · xj + γj∗ · yj, and update the value of xj to sj.
(d) Add the equation yj∗ = xj∗ to T."

`loopStep u T x` runs `findSolution u T x`. On `none` (no other solution: the loop ends) it
returns `none`. On `some y` it scans `j = 0, …, m - 1` (one tick each) and, for every `j` with
`y j ≠ x j`, computes `γ_j` as in (a); `j*` is the index of the least `γ_j`, ties going to
the lowest index; it computes `s_j = (1 - γ_{j*}) x_j + γ_{j*} y_j` for every `j` as in (c) and
returns `some (insert j* T, s)`. All rational operations are ticked.

**Formalization Note.** The argmin of (b) is not unique in general; the mission takes the lowest
index (Reading 3). `γ_j` is computed only where `y j ≠ x j`, so no division by zero occurs. If
`findSolution` returned `some y` with `y = x` (it does not, when `x` solves S ∪ T), the scan
finds no index and the step returns `none`. -/
def loopStep {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    StateM ℕ (Option (Finset (Fin m) × (Fin m → ℚ))) := do
  match ← findSolution u T x with
  | none => pure none
  | some y =>
    let best ← (List.finRange m).foldlM
      (fun (acc : Option (Fin m × ℚ)) (j : Fin m) => do
        tick 1
        let same ← qeq (y j) (x j)
        if same then pure acc
        else
          let up ← qlt (x j) (y j)
          let g ← if up then do
              let a ← qsub 1 (x j)
              let b ← qsub (y j) (x j)
              qdiv a b
            else do
              let b ← qsub (x j) (y j)
              qdiv (x j) b
          match acc with
          | none => pure (some (j, g))
          | some (_, g0) => do
            let lt ← qlt g g0
            pure (if lt then some (j, g) else acc))
      none
    match best with
    | none => pure none
    | some (js, g) =>
      let s ← (List.finRange m).mapM fun j => do
        tick 1
        let a ← qsub 1 g
        let p ← qmul a (x j)
        let q ← qmul g (y j)
        qadd p q
      pure (some (insert js T, fun j => s.getD j.val 0))

end ConsensusHalvingItems.Additive


