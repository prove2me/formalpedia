-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_findSolution
-- name    : ConsensusHalvingItems_Additive_findSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:30:58.721757+00:00
-- url     : https://prove2.me/theorems/3edd19e9-24a3-41ed-963c-23aeb0412ee2
-- title:
--   Step 3's test: another solution of $S \cup T$, or none
-- statement:
--   Given the value matrix $u$, the frozen set $T$ and the current point $x$, this procedure
--
--   1. builds the rows of the homogeneous system of $S \cup T$: the row $(u_i(1), \dots, u_i(m))$ for every agent $i$ (each value read with its cost) and the unit row $e_j$ for every $j \in T$, in increasing order;
--   2. runs the Gaussian elimination of the mission on these rows;
--   3. if only the trivial solution exists it reports that there is none; otherwise, with $d$ the returned nonzero solution, it returns $y = x + d$ (each sum charged).
--
--   When $x$ solves $S \cup T$, the returned $y$ is a solution of $S \cup T$ different from $x$, and "none" means that $x$ is the unique solution. This is Step 3's test "while there exists a solution $(y_1, \dots, y_m) \ne (x_1, \dots, x_m)$ to $S \cup T$", carried out as in footnote 5.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, Step 3, ¶2 and footnote 5, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_uAt
import Definitions.Def_ConsensusHalvingItems_Additive_qadd
import Definitions.Def_ConsensusHalvingItems_Additive_kernelDir

namespace ConsensusHalvingItems.Additive

/-- **Step 3's test: another solution of S ∪ T, or none.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, p. 5: "Finding a solution (y1, . . . , ym) to S ∪
T that is not equal to (x1, . . . , xm) or determining that such a solution does not exist (Step
3) can be done in polynomial time via Gaussian elimination", and footnote 5.

Given the value matrix `u`, the frozen set `T` and the current point `x` (a solution of
S ∪ T), `findSolution u T x`

1. builds the rows of the homogeneous system of S ∪ T: the row `j ↦ u i j` for each agent `i`
   (each entry read through `uAt`), then the unit row `Pi.single j 1` for each `j ∈ T` in
   increasing order of `j` (one tick per index scanned);
2. runs `kernelDir` on these rows; on `none` it returns `none`;
3. on `some d` it returns `some y` with `y j = x j + d j` (`qadd`).

When `x` solves S ∪ T, `y` is a solution of S ∪ T different from `x` (`d` is a nonzero
solution of the homogeneous system), and `none` means that `x` is the unique solution.

**Formalization Note.** Footnote 5 sets "one of the non-pivots yj to be an arbitrary number not
equal to xj"; here the lowest non-pivot gets `x_j + 1` and the other non-pivots keep `x_j`
(Reading 3). -/
def findSolution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    StateM ℕ (Option (Fin m → ℚ)) := do
  let urows ← (List.finRange n).mapM fun i => do
    let r ← (List.finRange m).mapM fun j => uAt u i j
    pure fun j : Fin m => r.getD j.val 0
  let trows ← (List.finRange m).filterMapM fun j => do
    tick 1
    pure (if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
  match ← kernelDir (urows ++ trows) with
  | none => pure none
  | some d =>
    let y ← (List.finRange m).mapM fun j => qadd (x j) (d j)
    pure (some fun j => y.getD j.val 0)

end ConsensusHalvingItems.Additive


