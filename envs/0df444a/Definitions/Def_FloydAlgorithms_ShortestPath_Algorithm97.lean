-- Prove2me | Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm97
-- name    : FloydAlgorithms_ShortestPath_Algorithm97
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:08:56.626972+00:00
-- url     : https://prove2.me/theorems/b4d1a0e9-07f9-44a2-9768-134bb3be5865
-- title:
--   Algorithm 97, Shortest Path, as an in-place matrix procedure
-- statement:
--   Algorithm 97 receives the direct-link length matrix $w$. Its current matrix $m$ is changed in place while pivot $i$, row $j$, and column $k$ run in that order. The column scan is entered only when $m(j,i)<\infty$; for each column with $m(i,k)<\infty$, the entry $m(j,k)$ is replaced by $m(j,i)+m(i,k)$ exactly when that sum is strictly smaller.
--
--   $$
--   m(j,k)\leftarrow m(j,i)+m(i,k)\quad\text{if }m(j,i)+m(i,k)<m(j,k).
--   $$
--
--   This is the procedure whose final matrix the main theorem identifies with shortest path lengths.
--
--   **Formalization Note** The outer row guard is evaluated once, and $m(j,i)$ is read afresh for each column. Each update is visible immediately. The paper's `inf := ₁₀10` is represented by $\infty$ rather than a finite bound, and its ALGOL `real` operations are modeled by exact real arithmetic.
-- source:
--   Floyd, Algorithm 97: Shortest Path, Communications of the ACM 5(6) (1962), p. 345, procedure body; https://doi.org/10.1145/367766.368168

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network

namespace FloydAlgorithms.ShortestPath

/-- The column loop of Algorithm 97. The entry `m j i` is re-read for every
column, while the outer row guard is evaluated once. -/
noncomputable def rowSweep {n : ℕ} (i j : Fin n) (m : LengthMatrix n) : LengthMatrix n :=
  if m j i < ⊤ then
    (List.finRange n).foldl (fun m k =>
      if m i k < ⊤ then
        let s := m j i + m i k
        if s < m j k then Function.update m j (Function.update (m j) k s)
        else m
      else m) m
  else m

/-- Algorithm 97, `shortest path`, preserving the printed in-place loop order. -/
noncomputable def algorithm97 {n : ℕ} (w : LengthMatrix n) : LengthMatrix n :=
  (List.finRange n).foldl (fun m i =>
    (List.finRange n).foldl (fun m j => rowSweep i j m) m) w

end FloydAlgorithms.ShortestPath


