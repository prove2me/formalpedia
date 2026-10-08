-- Prove2me | Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96
-- name    : FloydAlgorithms_ShortestPath_Algorithm96
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:48:55.244293+00:00
-- url     : https://prove2.me/theorems/d58bc970-ed4c-4ed0-8cd2-befd508cdf78
-- title:
--   Algorithm 96, Ancestor, on Boolean matrices
-- statement:
--   Given an $n\times n$ Boolean matrix $b$, Algorithm 96 regards $b(i,j)$ as saying that individual $i$ is a parent of individual $j$. It scans pivot $i$, row $j$, and column $k$ in that order. When the current entry $b(j,i)$ is true, it scans the row and sets $b(j,k)$ to true whenever the current entry $b(i,k)$ is true.
--
--   $$
--   b(j,k)\leftarrow\mathrm{true}\quad\text{if }b(j,i)\text{ and }b(i,k)\text{ are true}.
--   $$
--
--   This definition is the exact in-place Boolean procedure whose output is characterized by the Algorithm 96 milestone.
--
--   **Formalization Note** The row guard is tested once before the column loop; each later matrix read sees preceding updates. Indices are zero-based and the initial diagonal is unrestricted.
-- source:
--   Floyd, Algorithm 96: Ancestor, Communications of the ACM 5(6) (1962), pp. 344–345, procedure body; https://doi.org/10.1145/367766.368168

import Mathlib

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 96, `ancestor`: the Boolean matrix is updated in place in
pivot, row, column order. -/
def algorithm96 {n : ℕ} (b : Fin n → Fin n → Bool) : Fin n → Fin n → Bool :=
  (List.finRange n).foldl (fun m i =>
    (List.finRange n).foldl (fun m j =>
      if m j i then
        (List.finRange n).foldl (fun m k =>
          if m i k then Function.update m j (Function.update (m j) k true)
          else m) m
      else m) m) b

end FloydAlgorithms.ShortestPath


