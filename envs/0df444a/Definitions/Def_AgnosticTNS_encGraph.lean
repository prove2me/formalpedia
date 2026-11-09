-- Prove2me | Definitions.Def_AgnosticTNS_encGraph
-- name    : AgnosticTNS_encGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:06.86018+00:00
-- url     : https://prove2.me/theorems/f41ab7c6-8e8d-43d5-9be5-cd6db60f6356
-- title:
--   Graph as an input string
-- statement:
--   A graph on $[n]$ is written as its adjacency matrix, row by row. The graph is an input of the learner.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1, p.19

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace AgnosticTNS

/-- **A graph on `[n]` as an input string**, for the learner indices of Theorem 3.6 and
Corollaries 5.1, 5.2 (the graph is an input, p.19) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): its adjacency matrix, row by row. -/
noncomputable def encGraph {n : ℕ} (G : SimpleGraph (Fin n)) : QAlgorithms.Complexity.Str := by
  classical
  exact ((List.finRange n).map fun u => (List.finRange n).map fun v => decide (G.Adj u v)).flatten

end AgnosticTNS


