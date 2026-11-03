-- Prove2me | Definitions.Def_NearestDSM_IsConnectedMat
-- name    : NearestDSM_IsConnectedMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:32.925314+00:00
-- url     : https://prove2.me/theorems/90344b4e-9c87-4cda-8c8c-18d1035b48b8
-- title:
--   Connected matrices
-- statement:
--   A matrix $X\in\mathbb R^{m\times n}$ is **connected** if its bipartite row–column graph $G$ (rows and columns as nodes, an edge for every nonzero entry) is connected, and **disconnected** otherwise.
--
--   For instance, the $2\times 2$ identity matrix is disconnected, and a matrix with all entries nonzero is connected.
--
--   **Formalization Note** Connectedness is Mathlib's `SimpleGraph.Connected` of the bipartite graph.
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, §2.1, p.7

import Mathlib
import Definitions.Def_NearestDSM_bipGraph

namespace NearestDSM

/-- A matrix is **connected**, Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, §2.1, p.7, "if the graph G is connected", where
`G` is its bipartite graph of rows and columns (`bipGraph`). -/
def IsConnectedMat {m k : Type*} (M : Matrix m k ℝ) : Prop :=
  (bipGraph M).Connected

end NearestDSM


