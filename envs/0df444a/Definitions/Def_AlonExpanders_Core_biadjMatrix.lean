-- Prove2me | Definitions.Def_AlonExpanders_Core_biadjMatrix
-- name    : AlonExpanders_Core_biadjMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:46:04.141009+00:00
-- url     : https://prove2.me/theorems/dd936603-b579-4cde-8ef1-857d8a249b02
-- title:
--   The $I \times O$ binary matrix $C$ of a bipartite graph
-- statement:
--   Let $G$ be a graph on the vertex set $I \sqcup O$. Its **binary matrix** is the $I \times O$ real matrix $C = (c_{io})_{i \in I,\, o \in O}$ with
--
--   $$
--   c_{io} = \begin{cases} 1 & \text{if } io \in E, \\ 0 & \text{otherwise.} \end{cases}
--   $$
--
--   For a bipartite graph $G = (I, O; E)$ the adjacency matrix is $\begin{pmatrix} 0 & C \\ C^{T} & 0 \end{pmatrix}$, so the spectrum of $C^{T}C$ determines the Laplacian spectrum of a regular bipartite graph. It is used to state the eigenvalue step of the proof of Lemma 3.3.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 92, proof of Lemma 3.3 (the matrix C = (c_io))

import Mathlib

namespace AlonExpanders.Core

/-- The `I × O` binary matrix `C = (c_{io})` of a graph on `I ⊕ O` (Alon, *Eigenvalues and
expanders*, Combinatorica 6 (1986), proof of Lemma 3.3, p. 92): `c_{io} = 1` if `io` is an edge
and `0` otherwise. -/
def biadjMatrix {I O : Type} (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] : Matrix I O ℝ :=
  Matrix.of fun i o => if G.Adj (Sum.inl i) (Sum.inr o) then 1 else 0

end AlonExpanders.Core


