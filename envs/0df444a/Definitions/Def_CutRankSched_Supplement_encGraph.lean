-- Prove2me | Definitions.Def_CutRankSched_Supplement_encGraph
-- name    : CutRankSched_Supplement_encGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:49:57.342262+00:00
-- url     : https://prove2.me/theorems/a7730cb6-b5cb-4c46-9eba-128c9685978a
-- title:
--   The input encoding of a finite simple graph
-- statement:
--   A finite simple graph $G$ on the vertex set $\{0,\dots,N-1\}$ is encoded as a self-delimiting bit string: $N$ in unary followed by the adjacency matrix row by row, in the list format of the published machine model (the same format the base encoding uses for the hardware graph).
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 7.1, p.14

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace CutRankSched

namespace Supplement

/-- The input encoding of a finite simple graph `G` on `V = {0, …, N−1}` (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 7.1, p.14:
"Given any finite simple graph `G = (V, E)`"): `N` in unary (`encodeNat`) and the adjacency matrix
row by row, framed by `encodeList` in the published `SubexponentialSAT` format (as the base
`encInstance` encodes `H`). -/
noncomputable def encGraph {N : ℕ} (G : SimpleGraph (Fin N)) : List Bool := by
  classical
  exact Encoding.encodeList id
    [Encoding.encodeNat N,
      Encoding.encodeList id (List.ofFn fun a : Fin N => List.ofFn fun b : Fin N =>
        decide (G.Adj a b))]

end Supplement

end CutRankSched


