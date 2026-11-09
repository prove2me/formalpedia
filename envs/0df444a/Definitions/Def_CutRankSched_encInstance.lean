-- Prove2me | Definitions.Def_CutRankSched_encInstance
-- name    : CutRankSched_encInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:31:24.57952+00:00
-- url     : https://prove2.me/theorems/23158559-db26-43af-a0f6-0dbb73fcb05e
-- title:
--   Bit encoding of an instance
-- statement:
--   The **input encoding** of an instance is a self-delimiting bit string listing, in order: $m$ and $n$ in unary; the adjacency matrix of $H$ row by row; the $x$-bits and the $z$-bits of every $p_i$; the signs $\epsilon_i$; the vertex set of every $T_i$; and the adjacency matrix of every $T_i$. Each list is framed in the format of the published `SubexponentialSAT` encoding.
--
--   Its length is $O(nm^2)$, polynomial in $(n, m)$, and distinct instances get distinct codes.
--
--   **Formalization Note** The bits of the sets and relations are classical decisions, which is harmless in a statement.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Problem 3.2, p.5 (the input: H and the ordered events)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_CutRankSched_Instance

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace CutRankSched

/-- The input encoding of an instance (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Problem 3.2, p.5: "Given H, the ordered events
(p_i, ε_i, T_i)"), as a self-delimiting bit string in the published `SubexponentialSAT` format:
`m` and `n` in unary (`encodeNat`), the adjacency matrix of `H` row by row, the `x`- and
`z`-bits of each `p_i`, the signs, the vertex sets of the `T_i`, and the adjacency matrices of
the `T_i`, each list framed by `encodeList`.

**Formalization Note** The bits of the sets and relations are classical `decide`s; the encoding
is injective (checked in the sanity file). Its length is `O(nm²)`, polynomial in `(n, m)`. -/
noncomputable def encInstance (I : Instance) : List Bool := by
  classical
  exact Encoding.encodeList id
    [Encoding.encodeNat I.m, Encoding.encodeNat I.n,
      Encoding.encodeList id (List.ofFn fun a : Fin I.m => List.ofFn fun b : Fin I.m =>
        decide (I.H.Adj a b)),
      Encoding.encodeList id (List.ofFn fun i : Fin I.n => List.ofFn fun q : Fin I.m =>
        decide ((I.p i).1 q = 1)),
      Encoding.encodeList id (List.ofFn fun i : Fin I.n => List.ofFn fun q : Fin I.m =>
        decide ((I.p i).2 q = 1)),
      List.ofFn I.sign,
      Encoding.encodeList id (List.ofFn fun i : Fin I.n => List.ofFn fun q : Fin I.m =>
        decide (q ∈ (I.T i).verts)),
      Encoding.encodeList (Encoding.encodeList id) (List.ofFn fun i : Fin I.n =>
        List.ofFn fun a : Fin I.m => List.ofFn fun b : Fin I.m => decide ((I.T i).Adj a b))]

end CutRankSched


