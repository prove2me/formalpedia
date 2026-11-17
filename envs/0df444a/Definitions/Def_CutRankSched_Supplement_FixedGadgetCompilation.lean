-- Prove2me | Definitions.Def_CutRankSched_Supplement_FixedGadgetCompilation
-- name    : CutRankSched_Supplement_FixedGadgetCompilation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:43:22.537194+00:00
-- url     : https://prove2.me/theorems/5b6ab5e6-c22f-4cef-a3a8-a12dac64d090
-- title:
--   Compilations in the fixed-gadget class
-- statement:
--   A **fixed-gadget compilation** of an instance is a sequence of rounds $S_1,\dots,S_k$, each a list of events, such that
--
--   1. the concatenation $S_1S_2\cdots S_k$ is obtained from the input trace order $1,\dots,n$ by finitely many adjacent commuting swaps (so it retains every extracted rotation exactly once, and changes the trace by adjacent commuting swaps only), and
--   2. any two distinct events in one round have vertex-disjoint prescribed exposure regions, $V(T_i)\cap V(T_j)=\emptyset$.
--
--   Each event uses its prescribed exposure gadget $T_i$. The number of non-Clifford rounds of the compilation is $k$.
--
--   **Formalization Note** The class is stated combinatorially, as in the proof of Theorem 4.8. Empty rounds are allowed and counted; they never lower the minimum.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 4.8, p.7

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Supplement_CommSwap

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- A compilation in the **fixed-gadget compilation class** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 4.8, p.7), given by its
rounds `R = [S₁, …, S_k]` (each a list of events, in order): the concatenation `S₁ ++ ⋯ ++ S_k` is
obtained from the input trace order `1, …, n` by adjacent commuting swaps only (so each extracted
rotation is retained exactly once), and any two distinct events of one round have vertex-disjoint
prescribed exposure regions. Its number of non-Clifford rounds is `k`.

**Formalization Note** Events are 0-based (`List.finRange n`). Each event carries its prescribed
exposure `T_i` by construction. Empty rounds are allowed and counted; they never help to
minimize. -/
def FixedGadgetCompilation (I : Instance) (R : List (List (Fin I.n))) : Prop :=
  Relation.ReflTransGen (CommSwap I) (List.finRange I.n) R.flatten ∧
    ∀ S ∈ R, ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (I.T i).verts (I.T j).verts

end Supplement

end CutRankSched


