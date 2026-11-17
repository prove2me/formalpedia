-- Prove2me | Definitions.Def_CutRankSched_Supplement_CommSwap
-- name    : CutRankSched_Supplement_CommSwap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:42:55.067375+00:00
-- url     : https://prove2.me/theorems/5b0767d4-51ec-4948-8aff-25435085cfa5
-- title:
--   Adjacent commuting swaps of a trace order
-- statement:
--   For an instance with anticommutation matrix $A$, an **adjacent commuting swap** turns an ordering of the events $\ell_1\,a\,b\,\ell_2$ into $\ell_1\,b\,a\,\ell_2$, where $a,b$ are adjacent events with $A_{ab}=0$, i.e. their Pauli rotations commute. By Lemma 4.2 such a swap does not change the product of the rotations.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Lemma 4.2, p.6, and Theorem 4.8, p.7

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_A

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- One **adjacent commuting swap** of a trace order (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Lemma 4.2, p.6, and Theorem 4.8, p.7):
`l₁ ++ [a, b] ++ l₂ ↦ l₁ ++ [b, a] ++ l₂` for two adjacent events with `A_ab = 0`. -/
def CommSwap (I : Instance) (l l' : List (Fin I.n)) : Prop :=
  ∃ (l₁ l₂ : List (Fin I.n)) (a b : Fin I.n), A I a b = 0 ∧
    l = l₁ ++ a :: b :: l₂ ∧ l' = l₁ ++ b :: a :: l₂

end Supplement

end CutRankSched


