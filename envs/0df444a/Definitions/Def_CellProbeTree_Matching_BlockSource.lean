-- Prove2me | Definitions.Def_CellProbeTree_Matching_BlockSource
-- name    : CellProbeTree_Matching_BlockSource
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:34.911994+00:00
-- url     : https://prove2.me/theorems/8e599d56-76f2-493e-9ed5-bc609e962b77
-- title:
--   The $d$-block LR source with a fixed Dyck padding word
-- statement:
--   Fix block parameters $u, a, b$ and a number $d$ of blocks, and a fixed Dyck word $Y$ of $z$ pairs. For block inputs $x_1, \dots, x_d$ (each a pair of forests and an interleaving word, as in the LR block), the **source word** is the concatenation
--   $$W(x_1)\,W(x_2)\cdots W(x_d)\,Y$$
--   of the $d$ block words at fixed boundaries followed by $Y$. Choosing $x_1,\dots,x_d$ independently and uniformly among all block inputs gives the uniform $d$-block source of Proposition 4.3; its length is $N = 2(dB + z)$ with $B = a + b + 2u$.
--
--   **Formalization Note.** `sourceWord u a b d Y x` is the word for `x : Fin d → blockInputs u a b`. `wordBits N x` reads a word as its bracket pattern on positions $0,\dots,N-1$ (`true` at an opening); it is injective on words of length exactly $N$, and is used only to give the source a finite codomain for Shannon entropy.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 19, Proposition 4.3

import Mathlib
import Definitions.Def_CellProbeTree_Matching_LRBlock

/-!
# The `d`-block LR source

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, Proposition 4.3, p. 19.

`d` independent blocks with parameters `u, a, b` at fixed boundaries, followed by a fixed Dyck word
`Y`: the input word is `W_1 W_2 ⋯ W_d Y`, where `W_k` is the block word of the `k`-th block input.
Choosing the block inputs uniformly gives the uniform source of Proposition 4.3.

**Formalization Note.** To take entropies with a finite codomain, a word is also read as its
bracket pattern on the first `N` positions, `true` for an opening (`wordBits`); on words of length
exactly `N` this is injective.
-/

namespace CellProbeTree.Matching

/-- The word built from `d` block inputs followed by the fixed padding word `Y`. -/
def sourceWord (u a b d : ℕ) (Y : List DyckStep) (x : Fin d → ↥(blockInputs u a b)) :
    List DyckStep :=
  (List.ofFn fun k => blockWord u (x k).1.1 (x k).1.2.1 (x k).1.2.2).flatten ++ Y

/-- The bracket pattern of a word on positions `0, …, N-1`: `true` at an opening. -/
def wordBits (N : ℕ) (x : List DyckStep) : Fin N → Bool :=
  fun i => decide (x.getD i.1 DyckStep.D = DyckStep.U)

end CellProbeTree.Matching


