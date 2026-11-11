-- Prove2me | Definitions.Def_NecklacePPAD_Main_NSCounts
-- name    : NecklacePPAD_Main_NSCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:06:24.170854+00:00
-- url     : https://prove2.me/theorems/2d36f152-3c29-4a28-9e6a-e7120db1be2f
-- title:
--   The search problem Necklace-Splitting restricted to colour counts in A
-- statement:
--   The binary code of a necklace is $n$ and $N$ in self-delimiting binary (`encBin`), followed by the colour index of every bead. `NSCounts A` is the finite-string search problem (`TetrisHard.Rows.SearchProblem`) whose valid strings are codes of necklaces in which every colour $c$ of `Fin n` occurs an even number of times and that number lies in $A$, and whose answers on such a string are the codes of splits (the $N$ labels as a list of bits). Thus `NSCounts {10}` is Necklace-Splitting$_{10}$, `NSCounts {2 * b}` is Necklace-Splitting$_{2b}$, and `NSCounts {6, 8, 10}` is Necklace-Splitting restricted to necklaces in which every colour occurs 6, 8 or 10 times. Because every colour of `Fin n` must occur (its count lies in $A$, and $0\notin A$ in every use), $n$ is the number of colours of the word, as in "at most $n$ cuts".
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Definition 3.1, p. 5 (PDF 7), and Theorem 1.1, p. 1 (PDF 3)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Necklace
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

set_option autoImplicit false

namespace NecklacePPAD.Main

open QAlgorithms.LocalHamiltonian

/-- Binary code of a necklace: the number `n` of colours and the number `N` of beads in
self-delimiting binary (`encBin`), then the colour index of every bead in order. -/
def Necklace.code (a : Necklace) : List Bool :=
  encBin a.n ++ encBin a.beads.length ++ a.beads.flatMap (fun c => encBin c.val)

/-- **The search problem Necklace-Splitting restricted to colour counts in `A`** (Zeng, Wang, Cao,
Dai, Wang, STOC 2027 submission, sha256 d5b5449c…, Definition 3.1, p. 5 (PDF 7), and Theorem 1.1,
p. 1 (PDF 3)). Valid strings are codes of necklaces with colours `Fin n` in which every colour
occurs an even number of times and that number lies in `A`; an answer is the code of a split
(the labels of positions `1, …, N` as a list of bits).

`NSCounts {2 * b}` is Necklace-Splitting₂b, `NSCounts {10}` is Necklace-Splitting₁₀, and
`NSCounts {6, 8, 10}` is Necklace-Splitting restricted to necklaces in which every colour occurs
6, 8 or 10 times.

**Formalization Note** Every colour of `Fin n` must occur (its count lies in `A`, and `0 ∉ A` in
every use), so `n` is the number of colours of the word, as in "at most `n` cuts". -/
def NSCounts (A : Set ℕ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ a : Necklace, a.IsNecklace ∧ (∀ c : Fin a.n, a.beads.count c ∈ A) ∧ s = a.code
  answer s t := ∃ a : Necklace, a.IsNecklace ∧ (∀ c : Fin a.n, a.beads.count c ∈ A) ∧
    s = a.code ∧ ∃ ℓ : Fin a.N → Bool, a.IsSplit ℓ ∧ t = List.ofFn ℓ

end NecklacePPAD.Main


