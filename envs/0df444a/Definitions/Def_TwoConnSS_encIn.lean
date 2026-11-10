-- Prove2me | Definitions.Def_TwoConnSS_encIn
-- name    : TwoConnSS_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:00.28791+00:00
-- url     : https://prove2.me/theorems/6553c5ab-f001-420d-87ca-86e26e25e4d5
-- title:
--   Encodings of instances and edge lists for the polynomial-time clauses
-- statement:
--   To state "polynomial time" the mission uses Turing machines over the four-letter alphabet $\{0, 1, 2, 3\}$ (bits and a separator $3$). An instance is written as $n$ in unary followed by the $n^2$ entries of its adjacency matrix row by row; an edge list is written as its length followed by both entries of every pair in binary. Every field is followed by the separator. Tuples of edge lists (covers, pairings, solutions) are written as their number followed by each list, and the input of a procedure that receives covers is the instance followed by such a tuple.
--
--   The input length is at least $n^2$, so a running time polynomial in the code length is polynomial in $n$. No field contains the separator, so all encodings are injective.
--
--   **Formalization Note** The machine model is Mathlib's `Turing.TM2ComputableInPolyTime`; the alphabet and the binary numerals are the published `OnlineCRS.Combine.Sym`, `bit` and `encNat`. Injectivity of all four encodings is proved in the mission's sanity file.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Theorem 5.1, p.18 ("polynomial-time")

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_TwoConnSS_Inst

namespace TwoConnSS

open OnlineCRS.Combine

/-- Words joined into one tape: every word is followed by the separator symbol `3`. -/
def term (ws : List (List Sym)) : List Sym :=
  ws.flatMap fun w => w ++ [3]

/-- The words of a list of pairs of numbers: its length, then each entry of each pair, in binary. -/
def wList (l : List (ℕ × ℕ)) : List (List Sym) :=
  encNat l.length :: l.flatMap fun p => [encNat p.1, encNat p.2]

/-- The words of an instance: `n` in unary, then the `n` rows of the adjacency matrix, each row a
word of `n` bits. -/
def wInst (I : Inst) : List (List Sym) :=
  List.replicate I.n 0 :: List.ofFn fun u : Fin I.n => List.ofFn fun v : Fin I.n => bit (I.adj u v)

/-- **Encoding of an instance of 2ECSS for the polynomial-time clauses.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 5.1, p.18: "a
polynomial-time (1040/833 + ε)-approximation for 2ECSS".

`encIn I` is `n` in unary followed by the `n²` adjacency bits row by row, every field terminated by
the separator `3`.

**Formalization Note.** The source names no machine model. Polynomial time is read in Mathlib's
`Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`
(`0`, `1` bits, `3` separator). The length of `encIn I` is `n² + 2n + 2`, so polynomial in the code
length is polynomial in `n`. No word contains `3`, so the encoding is injective
(`Solutions/verification/TwoConnSS_sanity.lean`). -/
def encIn (I : Inst) : List Sym :=
  term (wInst I)

/-- **Encoding of an output edge list**: its length, then each pair of vertex numbers in binary,
every field terminated by `3`. Injective (`Solutions/verification/TwoConnSS_sanity.lean`). -/
def encOut (l : List (ℕ × ℕ)) : List Sym :=
  term (wList l)

/-- **Encoding of a tuple of edge lists** (covers, pairings, solutions), the output of the
milestone machines: the number of lists in binary, then each list as in `encOut`. -/
def encLists (ls : List (List (ℕ × ℕ))) : List Sym :=
  term (encNat ls.length :: ls.flatMap wList)

/-- **Encoding of an instance together with a tuple of edge lists**, the input of the milestone
machines (for example the graph `G`, the initial cover `S₀`, a cover `S` and a pairing `M`). -/
def encInL (x : Inst × List (List (ℕ × ℕ))) : List Sym :=
  term (wInst x.1 ++ encNat x.2.length :: x.2.flatMap wList)

end TwoConnSS


