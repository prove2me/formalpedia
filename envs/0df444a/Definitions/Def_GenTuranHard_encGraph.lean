-- Prove2me | Definitions.Def_GenTuranHard_encGraph
-- name    : GenTuranHard_encGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:20.919767+00:00
-- url     : https://prove2.me/theorems/8bc68dd5-c8a7-48d9-9285-9840df14dbea
-- title:
--   Codes of graphs and rationals, and the input of an answer map
-- statement:
--   Inputs are coded as binary strings:
--
--   1. a natural number $n$ in **unary**: $n$ ones followed by a zero;
--   2. a natural number in a **self-delimiting binary code**: each binary digit $b$ (least significant first) is written as the pair $1, b$, and the code ends with $0$;
--   3. a rational number $q = a/d$ in lowest terms ($d > 0$): the sign bit of $a$, then $|a|$ and $d$ in the self-delimiting binary code;
--   4. a **graph** $G$ on $\{0,\dots,n-1\}$: $n$ in unary followed by the $n^2$ adjacency bits, row by row.
--
--   The **input of an answer map** for a string $x$ over an alphabet $\Sigma$ and a rational answer $q$ is the string $x$, a separator, and the code of $q$, over the alphabet $\Sigma \sqcup \{0,1\} \sqcup \{\#\}$.
--
--   The graph code has length $n^2 + n + 1$, so "polynomial time in the input graph" is polynomial time in the code length. The paper fixes no format; these codes make the complexity statements precise (p.2: only the host graph $G$ is part of the input).
--
--   **Formalization Note** The graph and rational codes are injective; this is checked in the mission's verification file.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), p.2 (only the host graph G is part of the input); proof of Theorem 3.2, p.11 (rational L, S)

import Mathlib
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace GenTuranHard

/-- The unary code of a natural number: `n` ones followed by a zero. -/
def natUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A self-delimiting binary code of a natural number: each binary digit `b` of `n` (least
significant first) is written as the pair `true, b`, and the code ends with `false`. -/
def natBits (n : ℕ) : List Bool := (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- The binary code of a rational number `q = num/den` (in lowest terms, `den > 0`): the sign bit
`0 ≤ num`, then `|num|` and `den` in the self-delimiting binary code `natBits`. -/
def encRat (q : ℚ) : List Bool :=
  decide (0 ≤ q.num) :: (natBits q.num.natAbs ++ natBits q.den)

open scoped Classical in
/-- The **code of an input graph** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, p.2:
only the host graph `G` is part of the input): the number of vertices `n` in unary, then the `n²`
adjacency bits row by row. Its length is `n² + n + 1`, so polynomial time in the code length is
polynomial time in `n`. -/
noncomputable def encGraph (G : FinGraph) : List Bool :=
    natUnary G.1 ++ (List.ofFn fun i : Fin G.1 => List.ofFn fun j : Fin G.1 => decide (G.2.Adj i j)).flatten

/-- The input of the answer map of a reduction: the original string `x` over `Sym`, a separator
(`none`), and the binary code `encRat q` of the rational answer `q` returned for the constructed
instance (`some (inl a)` is a symbol of `x`, `some (inr b)` a bit of `encRat q`). -/
def pairInput {Sym : Type} (x : List Sym) (q : ℚ) : List (Option (Sym ⊕ Bool)) :=
  x.map (some ∘ Sum.inl) ++ none :: (encRat q).map (some ∘ Sum.inr)

end GenTuranHard


