-- Prove2me | Definitions.Def_AffDisp4n_encState
-- name    : AffDisp4n_encState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:39.341686+00:00
-- url     : https://prove2.me/theorems/61b20efe-b1c5-46a3-a2cb-f47eb4413def
-- title:
--   Encoding of a state of gate elimination
-- statement:
--   A state is written as the words $n$, $m$, $r$, the vector $b$, the matrix $L$, the table of $P$, the matrices $A$ and $N$, the vector $c$, and the acyclic part with its output. This is the input of the algorithm of Lemma 4.2.
--
--   **Formalization Note** The paper fixes no encoding. This one is injective. Its length is polynomial in $n + m + r$ and the number of gates, and at least each of them.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.4, p.16; proof of Theorem 4.1, p.26

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_AffDisp4n_vecWord
import Definitions.Def_AffDisp4n_Acyclic_tokens

namespace AffDisp4n

/-- A parameter (`inl`) or an auxiliary variable (`inr`) as a word: a tag bit, then its index in unary. -/
def internalWord {m r : ℕ} : Fin m ⊕ Fin r → List Bool
  | .inl x => false :: natWord x.val
  | .inr k => true :: natWord k.val

/-- The words of a state: `n`, `m`, `r`, the vector `b`, the matrix `L`, the table of `P`, the matrices `A`
and `N`, the vector `c`, and the acyclic part with its output. -/
def State.tokens {n : ℕ} (σ : State n) : List (List Bool) :=
  [natWord n, natWord σ.m, natWord σ.r, vecWord σ.b] ++ matWords σ.L ++ pairsWords σ.P ++
    matWords σ.A ++ matWords σ.N ++ [vecWord σ.c] ++ σ.circ.tokens internalWord

/-- **Encoding of a state of gate elimination**, the input of the algorithm of Lemma 4.2
(Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.4, p.16; p.26: "We store Φ through the vector b and the matrix L, and the set P as a list of
all pairs").

**Formalization Note** The paper fixes no encoding. This one is injective: the words `n`, `m`, `r` give the
number and the lengths of the words that follow. Its length is polynomial in `n + m + r` and the number
of gates, and is at least each of them, so "polynomial time" does not depend on the choices made here
(unary numbers, a table for `P` instead of a list). -/
def encState (x : Σ n, State n) : List (Fin 3) :=
  LowErrExt.encWords x.2.tokens

end AffDisp4n


