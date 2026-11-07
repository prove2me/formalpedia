-- Prove2me | Definitions.Def_MCPoise_encIn
-- name    : MCPoise_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:15.040213+00:00
-- url     : https://prove2.me/theorems/d117a333-748f-4172-8fdd-6db1972f45d5
-- title:
--   Binary encodings of instances and output edge lists
-- statement:
--   The input of the main algorithm is written over a four-letter alphabet as: the number $n$ in unary, then the edge list and the demand list, each preceded by its length, with vertices in binary. A variant appends a guess $L$ in binary. An output edge list is written in the same way.
--
--   The length of the encoding is $n + m + k$ up to logarithmic factors, the usual size of a graph.
--
--   **Formalization Note** The source names no machine. Polynomial time is read in Mathlib's Turing-machine model. Reuses the published encoders of `OnlineCRS.Combine`, `ReserveLB.tokList` and `EulerSparsify.joinW`. The encodings are injective, which is proved in the mission's sanity file.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.1, p.3; p.6; p.21

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_ReserveLB_tokList
import Definitions.Def_EulerSparsify_joinW

namespace MCPoise

open OnlineCRS.Combine

/-- The words of a list of pairs of numbers: its length first, then each pair in binary. -/
def tokPairs (l : List (ℕ × ℕ)) : List (List Sym) :=
  ReserveLB.tokList (fun a : ℕ × ℕ => [encNat a.1, encNat a.2]) l

/-- A list of pairs of vertices as a list of pairs of numbers. -/
def valPairs {n : ℕ} (l : List (Fin n × Fin n)) : List (ℕ × ℕ) :=
  l.map fun a => (a.1.val, a.2.val)

/-- The words of an instance: `n` in unary, the edge list, the demand list. -/
def tokInst (I : Inst) : List (List Sym) :=
  [List.replicate I.n 0] ++ tokPairs (valPairs I.edges) ++ tokPairs (valPairs I.dem)

/-- **Encoding of an instance of MC Poise.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.1, p.3: "an efficient algorithm"; p.21 gives running times in `n`.

`encIn I` joins by the separator `3` the words of `tokInst`.

**Formalization Note.** The source names no machine or encoding. Polynomial time is read in Mathlib's
`Turing.TM2ComputableInPolyTime`, over the published alphabet `OnlineCRS.Combine.Sym = Fin 4`. The number `n`
is written in unary and vertices in binary, so the length of `encIn I` is `n + m + k` up to logarithmic factors,
the usual size of a graph. Every list is length-prefixed and no word contains `3`, so the encoding is injective
(`Solutions/verification/MCPoise_sanity.lean`). -/
def encIn (I : Inst) : List Sym :=
  EulerSparsify.joinW (tokInst I)

/-- **Encoding of an instance together with a guess `L`,** in binary: the input of Lemma 2.1 and Theorem 1.7 (p.6:
"we guess the value L of the optimal solution"). -/
def encLIn (x : Inst × ℕ) : List Sym :=
  EulerSparsify.joinW (tokInst x.1 ++ [encNat x.2])

/-- **Encoding of an output edge list.** Length first, each pair in binary. Injective
(`Solutions/verification/MCPoise_sanity.lean`). -/
def encOut (out : List (ℕ × ℕ)) : List Sym :=
  EulerSparsify.joinW (tokPairs out)

end MCPoise


