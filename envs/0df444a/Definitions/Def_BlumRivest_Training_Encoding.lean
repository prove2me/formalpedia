-- Prove2me | Definitions.Def_BlumRivest_Training_Encoding
-- name    : BlumRivest_Training_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:42:11.129677+00:00
-- url     : https://prove2.me/theorems/24c13d1a-055d-43a9-ae4c-ddb4a3df7873
-- title:
--   Section 2 — explicit finite-string encoding of the exact training problem
-- statement:
--   Use the five-symbol alphabet $\{0,1,2,3,4\}$. A dimension-$n$ instance begins with $n$ copies of token 0 followed by token 1. Each example then contributes its $n$ input bits in coordinate order, its label bit, and token 4. False and true bits are written as tokens 2 and 3, respectively; a false label means −1, and a true label means +1.
--
--   With $m$ example rows, the code has length $n+1+m(n+2)$. Empty data are represented by the header alone, including the one-symbol header `[1]` at dimension zero. Row boundaries and the dimension header make the code unambiguous. There is no compressed vector representation or semantic information in the code.
--
--   The training language consists exactly of the encodings of trainable instances, with feasibility defined by unrestricted real parameters. All strings outside the encoder's range are excluded. One language includes every dimension and every finite training list. Complexity uses the published CookPvsNP definitions for finite strings, polynomial-time Turing machines, witnesses and many-one reductions.
-- source:
--   Blum and Rivest (1992), Section 2 and Theorem 1, printed p. 119 (PDF p. 3), DOI 10.1016/S0893-6080(05)80010-3; explicit string representation of the source's Boolean training input.

import Definitions.Def_BlumRivest_Training_Model
import Definitions.Def_CookPvsNP_defs

namespace BlumRivest.Training

/-- Tokens: 0 = dimension tick, 1 = header end, 2/3 = false/true, 4 = row end. -/
abbrev CodeSymbol := Fin 5

def encodeBit (b : Bool) : CodeSymbol := if b then 3 else 2

/-- The `n` input bits in coordinate order, the label bit, then a row terminator. -/
def encodeExample {n : ℕ} (e : (Fin n → Bool) × Bool) : List CodeSymbol :=
  (List.ofFn e.1).map encodeBit ++ [encodeBit e.2, 4]

/-- Unary dimension header, its terminator, and all explicitly listed rows. -/
def encodeInstance (I : Instance) : List CodeSymbol :=
  List.replicate I.dim 0 ++ [1] ++ I.examples.flatMap encodeExample

/-- Exactly the codes of feasible instances. Strings outside the encoder's range are rejected. -/
def trainingLanguage : CookPvsNP.Lang CodeSymbol :=
  {s | ∃ I : Instance, s = encodeInstance I ∧ Trainable I}

end BlumRivest.Training


