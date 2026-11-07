-- Prove2me | Definitions.Def_ReadTwiceCount_encodeFormula
-- name    : ReadTwiceCount_encodeFormula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:29.57719+00:00
-- url     : https://prove2.me/theorems/da3f9892-fe6c-41db-a0c8-c5d970d3fc5a
-- title:
--   Encoding of a formula with its variable universe; encoding length $N$
-- statement:
--   The input word of a formula $F$ on $M$ variables lists the universe in unary ($M$ ones followed by a zero), then the number of clauses, then for each clause its length followed by, for each literal, its variable index and one sign bit. Every number is written with the published self-delimiting binary code `encodeNat` (unary bit length, a separator, then the bits). The **encoding length** $N$ is the length of this word.
--
--   The theorem's running time is measured against $N$, which includes the universe. The paper notes that this convention accounts for the $M+1$ bits needed to write $2^M$ when all variables are free.
--
--   **Formalization Note** The paper fixes no format. Listing the universe in unary is what the paper's "including the variable universe" requires: with $M$ written in binary the main theorem would be false, since the empty formula on $2^k$ variables has count $2^{2^k}$.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Theorem 1.1, p.1

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_ReadTwiceCount_Formula

namespace ReadTwiceCount

open ExponomialAssortment.FPTAS (encodeNat)

/-- **The encoding of a formula, including its variable universe.** He, *A Deterministic
Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027 submission (manuscript
sha256 7a2a9dcd…), Theorem 1.1, p.1: "Let N be its encoding length, including the variable
universe"; p.1: "The variable universe is part of the explicit input".

The word is: the universe listed in unary (`M` ones and a zero), then the number of clauses, then
for each clause its length followed by, for each literal, its variable index and one sign bit. All
numbers use the published self-delimiting binary code `encodeNat`.

**Formalization Note** The paper fixes no format. The universe is written in unary because the paper
counts it in `N` ("this convention accounts for the M + 1 bits needed to write the count 2^M"); with
`M` in binary the theorem would be false (the empty formula on `2^k` variables). The code is
injective and its length is within a constant factor of any standard explicit encoding. -/
def encodeFormula {M : ℕ} (F : Formula M) : List Bool :=
  List.replicate M true ++ [false] ++ encodeNat F.clauses.length ++
    F.clauses.flatMap fun C =>
      encodeNat C.length ++ C.flatMap fun l => encodeNat l.1.val ++ [l.2]

/-- **The encoding length `N`** of a formula (He, STOC 2027 submission, manuscript sha256
7a2a9dcd…, Theorem 1.1, p.1). -/
def N {M : ℕ} (F : Formula M) : ℕ := (encodeFormula F).length

end ReadTwiceCount


