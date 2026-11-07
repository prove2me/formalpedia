-- Prove2me | Definitions.Def_AvgValueAlloc_encIn
-- name    : AvgValueAlloc_encIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:27.20819+00:00
-- url     : https://prove2.me/theorems/9ce7b744-bb25-4eb6-b2fb-bf8b85fb6db6
-- title:
--   Binary encoding of the learner's observation and coins
-- statement:
--   The observation is written over the alphabet $\{0,1,2,3\}$: rationals in binary (numerator, separator $2$, denominator), every list preceded by its length, $T$ and $S$ in **unary**, words separated by $3$. The coin bits form one further word.
--
--   The encoding fixes the input length of the polynomial-time learner. Writing $T$ and $S$ in unary makes the input length at least $T+S$, so "polynomial in the input length" includes "polynomial in $n,S,T$ and the observed binary input".
--
--   **Formalization Note** No word contains the separator, so the encoding is injective (checked in the mission's verification file).
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2; Appendix A.2, p.14

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_AvgValueAlloc_LearnerInput

namespace AvgValueAlloc

open OnlineCRS.Combine

/-- Words of a rational vector: its length, then its coordinates. -/
def tokVec (v : List ℚ) : List (List Sym) := encNat v.length :: v.flatMap fun q => [encRat q]

/-- Words of a list of rational vectors: its length, then each vector. -/
def tokVecs (l : List (List ℚ)) : List (List Sym) := encNat l.length :: l.flatMap tokVec

/-- A natural number in unary. -/
def unary (k : ℕ) : List Sym := List.replicate k 1

/-- The words of an observation: `rho`, `T` and `S` in unary, `hist`, `past`, `cur`. -/
def inputWords (x : LearnerInput) : List (List Sym) :=
  tokVec x.rho ++ [unary x.T, unary x.S] ++ tokVecs x.hist ++ tokVecs x.past ++ tokVec x.cur

/-- **Binary encoding of the learner's observation, and of observation plus coins.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "Runtime is polynomial in n, S, T and
observed binary input, not in an unobserved support"; Appendix A.2, p.14: "Precision is polynomial
in the full observed encoding".

`encInput x` is the words of `rho`, `T` and `S` in unary, `hist`, `past` and `cur`, joined by the
separator `3`; rationals are binary (`OnlineCRS.Combine.encRat`) and every list is preceded by its
length. `encIn (x, w)` appends one more word, the coin bits `w`.

**Formalization Note.** `T` and `S` are written in unary, so the input length is at least
`T + S` and "polynomial in the input length" includes "polynomial in n, S, T". No word contains
`3`, so both encodings are injective (proved in `Solutions/verification/AvgValueAlloc_checks.lean`). -/
def encInput (x : LearnerInput) : List Sym := [3].intercalate (inputWords x)

/-- The observation followed by the coin bits. -/
def encIn (x : LearnerInput × List Bool) : List Sym :=
  [3].intercalate (inputWords x.1 ++ [x.2.map bit])

end AvgValueAlloc


