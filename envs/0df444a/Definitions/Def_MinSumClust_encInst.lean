-- Prove2me | Definitions.Def_MinSumClust_encInst
-- name    : MinSumClust_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:27.547206+00:00
-- url     : https://prove2.me/theorems/f37e93e7-af9c-4960-840f-5336d92d6fbb
-- title:
--   Binary encodings of instances, coin strings, opening costs and labellings
-- statement:
--   To speak about polynomial time, inputs and outputs are words over the four-letter alphabet $\{0,1,2,3\}$ of the published `OnlineCRS.Combine.Sym`: $0,1$ are bits, $2$ separates numerator and denominator of a rational, and $3$ ends a token. Natural numbers are written in binary, integers as a sign bit and the binary absolute value, and rationals as reduced numerator and denominator.
--
--   1. An **instance** is the token sequence $k$, $n$, and then, row by row, the row length followed by its entries.
--   2. An **instance with a coin string** $w\in\{0,1\}^*$ (input of Theorem 1) is the instance tokens followed by one token of coin bits.
--   3. An **instance with an opening cost** $f\in\mathbb Q$ (input of Theorem 2) is the instance tokens followed by the token of $f$.
--   4. A **labelling** (the output) is the sequence of its labels in binary.
--
--   Each encoding is injective (checked in the mission's sanity file), and no number is written in unary, so input length is the usual bit length.
--
--   **Formalization Note** The paper names no machine model. The mission reads "polynomial time" in Mathlib's `Turing.TM2ComputableInPolyTime`, which needs these fixed encodings.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Theorem 1, p.1 (PDF p.3) and Theorem 2, p.4 (PDF p.6); encoding chosen by the mission (the paper names no machine)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_MinSumClust_Inst

namespace MinSumClust

open OnlineCRS.Combine

/-- Words joined as tokens: every word followed by the separator symbol `3`. -/
def tokJoin (ws : List (List Sym)) : List Sym :=
  ws.flatMap fun w => w ++ [3]

/-- The tokens of an instance: `k`, the number of rows, then for each row its length followed by
its entries. -/
def instTokens (I : Inst) : List (List Sym) :=
  [encNat I.k, encNat I.dist.length] ++
    I.dist.flatMap fun r => encNat r.length :: r.map encRat

/-- **Binary encoding of an instance** (input of the machines of Theorems 1 and 2).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Theorem 1, p.1 ("polynomial-time").

**Formalization Note.** The paper names no machine model. "Polynomial time" is read in Mathlib's
`Turing.TM2ComputableInPolyTime`, which needs a fixed encoding over a finite alphabet. The alphabet
is the published `OnlineCRS.Combine.Sym` (`0`, `1` bits, `2` inside a rational, `3` separator);
numbers are binary (`encNat`), rationals are reduced numerator and denominator (`encRat`); every
token is followed by `3`. The layout is `k`, the number of rows, then each row as its length and its
entries. No number is written in unary. -/
def encInst (I : Inst) : List Sym :=
  tokJoin (instTokens I)

/-- **Encoding of an instance with a coin string** (input of the machine of Theorem 1): the
instance tokens, then one token of coin bits (`bit true = 1`, `bit false = 0`). -/
def encInstCoins (x : Inst × List Bool) : List Sym :=
  tokJoin (instTokens x.1 ++ [x.2.map bit])

/-- **Encoding of an instance with an opening cost `f`** (input of the machine of Theorem 2, p.4):
the instance tokens, then the token `encRat f`. -/
def encInstF (x : Inst × ℚ) : List Sym :=
  tokJoin (instTokens x.1 ++ [encRat x.2])

/-- **Encoding of an output labelling**: the labels in binary, each followed by `3`. -/
def encLabels (L : List ℕ) : List Sym :=
  tokJoin (L.map encNat)

end MinSumClust


