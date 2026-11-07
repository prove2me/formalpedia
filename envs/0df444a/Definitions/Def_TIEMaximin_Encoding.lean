-- Prove2me | Definitions.Def_TIEMaximin_Encoding
-- name    : TIEMaximin_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:33.461416+00:00
-- url     : https://prove2.me/theorems/bdcf5a4a-d0f3-49df-96aa-ee851eb376e3
-- title:
--   Binary encodings of the inputs and outputs of Theorem 1.1
-- statement:
--   The computational sentence of Theorem 1.1 takes rational valuations in binary and outputs an explicit lottery. The input is the triple $(n,m,\text{rows of }v)$ and the output a list of pairs (rational weight, word listing the receiving agents of goods $0,\dots,m-1$). All numbers are in binary; every number has a terminator and every list a length prefix.
--
--   An output list is a **well-formed lottery** if every weight is nonnegative, every word has length $m$ with entries below $n$, and the weights sum to one. The **weight of an allocation** in a list is the sum of the weights of all entries equal to it.
--
--   **Formalization Note** Polynomial time is read in Mathlib's `Turing.TM2ComputableInPolyTime` over the published alphabet `OnlineCRS.Combine.Sym`, with numbers from the published `OnlineCRS.Combine` encoders. Both encodings are prefix codes, hence injective; this is proved in `Solutions/verification/TIEMaximin_encodings.lean`. The encoding of the $n$ rows makes the input length at least $n$, so polynomial in the input length is polynomial in $n$ and $m$ as well.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Theorem 1.1, p.2; Appendix A.1, p.38

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat

namespace TIEMaximin

open OnlineCRS.Combine

/-- Self-delimiting binary word of a natural number: `encNat k` followed by the terminator `2`
(auxiliary encoding for "rational valuations encoded in binary", Theorem 1.1, p.2 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…).

**Formalization Note.** `encNat 0` is the empty word, so the terminator is what keeps `0` visible. -/
def encWNat (k : ℕ) : List Sym := encNat k ++ [2]

/-- Self-delimiting binary word of a rational number: the published `encRat q` (reduced numerator,
separator `2`, denominator) followed by the terminator `3` (arXiv:2609.35670, version of 2026-11-03,
sha256 4e68de70…, Theorem 1.1, p.2). -/
def encWRat (q : ℚ) : List Sym := encRat q ++ [3]

/-- Length-prefixed concatenation of the words of a list: the binary length of `l`, then the word of
every entry (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Theorem 1.1, p.2). -/
def encWList {α : Type} (enc : α → List Sym) (l : List α) : List Sym :=
  encWNat l.length ++ l.flatMap enc

/-- **Raw inputs of the algorithm of Theorem 1.1** (p.2): the number of agents `n`, the number of
goods `m`, and the list of rows of the rational valuation matrix (arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…).

**Formalization Note.** A raw input need not be well formed: its rows may have the wrong shape or
negative entries. Theorem 1.1 constrains the output only on inputs `mkIn n m v` with `v ≥ 0`; the
machine may output anything else on the others, but it must halt in polynomial time on them too. -/
abbrev MechIn : Type := ℕ × ℕ × List (List ℚ)

/-- The raw input of the rational profile `v`: `(n, m, rows of v)` (arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…, Theorem 1.1, p.2). -/
def mkIn (n m : ℕ) (v : Fin n → Fin m → ℚ) : MechIn :=
  (n, m, List.ofFn fun i => List.ofFn (v i))

/-- **Input encoding of Theorem 1.1** (p.2, "rational valuations encoded in binary"): `n`, `m` and
every matrix entry in binary, every list length-prefixed (arXiv:2609.35670, version of 2026-11-03,
sha256 4e68de70…).

**Formalization Note.** Polynomial time is read in Mathlib's `Turing.TM2ComputableInPolyTime` over
the published alphabet `OnlineCRS.Combine.Sym = Fin 4`. The `n` rows and `m` entries per row are
written out, so a well-formed input has length at least `n + n * m`, plus the bit sizes of the
entries. The encoding is injective (`Solutions/verification/TIEMaximin_encodings.lean`). -/
def encMechIn (I : MechIn) : List Sym :=
  encWNat I.1 ++ encWNat I.2.1 ++ encWList (encWList encWRat) I.2.2

/-- **Output encoding of Theorem 1.1** (p.2, "an explicit lottery"): the length-prefixed list of
(rational weight, allocation word), the allocation word listing the receiving agent of the goods
`0, …, m − 1`, all numbers in binary (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…).
The encoding is injective (`Solutions/verification/TIEMaximin_encodings.lean`). -/
def encLottery (L : List (ℚ × List ℕ)) : List Sym :=
  encWList (fun e => encWRat e.1 ++ encWList encWNat e.2) L

/-- An output list is **a well-formed explicit lottery** over allocations of `m` goods to `n`
agents: every entry has a nonnegative weight and a word of length `m` with entries `< n`, and the
weights sum to one (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Theorem 1.1, p.2). -/
def IsLotteryList (n m : ℕ) (L : List (ℚ × List ℕ)) : Prop :=
  (∀ e ∈ L, 0 ≤ e.1 ∧ e.2.length = m ∧ ∀ a ∈ e.2, a < n) ∧ (L.map Prod.fst).sum = 1

/-- The total weight that the list `L` gives to the allocation `A`: the sum of the weights of all
entries whose word is `A`'s (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Theorem 1.1,
p.2).

**Formalization Note.** Entries may repeat; their weights add up. -/
noncomputable def listWeight {n m : ℕ} (L : List (ℚ × List ℕ)) (A : Fin m → Fin n) : ℝ :=
  ((L.filter fun e => e.2 == List.ofFn fun g => (A g : ℕ)).map fun e => ((e.1 : ℚ) : ℝ)).sum

/-- Input encoding of the TPS computation of Appendix A.1 (p.38): `n` and the list of an agent's
item values, in binary (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
def encTPSIn (I : ℕ × List ℚ) : List Sym :=
  encWNat I.1 ++ encWList encWRat I.2

end TIEMaximin


