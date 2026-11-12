-- Prove2me | Definitions.Def_SqrtLogHier_Main_StringArrays
-- name    : SqrtLogHier_Main_StringArrays
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:55:32.368381+00:00
-- url     : https://prove2.me/theorems/c2d0320b-c1de-40d2-88ed-f4110379cb41
-- title:
--   Strings and string arrays: occurrences, LF, ILF, Φ, Φ⁻¹, BWT, rank, runs, distinct substrings, de Bruijn sequences, nonoverlapping LZ77, wavelet-tree nodes
-- statement:
--   Strings are finite lists; positions are 1-based. Write $n = |T|$. On top of the published suffix array $\mathrm{SA}_T$, inverse suffix array $\mathrm{ISA}_T$, $\mathrm{LCP}_T$, $\mathrm{PLCP}_T$ and PLCP bitvector (CentralStrQ definitions, same authors and conventions), this item defines the cyclic predecessor and successor $\mathrm{prev}_n(1)=n$, $\mathrm{prev}_n(i)=i-1$, $\mathrm{next}_n(n)=1$, $\mathrm{next}_n(i)=i+1$ (Definition 3.9), and
--
--   $$\mathrm{LF}_T[i]=\mathrm{ISA}_T[\mathrm{prev}_n(\mathrm{SA}_T[i])],\quad \mathrm{ILF}_T[i]=\mathrm{ISA}_T[\mathrm{next}_n(\mathrm{SA}_T[i])],\quad \Phi_T[j]=\mathrm{SA}_T[\mathrm{prev}_n(\mathrm{ISA}_T[j])],\quad \Phi^{-1}_T[j]=\mathrm{SA}_T[\mathrm{next}_n(\mathrm{ISA}_T[j])],\quad \mathrm{BWT}_T[i]=T[\mathrm{prev}_n(\mathrm{SA}_T[i])]$$
--
--   (Definition 3.10; cyclic, no sentinel). It also defines $\mathrm{rank}_S(i,a)=|\{j\in[1..i]:S[j]=a\}|$ (Definition 4.25; selection is the published `CentralStrQ.select`, with $\infty$ as $\top$), the number $\mathrm{occ}(P,T)$ of occurrences of $P$ in $T$ (the empty string occurs $|T|+1$ times), the set $F(T)$ of nonempty substrings and $D(T)=|F(T)|$ (Definition 9.7), de Bruijn sequences of order $k$ over a finite alphabet of size $\sigma$ (length $\sigma^k+k-1$, every length-$k$ string exactly once; Definition 4.11), the runs of a string (maximal nonempty intervals of equal symbols; Definition 3.13), the nonoverlapping longest previous factor and the nonoverlapping LZ77 phrases (Definition 3.12; the overlapping $\mathrm{LPF}_T$ and LZ77 are the published DynLZ77 definitions), and the internal nodes and routing bitvectors of a binary wavelet tree of $h$-bit representations (Definition 3.14), nodes in level order with increasing prefix value.
-- source:
--   Kempa, Kociumaka, A Unified and Robust Theory of Lower and Upper Bounds for the √log n Barrier, STOC 2027 submission (manuscript sha256 7a17340d…), pp. 10-13, Definitions 3.9-3.14; p. 21, Definition 4.11; p. 24, Definition 4.25; p. 54, Definition 9.7

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_CentralStrQ_PLCPBitvector
import Definitions.Def_DynLZ77_Main_Strings

set_option autoImplicit false

namespace SqrtLogHier.Main

/-!
# Strings and string arrays: occurrences, LF, ILF, Φ, Φ⁻¹, BWT, runs, LZ77, wavelet trees

Kempa, Kociumaka, *A Unified and Robust Theory of Lower and Upper Bounds for the √log n Barrier*,
STOC 2027 submission (manuscript sha256 7a17340d…): §3.1 (p. 10), Definitions 3.6-3.14
(pp. 12-13), Definition 4.11 (p. 21), Definition 4.25 (p. 24), Definition 9.7 (p. 54).

**Formalization Note.**
* A string is a `List`; positions are **1-based** as in the paper. The suffix array `SA`, the
  inverse suffix array `ISA`, the arrays `LCP`, `PLCP`, the factor `T[i..j)` (`factor`) and the
  PLCP bitvector (`plcpBits`, Definition 3.8) are the published `CentralStrQ` definitions (same
  authors, same lexicographic order with a proper prefix smaller, same 1-based indexing).
  `select` (Definition 4.25) is the published `CentralStrQ.select`, with value `⊤ : ℕ∞` for `∞`.
* `LPF_T[j]` (Definition 3.11, overlapping occurrences allowed) is the published
  `DynLZ77.Main.lpf`, `max_{p ∈ [1..j)} lcp(T[j..n], T[p..n])`, and the overlapping LZ77
  factorization (Definition 3.12) is the published `DynLZ77.Main.LZ77`, a list of phrases
  `(b_i, b_{i+1} − 1)`; `z = DynLZ77.Main.z`. The nonoverlapping variant is defined here.
* Definition 3.10 is **cyclic**: `prev_n(1) = n`, `next_n(n) = 1`; there is no sentinel symbol.
  Strings whose BWT is formed are over `ℕ` (symbols are integers, §3.6).
* `occ P T` is the number of occurrences of `P` in `T`, i.e. of starting positions
  `i ∈ [1..|T| − |P| + 1]` with `T[i..i + |P|) = P`; the empty string has `|T| + 1`
  occurrences (problem 5, p. 14).
-/

variable {β : Type}

/-- `prev_n(i)` (Definition 3.9): `prev_n(1) = n` and `prev_n(i) = i − 1` otherwise. -/
def prevC (n i : ℕ) : ℕ := if i = 1 then n else i - 1

/-- `next_n(i)` (Definition 3.9): `next_n(n) = 1` and `next_n(i) = i + 1` otherwise. -/
def nextC (n i : ℕ) : ℕ := if i = n then 1 else i + 1

section Arrays

variable {α : Type} [LinearOrder α]

/-- `LF_T[i] = ISA_T[prev_n(SA_T[i])]` (Definition 3.10). -/
def LF (T : List α) (i : ℕ) : ℕ := CentralStrQ.ISA T (prevC T.length (CentralStrQ.SA T i))

/-- `ILF_T[i] = ISA_T[next_n(SA_T[i])]` (Definition 3.10). -/
def ILF (T : List α) (i : ℕ) : ℕ := CentralStrQ.ISA T (nextC T.length (CentralStrQ.SA T i))

/-- `Φ_T[j] = SA_T[prev_n(ISA_T[j])]` (Definition 3.10). -/
def Phi (T : List α) (j : ℕ) : ℕ := CentralStrQ.SA T (prevC T.length (CentralStrQ.ISA T j))

/-- `Φ⁻¹_T[j] = SA_T[next_n(ISA_T[j])]` (Definition 3.10). -/
def PhiInv (T : List α) (j : ℕ) : ℕ := CentralStrQ.SA T (nextC T.length (CentralStrQ.ISA T j))

end Arrays

/-- `BWT_T[i] = T[prev_n(SA_T[i])]` (Definition 3.10), for a string over `ℕ`. -/
def BWT (T : List ℕ) (i : ℕ) : ℕ := T.getD (prevC T.length (CentralStrQ.SA T i) - 1) 0

/-- The string `BWT_T = BWT_T[1] ⋯ BWT_T[n]` (empty for the empty string). -/
def bwt (T : List ℕ) : List ℕ := (List.range' 1 T.length).map (BWT T)

/-- `rank_S(i, a) = |{j ∈ [1..i] : S[j] = a}|` (Definition 4.25). -/
def rank [DecidableEq β] (S : List β) (i : ℕ) (a : β) : ℕ := (S.take i).count a

/-- The number of occurrences of `P` in `T`: the starting positions `i ∈ [1..|T| + 1]` such that
`P` is a prefix of the suffix `T[i..|T|]` (the empty pattern occurs `|T| + 1` times). -/
def occ [DecidableEq β] (P T : List β) : ℕ :=
  ((List.range (T.length + 1)).filter fun i => decide (P <+: T.drop i)).length

/-- `F(T)`, the set of nonempty substrings of `T` (Definition 9.7). -/
def substrs (T : List β) : Set (List β) := {U | U ≠ [] ∧ U <:+: T}

/-- `D(T) = |F(T)|` (Definition 9.7); `F(T)` is finite, so `Set.ncard` is its size. -/
noncomputable def distinctCount (T : List β) : ℕ := (substrs T).ncard

/-- A de Bruijn sequence of order `k` over the finite alphabet `β` (Definition 4.11, with
`[0..σ)` replaced by any alphabet of size `σ`): a string of length `σ^k + k − 1` containing every
string of length `k` exactly once as a substring. -/
def IsDeBruijn [Fintype β] [DecidableEq β] (k : ℕ) (B : List β) : Prop :=
  B.length = Fintype.card β ^ k + k - 1 ∧ ∀ V : List β, V.length = k → occ V B = 1

/-- The runs of `S` (Definition 3.13): maximal nonempty intervals `[a..b] ⊆ [1..|S|]` on which all
symbols are equal. -/
def runs (S : List β) : Set (ℕ × ℕ) :=
  {p | 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ S.length ∧
    (∀ i, p.1 ≤ i → i ≤ p.2 → S[i - 1]? = S[p.1 - 1]?) ∧
    (p.1 = 1 ∨ S[p.1 - 2]? ≠ S[p.1 - 1]?) ∧ (p.2 = S.length ∨ S[p.2]? ≠ S[p.2 - 1]?)}

section LZ

variable [DecidableEq β]

/-- The nonoverlapping longest previous factor at `j` (Definition 3.12, nonoverlapping variant):
the largest `ℓ` such that `T[p..p + ℓ) = T[j..j + ℓ)` for some `p ∈ [1..j)` with `p + ℓ ≤ j`. -/
def lpfNO (T : List β) (j : ℕ) : ℕ :=
  (Finset.Ico 1 j).sup fun p => min (DynLZ77.Main.lcpAt T j p) (j - p)

/-- The greedy nonoverlapping LZ77 scan from position `i`: phrase `(i, i + max(1, LPF^no_T[i]) − 1)`,
then continue at `i + max(1, LPF^no_T[i])`, until `i` leaves `[1..|T|]`. -/
def lz77NOFrom (T : List β) (i : ℕ) : List (ℕ × ℕ) :=
  if 1 ≤ i ∧ i ≤ T.length then (i, i + max (lpfNO T i) 1 - 1) :: lz77NOFrom T (i + max (lpfNO T i) 1)
  else []
termination_by T.length + 1 - i
decreasing_by
  have h1 : 1 ≤ max (lpfNO T i) 1 := le_max_right _ _
  omega

/-- The nonoverlapping LZ77 factorization (Definition 3.12) as its list of phrases
`(b_i, b_{i+1} − 1)`. -/
def lz77NO (T : List β) : List (ℕ × ℕ) := lz77NOFrom T 1

end LZ

section Wavelet

/-- The `h`-bit binary representation of `a`, most significant bit first. -/
def binRep (h a : ℕ) : List ℕ := (List.range h).reverse.map fun i => a / 2 ^ i % 2

/-- The internal nodes of the binary wavelet tree of the `h`-bit representations of `A`
(Definition 3.14): the prefixes `X` with `|X| < h` of some `binRep h (A[i])`, encoded as pairs
`(|X|, value of X)`, in level order and increasing value within a level. -/
def wtNodes (h : ℕ) (A : List ℕ) : List (ℕ × ℕ) :=
  (List.range h).flatMap fun d =>
    ((List.range (2 ^ d)).filter fun v => decide (∃ a ∈ A, a / 2 ^ (h - d) = v)).map fun v => (d, v)

/-- The routing bitvector of the node `(d, v)`: for the strings with prefix `X` (value `v`,
length `d`) in their original order, the symbol at position `d + 1`. -/
def wtBits (h : ℕ) (A : List ℕ) (node : ℕ × ℕ) : List ℕ :=
  (A.filter fun a => a / 2 ^ (h - node.1) = node.2).map fun a => a / 2 ^ (h - node.1 - 1) % 2

end Wavelet

end SqrtLogHier.Main


