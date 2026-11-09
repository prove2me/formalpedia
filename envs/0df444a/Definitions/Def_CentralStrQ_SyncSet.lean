-- Prove2me | Definitions.Def_CentralStrQ_SyncSet
-- name    : CentralStrQ_SyncSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:30.278619+00:00
-- url     : https://prove2.me/theorems/a5c0c9b9-faa7-4909-a6b9-ce224b8138e5
-- title:
--   Periods, τ-periodic positions, τ-synchronizing sets and their labels
-- statement:
--   Let $T\in\Sigma^n$.
--
--   1. An integer $p\in[1\,.\,.\,|S|]$ is a **period** of $S$ if $S[i]=S[i+p]$ for every $i\in[1\,.\,.\,|S|-p]$; $\mathrm{per}(S)$ is the smallest period (p.13).
--   2. The **τ-periodic positions** are $R(\tau,T)=\{i\in[1\,.\,.\,n-3\tau+2]:\mathrm{per}(T[i\,.\,.\,i+3\tau-1))\le\tfrac13\tau\}$ (Definition 3.38).
--   3. For $n\ge2$ and $\tau\in[1\,.\,.\,\lfloor n/2\rfloor]$, a set $S\subseteq[1\,.\,.\,n-2\tau+1]$ is a **τ-synchronizing set** if (consistency) $T[i\,.\,.\,i+2\tau)=T[j\,.\,.\,j+2\tau)$ implies $i\in S\iff j\in S$ for $i,j\in[1\,.\,.\,n-2\tau+1]$, and (density) $S\cap[i\,.\,.\,i+\tau)=\emptyset\iff i\in R(\tau,T)$ for $i\in[1\,.\,.\,n-3\tau+2]$ (Definition 3.40).
--   4. $\mathrm{LexSorted}(Q,T)$ lists the positions of $Q$ in the lexicographic order of their suffixes (Definition 3.14).
--   5. **Labels** (Definition 9.11). Let $S$ be a nonempty τ-synchronizing set, $k=|S|$ and $(s_i)_{i\in[1..k]}=\mathrm{LexSorted}(S,T)$. Let $s_i^-$ be the largest element of $S$ smaller than $s_i$, or $0$ if $s_i=\min S$. Then $a_i=\max\{s_i^-,s_i-\tau\}+1$, the owned set is $J_i=[a_i\,.\,.\,s_i]$, the label $W[i]$ is the **reverse** of $T[a_i\,.\,.\,s_i+2\tau)$, and for $C\ge0$ the $C$-capped LCE sequence is $A[i]=\min\{C,\mathrm{LCE}_T(s_i,s_{i+1})\}$ for $i\in[1\,.\,.\,k)$.
--
--   Synchronizing sets, due to Kempa and Kociumaka, select few positions consistently by their context; Section 9.2 turns their labels and capped LCE values into an instance of LCP-Profile Construction whose output contains the PLCP marks of the nonperiodic positions. Example 3.41: $\{1,4,7,14,17,20\}$ is a 3-synchronizing set of $cdefghx\,a^{11}\,y\,cdefgh$, with $R(3,T)=\{8,9,10,11\}$.
--
--   **Formalization Note** The text layer of the manuscript drops the overline in Definition 9.11; the printed page, the proof of Lemma 9.12 and Proposition 9.14 step 1(d) show that the label is reversed. Ranges $[1\,.\,.\,n-3\tau+2]$ use natural subtraction and are empty exactly when the paper's range is. $\mathrm{LexSorted}$ sorts the elements of $Q$ by suffix order; distinct positions have distinct suffixes, so the order is unique.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Section 3.1, p.13 (PDF p.14); Definition 3.14, p.16 (PDF p.17); Definitions 3.38 and 3.40, p.21 (PDF p.22); Definition 9.11, p.166 (PDF p.167)

import Mathlib
import Definitions.Def_CentralStrQ_Strings

set_option autoImplicit false

namespace CentralStrQ

/-!
# Periods, periodic positions, synchronizing sets and their labels
(Section 3.1, Definitions 3.14, 3.38, 3.40 and 9.11)

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346): periods, p.13 (PDF p.14);
Definition 3.14, p.16 (PDF p.17); Definitions 3.38 and 3.40, p.21 (PDF p.22); Definition 9.11,
p.166 (PDF p.167).

* p.13: "An integer p ∈ [1..|S|] is a period of S if S[i] = S[i+p] holds for every
  i ∈ [1..|S|−p]. We denote the smallest period of S as per(S)."
* Definition 3.38: `R(τ, T) = {i ∈ [1..n−3τ+2] : per(T[i..i+3τ−1)) ≤ τ/3}`.
* Definition 3.40: for `n ≥ 2`, `T ∈ Σⁿ`, `τ ∈ [1..⌊n/2⌋]`, a set `S ⊆ [1..n−2τ+1]` is a
  τ-synchronizing set if (consistency) `T[i..i+2τ) = T[j..j+2τ)` implies `i ∈ S ⟺ j ∈ S` for
  `i, j ∈ [1..n−2τ+1]`, and (density) `S ∩ [i..i+τ) = ∅ ⟺ i ∈ R(τ,T)` for `i ∈ [1..n−3τ+2]`.
* Definition 3.14: `LexSorted(Q, T)` lists `Q` in the lexicographic order of the suffixes.
* Definition 9.11: with `(s_i)_{i∈[1..k]} = LexSorted(S, T)`, `s⁻_i` the largest element of `S`
  smaller than `s_i` (zero if none), `a_i = max{s⁻_i, s_i − τ} + 1`, `J_i = [a_i..s_i]`,
  `W[i]` = the **reverse** of `T[a_i..s_i+2τ)`, and the C-capped LCE sequence
  `A[i] = min{C, LCE_T(s_i, s_{i+1})}` for `i ∈ [1..k)`.

**Formalization Note.** Positions are 1-based natural numbers; `[a..b]` is `Finset.Icc a b`,
and the upper ends `n − 3τ + 2`, `n − 2τ + 1` are written `n + 2 − 3τ`, `n + 1 − 2τ` (natural
subtraction, giving the empty range exactly when the paper's range is empty). `per` of the empty
string is `0` (never used). The text layer of the manuscript drops the overline in Definition
9.11; the rendered page, the proof of Lemma 9.12 ("W[h] has prefix D̄") and Proposition 9.14 step
1(d) show that `W[i]` is reversed, and `labels` reverses it. `s_i` for `i` outside `[1..k]` is
`0` (never used). In `labelStart`, `s_i − τ` is natural subtraction; when `s_i < τ` the maximum
is `s⁻_i` either way.
-/

variable {α : Type} [LinearOrder α]

/-- `p` is a period of `S`. -/
def IsPeriod (S : List α) (p : ℕ) : Prop :=
  1 ≤ p ∧ p ≤ S.length ∧ ∀ i ∈ Finset.Icc 1 (S.length - p), S[i - 1]? = S[i + p - 1]?

instance (S : List α) : DecidablePred (IsPeriod S) := fun _ => by
  unfold IsPeriod; infer_instance

omit [LinearOrder α] in
/-- A nonempty string has the period `|S|`. -/
theorem isPeriod_length (S : List α) (h : 0 < S.length) : IsPeriod S S.length :=
  ⟨h, le_rfl, by simp⟩

/-- `per(S)`, the smallest period (`0` for the empty string). -/
def per (S : List α) : ℕ :=
  if h : 0 < S.length then Nat.find (⟨S.length, isPeriod_length S h⟩ : ∃ p, IsPeriod S p) else 0

/-- The τ-periodic positions `R(τ, T)` (Definition 3.38). -/
def periodicPositions (τ : ℕ) (T : List α) : Finset ℕ :=
  (Finset.Icc 1 (T.length + 2 - 3 * τ)).filter fun i => 3 * per (factor T i (i + 3 * τ - 1)) ≤ τ

/-- `S` is a τ-synchronizing set of `T` (Definition 3.40), including its standing assumptions
`n ≥ 2` and `τ ∈ [1..⌊n/2⌋]`. -/
def IsSyncSet (τ : ℕ) (T : List α) (S : Finset ℕ) : Prop :=
  2 ≤ T.length ∧ 1 ≤ τ ∧ 2 * τ ≤ T.length ∧ S ⊆ Finset.Icc 1 (T.length + 1 - 2 * τ) ∧
    (∀ i ∈ Finset.Icc 1 (T.length + 1 - 2 * τ), ∀ j ∈ Finset.Icc 1 (T.length + 1 - 2 * τ),
      factor T i (i + 2 * τ) = factor T j (j + 2 * τ) → (i ∈ S ↔ j ∈ S)) ∧
    ∀ i ∈ Finset.Icc 1 (T.length + 2 - 3 * τ),
      (S ∩ Finset.Ico i (i + τ) = ∅ ↔ i ∈ periodicPositions τ T)

/-- `LexSorted(Q, T)`: the positions of `Q` in the lexicographic order of their suffixes
(Definition 3.14).
The elements of `Q` are listed in increasing order and then insertion-sorted by suffix order;
distinct positions of `[1..|T|+1]` have distinct suffixes, so the result is the unique such list. -/
def lexSorted (T : List α) (Q : Finset ℕ) : List ℕ :=
  ((List.range (Q.sup id + 1)).filter (· ∈ Q)).insertionSort fun a b => suffix T a ≤ suffix T b

/-- `s_i`, the `i`-th position of `LexSorted(S, T)` (1-based). -/
def sAt (T : List α) (S : Finset ℕ) (i : ℕ) : ℕ := (lexSorted T S).getD (i - 1) 0

/-- `s⁻`: the largest element of `S` smaller than `s`, or `0` if there is none. -/
def sMinus (S : Finset ℕ) (s : ℕ) : ℕ := (S.filter (· < s)).sup id

/-- `a_i = max{s⁻_i, s_i − τ} + 1`. -/
def labelStart (T : List α) (τ : ℕ) (S : Finset ℕ) (i : ℕ) : ℕ :=
  max (sMinus S (sAt T S i)) (sAt T S i - τ) + 1

/-- The owned set `J_i = [a_i..s_i]`. -/
def owned (T : List α) (τ : ℕ) (S : Finset ℕ) (i : ℕ) : Finset ℕ :=
  Finset.Icc (labelStart T τ S i) (sAt T S i)

/-- The labels `W[1..k]`, `W[i]` = reverse of `T[a_i..s_i+2τ)` (Definition 9.11). -/
def labels (T : List α) (τ : ℕ) (S : Finset ℕ) : List (List α) :=
  (List.range' 1 S.card).map fun i => (factor T (labelStart T τ S i) (sAt T S i + 2 * τ)).reverse

/-- The C-capped LCE sequence `A[1..k)`, `A[i] = min{C, LCE_T(s_i, s_{i+1})}`. -/
def cappedLCE (T : List α) (S : Finset ℕ) (C : ℕ) : List ℕ :=
  (List.range' 1 (S.card - 1)).map fun i => min C (LCE T (sAt T S i) (sAt T S (i + 1)))

end CentralStrQ


