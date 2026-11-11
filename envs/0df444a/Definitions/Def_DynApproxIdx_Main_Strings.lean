-- Prove2me | Definitions.Def_DynApproxIdx_Main_Strings
-- name    : DynApproxIdx_Main_Strings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:51:24.583912+00:00
-- url     : https://prove2.me/theorems/0474193a-6684-4087-9869-490546ae45de
-- title:
--   k-mismatch occurrences, sorted interval lists and the alignment map of §7.1
-- statement:
--   Strings are finite sequences over the integer alphabet, written as lists of natural numbers and indexed from $0$; $T[a..b)$ is the fragment $T[a]T[a+1]\cdots T[b-1]$ (the published `PMEdits_Main_Strings` supplies fragments, the edit distance $\delta_E$, alignment-graph paths and the set $\mathrm{Occ}_k(P,T)$ of $k$-edit occurrences).
--
--   **Hamming distance and $k$-mismatch occurrences.** For strings $X,Y$ of equal length, $\delta_H(X,Y)=|\{i\in[0..|X|) : X[i]\ne Y[i]\}|$ (the published `HammingSumset729.Approximation.distance`). A pattern $P$ has a **$k$-mismatch occurrence** at position $i$ of a text $T$ when $i+|P|\le|T|$ and $\delta_H(P,T[i..i+|P|))\le k$:
--   $$\mathrm{Occ}^H_k(P,T)=\{\,i : i+|P|\le |T|,\ \delta_H(P,T[i..i+|P|))\le k\,\}.$$
--
--   **Intervals.** An interval $[a..b)$ of positions is the pair $(a,b)$ with $a<b$; its length is $b-a$ and $\max[a..b)+1=b$. A **sorted partition** of $[0..m)$ is a list $I_1,\dots,I_t$ of nonempty intervals with $I_1=[0..e_1)$, $I_2=[e_1..e_2)$, …, $I_t=[e_{t-1}..m)$. A list $J_1,\dots,J_w$ of nonempty intervals is **sorted pairwise disjoint** when $\max J_j<\min J_{j+1}$ for every $j$. $J\subseteq I$ is containment of intervals.
--
--   **The alignment map of §7.1.** An alignment of $X$ and $Y$ is a path of the alignment graph from $(0,0)$ to $(|X|,|Y|)$ (deletion, insertion and diagonal edges; a diagonal edge $(i,j)\to(i+1,j+1)$ costs $0$ when $X[i]=Y[j]$ and $1$ otherwise). It induces the partial map $A$ with $A(i)=j$ exactly when the path takes the diagonal edge $(i,j)\to(i+1,j+1)$ and $X[i]=Y[j]$: the positions preserved by the corresponding edit transformation.
--
--   These notions are used by Lemmas 7.1, 7.2 and Fact 7.7, and $\mathrm{Occ}^H_k$ by Theorem 1.1.
--
--   **Formalization Note.** The Hamming distance is only applied to strings of equal length (the paper sets it to $\infty$ otherwise; no statement uses that case). The paper defines a $k$-alignment from a transformation of $X$ and $Y$ into a common string by at most $k$ deletions in $X$ and $Y$ and substitutions in $X$; such transformations correspond to alignment-graph paths of the same cost, and the matched pairs are the zero-cost diagonal edges.
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), §3, p. 13 (PDF 15); §7.1, pp. 28–30 (PDF 30–32)

import Mathlib
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_HammingSumset729_Approximation_Strings

namespace DynApproxIdx.Main

open PMEdits.Main

/-! # k-mismatch occurrences, interval lists and the alignment map of §7.1

Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC 2027 submission
(manuscript sha256 7f902057…): §3, p. 13 (PDF 15); §6.1, p. 22 (PDF 24); §7.1, pp. 28–30 (PDF 30–32).

**Formalization Note.**
* Strings are `List ℕ` (the integer alphabet), indexed from `0`, as in the published
  `PMEdits_Main_Strings`; `frag T a b` is the fragment `T[a..b)`, `ed` is the edit distance `δ_E`
  and `Occ k P T` the set of `k`-edit occurrence positions.
* `δ_H(X, Y)` is the published `HammingSumset729.Approximation.distance X Y`, the number of
  positions `i` with `X[i] ≠ Y[i]`. It is only applied to strings of equal length (the paper sets
  `δ_H = ∞` for different lengths; no statement uses that case).
* An interval `[a..b)` of integers is the pair `(a, b) : ℕ × ℕ`; it is nonempty when `a < b`, and
  `max [a..b) + 1 = b`.
* The §7.1 alignment `A` of `X` and `Y` (a partial map `i ↦ j`) is encoded by a path of the
  alignment graph `AG(X, Y)` from `(0, 0)` to `(|X|, |Y|)`: `A(i) = j` when the path takes the
  diagonal edge `(i, j) → (i+1, j+1)` and `X[i] = Y[j]`. -/

/-- `Occ^H_k(P, T)`: the positions `i ∈ [0..|T| − |P|]` at which `P` has a `k`-mismatch
occurrence in `T`, i.e. `δ_H(P, T[i..i+|P|)) ≤ k` (§3, p. 13). Empty when `|P| > |T|`. -/
def OccH (k : ℕ) (P T : List ℕ) : Set ℕ :=
  {i | i + P.length ≤ T.length ∧
    HammingSumset729.Approximation.distance P (frag T i (i + P.length)) ≤ k}

/-- The length `|[a..b)| = b − a` of an interval. -/
def ilen (J : ℕ × ℕ) : ℕ := J.2 - J.1

/-- `I_1, …, I_t` is a sorted list of nonempty intervals forming a partition of `[0..m)`:
`I_1 = [0..e_1), I_2 = [e_1..e_2), …, I_t = [e_{t−1}..m)` with `0 < e_1 < ⋯ < e_{t−1} < m`
(the empty list when `m = 0`). -/
def IsSortedPartition (m : ℕ) (I : List (ℕ × ℕ)) : Prop :=
  (∀ J ∈ I, J.1 < J.2) ∧ List.IsChain (fun J J' => J.2 = J'.1) I ∧
  (∀ J ∈ I.head?, J.1 = 0) ∧ (∀ J ∈ I.getLast?, J.2 = m) ∧ (I = [] → m = 0)

/-- `J_1, …, J_w` is a sequence of sorted pairwise disjoint (nonempty) intervals:
`max J_j < min J_{j+1}` for every `j`. -/
def IsSortedDisjoint (J : List (ℕ × ℕ)) : Prop :=
  (∀ x ∈ J, x.1 < x.2) ∧ List.IsChain (fun x y => x.2 ≤ y.1) J

/-- `J ⊆ I` for intervals `J = [J.1..J.2)` and `I = [I.1..I.2)`. -/
def Subinterval (J I : ℕ × ℕ) : Prop := I.1 ≤ J.1 ∧ J.2 ≤ I.2

/-- `A(i) = j` for the alignment `A` of `X` and `Y` given as an alignment-graph path: the path
takes the diagonal edge `(i, j) → (i+1, j+1)`, and `X[i] = Y[j]` (no substitution). -/
def AlignMap (X Y : List ℕ) (A : List (ℤ × ℤ)) (i j : ℤ) : Prop :=
  ((i, j), (i + 1, j + 1)) ∈ edges A ∧ chars X i = chars Y j

end DynApproxIdx.Main


