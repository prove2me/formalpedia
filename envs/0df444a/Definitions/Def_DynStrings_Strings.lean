-- Prove2me | Definitions.Def_DynStrings_Strings
-- name    : DynStrings_Strings
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:02.281886+00:00
-- url     : https://prove2.me/theorems/fc4ec8a6-bc54-4e7f-83a7-28d148713eba
-- title:
--   Fragments, substring complexity $\delta$, the space bound $D$, and relative novelty $e_m(X\mid\mathcal C)$, $\delta(X\mid\mathcal C)$, $\Lambda(X\mid\mathcal C)$
-- statement:
--   The string vocabulary of the mission.
--
--   A string $S$ of length $n=|S|$ has characters $S[1],\dots,S[n]$; a cut is an integer in $[0..n]$, and for cuts $i\le j$ the fragment $S(i..j]=S[i+1]\cdots S[j]$. For $m\ge1$, $d_m(S)$ is the number of distinct length-$m$ substrings of $S$ (zero for $m>|S|$), and the substring complexity is
--
--   $$\delta(S)=\max_{m\ge1}\frac{d_m(S)}{m}.$$
--
--   Further, $\sigma=d_1(S)$ is the number of distinct characters, $\log$ is the base-2 logarithm, $\lg x=\log\max\{2,x\}$, and
--
--   $$D=\delta\,\lg\Big(\frac{n\log\sigma}{\delta\log n}\Big).$$
--
--   A collection $\mathcal C$ is a finite multiset of strings, and $\mathrm{Sub}_m(\mathcal C)$ is the set of length-$m$ substrings of its members. The novelty profile, the relative substring complexity and the dyadic novelty of $X$ relative to $\mathcal C$ are
--
--   $$e_m(X\mid\mathcal C)=|\mathrm{Sub}_m(X)\setminus\mathrm{Sub}_m(\mathcal C)|,\qquad \delta(X\mid\mathcal C)=\max_{m\ge1}\frac{e_m(X\mid\mathcal C)}{m},\qquad \Lambda(X\mid\mathcal C)=\sum_{p=0}^{\lceil\lg|X|\rceil}\Big(1+\frac{e_{2^p}(X\mid\mathcal C)}{2^p}\Big).$$
--
--   These quantities measure the compressibility of a string, alone and relative to strings already stored; every bound of the mission is stated in terms of them.
--
--   **Formalization Note** Strings are lists over an arbitrary alphabet type with decidable equality. The maxima over $m\ge1$ are computed over $1\le m\le\max\{1,|S|\}$, beyond which the counts vanish; both are $0$ for the empty string.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), §3, p.13 (logarithms, fragments, d_m, δ, σ, D); p.14 (collections); §5.1, p.19 (e_m, δ(X | C), Λ(X | C))

import Mathlib

namespace DynStrings

/-!
# Strings, substring complexity, and relative novelty

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), §3, p.13 (logarithms, fragments, substring complexity, `D`), p.14
(collections), and §5.1, p.19 (novelty profile, relative substring complexity, dyadic novelty).

**Formalization Note.**
* Strings are `List α` over an arbitrary alphabet type `α` with decidable equality (the paper fixes
  a countably infinite alphabet `Σ`).
* Cuts are natural numbers in `[0, |S|]`; the fragment `S(i..j] = S[i+1] ⋯ S[j]` (1-based
  characters) is `frag S i j = (S.drop i).take (j - i)`.
* `log` is `Real.logb 2`, `ln` is `Real.log`, and `lg x = Real.logb 2 (max 2 x)`.
* A maximum `max_{m ≥ 1} f(m)/m` of a count `f` that vanishes for `m > N` is computed as a
  maximum over the finite range `1 ≤ m ≤ max 1 N` (`maxRatio`); it is `0` for the empty string, as
  the paper's maximum is.
* Collections are finite multisets `Multiset (List α)`; a substring of a collection is a substring
  of one of its members.
-/

/-- The fragment `S(i..j] = S[i+1] S[i+2] ⋯ S[j]` of a string over any alphabet (p.13), for cuts
`i ≤ j`. -/
def frag {β : Type} (S : List β) (i j : ℕ) : List β := (S.drop i).take (j - i)

/-- `Sub_m(S)`: the set of distinct length-`m` substrings of `S` (p.13, p.19). It is empty for
`m > |S|`. -/
def subs {α : Type} [DecidableEq α] (m : ℕ) (S : List α) : Finset (List α) :=
  ((List.range (S.length + 1 - m)).map fun i => frag S i (i + m)).toFinset

/-- `d_m(S)`: the number of distinct length-`m` substrings of `S` (p.13). -/
def dsub {α : Type} [DecidableEq α] (m : ℕ) (S : List α) : ℕ := (subs m S).card

/-- `max_{m ≥ 1} f(m)/m` for a count `f` vanishing beyond `N`, computed over `1 ≤ m ≤ max 1 N`. -/
noncomputable def maxRatio (f : ℕ → ℕ) (N : ℕ) : ℝ :=
  (Finset.Icc 1 (max 1 N)).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩⟩
    (fun m => (f m : ℝ) / m)

/-- The substring complexity `δ(S) = max_{m ≥ 1} d_m(S)/m` (p.13). -/
noncomputable def delta {α : Type} [DecidableEq α] (S : List α) : ℝ :=
  maxRatio (fun m => dsub m S) S.length

/-- `σ = d_1(S)`, the number of distinct characters of `S` (p.13). -/
def sigma {α : Type} [DecidableEq α] (S : List α) : ℕ := dsub 1 S

/-- The truncated logarithm `lg x = log max{2, x}` (base 2, p.13). -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 (max 2 x)

/-- `D = δ lg(n log σ / (δ log n))`, the optimal worst-case space (p.13), with `n = |S|`. -/
noncomputable def Dspace {α : Type} [DecidableEq α] (S : List α) : ℝ :=
  delta S * lg ((S.length : ℝ) * Real.logb 2 (sigma S) / (delta S * Real.logb 2 S.length))

/-- `Sub_m(𝒞)`: the length-`m` substrings of the members of a collection (p.14, p.19). -/
def subsColl {α : Type} [DecidableEq α] (m : ℕ) (𝒞 : Multiset (List α)) : Finset (List α) :=
  𝒞.toFinset.biUnion (subs m)

/-- The novelty profile `e_m(X | 𝒞) = |Sub_m(X) \ Sub_m(𝒞)|` (§5.1, p.19). -/
def enov {α : Type} [DecidableEq α] (m : ℕ) (X : List α) (𝒞 : Multiset (List α)) : ℕ :=
  (subs m X \ subsColl m 𝒞).card

/-- The relative substring complexity `δ(X | 𝒞) = max_{m ≥ 1} e_m(X | 𝒞)/m` (§5.1, p.19). -/
noncomputable def deltaRel {α : Type} [DecidableEq α] (X : List α) (𝒞 : Multiset (List α)) : ℝ :=
  maxRatio (fun m => enov m X 𝒞) X.length

/-- The dyadic novelty `Λ(X | 𝒞) = ∑_{p=0}^{⌈lg |X|⌉} (1 + e_{2^p}(X | 𝒞)/2^p)` (§5.1, p.19). -/
noncomputable def Lam {α : Type} [DecidableEq α] (X : List α) (𝒞 : Multiset (List α)) : ℝ :=
  ∑ p ∈ Finset.range (⌈lg X.length⌉₊ + 1), (1 + (enov (2 ^ p) X 𝒞 : ℝ) / 2 ^ p)

end DynStrings


