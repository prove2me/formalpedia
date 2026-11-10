-- Prove2me | Definitions.Def_SliceLinearity_Tests_Pivot
-- name    : SliceLinearity_Tests_Pivot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:51.099637+00:00
-- url     : https://prove2.me/theorems/aa841606-fb81-406e-a1c1-b1eb7496e753
-- title:
--   The pivot test on the constant-weight slice $S(r)$ ($r+1$ queries for even $r$, $2r+2$ for odd $r$)
-- statement:
--   Identify a point of $S(r)$ with the $r$-set of its nonzero coordinates, and write $\mathbb 1_A$ for the indicator vector of $A\subseteq[n]$.
--
--   **One check.** Choose a uniform $(r-1)$-set $B$ (the pivot) and a uniform $r$-set $S$ disjoint from $B$. Query $f(\mathbb 1_S)$ and $f(\mathbb 1_{B\cup\{i\}})$ for $i\in S$, and accept if $f(S)=\chi_B(S)=\sum_{i\in S}f(B\cup\{i\})$. Its $r+1$ queries sum to $0$ when $r$ is even.
--
--   **Pivot test.**
--   - For **even** $r$ the test is one check ($r+1$ queries).
--   - For **odd** $r$ it is two independent checks with the same pivot, $S$ and $T$, accepting if $f(S)+f(T)=\chi_B(S)+\chi_B(T)$ ($2r+2$ queries, which sum to $0$).
--
--   **Formalization Note** The $r$-set $S$ is drawn as the image of a uniformly random injective $s:[r]\to[n]\setminus B$, so it is uniform and its elements come in uniformly random order. The tuple is $(\mathbb 1_S,\mathbb 1_{B\cup\{s_0\}},\dots,\mathbb 1_{B\cup\{s_{r-1}\}})$. For odd $r$ the two checks are concatenated. Query order changes neither acceptance nor completeness.
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6.3 and the proof of Proposition 6.17, pp. 50–51 (PDF 52–53)

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests

set_option autoImplicit false

namespace SliceLinearity.Tests

/-! # The pivot test on the constant-weight slice `S(r)`

Aydin, Larsen, Mittal, Richelson, Roy, *Low Soundness Linearity Testing on Subsets of the Hypercube*,
STOC 2027 submission (manuscript sha256 457be236…), §6.3 and the proof of Proposition 6.17,
pp. 50–51 (PDF 52–53).

A point of `S(r)` is the indicator of an `r`-set. A uniform `(r−1)`-set `B` (the pivot) is chosen;
an `r`-set disjoint from `B` is drawn as the image of a uniformly random injective
`s : Fin r → Fin n` avoiding `B` (this is a uniform `r`-set `S ⊆ Bᶜ`, listed in uniformly random
order). One check queries `1_S` and `1_{B ∪ {s_j}}` for `j < r`. -/

open Classical in
/-- The indicator vector `1_A ∈ F₂ⁿ` of `A ⊆ [n]`. -/
noncomputable def indicator {n : ℕ} (A : Finset (Fin n)) : Cube n :=
  fun i => if i ∈ A then 1 else 0

/-- `s` lists `r` distinct coordinates outside the pivot `B`. -/
def PivotGood {n r : ℕ} (B : Finset (Fin n)) (s : Fin r → Fin n) : Prop :=
  Function.Injective s ∧ ∀ j, s j ∉ B

open Classical in
/-- The number of injective `s : Fin r → Fin n` avoiding `B`. -/
noncomputable def pivotCount (n r : ℕ) (B : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun s : Fin r → Fin n => PivotGood B s).card

open Classical in
/-- One check of the pivot test: the `r + 1` queries `1_S, 1_{B ∪ {s₀}}, …, 1_{B ∪ {s_{r−1}}}`
with `S = {s₀, …, s_{r−1}}`. -/
noncomputable def pivotCheck {n r : ℕ} (B : Finset (Fin n)) (s : Fin r → Fin n) :
    Fin (r + 1) → Cube n :=
  Fin.cons (indicator (Finset.univ.image s)) fun j => indicator (insert (s j) B)

open Classical in
/-- The query distribution of the pivot test for **even** `r` (`r + 1` queries): a uniform
`(r−1)`-set `B` and one uniform check. -/
noncomputable def pivotEvenW (n r : ℕ) (t : Fin (r + 1) → Cube n) : ℝ :=
  ∑ B ∈ Finset.powersetCard (r - 1) (Finset.univ : Finset (Fin n)), ∑ s : Fin r → Fin n,
    if PivotGood B s ∧ t = pivotCheck B s then
      1 / (((n.choose (r - 1) : ℕ) : ℝ) * (pivotCount n r B : ℝ)) else 0

open Classical in
/-- The query distribution of the pivot test for **odd** `r` (`2r + 2` queries): a uniform
`(r−1)`-set `B` and two independent uniform checks, queried one after the other. -/
noncomputable def pivotOddW (n r : ℕ) (t : Fin (2 * r + 2) → Cube n) : ℝ :=
  ∑ B ∈ Finset.powersetCard (r - 1) (Finset.univ : Finset (Fin n)), ∑ s : Fin r → Fin n,
    ∑ s' : Fin r → Fin n,
      if PivotGood B s ∧ PivotGood B s' ∧
          t = Fin.append (pivotCheck B s) (pivotCheck B s') ∘ Fin.cast (by omega) then
        1 / (((n.choose (r - 1) : ℕ) : ℝ) * (pivotCount n r B : ℝ) ^ 2) else 0

end SliceLinearity.Tests


