-- Prove2me | Definitions.Def_LewensteinGreedy_Competitive_Quotient
-- name    : LewensteinGreedy_Competitive_Quotient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:03.953958+00:00
-- url     : https://prove2.me/theorems/8371fa7d-71f3-4360-b42b-969ff0681fd0
-- title:
--   The inactive-gap quotient, the visibility potential $\Phi_A$ and the active touches $U$ (§6, eq. (6.1))
-- statement:
--   Let $A=\{x_1,\dots,x_m\}$ be the set of requested keys and $k=|A|$. **Inactive gaps** are the nonempty maximal intervals of $[n]$ containing no key of $A$. Partition $[n]$ into the active singletons $\{a\}$, $a\in A$, and the inactive gaps; let $N$ be the number of parts and $\pi:[n]\to[N]$ the order-preserving quotient map (the rank of a key's part in key order). $Y=(\pi(x_1),\dots,\pi(x_m))$, and $\bar h(J)=\max_{v\in J}h(v)$ is the quotient profile. Greedy on $Y$ runs on $[N]$ from $\bar h$.
--
--   For an inactive gap $J$, $V_J(h)$ is the union of the strict prefix-height records and the strict suffix-height records of $J$ (scan $J$ from each end; a key is included if its height exceeds every height preceding it in at least one of the scans; each end key is a record). $\Phi_A(h)=\sum_{J\text{ inactive}}|V_J(h)|$ (6.1). $U$ is the total number of touches on keys of $A$ in Greedy's execution on $X$ from $h$, including active keys touched when not requested.
--
--   **Formalization Note.** `inactiveGaps n A` are the sets `Icc a b` ⊆ $[n]$, $a\le b$, disjoint from $A$, with ($a=1$ or $a-1\in A$) and ($b=n$ or $b+1\in A$). `quotientParts n X` adds the singletons of `X.toFinset`; `quotientSize n X` $=N$; `quotientMap n X v` $=\pi(v)$ is the number of parts whose least key is $\le v$; `quotientSequence n X` $=Y$; `quotientProfile n X h i` is the maximum of $h$ over the keys $v\in[n]$ with $\pi(v)=i$. The quotient execution uses the same Greedy definition on $[N]$; its new height $\max\bar h+1$ equals the original's $\max h+1$ as long as $\bar h$ is the partwise maximum of $h$, which is the source's "same new height in both executions". `visibleRecords J h` $=V_J(h)$, `visibilityPotential n X h` $=\Phi_A(h)$, `activeTouches n X h` $=U=\sum_t|S_t\cap A|$.
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, §6, eq. (6.1), printed p. 38–39 / PDF 39–40

import Mathlib
import Definitions.Def_LewensteinGreedy_Competitive_Greedy

set_option autoImplicit false

noncomputable section

namespace LewensteinGreedy.Competitive

/-!
# The inactive-gap quotient, the visibility potential `Φ_A` and active touches `U`

Lewenstein, *Greedy BST is O(log log n)-Competitive*, supplied 2026 artifact (SHA-256
04ac49f6…), §6, printed pp.38–39 / PDF 39–40, equation (6.1).

Let `A = X.toFinset` be the set of requested keys (`k = |A|`).

* `inactiveGaps n A`: the maximal nonempty intervals `[a, b] ⊆ [n]` containing no key of `A`.
* `quotientParts n X`: the partition of `[n]` into the active singletons `{x}`, `x ∈ A`, and the
  inactive gaps; `quotientSize n X = N` is the number of parts.
* `quotientMap n X v = π(v)`: the rank (`1..N`, in key order) of the part containing `v`, i.e. the
  number of parts whose least key is `≤ v`. It is the order-preserving quotient map `[n] → [N]`.
* `quotientSequence n X = Y = (π(x_1), …, π(x_m))`.
* `quotientProfile n X h = h̄`, `h̄(i) = max {h v : v ∈ [n], π v = i}`.
  The quotient execution of Greedy on `Y` from `h̄` uses `greedyStep N`, whose new height
  `max h̄ + 1` coincides with the original execution's `max h + 1` as long as `h̄` is the
  partwise maximum of `h` (the source chooses "the same new height in both executions").
* `visibleRecords J h = V_J(h)`: the keys of `J` that are strict prefix-height records or strict
  suffix-height records of `J` (each end key is a record).
* `visibilityPotential n X h = Φ_A(h) = ∑_{J inactive} |V_J(h)|`.
* `activeTouches n X h = U`: the total number of touches on keys of `A` in Greedy's execution on
  `X` from `h`, including active keys touched when not requested.
-/

/-- The maximal nonempty intervals of `[n]` avoiding `A`. -/
def inactiveGaps (n : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((Finset.Icc 1 n).powerset).filter fun J =>
    ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ n ∧ J = Finset.Icc a b ∧
      Disjoint J A ∧ (a = 1 ∨ a - 1 ∈ A) ∧ (b = n ∨ b + 1 ∈ A)

/-- The partition of `[n]` into active singletons and inactive gaps. -/
def quotientParts (n : ℕ) (X : List ℕ) : Finset (Finset ℕ) :=
  inactiveGaps n X.toFinset ∪ X.toFinset.image (fun x => {x})

/-- The order-preserving quotient map `π : [n] → [N]`. -/
def quotientMap (n : ℕ) (X : List ℕ) (v : ℕ) : ℕ := by
  classical
  exact ((quotientParts n X).filter fun J => (J.sort (· ≤ ·)).headD 0 ≤ v).card

/-- `N`, the number of partition intervals. -/
def quotientSize (n : ℕ) (X : List ℕ) : ℕ := (quotientParts n X).card

/-- `Y = π(X)`. -/
def quotientSequence (n : ℕ) (X : List ℕ) : List ℕ := X.map (quotientMap n X)

/-- `h̄(i)`: the maximum original height in the `i`-th part. -/
def quotientProfile (n : ℕ) (X : List ℕ) (h : Profile) : Profile := fun i =>
  maxHeight ((Finset.Icc 1 n).filter fun v => quotientMap n X v = i) h

/-- `V_J(h)`: strict prefix-height records or strict suffix-height records of `J`. -/
def visibleRecords (J : Finset ℕ) (h : Profile) : Finset ℕ := by
  classical
  exact J.filter fun v => (∀ u ∈ J, u < v → h u < h v) ∨ (∀ u ∈ J, v < u → h u < h v)

/-- `Φ_A(h) = ∑_{J inactive} |V_J(h)|`, (6.1). -/
def visibilityPotential (n : ℕ) (X : List ℕ) (h : Profile) : ℕ :=
  ∑ J ∈ inactiveGaps n X.toFinset, (visibleRecords J h).card

/-- `U`: all touches on requested keys during Greedy's execution of `X` from `h`. -/
def activeTouches (n : ℕ) (X : List ℕ) (h : Profile) : ℕ :=
  ((touchRows n X h).map fun S => (S ∩ X.toFinset).card).sum

end LewensteinGreedy.Competitive


