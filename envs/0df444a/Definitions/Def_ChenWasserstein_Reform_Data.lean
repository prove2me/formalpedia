-- Prove2me | Definitions.Def_ChenWasserstein_Reform_Data
-- name    : ChenWasserstein_Reform_Data
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:13.831271+00:00
-- url     : https://prove2.me/theorems/7c38eb0c-c661-4aba-b4d4-b8f36482dcd5
-- title:
--   Fractional sorted sums and the explicit greedy transport law
-- statement:
--   For a finite array $k$ of $N$ real values, let $k_{(j)}$ be its order statistics counting multiplicities. For $0\le\ell\le N$, define the fractional sum of the smallest values by
--   $$F_k(\ell)=\sum_{j=1}^{\lfloor\ell\rfloor}k_{(j)}+(\ell-\lfloor\ell\rfloor)k_{(\lfloor\ell\rfloor+1)}.$$
--   At $\ell=N$ the fractional term is omitted. The integer prefix of an already ordered array $d$ is $D(j)=\sum_{i=1}^j d_i$. Let $I$ count the zero entries and let $j^*=\max\{0\le j\le N:D(j)\le\theta N\}$. If $j^*<N$, set $p^*=(\theta N-D(j^*))/d_{j^*+1}$; otherwise set $p^*=0$.
--
--   Given samples $\xi_i$ and target points $\eta_i$, the full law retains the first $I$ atoms and moves the rest to $\eta_i$, each with mass $1/N$. The partial law retains the first $I$ atoms, moves indices $I+1,\ldots,j^*$ fully, splits atom $j^*+1$ between $\eta_{j^*+1}$ and $\xi_{j^*+1}$ with fractions $p^*$ and $1-p^*$, and retains the remaining atoms. The greedy law selects the full law when $j^*=N$ and the partial law otherwise.
--
--   These constructions supply the fractional sums and explicit measures in the three supporting results. They make no assertion of optimality.
--
--   **Formalization Note** Indices are zero-based. The total functions also accept inputs outside the mathematical domain: the integer prefix saturates above $N$; the fractional full-prefix length is capped at $N$; the natural floor is zero for negative arguments; an empty affordable set has maximum zero; division by zero is zero; a negative measure coefficient is truncated by conversion to an extended nonnegative real. With $N=0$ both laws are zero measures. Theorems impose $N>0$, positive radius, genuine nonnegative sorted distances, and closest unsafe targets, so these defaults do not alter their intended cases. Published order statistics, empirical measures, distances and transport costs are reused.
-- source:
--   Chen, Kuhn and Wiesemann, Technical Note—Data-Driven Chance Constrained Programs over Wasserstein Balls, Operations Research 72(1) (2024), 410–424, https://doi.org/10.1287/opre.2022.2330, §1.2 and Theorem 1, printed p. 413, PDF p. 4

import Mathlib
import Definitions.Def_WassDRCCP_Improved_Setting

open MeasureTheory
open scoped ENNReal BigOperators

/- Imported declaration body, quoted verbatim for standalone blind auditing.
noncomputable def kthSmallest {N : ℕ} (v : Fin N → ℝ) (j : ℕ) : ℝ :=
  ((Finset.univ.val.map v).sort (· ≤ ·)).getD j 0
-/

namespace ChenWasserstein.Reform

/-- Integer prefix of an already ordered array; paper indices 1,...,j are Fin indices < j. -/
noncomputable def prefixSum {N : ℕ} (d : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, if i.val < j then d i else 0

/-- Fractional sum of the smallest ℓ entries, with multiplicity. At ℓ = N the next
entry is not read. The intended domain is 0 ≤ ℓ ≤ N. -/
noncomputable def fractionalSmallest {N : ℕ} (k : Fin N → ℝ) (ℓ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (min ⌊ℓ⌋₊ N), WassDRCCP.Improved.kthSmallest k j) +
    if ⌊ℓ⌋₊ < N then
      (ℓ - (⌊ℓ⌋₊ : ℝ)) * WassDRCCP.Improved.kthSmallest k ⌊ℓ⌋₊ else 0

/-- The number I of zero distances. For nonnegative ordered d these form the first I entries. -/
noncomputable def zeroCount {N : ℕ} (d : Fin N → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => d i = 0)).card

/-- Largest integer prefix affordable with the unnormalized budget θ N.
The finite supremum defaults to 0 if its set is empty; for θ > 0 the set contains 0. -/
noncomputable def jStar {N : ℕ} (d : Fin N → ℝ) (θ : ℝ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun j => prefixSum d j ≤ θ * (N : ℝ))).sup id

/-- The fraction of the next atom transported. The jStar = N branch returns 0 and
does not evaluate a next entry. Under Theorem 1's assumptions its active denominator is positive. -/
noncomputable def pStar {N : ℕ} (d : Fin N → ℝ) (θ : ℝ) : ℝ :=
  if h : jStar d θ < N then
    (θ * (N : ℝ) - prefixSum d (jStar d θ)) / d ⟨jStar d θ, h⟩
  else 0

/-- Theorem 1(i): retain the first I atoms and move all remaining atoms to η. -/
noncomputable def fullLaw {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξ η : Fin N → E) (d : Fin N → ℝ) : Measure E :=
  (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N,
    if i.val < zeroCount d then Measure.dirac (ξ i) else Measure.dirac (η i)

/-- Theorem 1(ii), with paper's jStar+1 represented by Fin index jStar.
The outer normalization gives weights 1/N, pStar/N and (1-pStar)/N. -/
noncomputable def partialLaw {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξ η : Fin N → E) (d : Fin N → ℝ) (θ : ℝ) : Measure E :=
  (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N,
    if i.val < zeroCount d then Measure.dirac (ξ i)
    else if i.val < jStar d θ then Measure.dirac (η i)
    else if i.val = jStar d θ then
      ENNReal.ofReal (pStar d θ) • Measure.dirac (η i) +
        ENNReal.ofReal (1 - pStar d θ) • Measure.dirac (ξ i)
    else Measure.dirac (ξ i)

/-- The explicitly constructed measure PStar, with both cases of Theorem 1. -/
noncomputable def greedyLaw {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξ η : Fin N → E) (d : Fin N → ℝ) (θ : ℝ) : Measure E :=
  if jStar d θ = N then fullLaw ξ η d else partialLaw ξ η d θ

end ChenWasserstein.Reform


