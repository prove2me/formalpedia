-- Prove2me | Definitions.Def_Lubbecke2005_SubcolumnPricing_Columns
-- name    : Lubbecke2005_SubcolumnPricing_Columns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:07:50.762057+00:00
-- url     : https://prove2.me/theorems/fd097a7e-d24f-4fae-bac4-b96e504d1593
-- title:
--   Set-partitioning columns: incidence vectors, (strictly) redundant columns (30), subcolumn property, ratio pricing objective (31)
-- statement:
--   Fix $m$ rows $\{1,\dots,m\}$ of a set-partitioning master problem. A **column** is identified with the set $s \subseteq \{1,\dots,m\}$ of rows it covers; its **incidence vector** is $\mathbf a_s \in \{0,1\}^m$, with $(\mathbf a_s)_i = 1$ if $i \in s$ and $0$ otherwise. Let $\mathcal A$ be a finite collection of columns and let $\mathbf c$ assign a cost $c_s$ to each column.
--
--   1. **Redundant column (eq. (30)).** A column $s$ is *redundant* (with respect to $\mathcal A$ and $\mathbf c$) if there are multipliers $\lambda_r \ge 0$ such that
--   $$\mathbf a_s = \sum_{r \in \mathcal A,\ r \subsetneq s} \mathbf a_r \lambda_r \qquad\text{and}\qquad c_s \ge \sum_{r \in \mathcal A,\ r \subsetneq s} c_r \lambda_r .$$
--   2. **Strictly redundant column.** The same, with the strict cost inequality $c_s > \sum_{r \subsetneq s} c_r \lambda_r$.
--   3. **Subcolumn property.** The pair $(\mathcal A, \mathbf c)$ has the subcolumn property if $c_r < c_s$ for all $r, s \in \mathcal A$ with $r \subsetneq s$.
--   4. **Ratio pricing objective (eq. (31)).** For a vector of dual multipliers $\bar{\mathbf u} \in \mathbb R^m$, the ratio of a column $\mathbf a$ is
--   $$\frac{c(\mathbf a) - \bar{\mathbf u}^{\mathsf T}\mathbf a}{\mathbf 1^{\mathsf T}\mathbf a},$$
--   its reduced cost divided by the number of rows it covers.
--
--   A redundant column corresponds to a constraint $\bar{\mathbf u}^{\mathsf T}\mathbf a_s \le c_s$ of the dual of the master problem that is implied by the constraints of its subcolumns, so it adds nothing to the dual polyhedron. These notions are the vocabulary of Proposition 2 of the paper.
--
--   **Formalization Note.** The paper writes (30) without a sign on $\lambda_r$ and without saying over which $r$ the sums range; this definition reads it as $\lambda_r \ge 0$ (the Farkas form of "the corresponding constraint is redundant for the dual problem"; with signed $\lambda$ Proposition 2 is false) and as a sum over the columns $r \in \mathcal A$ that are proper subsets of $s$ (the paper's $r \subset s$ is proper inclusion). Columns are `Finset (Fin m)` (rows indexed from $0$), costs a function `Finset (Fin m) → ℝ` of which only the values on $\mathcal A$ matter, and the multipliers a function on all sets of which only the values on the proper subcolumns of $s$ enter. "Strictly redundant" makes the cost inequality strict; the equality part of (30) is unchanged. The denominator $\mathbf 1^{\mathsf T}\mathbf a$ is written as a dot product with the all-ones vector; it equals $|a|$. On the empty column it is $0$ and Lean's division returns $0$; theorems using the ratio exclude the empty column.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1015, §5.1, Eq. (30) and the subcolumn property; p. 1016, Eq. (31)

import Mathlib

namespace Lubbecke2005.SubcolumnPricing

/-- The incidence vector `𝐚_r ∈ {0,1}^m` of a set `r` of rows: entry `1` on the rows in `r`,
`0` elsewhere. -/
noncomputable def incidence {m : ℕ} (r : Finset (Fin m)) : Fin m → ℝ :=
  fun i => if i ∈ r then 1 else 0

/-- Redundant column, eq. (30): the column `𝐚_s` is a nonnegative combination of the columns
`𝐚_r`, `r ∈ 𝒜`, `r ⊊ s`, whose cost is at most `c_s`:
`𝐚_s = ∑_{r ⊂ s} 𝐚_r λ_r` and `c_s ≥ ∑_{r ⊂ s} c_r λ_r`, with `λ ≥ 0` (here `lam`). -/
def IsRedundant {m : ℕ} (𝒜 : Finset (Finset (Fin m))) (c : Finset (Fin m) → ℝ)
    (s : Finset (Fin m)) : Prop :=
  ∃ lam : Finset (Fin m) → ℝ, (∀ r, 0 ≤ lam r) ∧
    (∑ r ∈ 𝒜.filter (· ⊂ s), lam r • incidence r) = incidence s ∧
    ∑ r ∈ 𝒜.filter (· ⊂ s), c r * lam r ≤ c s

/-- Strictly redundant column: (30) with strict cost inequality
`𝐚_s = ∑_{r ⊂ s} 𝐚_r λ_r` and `c_s > ∑_{r ⊂ s} c_r λ_r`, with `λ ≥ 0` (here `lam`). -/
def IsStrictlyRedundant {m : ℕ} (𝒜 : Finset (Finset (Fin m))) (c : Finset (Fin m) → ℝ)
    (s : Finset (Fin m)) : Prop :=
  ∃ lam : Finset (Fin m) → ℝ, (∀ r, 0 ≤ lam r) ∧
    (∑ r ∈ 𝒜.filter (· ⊂ s), lam r • incidence r) = incidence s ∧
    ∑ r ∈ 𝒜.filter (· ⊂ s), c r * lam r < c s

/-- Subcolumn property of `(𝒜, 𝐜)`: `c_r < c_s` for all `r ⊊ s` with `r, s ∈ 𝒜`. -/
def SubcolumnProperty {m : ℕ} (𝒜 : Finset (Finset (Fin m))) (c : Finset (Fin m) → ℝ) : Prop :=
  ∀ r ∈ 𝒜, ∀ s ∈ 𝒜, r ⊂ s → c r < c s

/-- The objective of the ratio pricing problem (31) at the column `𝐚` (row set `a`):
`(c(𝐚) − ūᵀ𝐚) / 𝟏ᵀ𝐚`, where `𝟏ᵀ𝐚 = |a|` is the number of rows the column covers. -/
noncomputable def pricingRatio {m : ℕ} (c : Finset (Fin m) → ℝ) (u : Fin m → ℝ)
    (a : Finset (Fin m)) : ℝ :=
  (c a - u ⬝ᵥ incidence a) / ((1 : Fin m → ℝ) ⬝ᵥ incidence a)

end Lubbecke2005.SubcolumnPricing


