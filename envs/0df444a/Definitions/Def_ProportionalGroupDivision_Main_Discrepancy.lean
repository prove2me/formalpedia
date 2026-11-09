-- Prove2me | Definitions.Def_ProportionalGroupDivision_Main_Discrepancy
-- name    : ProportionalGroupDivision_Main_Discrepancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:03.318467+00:00
-- url     : https://prove2.me/theorems/54ae74ba-f35f-484c-9c58-55534a16ebd6
-- title:
--   Definitions 2–3 — one-sided $k$-matrix discrepancy $\mathrm{disc}^k_>(n_1,\dots,n_k)$
-- statement:
--   Let $A^1\in[0,1]^{n_1\times m},\dots,A^k\in[0,1]^{n_k\times m}$ be matrices; $A^i_j$ is the $j$-th row of $A^i$ (the valuation vector of agent $j$ of group $i$). A **partition** is a family $v_1,\dots,v_k\in\{0,1\}^m$ with $\sum_i v_i=\mathbf 1$. The **one-sided $k$-matrix discrepancy** $\mathrm{disc}^k_>(A^1,\dots,A^k)$ is the smallest $c$ such that some partition satisfies
--
--   $$\langle A^i_j,v_i\rangle\ \ge\ \langle A^i_j,\mathbf 1/k\rangle-c\qquad\text{for all } i\in[k],\ j\in[n_i],$$
--
--   and the worst case over all positive integers $m$ and all such matrices is
--
--   $$\mathrm{disc}^k_>(n_1,\dots,n_k)=\sup_{m\ge1}\ \sup_{A^i\in[0,1]^{n_i\times m}}\ \mathrm{disc}^k_>(A^1,\dots,A^k).$$
--
--   Since there are finitely many partitions, the inner minimum is attained; the outer supremum need not be. This is the discrepancy counterpart of $\mathrm{PROP}$ (Lemma 3). The ceiling $\lceil x\rceil$ of an extended nonnegative real, with $\lceil\infty\rceil=\infty$, is also defined here.
--
--   **Formalization Note** A partition is a map $\sigma$ from columns to groups ($v_i$ is the indicator of $\sigma^{-1}(i)$). One instance's value is the minimum over $\sigma$ of the largest shortfall $\langle A^i_j,\mathbf 1/k\rangle-\langle A^i_j,v_i\rangle$ truncated at $0$, in $\mathbb R_{\ge0}\cup\{\infty\}$; the worst case is an extended supremum, so an unbounded family would give $\infty$ rather than a junk real value. The truncation at $0$ does not change the worst case: the zero matrices are admissible and have value $0$.
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Definitions 2 and 3, PDF p. 3 = printed p. 3

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Model

open scoped BigOperators ENNReal

namespace ProportionalGroupDivision.Main

/-!
# One-sided `k`-matrix discrepancy (Definitions 2–3, PDF p. 3)

Group `i` has a matrix `A^i ∈ [0,1]^{n_i × m}` whose row `j` is the valuation vector of agent
`(i, j)`. A partition `v_1, …, v_k ∈ {0,1}^m` with `∑ v_i = 𝟙` is a map `σ : Fin m → Fin k`
(`v_i` is the indicator of `bundle σ i`). Row `(i, j)` has ideal share `⟨A^i_j, 𝟙/k⟩` and receives
`⟨A^i_j, v_i⟩`. The one-sided discrepancy `disc^k_>(A^1, …, A^k)` is the smallest `c` such that
some partition has `⟨A^i_j, v_i⟩ ≥ ⟨A^i_j, 𝟙/k⟩ − c` for all rows, and
`disc^k_>(n_1, …, n_k)` is its maximum over all positive `m` and all such matrices.
-/

/-- The matrices `A^1, …, A^k` of an instance with row counts `n` and `m` columns. -/
abbrev GroupMatrices {k : ℕ} (n : Fin k → ℕ) (m : ℕ) : Type :=
  (i : Fin k) → Matrix (Fin (n i)) (Fin m) ℝ

/-- Every entry lies in `[0, 1]`. -/
def IsUnitEntries {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (A : GroupMatrices n m) : Prop :=
  ∀ i j g, 0 ≤ A i j g ∧ A i j g ≤ 1

/-- The ideal share `⟨A^i_j, 𝟙/k⟩ = (∑_g A^i_{j,g}) / k` of row `(i, j)`. -/
noncomputable def rowShare {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (A : GroupMatrices n m) (i : Fin k)
    (j : Fin (n i)) : ℝ :=
  (∑ g, A i j g) / (k : ℝ)

/-- The value `⟨A^i_j, v_i⟩` row `(i, j)` receives under the partition `σ`. -/
def rowGain {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (A : GroupMatrices n m) (σ : Fin m → Fin k)
    (i : Fin k) (j : Fin (n i)) : ℝ :=
  ∑ g ∈ bundle σ i, A i j g

/-- The largest one-sided shortfall `max_{i,j} (⟨A^i_j, 𝟙/k⟩ − ⟨A^i_j, v_i⟩)` of a partition,
truncated at `0` (an `ℝ≥0∞` value). -/
noncomputable def shortfall {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (A : GroupMatrices n m)
    (σ : Fin m → Fin k) : ℝ≥0∞ :=
  ⨆ (i : Fin k) (j : Fin (n i)), ENNReal.ofReal (rowShare A i j - rowGain A σ i j)

/-- Definition 3 (p. 3), one instance: `max(0, disc^k_>(A^1, …, A^k))`, the minimum over the
(finitely many) partitions of the largest shortfall. -/
noncomputable def instanceDisc {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (A : GroupMatrices n m) : ℝ≥0∞ :=
  ⨅ σ : Fin m → Fin k, shortfall A σ

/-- Definitions 2–3 (p. 3): the worst-case one-sided discrepancy `disc^k_>(n_1, …, n_k)`, the
supremum over all positive integers `m` and all matrices `A^i ∈ [0,1]^{n_i × m}`. It is an
`ℝ≥0∞` supremum, so an unbounded family gives `⊤`; no attainment is assumed. -/
noncomputable def discOne {k : ℕ} (n : Fin k → ℕ) : ℝ≥0∞ :=
  ⨆ (m : ℕ) (_ : 0 < m) (A : GroupMatrices n m) (_ : IsUnitEntries A), instanceDisc A

/-- The ceiling `⌈x⌉` of an extended nonnegative real, in `ℕ∞` (`⌈⊤⌉ = ⊤`). -/
noncomputable def ceilE (x : ℝ≥0∞) : ℕ∞ :=
  if x = ⊤ then ⊤ else ((⌈x.toReal⌉₊ : ℕ) : ℕ∞)

end ProportionalGroupDivision.Main


