-- Prove2me | Definitions.Def_MinSumFPT_Supplement_Median2
-- name    : MinSumFPT_Supplement_Median2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:17:17.912198+00:00
-- url     : https://prove2.me/theorems/0a5d11da-fec7-4944-aacb-1c5ffa0bd2da
-- title:
--   Gap balanced 2-median instances
-- statement:
--   An instance consists of facilities $f_1,\dots,f_n$, clients $c_1,\dots,c_m$ and a distance function $\Delta:C\times F\to\mathbb R_{\ge0}$ (no metric axioms).
--
--   1. **Completeness case**: there are $i,j\in[n]$ and an equipartition $C=C_1\sqcup C_2$, $|C_1|=|C_2|$, with
--   $$
--   \sum_{c\in C_1}\Delta(c,f_i)+\sum_{c\in C_2}\Delta(c,f_j)=|C|.
--   $$
--   2. **Soundness case** (for a gap $\delta$): for every $i,j\in[n]$,
--   $$
--   \sum_{c\in C}\min\{\Delta(c,f_i),\Delta(c,f_j)\}\ge(1+\delta)\,|C|.
--   $$
--
--   The completeness case says that the balanced 2-median problem has a solution of cost $|C|$; the soundness case that even the unbalanced 2-median problem costs at least $(1+\delta)|C|$. They are disjoint as soon as there is a client and $\delta>0$. In both cases $i=j$ is allowed.
--
--   **Formalization Note** The input is the integer list $[n,m]$ and the real list of the $mn$ distances, row-major in $(c,i)$; nonnegativity of $\Delta$ is a hypothesis of Theorem 39.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 39, p.47 (completeness and soundness cases)

import Mathlib
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-!
# Gap (balanced) 2-median instances (Theorem 39)

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Theorem 39, p.47: facilities `F = {f_1, …, f_n}`, clients `C = {c_1, …, c_m}` and a
distance function `∆ : C × F → ℝ≥0`; completeness: an equipartition `C = C_1 ∪̇ C_2` with
`(∑_{c∈C_1} ∆(c, f_i)) + (∑_{c∈C_2} ∆(c, f_j)) = |C|`; soundness: for every `i, j`,
`∑_{c∈C} min{∆(c, f_i), ∆(c, f_j)} ≥ (1 + δ) · |C|`.

This module bundles `encodeMedian`, `MedianYes` and `MedianNo`.

**Formalization Note.** Clients are `Fin m`, facilities `Fin n`, and `∆ c i` is `∆(c, f_i)`; no
metric axioms (nonnegativity is a hypothesis of the theorem). `i = j` is allowed, as printed. The
input is the integer list `[n, m]` and the real list of the `m · n` distances, row-major in
`(c, i)` (the distances are real data: one unit per read). -/

/-- The input `([n, m], distances…)` of a 2-median instance. -/
def encodeMedian {n m : ℕ} (Δ : Fin m → Fin n → ℝ) : List ℤ × List ℝ :=
  ([(n : ℤ), (m : ℤ)], (List.finRange m).flatMap fun c => (List.finRange n).map fun i => Δ c i)

/-- Completeness case: a balanced 2-median solution of cost exactly `|C|`. -/
def MedianYes {n m : ℕ} (Δ : Fin m → Fin n → ℝ) : Prop :=
  ∃ i j : Fin n, ∃ C₁ : Finset (Fin m), C₁.card = C₁ᶜ.card ∧
    (∑ c ∈ C₁, Δ c i) + (∑ c ∈ C₁ᶜ, Δ c j) = m

/-- Soundness case: every pair of facilities has 2-median cost at least `(1 + δ) · |C|`. -/
def MedianNo {n m : ℕ} (δ : ℝ) (Δ : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, (1 + δ) * m ≤ ∑ c, min (Δ c i) (Δ c j)

end MinSumFPT.Supplement


