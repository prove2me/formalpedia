-- Prove2me | Definitions.Def_SchattenSketch_Main_Testing
-- name    : SchattenSketch_Main_Testing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:37.594074+00:00
-- url     : https://prove2.me/theorems/78c5497e-796a-47e6-b227-7b221a08009f
-- title:
--   Total variation distance, row coisometries and the multiplicative enlargement $(1\pm\varepsilon)I$
-- statement:
--   For two finite measures $\mu,\nu$ on a measurable space, the **total variation distance** is
--   $$d_{TV}(\mu,\nu)=\sup_{E}\,|\mu(E)-\nu(E)|,$$
--   the supremum over measurable sets $E$ (3.4).
--
--   Identify $\mathbb R^{n\times n}$ with $\mathbb R^{n^2}$ through the Frobenius inner product. A **row coisometry** of rank $r$ is a matrix $L\in\mathbb R^{r\times n^2}$ with orthonormal rows, $LL^\top=I_r$; it acts on matrices by $(LA)_q=\sum_{i,j}L_{q,(i,j)}A_{ij}$. For an input law $\Pi$ the pushforward $L_\#\Pi$ is the law of $LA$ with $A\sim\Pi$ (4.0).
--
--   For $\varepsilon\in\mathbb R$ and $I\subseteq[0,\infty)$ the **multiplicative enlargement** is
--   $$(1\pm\varepsilon)I=\{y\ge 0:\ (1-\varepsilon)x\le y\le(1+\varepsilon)x\ \text{for some }x\in I\}.$$
--
--   **Formalization Note.** `tvDist μ ν` is the real supremum of $|\mu(E)-\nu(E)|$ over the subtype of measurable sets: it is nonempty ($E=\varnothing$) and bounded for finite measures. `IsRowCoisometry L` is `Matrix.of L * (Matrix.of L)ᵀ = 1` for `L : Fin r → Fin n × Fin n → ℝ`; the pushforward is `Measure.map (fun A => sketchApply L (Matrix.of A))`.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 12, (3.4); p. 13, §4.1 and (4.0); p. 14, Lemma 4.1

import Mathlib

open MeasureTheory

namespace SchattenSketch.Main

/-- Total variation distance `d_TV(μ, ν) = sup_E |μ(E) - ν(E)|` over measurable sets `E` (Yang,
p. 12, (3.4)). For finite measures the set of values is nonempty (`E = ∅`) and bounded. -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ E : {E : Set α // MeasurableSet E}, |(μ E.1).toReal - (ν E.1).toReal|

/-- A row coisometry `L ∈ ℝ^{r × n²}` (Yang, p. 13): its rows are orthonormal in the Frobenius
inner product, `L Lᵀ = I_r`. It is a linear map `ℝ^{n×n} → ℝ^r` of rank `r`. -/
def IsRowCoisometry {n r : ℕ} (L : Fin r → Fin n × Fin n → ℝ) : Prop :=
  Matrix.of L * (Matrix.of L).transpose = 1

/-- The multiplicative enlargement `(1 ± ε) I = {y ≥ 0 : (1 - ε)x ≤ y ≤ (1 + ε)x for some x ∈ I}`
of a set `I ⊆ [0, ∞)` (Yang, p. 14, Lemma 4.1). -/
def enlarge (ε : ℝ) (I : Set ℝ) : Set ℝ :=
  {y | 0 ≤ y ∧ ∃ x ∈ I, (1 - ε) * x ≤ y ∧ y ≤ (1 + ε) * x}

end SchattenSketch.Main


