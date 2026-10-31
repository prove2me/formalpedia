-- Prove2me | Definitions.Def_QiFixedDesign_Concentration_Design
-- name    : QiFixedDesign_Concentration_Design
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:04.823732+00:00
-- url     : https://prove2.me/theorems/692068ba-a8ce-44a8-8710-5be6dfcf47b1
-- title:
--   Fixed design prefixes, admissible sample sizes and Gram limit
-- statement:
--   Fix a finite number $p$ of covariates and one deterministic sequence $x_i\in\mathbb R^p$. The design matrix $X_N$ consists of its first $N$ rows and $G_N=X_N^T X_N$. A sample size is admissible when $N>0$ and $\det G_N\ne0$. Assumption 2 is the existence of a real matrix $M$ with $\det M\ne0$ such that $G_N/N\to M$.
--
--   Rows and coordinates use zero-based finite indices. No random-design, bounded-feature or concentration hypothesis is included. Nonadmissible prefixes are never used in a finite-sample assertion; values of inverse or division formulas at such prefixes are only total-function extensions. No separate intercept is appended. Unlike the source model, the definition also permits supplied constant feature columns; the downstream theorem metadata declares this generalization.
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, §3, Assumptions 1–2 and (17), PDF/printed pp. 8, 12

import Mathlib

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

def designMatrix {p : ℕ} (x : ℕ → Fin p → ℝ) (N : ℕ) : Matrix (Fin N) (Fin p) ℝ :=
  fun i j => x i.val j

noncomputable def gram {p : ℕ} (x : ℕ → Fin p → ℝ) (N : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  (designMatrix x N).transpose * designMatrix x N

def admissible {p : ℕ} (x : ℕ → Fin p → ℝ) (N : ℕ) : Prop :=
  0 < N ∧ (gram x N).det ≠ 0

def GramLimit {p : ℕ} (x : ℕ → Fin p → ℝ) : Prop :=
  ∃ M : Matrix (Fin p) (Fin p) ℝ, M.det ≠ 0 ∧
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • gram x N) atTop (𝓝 M)

end QiFixedDesign.Concentration


