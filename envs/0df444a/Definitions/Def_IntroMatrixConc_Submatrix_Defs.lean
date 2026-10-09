-- Prove2me | Definitions.Def_IntroMatrixConc_Submatrix_Defs
-- name    : IntroMatrixConc_Submatrix_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:17.85883+00:00
-- url     : https://prove2.me/theorems/dca58854-d80a-462f-bf19-ef8e73f3e462
-- title:
--   §§2.2.2, 5.2, 7.2.2 — Bernoulli selection, row and column submatrices, stable rank
-- statement:
--   Let $B\in\mathbb C^{d\times n}$ be fixed. A Bernoulli variable with parameter $q$ takes the values zero and one and has probability $q$ of being one. For row indicators $\delta_j$ and column indicators $\xi_k$, define the sampled matrices
--
--   $$
--   P=\operatorname{diag}(\delta_1,\ldots,\delta_d),\qquad R=\operatorname{diag}(\xi_1,\ldots,\xi_n),\qquad PB,\quad BR,\quad Z=PBR.
--   $$
--
--   The definitions also provide the maximum squared column norm, row norm, and entry magnitude of $B$, together with the maximum sampled column norm of $PB$. Stable rank is
--
--   $$
--   \operatorname{srank}(B)=\frac{\sum_{j,k}|b_{jk}|^2}{\|B\|^2}.
--   $$
--
--   This shared vocabulary makes the four displays leading to (5.2.2) refer to exactly the same random submatrix and the same deterministic maxima.
--
--   **Formalization Note** Bernoulli measurability, independence, and parameter ranges are hypotheses of the theorems using these definitions. The stable rank of the zero matrix has Lean's total-division value zero; the identity involving it excludes the zero matrix.
-- source:
--   Tropp, arXiv:1501.01571v1, (2.1.25), p. 24; §2.2.2, p. 26; §§5.2.1–5.2.2, pp. 64–66; §7.2.2, pp. 107–108

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.Submatrix

/-- A Bernoulli random variable with success probability `q`, as in §2.2.2. -/
def IsBernoulli {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (δ : Ω → ℝ) (q : ℝ) : Prop :=
  (∀ᵐ ω ∂μ, δ ω = 0 ∨ δ ω = 1) ∧ (μ {ω | δ ω = 1}).toReal = q

/-- The row projector `P = diag(δ₁,…,δ_d)` applied to `B`. -/
def selectedRows {Ω : Type*} {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ)
    (δ : Fin d → Ω → ℝ) (ω : Ω) : Matrix (Fin d) (Fin n) ℂ :=
  Matrix.diagonal (fun j => (δ j ω : ℂ)) * B

/-- The column projector applied to `B`, as in §5.2.1. -/
def selectedColumns {Ω : Type*} {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ)
    (ξ : Fin n → Ω → ℝ) (ω : Ω) : Matrix (Fin d) (Fin n) ℂ :=
  B * Matrix.diagonal (fun k => (ξ k ω : ℂ))

/-- The random row-and-column submatrix `Z = PBR` of §5.2.2. -/
def selectedSubmatrix {Ω : Type*} {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ)
    (δ : Fin d → Ω → ℝ) (ξ : Fin n → Ω → ℝ) (ω : Ω) :
    Matrix (Fin d) (Fin n) ℂ :=
  selectedRows B δ ω * Matrix.diagonal (fun k => (ξ k ω : ℂ))

/-- The largest squared Euclidean norm of a column of `B`. -/
def maxColumnSq {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) : ℝ :=
  ⨆ k : Fin n, ∑ j : Fin d, ‖B j k‖ ^ 2

/-- The largest squared Euclidean norm of a row of `B`. -/
def maxRowSq {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) : ℝ :=
  ⨆ j : Fin d, ∑ k : Fin n, ‖B j k‖ ^ 2

/-- The squared modulus of the largest entry of `B`. -/
def maxEntrySq {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) : ℝ :=
  ⨆ j : Fin d, ⨆ k : Fin n, ‖B j k‖ ^ 2

/-- The maximum squared column norm after row selection. -/
def maxSelectedColumnSq {Ω : Type*} {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ)
    (δ : Fin d → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ k : Fin n, ∑ j : Fin d, ‖selectedRows B δ ω j k‖ ^ 2

/-- Stable rank, equation (2.1.25). -/
def srank {d n : ℕ} (B : Matrix (Fin d) (Fin n) ℂ) : ℝ :=
  (∑ j : Fin d, ∑ k : Fin n, ‖B j k‖ ^ 2) /
    TroppMatrixConcentration.spectralNorm B ^ 2

end IntroMatrixConc.Submatrix


