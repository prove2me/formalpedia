-- Prove2me | Definitions.Def_MatrixTail_Gaussian_Model
-- name    : MatrixTail_Gaussian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:12.700898+00:00
-- url     : https://prove2.me/theorems/a5f5de80-d468-4b11-b7dd-c49d14ad0298
-- title:
--   §2 — spectral norm of square and rectangular complex matrices; Rademacher and standard normal variables
-- statement:
--   This file adds, on top of the shared conventions `MatrixTail.Master.Model` (complex Hermitian matrices, $\lambda_{\max}$, the matrix exponential and logarithm, the trace exponential, entrywise expectation and integrability of random matrices), the norms and scalar laws used by the Gaussian-series and Bernstein results of Tropp's *User-Friendly Tail Bounds for Sums of Random Matrices*.
--
--   1. **Spectral norm.** For a $d\times d$ complex matrix $A$, $\|A\|$ is the operator norm of $A$ acting on $\mathbb C^d$ with the Euclidean ($\ell_2$) norm; it equals the largest singular value of $A$ (§2.1).
--   2. **Rectangular spectral norm.** For a rectangular $d_1\times d_2$ complex matrix $B$, $\|B\|$ is its operator norm from $(\mathbb C^{d_2},\ell_2)$ to $(\mathbb C^{d_1},\ell_2)$, i.e. its largest singular value (§2.1; used in Corollary 4.2).
--   3. **Rademacher variable.** A real random variable $\varepsilon$ is Rademacher when it is measurable and uniformly distributed on $\{\pm1\}$ (footnote 1, p. 4):
--   $$\mathbb P\{\varepsilon = 1\} = \mathbb P\{\varepsilon = -1\} = \tfrac12 .$$
--   4. **Standard normal variable.** A real random variable $\gamma$ is standard normal when it is measurable and its law is $N(0,1)$.
--
--   These objects state the Gaussian and Rademacher series bounds (§4) and the variance parameter $\sigma^2 = \|\sum_k A_k^2\|$ used throughout §§4–7.
--
--   **Formalization Note** The spectral norm is Mathlib's operator norm of `Matrix.toEuclideanCLM A`; the rectangular one is Mathlib's scoped $\ell_2$-operator norm on `Matrix m n ℂ`, and the two agree on square matrices. The Rademacher law reuses the published definition `HighDimStat.UniformLaws.IsRademacherVariable` ($P\{\varepsilon=1\} = P\{\varepsilon=-1\} = 1/2$), to which measurability is added; every theorem using these laws assumes a probability measure.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 4 (footnote 1), p. 7 (§2.1), p. 14 (§4.1), p. 15 (Corollary 4.2)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_IsRademacherVariable
import Definitions.Def_MatrixTail_Master_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- `‖A‖`, the spectral norm: the operator norm of `A` acting on `ℂ^d` with the ℓ₂ norm
(Tropp, arXiv:1004.4389v7, §2.1, p. 7). -/
noncomputable def specNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

/-- `ξ` is a Rademacher random variable, "uniformly distributed on {±1}" (Tropp, arXiv:1004.4389v7,
footnote 1, p. 4): measurable, with the law of the published
`HighDimStat.UniformLaws.IsRademacherVariable` (P{ξ = 1} = P{ξ = −1} = 1/2). -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → ℝ) : Prop :=
  Measurable ξ ∧ HighDimStat.UniformLaws.IsRademacherVariable ξ P

/-- `γ` is a standard normal random variable (Tropp, arXiv:1004.4389v7, §4.1, p. 14): measurable, with law
`N(0, 1)`. -/
def IsStdGaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : Ω → ℝ) : Prop :=
  Measurable γ ∧ P.map γ = gaussianReal 0 1

open scoped Matrix.Norms.L2Operator in
/-- `‖B‖`, the spectral norm (largest singular value) of a rectangular `d₁ × d₂` complex matrix: its operator
norm from `ℂ^{d₂}` to `ℂ^{d₁}` with the ℓ₂ norms (Tropp, arXiv:1004.4389v7, §2.1, p. 7; used in
Corollary 4.2, p. 15). Formalization Note: Mathlib's scoped ℓ₂-operator norm on `Matrix m n ℂ`; on square
matrices it agrees with `specNorm` (`Matrix.cstar_norm_def`). -/
noncomputable def rectSpecNorm {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℂ) : ℝ := ‖B‖

end MatrixTail.Gaussian


