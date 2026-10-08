-- Prove2me | Definitions.Def_MatrixTail_Azuma_Model
-- name    : MatrixTail_Azuma_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:20.37537+00:00
-- url     : https://prove2.me/theorems/96a62a15-e76f-402d-aad9-787d6f1beab6
-- title:
--   §2 — complex Hermitian matrices, λmax, spectral norm, matrix exp/log, trace exponential, entrywise expectation, Rademacher variables
-- statement:
--   This file fixes the objects of Tropp's *User-Friendly Tail Bounds for Sums of Random Matrices* used by the matrix Azuma inequality.
--
--   A **matrix** is a $d\times d$ array of complex numbers, and a **self-adjoint** (s.a.) matrix is a Hermitian one. For such a matrix $A$:
--
--   1. $\lambda_{\max}(A)$ is its algebraically largest eigenvalue, defined as the supremum of its real spectrum;
--   2. $\|A\|$ is the **spectral norm**, the operator norm of $A$ acting on $\mathbb C^d$ with the Euclidean norm;
--   3. $e^{A}$ and $\log A$ are defined spectrally: if $A = Q\Lambda Q^*$ then $f(A) = Q f(\Lambda) Q^*$ with $f=\exp$ or $f=\log$ (display (2.1)); the logarithm is used on positive-definite matrices, where it inverts the exponential (display (2.7));
--   4. $\operatorname{tr} e^{A}$ is the **trace exponential**, a real number.
--
--   A **random matrix** is a measurable map $X:\Omega\to\mathbb C^{d\times d}$ (the space of matrices carries its Borel σ-algebra). Its **expectation** is taken entrywise,
--   $$
--   (\mathbb E X)_{ij} = \int_\Omega X(\omega)_{ij}\, d\mathbb P(\omega),
--   $$
--   and a random matrix is called **integrable** when all of its entries are integrable. A real random variable $\xi$ is **Rademacher** if it is measurable and $\mathbb P\{\xi = 1\} = \mathbb P\{\xi=-1\} = 1/2$.
--
--   These are the objects in which the matrix Laplace transform method, the Golden–Thompson inequality, the symmetrization lemma and the matrix Azuma inequality are stated.
--
--   **Formalization Note** The exponential and logarithm are Mathlib's continuous functional calculus `cfc` applied to `Real.exp` and `Real.log`. The trace exponential is the real part of the trace of the matrix exponential. At $d=0$ the spectrum is empty and $\lambda_{\max}$ takes the value $0$, so every statement involving $\lambda_{\max}$ assumes $d\ge 1$. The Rademacher law is the published definition `HighDimStat.UniformLaws.IsRademacherVariable`, wrapped together with measurability. The semidefinite order $A\preceq B$ is Mathlib's `A ≤ B` under `MatrixOrder`, i.e. $B-A$ positive semidefinite.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, pp. 4, 7–9, footnote 1, §§2.1–2.5, (2.1), (2.7)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_IsRademacherVariable

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- The Borel (product) σ-algebra on `d × d` complex matrices, so that a random matrix is a measurable map
`Ω → Matrix (Fin d) (Fin d) ℂ` and `IndepFun` applies to random matrices.
(Tropp, arXiv:1004.4389v7, §2.2, p. 7: random matrices.) -/
noncomputable instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℂ) := by
  unfold Matrix; infer_instance

/-- `λmax(A)`, the algebraically largest eigenvalue of a self-adjoint matrix (Tropp, arXiv:1004.4389v7,
§2.1, p. 7): the supremum of its real spectrum. For a Hermitian matrix with `d ≥ 1` this is its largest
eigenvalue. Formalization Note: at `d = 0` the spectrum is empty and the value is `sSup ∅ = 0`; every
statement using `lambdaMax` assumes `[NeZero d]`. -/
noncomputable def lambdaMax {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := sSup (spectrum ℝ A)

/-- `‖A‖`, the spectral norm: the operator norm of `A` acting on `ℂ^d` with the ℓ₂ norm
(Tropp, arXiv:1004.4389v7, §2.1, p. 7). -/
noncomputable def specNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

/-- `e^A`, by the spectral definition (2.1) with `f = exp` (Tropp, arXiv:1004.4389v7, §2.4, p. 8).
Formalization Note: Mathlib's continuous functional calculus `cfc`, which on a Hermitian matrix is the
eigen-decomposition formula (2.1). -/
noncomputable def mexp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := cfc Real.exp A

/-- `log A` on the positive-definite cone, by (2.1) with `f = log`; the inverse of `mexp` there
(Tropp, arXiv:1004.4389v7, §2.5, (2.7), p. 8). -/
noncomputable def mlog {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := cfc Real.log A

/-- The trace exponential `tr e^A` (Tropp, arXiv:1004.4389v7, §2.4, p. 8), real for Hermitian `A`. -/
noncomputable def trExp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (mexp A)).re

/-- `E X`, the entrywise expectation of a random matrix (Tropp, arXiv:1004.4389v7, §2.2, p. 7). -/
noncomputable def mean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂P

/-- Every entry of the random matrix `X` is integrable: the §2.2 regularity (Tropp, arXiv:1004.4389v7,
p. 7) made explicit. -/
def MatIntegrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i j, Integrable (fun ω => X ω i j) P

/-- `ξ` is a Rademacher random variable, "uniformly distributed on {±1}" (Tropp, arXiv:1004.4389v7,
footnote 1, p. 4): measurable, with the law of the published
`HighDimStat.UniformLaws.IsRademacherVariable` (P{ξ = 1} = P{ξ = −1} = 1/2). -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → ℝ) : Prop :=
  Measurable ξ ∧ HighDimStat.UniformLaws.IsRademacherVariable ξ P

end MatrixTail.Azuma


