-- Prove2me | Definitions.Def_UnderstandingML_DimReduction
-- name    : UnderstandingML_DimReduction
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:18:49.975429+00:00
-- url     : https://prove2.me/theorems/f60a4c62-712e-4efd-9f95-e6b2e9320233
-- title:
--   Chapter 23: the PCA objective (23.1) and scatter matrix, Gaussian random matrices, sparsity ‖·‖₀, restriction v_I, and the restricted isometry property (Definition 23.5)
-- statement:
--   Chapter 23 of Shalev-Shwartz and Ben-David. Vectors are functions $\mathbb{R}^d$ with `sqNorm v` $= \|v\|_2^2 = \sum_i v_i^2$, `l1Norm v` $= \|v\|_1$, `l0Norm v` $= \|v\|_0 = |\{i : v_i \ne 0\}|$ and `restrictTo I v` $= v_I$ ($v$ on $I$, $0$ elsewhere). **PCA (§23.1):** `pcaObjective x U W` $= \sum_{i=1}^m \|x_i - UWx_i\|_2^2$ for a recovery matrix $U \in \mathbb{R}^{d \times n}$ and a compression matrix $W \in \mathbb{R}^{n \times d}$ (23.1); `scatterMatrix x` $= A = \sum_i x_i x_i^\top$. **Random projections (§23.2):** `gaussianMatrixLaw n d v` is the law of an $n \times d$ matrix with independent $N(0, v)$ entries (a measure on `Fin n → Fin d → ℝ`, applied through `Matrix.of`). **Compressed sensing (§23.3):** `IsRIP ε s W` is Definition 23.5, $W$ is $(\epsilon, s)$-RIP if $\big|\|Wx\|_2^2/\|x\|_2^2 - 1\big| \le \epsilon$ for all $x \ne 0$ with $\|x\|_0 \le s$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.1 pp. 324-325 (Equation (23.1), A = ∑ xᵢxᵢᵀ), §23.2 p. 329 (random matrices), §23.3 pp. 330-333 (‖x‖₀, Definition 23.5, v_I)

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 23: dimensionality
# reduction

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.1–§23.3.

**PCA (§23.1, p. 324).** For `x₁, …, x_m ∈ ℝ^d`, a compression matrix `W ∈ ℝ^{n×d}` and a
recovery matrix `U ∈ ℝ^{d×n}`, PCA solves `argmin_{W, U} ∑ᵢ ‖xᵢ − UWxᵢ‖²` (23.1). With
`A = ∑ᵢ xᵢxᵢᵀ`, the solution is `U` whose columns are `n` eigenvectors of `A` for its `n`
largest eigenvalues, and `W = Uᵀ` (Theorem 23.2).

**Random projections (§23.2, p. 329).** `W ∈ ℝ^{n×d}` with independent normal entries; the
distortion of `x` is `|‖Wx‖²/‖x‖² − 1|`. Entries are `N(0, 1)` in Lemma 23.3 and `N(0, 1/n)`
in Lemma 23.4 and §23.3.

**Compressed sensing (§23.3, p. 331).** `‖x‖₀ = |{i : xᵢ ≠ 0}|`; `W` is `(ε, s)`-RIP if
`|‖Wx‖²/‖x‖² − 1| ≤ ε` for all `x ≠ 0` with `‖x‖₀ ≤ s` (Definition 23.5). For a vector `v` and
an index set `I`, `v_I` is `v` on `I` and `0` elsewhere (p. 333).

**Conventions.** Vectors are plain functions `Fin d → ℝ`, with `‖v‖² = ∑ vᵢ²` (`sqNorm`),
`‖v‖₁ = ∑ |vᵢ|` and `‖v‖₀`; matrices are Mathlib matrices. A random matrix is a function
`Fin n → Fin d → ℝ` with the product of Gaussian laws on its entries, applied through
`Matrix.of`. "Eigenvectors for the `n` largest eigenvalues" are the first `n` columns of a
spectral decomposition `A = V diag(D) Vᵀ` with `D` nonincreasing.
-/

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

section Vectors

variable {d : ℕ}

/-- The squared Euclidean norm `‖v‖₂² = ∑ᵢ vᵢ²`. -/
def sqNorm (v : Fin d → ℝ) : ℝ := ∑ i, v i ^ 2

/-- The `ℓ₁` norm `‖v‖₁ = ∑ᵢ |vᵢ|`. -/
def l1Norm (v : Fin d → ℝ) : ℝ := ∑ i, |v i|

/-- The sparsity `‖v‖₀ = |{i : vᵢ ≠ 0}|` (p. 330). -/
noncomputable def l0Norm (v : Fin d → ℝ) : ℕ := by
  classical exact (Finset.univ.filter (fun i ↦ v i ≠ 0)).card

/-- `v_I`: the vector equal to `v` on the index set `I` and `0` elsewhere (p. 333). -/
def restrictTo (I : Finset (Fin d)) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ if i ∈ I then v i else 0

end Vectors

section PCA

variable {m d n : ℕ}

/-- The PCA objective `∑ᵢ ‖xᵢ − UWxᵢ‖²` of a compression matrix `W ∈ ℝ^{n×d}` and a recovery
matrix `U ∈ ℝ^{d×n}` (23.1). -/
noncomputable def pcaObjective (x : Fin m → Fin d → ℝ) (U : Matrix (Fin d) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  ∑ i, sqNorm (x i - U.mulVec (W.mulVec (x i)))

/-- The scatter matrix `A = ∑ᵢ xᵢxᵢᵀ` (p. 325). -/
noncomputable def scatterMatrix (x : Fin m → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, Matrix.vecMulVec (x i) (x i)

end PCA

section Random

/-- The law of a random `n × d` matrix whose entries are independent `N(0, v)` variables
(§23.2), as a measure on `Fin n → Fin d → ℝ`. -/
noncomputable def gaussianMatrixLaw (n d : ℕ) (v : NNReal) : Measure (Fin n → Fin d → ℝ) :=
  Measure.pi (fun _ ↦ Measure.pi (fun _ ↦ gaussianReal 0 v))

end Random

section RIP

variable {n d : ℕ}

/-- **Definition 23.5 (RIP).** `W ∈ ℝ^{n×d}` is `(ε, s)`-RIP if for all `x ≠ 0` with `‖x‖₀ ≤ s`,
`|‖Wx‖₂²/‖x‖₂² − 1| ≤ ε`. -/
def IsRIP (ε : ℝ) (s : ℕ) (W : Matrix (Fin n) (Fin d) ℝ) : Prop :=
  ∀ x : Fin d → ℝ, x ≠ 0 → l0Norm x ≤ s → |sqNorm (W.mulVec x) / sqNorm x - 1| ≤ ε

end RIP

end UnderstandingML


