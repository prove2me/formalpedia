-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_Core
-- name    : OptimalTraceDistance_Estimation_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:32:57.967982+00:00
-- url     : https://prove2.me/theorems/f88ce88f-6f46-42d7-9ed6-61cf961d99c6
-- title:
--   Matrices, physical two-state measurements and Born laws
-- statement:
--   States are positive semidefinite complex matrices of trace one, reusing the published density predicate. Write $S_+=(\rho+\sigma)/2$, $S_-=(\rho-\sigma)/2$, and $d_{\rm tr}(\rho,\sigma)=\|\rho-\sigma\|_1/2$. Orthogonal projectors satisfy $Q^*=Q^2=Q$, and compression is $X\mapsto QXQ$ without renormalization.
--
--   The operator norm is induced by the Euclidean norm; trace norm and Schatten norms reuse published definitions. Tensor products are indexed by functions on finite coordinate sets. Weighted inner products and observable variances are finite matrix traces. A two-state experiment is a normalized positive countably additive operator measure with real outputs on $\rho^{\otimes N}\otimes\sigma^{\otimes N}$. Its Born law uses that actual input, whose density legality is a structural tensor identity. No accuracy property is included. Matrices carry their Borel sigma algebra.
--
--   Tensor products are aliases of the published finite tensor-family definition, with identical coordinate products.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), §§1, 2.1, 4.1, 5, pp.3,6,13,21.

import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
import Definitions.Def_WHMultiplicativity_schattenNorm
import Definitions.Def_OptimalSpectrum_Entangled_kronFamily

open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace OptimalTraceDistance.Estimation

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
instance matrixMeasurable (d : ℕ) : MeasurableSpace (Mat d) := borel _
instance matrixBorel (d : ℕ) : BorelSpace (Mat d) := ⟨rfl⟩

abbrev Register (d n : ℕ) := Fin n → Fin d
abbrev Op (d n : ℕ) := Matrix (Register d n) (Register d n) ℂ
abbrev Density {d : ℕ} (A : Mat d) := QAlgorithms.IsDensityMatrix A

def tr {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ := A.trace.re
def opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
def lePSD {d : ℕ} (A B : Mat d) : Prop := (B - A).PosSemidef
def projector {d : ℕ} (Q : Mat d) : Prop := Q.IsHermitian ∧ Q * Q = Q
def compress {d : ℕ} (Q X : Mat d) : Mat d := Q * X * Q
def plus {d : ℕ} (ρ σ : Mat d) : Mat d := (2 : ℂ)⁻¹ • (ρ + σ)
def minus {d : ℕ} (ρ σ : Mat d) : Mat d := (2 : ℂ)⁻¹ • (ρ - σ)
def distance {d : ℕ} (ρ σ : Mat d) : ℝ := QAlgorithms.traceNorm (ρ - σ) / 2
def absMat {d : ℕ} (A : Mat d) : Mat d := cfc Real.sqrt (Aᴴ * A)
def sqrtMat {d : ℕ} (A : Mat d) : Mat d := cfc Real.sqrt A
def logMat {d : ℕ} (A : Mat d) : Mat d := cfc Real.log A

abbrev tensor {ι : Type*} [Fintype ι] (r : ℕ) (A : Fin r → Matrix ι ι ℂ) :
    Matrix (Fin r → ι) (Fin r → ι) ℂ := OptimalSpectrum.Entangled.kronFamily A
def powerState {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (r : ℕ) :
    Matrix (Fin r → ι) (Fin r → ι) ℂ := tensor r (fun _ => A)
def hermPart {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (A + Aᴴ)
def weightedInner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Matrix ι ι ℂ) (r : ℕ) (A B : Matrix (Fin r → ι) (Fin r → ι) ℂ) : ℂ :=
  (powerState τ r * Aᴴ * B).trace
def weightedNormSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Matrix ι ι ℂ) (r : ℕ) (A : Matrix (Fin r → ι) (Fin r → ι) ℂ) : ℝ :=
  (weightedInner τ r A A).re
def variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Matrix ι ι ℂ) (r : ℕ) (G : Matrix (Fin r → ι) (Fin r → ι) ℂ) : ℝ :=
  tr (powerState τ r * G ^ 2) - tr (powerState τ r * G) ^ 2

def rate (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ)^2 / (ε^2 * (Real.log d)^2 * max 1 (ε^2 * (Real.log d)^2))

/-- Source pp.3–4, §5 p.21: the physical input register contains N copies of each state. -/
def jointInput {d : ℕ} (N : ℕ) (ρ σ : Mat d) :=
  Matrix.kronecker (QAlgorithms.piKron N ρ) (QAlgorithms.piKron N σ)

/-- This is only tensor-density legality, not an estimator accuracy certificate. -/
theorem jointInput_density {d : ℕ} (N : ℕ) (ρ σ : Mat d)
    (hρ : Density ρ) (hσ : Density σ) : QAlgorithms.IsDensityMatrix (jointInput N ρ σ) := by
  refine ⟨(QAlgorithms.Tomography.tensorDensity ρ hρ N).1.kronecker
    (QAlgorithms.Tomography.tensorDensity σ hσ N).1, ?_⟩
  simp [jointInput, Matrix.trace_kronecker,
    (QAlgorithms.Tomography.tensorDensity ρ hρ N).2,
    (QAlgorithms.Tomography.tensorDensity σ hσ N).2]

abbrev TwoStateMeasurement (d N : ℕ) :=
  QAlgorithms.Measurements.OperatorPOVM (Register d N × Register d N) ℝ

def outcomeLaw {d N : ℕ} (M : TwoStateMeasurement d N) (ρ σ : Mat d)
    (hρ : Density ρ) (hσ : Density σ) : MeasureTheory.Measure ℝ :=
  QAlgorithms.Measurements.bornLaw M (jointInput N ρ σ) (jointInput_density N ρ σ hρ hσ)

end OptimalTraceDistance.Estimation


