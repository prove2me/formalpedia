-- Prove2me | Definitions.Def_OAIQWFE002
-- name    : OAIQWFE002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:09:01.355995+00:00
-- url     : https://prove2.me/theorems/5fe3912b-f45a-472e-9daf-7b48a56944b7
-- title:
--   OpenAI finite-entropy separation split: definitions bundle 3 (matrix heat laws and normalized matrix entropy and Fisher information)
-- statement:
--   The third definitions bundle of the split of OpenAI's proof of `OAI.FiniteEntropySeparation.main`. It holds OpenAI's remaining definitions from `lean/OAI/Analysis/FreeEntropy` (OpenAI, *A finite-entropy separation of microstates and nonmicrostates free entropy*, OpenAI Math Release, September 25, 2026, result family 298, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a: among them the matrix heat law `matrixHeatLaw` (the law of a matrix microstate after Gaussian smoothing), the normalized matrix entropy and Fisher information `normalizedMatrixEntropy` and `normalizedMatrixFisher`, time derivatives of the smoothed densities, the projected conjugate variables `projectedConjugate`, and the spectral parameters `spectralBasis` (Lagrange basis polynomials at the atoms `equidiscreteAtom`) and `spectralGood`, with the lemmas they use. It imports the published bundle `Def_FiniteEntropySeparation` and the definitions bundles `OAIQWFE000` and `OAIQWFE001`.
--
--   Modules: `Basic`, `TensorHermite`, `GaussianDifferential`, `GaussianConvolution`, `NormalLaw`, `MatrixWordDerivative`, `MatrixScoreWords`, `MatrixPolynomialNorm`, `MatrixHilbertSchmidt`, `GUEDerivative`, `GUEBounds`, `MatrixReparam`, `MatrixHeatLaw`, `SpectralParameters`, `WickTensor`, `MatrixFisherTest`, `MatrixFisherLiminf`, `MatrixFlow`, `TensorMatrices`.
--
--   The theorems that the definitions do not need are proved in the fourteen solutions of this split: three named results published as standalone statements (Hermite orthogonality, the Gaussian Poincaré inequality for polynomials, and the lower semicontinuity of free Fisher information), ten intermediate statements of OpenAI's argument, and the external goal `OAI.FiniteEntropySeparation.main`. Gaussian integration by parts is not re-proved: it is the published statement `HighDimProb.RandomProcesses.gaussian_integration_by_parts`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); definitions carved from lean/OAI/Analysis/FreeEntropy at commit adc7f12

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE000
import Definitions.Def_OAIQWFE001

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance polynomialL2_complete {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) : CompleteSpace (polynomialL2 τ X) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def projectedConjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H) (i : Fin n) : H :=
  (polynomialL2 τ X).starProjection (η i)

def vacuumRankOne {M : VonNeumannAlgebra H} (τ : TracialVector M) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ τ.vacuum τ.vacuum

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
instance instIsProbabilityMeasureForallRealProductGaussian : IsProbabilityMeasure (productGaussian ι) := by unfold productGaussian; infer_instance

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
def normalTimeDerivative (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  (-(Fintype.card ι:ℝ)/(2*s)+‖x‖^2/(2*s^2))*normalKernel s x
def normalSecond (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ := ((x i)^2/s^2-1/s)*normalKernel s x
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def smoothedTimeDerivative (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫a,normalTimeDerivative s (x-a) ∂μ
def smoothedSecond (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ :=
  ∫a,normalSecond s (x-a) i ∂μ
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NormalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 def normalLaw (s : ℝ) : Measure (EuclideanSpace ℝ ι) :=
    volume.withDensity (fun x => ENNReal.ofReal (normalKernel s x))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixWordDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {d : ℕ}
 def matrixWordVariation (A D : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) : Matrix (Fin d) (Fin d) ℂ :=
   ∑ r : Fin w.length, matrixWord A (w.take r.val) * D w[r.val] * matrixWord A (w.drop (r.val+1))
 @[simp] theorem matrixWordVariation_nil (A D : α → Matrix (Fin d) (Fin d) ℂ) : matrixWordVariation A D [] = 0 := by simp [matrixWordVariation]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixScoreWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixScoreWord (w : List (Fin n)) (j k : Fin d) (x : MatrixIndex n d → ℝ) : ℂ :=
    Matrix.trace (hermitianBasis j k*matrixWord (coordinateMatrix x) w)
 def matrixPolynomial (p : WordPolynomial n) (A : Fin n → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
    p.sum (fun w c => c • matrixWord A w)
 def matrixScorePolynomial (p : WordPolynomial n) (j k : Fin d) (x : MatrixIndex n d → ℝ) : ℂ :=
    Matrix.trace (hermitianBasis j k*matrixPolynomial p (coordinateMatrix x))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixPolynomialNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixPolynomialNorm (p : WordPolynomial n) (a : MatrixCoordinates n d) : ℝ :=
    (∑u∈p.support,∑v∈p.support,star (p u)*p v*matrixMoment a (u.reverse++v)).re
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def hsNorm (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := ‖hsVector A‖
 theorem hsNorm_sq (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm A^2=∑j,∑k,Complex.normSq (A j k) := by
  rw [hsNorm,EuclideanSpace.norm_sq_eq]
  simp [hsVector,Fintype.sum_prod_type,Complex.normSq_eq_norm_sq]
 theorem hsNorm_nonneg (A : Matrix (Fin d) (Fin d) ℂ) : 0≤hsNorm A := norm_nonneg _
 theorem hsNorm_unitary_conjugate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ))=hsNorm A := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  rw [hsNorm_sq,hsNorm_sq,← trace_conjTranspose_mul_re,← trace_conjTranspose_mul_re]
  congr 1
  simp only [← Matrix.star_eq_conjTranspose,star_mul,star_star]
  have h1 : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_mul_star_self U
  have h2 : star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_star_mul_self U
  calc
    _ = Matrix.trace (star (U:Matrix (Fin d) (Fin d) ℂ)*(star A*A)*(U:Matrix (Fin d) (Fin d) ℂ)) := by
      congr 1
      calc
        _ = star (U:Matrix (Fin d) (Fin d) ℂ)*star A*((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ))*A*(U:Matrix (Fin d) (Fin d) ℂ) := by noncomm_ring
        _ = _ := by rw [h1]; noncomm_ring
    _ = _ := by rw [Matrix.trace_mul_cycle, h1,one_mul]
 theorem hermitianMatrix_rotate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (rotateCoordinates U a) i=star (U:Matrix (Fin d) (Fin d) ℂ)*hermitianMatrix a i*U :=
  hermitianMatrix_coordinatesOfHermitian _ (fun i => conjugate_hermitian U _ (hermitianMatrix_isHermitian a i)) i
 theorem rotateCoordinates_norm (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) :
    ‖rotateCoordinates U a‖=‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← hermitianChart_normSq,← hermitianChart_normSq]
  simp_rw [hermitianMatrix_rotate,← hsNorm_sq]
  apply sum_congr rfl
  intro i _
  rw [hsNorm_unitary_conjugate]
 def rotateLinearIsometryEquiv (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    MatrixCoordinates n d ≃ₗᵢ[ℝ] MatrixCoordinates n d where
  toFun := rotateCoordinates U
  invFun := rotateCoordinates (star U)
  left_inv a := by
    apply hermitianChart_injective
    funext i
    simp only [hermitianChart,LinearMap.coe_mk,AddHom.coe_mk,hermitianMatrix_rotate,Unitary.coe_star,star_star]
    have h : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_mul_star_self U
    calc
      _ = ((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ))*hermitianMatrix a i*((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)) := by noncomm_ring
      _ = _ := by rw [h,one_mul,mul_one]
  right_inv a := by
    apply hermitianChart_injective
    funext i
    simp only [hermitianChart,LinearMap.coe_mk,AddHom.coe_mk,hermitianMatrix_rotate,Unitary.coe_star,star_star]
    have h : star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ)=1 := Unitary.coe_star_mul_self U
    calc
      _ = (star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ))*hermitianMatrix a i*(star (U:Matrix (Fin d) (Fin d) ℂ)*(U:Matrix (Fin d) (Fin d) ℂ)) := by noncomm_ring
      _ = _ := by rw [h,one_mul,mul_one]
  map_add' a b := by
    apply hermitianChart_injective
    funext i
    simp [hermitianChart,hermitianMatrix_rotate,hermitianMatrix_add,mul_add,add_mul]
  map_smul' r a := by
    apply hermitianChart_injective
    funext i
    simp [hermitianChart,hermitianMatrix_rotate,hermitianMatrix_smul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  norm_map' := rotateCoordinates_norm U
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate Classical
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {n d : ℕ}
 def noiseDirection (q : MatrixIndex n d) : α ⊕ Fin n → Matrix (Fin d) (Fin d) ℂ := fun a =>
   if a=Sum.inr q.1 then ((Real.sqrt d : ℂ)⁻¹) • hermitianBasis q.2.1 q.2.2 else 0
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 def jointNoiseBound {n d : ℕ} (R : ℝ) (x : MatrixIndex n d → ℝ) : ℝ := R+∑ i, matrixOpNorm (gueMatrix x i)
 def jointMomentBound (n : ℕ) (R : ℝ) : ℕ → ℝ
   | 0 => 1
   | m+1 => (n+1:ℝ)^m*(R^(m+1)+(n:ℝ)*gaussianMomentMajorant m)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries
 def jointFinMatrix {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) : Fin (n+n) → Matrix (Fin d) (Fin d) ℂ :=
  Fin.addCases A (gueMatrix x)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHeatLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixHeatLaw (μ : Measure (MatrixCoordinates n d)) (s : ℝ) : Measure (MatrixCoordinates n d) :=
    volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ (s/d) x))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {p : ℕ}
 def spectralBasis (p : ℕ) (l : Fin p) : Polynomial ℝ := Lagrange.basis univ (equidiscreteAtom p) l
 def spectralAnnihilator (p : ℕ) : Polynomial ℝ := ∏l : Fin p,(Polynomial.X-Polynomial.C (equidiscreteAtom p l))
 def spectralGood (p : ℕ) (δ Δ : ℝ) (m : List (Fin (p+1)) → ℂ) : Prop :=
    (∀i : Fin p,(3:ℝ)/4<(m [i.castSucc,i.castSucc]).re ∧
      (m [i.castSucc,i.castSucc,i.castSucc,i.castSucc]).re<4 ∧
      commutatorMoment m i.castSucc (Fin.last p)<Δ^2/64) ∧
    (∀l : Fin p,univariateMoment m ((spectralBasis p l)^2) (Fin.last p)<9/(8*p)) ∧
    univariateMoment m ((spectralAnnihilator p)^2) (Fin.last p)<badFraction p*δ^(2*p)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def reverseDerivativeMoment {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) : List (Fin n) → List (Fin n) → ℂ
  | [], w => wordMoment τ X w
  | i :: js, w => ∑ r : Fin w.length, if w[r.val] = i then
      reverseDerivativeMoment τ X js (w.take r.val) *
        wordMoment τ X (w.drop (r.val + 1)) else 0

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFisherTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixPolynomialDerivative (p : WordPolynomial n) (i : Fin n) (a : MatrixCoordinates n d) : ℂ :=
    ∑w∈p.support,p w*∑r : Fin w.length,if w[r.val]=i then
      matrixMoment a (w.take r.val)*matrixMoment a (w.drop (r.val+1)) else 0
 def matrixFisherTest (p : WordPolynomial n) (i : Fin n) (a : MatrixCoordinates n d) : ℝ :=
    2*(matrixPolynomialDerivative p i a).re-matrixPolynomialNorm p a
 def matrixRealScore (p : WordPolynomial n) (j k : Fin d) (x : MatrixIndex n d → ℝ) : ℝ :=
    (d:ℝ)*(matrixScorePolynomial p j k x).re
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFisherLiminf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
def normalizedMatrixFisher (μ : Measure (MatrixCoordinates n d)) (s : ℝ) : ℝ :=
  classicalFisher μ (s/d)/(d:ℝ)^3
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
def normalizedMatrixEntropy (μ : Measure (MatrixCoordinates n d)) (s : ℝ) : ℝ :=
  classicalEntropy μ (s/d)/(d:ℝ)^2+(n:ℝ)/2*Real.log d
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries FreeTensor
 def tensorMatrixTuple {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) : Option (Fin p) → Matrix (Fin (d*p)) (Fin (d*p)) ℂ :=
  fun a => matrixBlocks (fun l : Fin p => optionTuple A ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) a)
end FiniteEntropySeparation

end

end OAI
end


