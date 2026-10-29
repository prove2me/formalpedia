-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
-- name    : LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:35:50.734578+00:00
-- url     : https://prove2.me/theorems/11d5e58f-3882-4134-91be-19064ec9a316
-- title:
--   LIDT definitions: LDT / ExpansionHypercubeGraph / MatrixRealization / Core
-- statement:
--   This bundle gives the concrete matrix realization of the hypercube expansion model. It defines tensor Hilbert spaces and rectangular operators, realizes operator families as matrices, specifies the rerandomized edge distribution, and packages constant and orthogonal Fourier modes with the spectral-gap conclusion.
--
--   Principal definitions:
--   - `tensorHilbertSpace`: the finite Hilbert space on the Cartesian product of two index types.
--   - `matrixTensorOperator`: the concrete Kronecker product operator.
--   - `RectangularMatrixOperator`: a matrix representation of an operator between two finite spaces.
--   - `MatrixOperatorFamilyRealization`: the matrix family used in variance calculations.
--   - `matrixHypercubeEdgeDistribution`: the hypercube edge distribution for the matrix model.
--   - `constantModeProjectorMatrix`: the projector onto the normalized constant mode.
--   - `orthogonalModeProjectorMatrix`: the projector onto the orthogonal complement.
--   - `LaplacianSpectralGapConclusion`: the Fourier-indexed spectral-gap conclusion.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean#L28-L584

-- Generated from MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 7 — Matrix realization

This file gives concrete finite-dimensional matrix realizations of the
hypercube variance operators, Fourier projectors, and spectral inequalities
introduced in `Defs`.

## References

- `blueprint/src/chapter/ch05_expansion.tex`
- `references/ldt-paper/expansion.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

universe u

/-- Tensor two finite Hilbert spaces by taking the cartesian product of indices. -/
def tensorHilbertSpace (H K : FiniteHilbertSpace) : FiniteHilbertSpace where
  carrier := H.carrier × K.carrier
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- Kronecker product of two concrete operators. -/
def matrixTensorOperator {H K : FiniteHilbertSpace}
    (A : MatrixOperator H) (B : MatrixOperator K) :
    MatrixOperator (tensorHilbertSpace H K) :=
  Matrix.kronecker A B

/-- Rectangular operators from `H` into `K`, represented as concrete matrices. -/
abbrev RectangularMatrixOperator (H K : FiniteHilbertSpace) :=
  Matrix K.carrier H.carrier ℂ

/-- The concrete matrix family underlying the variance calculations. -/
structure MatrixOperatorFamilyRealization (params : Parameters) where
  space : FiniteHilbertSpace.{u}
  state : PositiveMatrixState space
  family : Point params → MatrixOperator space

/-- The Section 7.1 edge distribution used by the matrix model. -/
noncomputable def matrixHypercubeEdgeDistribution (params : Parameters) :
    Distribution (Point params × Point params) :=
  rerandomizeCoord params

/-- The normalized all-ones projector onto the constant mode. -/
noncomputable def constantModeProjectorMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun _ _ => (hypercubeVertexCount params : ℂ)⁻¹

/-- The projector onto the orthogonal complement of the constant mode. -/
noncomputable def orthogonalModeProjectorMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  1 - constantModeProjectorMatrix params

private lemma fourierBasisState_apply_comm (params : Parameters) (α u : Point params) :
    fourierBasisState params α u = fourierBasisState params u α := by
  unfold fourierBasisState
  have hdot : dotProductZMod params u α = dotProductZMod params α u := by
    unfold dotProductZMod
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod,
    addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, hdot]

private lemma fourierBasisState_inner_product_dual (params : Parameters) (u v : Point params) :
    ∑ α : Point params,
      star (fourierBasisState params α u) * fourierBasisState params α v =
        if u = v then 1 else 0 := by
  conv_lhs =>
    arg 2; ext α
    rw [fourierBasisState_apply_comm params α u, fourierBasisState_apply_comm params α v]
  exact fourierBasisState_inner_product params u v

private lemma sum_fourierBasisProjector_eq_one (params : Parameters) :
    (∑ α : Point params, fourierBasisProjector params α) =
      (1 : MatrixOperator (pointHilbertSpace params)) := by
  ext u v
  have key :
      ∑ α : Point params,
        (fourierBasisProjector params α) u v =
      ∑ α : Point params,
        star (fourierBasisState params α v) * fourierBasisState params α u := by
    refine Finset.sum_congr rfl ?_
    intro α _
    simp [fourierBasisProjector, Matrix.vecMulVec_apply]; ring
  have hsum :
      (∑ α : Point params, fourierBasisProjector params α) u v =
        ∑ α : Point params, (fourierBasisProjector params α) u v := by
    simpa using
      (Matrix.sum_apply u v (Finset.univ : Finset (Point params))
        (fun α => fourierBasisProjector params α))
  rw [hsum, key, fourierBasisState_inner_product_dual params v u]
  by_cases h : v = u
  · subst v
    change (if u = u then (1 : ℂ) else 0) = (if u = u then 1 else 0)
    rfl
  · change (if v = u then (1 : ℂ) else 0) = (if u = v then 1 else 0)
    simp [h, show u ≠ v by intro huv; exact h huv.symm]

private lemma frequencyWeight_zero (params : Parameters) :
    frequencyWeight params (0 : Point params) = 0 := by
  simp [frequencyWeight]

private lemma frequencyWeight_pos_of_ne_zero (params : Parameters) {α : Point params}
    (hα : α ≠ 0) : 0 < frequencyWeight params α := by
  rw [frequencyWeight, Finset.card_pos]
  by_contra hempty
  apply hα
  funext i
  by_contra hi
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin params.m => α j ≠ (0 : Fq params)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  exact hempty ⟨i, hi_mem⟩







private lemma fourierBasis_norm_sq (params : Parameters) :
    (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
      star (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ))) =
        (hypercubeVertexCount params : ℂ)⁻¹ := by
  have hMpos : 0 < (hypercubeVertexCount params : ℝ) := by
    exact_mod_cast (pow_pos params.hq params.m)
  have hsqrt_ne : Real.sqrt (hypercubeVertexCount params : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 hMpos
  have hnormR : (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ *
      (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ =
    (hypercubeVertexCount params : ℝ)⁻¹ := by
    field_simp [hsqrt_ne]
    nlinarith [Real.sq_sqrt (le_of_lt hMpos)]
  have hstar : star ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) =
    ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hstar]
  simpa [Complex.ofReal_inv, Complex.ofReal_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) hnormR

private lemma constantModeProjectorMatrix_eq_fourierBasisProjector_zero (params : Parameters) :
    constantModeProjectorMatrix params = fourierBasisProjector params 0 := by
  ext u v
  simp only [constantModeProjectorMatrix, fourierBasisProjector, fourierBasisState,
    Matrix.vecMulVec_apply, Pi.star_apply]
  have hzero : ∀ w : Point params, addCharFq params (dotProductFq params w 0) = 1 := by
    intro w
    have : dotProductFq params w 0 = ⟨0, params.hq⟩ := by simp [dotProductFq]
    rw [this]; simp [addCharFq]
  simp only [star_mul]
  rw [hzero u, hzero v]
  simpa [mul_assoc] using (fourierBasis_norm_sq params).symm

private lemma orthogonalModeProjectorMatrix_eq_sum (params : Parameters) :
    orthogonalModeProjectorMatrix params =
      ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
  have hsplit :
      fourierBasisProjector params 0 +
          ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α =
        ∑ α : Point params, fourierBasisProjector params α := by
    exact
      (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
         (f := fun α => fourierBasisProjector params α) (Finset.mem_univ _))
  calc
    orthogonalModeProjectorMatrix params
      = (∑ α : Point params, fourierBasisProjector params α) - fourierBasisProjector params 0 := by
          rw [orthogonalModeProjectorMatrix,
            constantModeProjectorMatrix_eq_fourierBasisProjector_zero,
            sum_fourierBasisProjector_eq_one]
    _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
          rw [← hsplit]
          simp [sub_eq_add_neg, add_left_comm]

private lemma matrixAdjacencyOperator_spectral_decomp (params : Parameters) :
    matrixAdjacencyOperator params =
      ∑ α : Point params,
        (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
  ext u v
  rw [Matrix.sum_apply]
  calc
    (matrixAdjacencyOperator params) u v
      = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            (if v = w then (1 : ℂ) else 0) := by
              symm
              simp
    _ = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            ∑ α : Point params,
              star (fourierBasisState params α v) * fourierBasisState params α w := by
            congr 1 with w
            rw [fourierBasisState_inner_product_dual params v w]
    _ = ∑ α : Point params,
          star (fourierBasisState params α v) *
            ((matrixAdjacencyOperator params).mulVec (fourierBasisState params α)) u := by
          calc
            ∑ w : Point params,
                (matrixAdjacencyOperator params) u w *
                  ∑ α : Point params,
                    star (fourierBasisState params α v) * fourierBasisState params α w
              = ∑ w : Point params,
                  ∑ α : Point params,
                    (matrixAdjacencyOperator params) u w *
                      (star (fourierBasisState params α v) * fourierBasisState params α w) := by
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        rw [Finset.mul_sum]
            _ = ∑ α : Point params,
                  ∑ w : Point params,
                    star (fourierBasisState params α v) *
                      ((matrixAdjacencyOperator params) u w * fourierBasisState params α w) := by
                        rw [Finset.sum_comm]
                        refine Finset.sum_congr rfl ?_
                        intro α _
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        ring
            _ = ∑ α : Point params,
                  star (fourierBasisState params α v) *
                    ((matrixAdjacencyOperator params).mulVec (fourierBasisState params α)) u := by
                        refine Finset.sum_congr rfl ?_
                        intro α _
                        rw [Matrix.mulVec, dotProduct]
                        exact
                          (Finset.mul_sum
                            (s := (Finset.univ : Finset (Point params)))
                            (a := star (fourierBasisState params α v))
                            (f := fun i =>
                              (matrixAdjacencyOperator params) u i *
                                fourierBasisState params α i)).symm
    _ = ∑ α : Point params,
          (((adjacencyEigenvalue params α : Error) : ℂ) •
            fourierBasisProjector params α) u v := by
          refine Finset.sum_congr rfl ?_
          intro α _
          have hα := congrFun (eigenvectors params α) u
          simp only [Pi.smul_apply] at hα
          simp [fourierBasisProjector, Matrix.vecMulVec_apply, hα, mul_assoc, mul_comm]

private lemma matrixLaplacianOperator_spectral_decomp (params : Parameters) :
    matrixLaplacianOperator params =
      ∑ α : Point params,
        (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
  have hrel :
      ∀ α : Point params,
        (((laplacianEigenvalue params α : Error) : ℂ)) =
          (hypercubeVertexCount params : ℂ)⁻¹ -
            (((adjacencyEigenvalue params α : Error) : ℂ)) := by
    intro α
    simpa [one_div] using
      congrArg (fun x : Error => (x : ℂ))
        (laplacianEigenvalue_eq params α)
  calc
    matrixLaplacianOperator params
      = ((hypercubeVertexCount params : ℂ)⁻¹) •
            ∑ α : Point params, fourierBasisProjector params α -
          ∑ α : Point params,
            (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          rw [matrixLaplacianOperator, sum_fourierBasisProjector_eq_one,
            matrixAdjacencyOperator_spectral_decomp]
    _ = ∑ α : Point params,
          (((hypercubeVertexCount params : ℂ)⁻¹ -
              (((adjacencyEigenvalue params α : Error) : ℂ))) •
            fourierBasisProjector params α) := by
          rw [Finset.smul_sum]
          ext u v
          rw [Matrix.sub_apply, Matrix.sum_apply, Matrix.sum_apply, Matrix.sum_apply,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro α _
          simp [sub_mul]
    _ = ∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          refine Finset.sum_congr rfl ?_
          intro α _
          rw [hrel α]













private lemma laplacianEigenvalue_zero (params : Parameters) :
    laplacianEigenvalue params (0 : Point params) = 0 := by
  simp [laplacianEigenvalue, frequencyWeight_zero]

private lemma hypercubeSpectralGap_operator_posSemidef (params : Parameters) :
    (matrixLaplacianOperator params -
      ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params)).PosSemidef := by
  have hlap0 := laplacianEigenvalue_zero params
  have hcoeff_nonneg :
      ∀ α ∈ (Finset.univ.erase (0 : Point params)),
        0 ≤ laplacianEigenvalue params α - hypercubeSpectralGap params := by
    intro α hα
    have hα0 : α ≠ 0 := by simpa using Finset.mem_erase.mp hα |>.1
    exact sub_nonneg.mpr <|
      hypercubeSpectralGap_le_laplacianEigenvalue params α
        (frequencyWeight_pos_of_ne_zero params hα0)
  have hdecomp :
      matrixLaplacianOperator params -
          ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params) =
        ∑ α ∈ (Finset.univ.erase (0 : Point params)),
          (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
            fourierBasisProjector params α) := by
    rw [matrixLaplacianOperator_spectral_decomp, orthogonalModeProjectorMatrix_eq_sum]
    have hweighted :
        ∑ α : Point params,
            (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) =
          ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α) := by
      have hsplit :
          (((laplacianEigenvalue params 0 : Error) : ℂ) • fourierBasisProjector params 0) +
              ∑ α ∈ (Finset.univ.erase (0 : Point params)),
                (((laplacianEigenvalue params α : Error) : ℂ) •
                  fourierBasisProjector params α) =
            ∑ α : Point params,
              (((laplacianEigenvalue params α : Error) : ℂ) •
                fourierBasisProjector params α) := by
        exact
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
            (f := fun α =>
              (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α))
            (Finset.mem_univ _))
      rw [← hsplit]
      simp [hlap0]
    calc
      (∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α)) -
          ((hypercubeSpectralGap params : ℂ) •
            ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α)
        = (∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α)) -
            ((hypercubeSpectralGap params : ℂ) •
              ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α) := by
            rw [hweighted]
      _ = (∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α)) -
            ∑ α ∈ (Finset.univ.erase (0 : Point params)),
              ((hypercubeSpectralGap params : ℂ) • fourierBasisProjector params α) := by
            rw [Finset.smul_sum]
      _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            ((((laplacianEigenvalue params α : Error) : ℂ) •
                fourierBasisProjector params α) -
              ((hypercubeSpectralGap params : ℂ) • fourierBasisProjector params α)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
              fourierBasisProjector params α) := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            rw [← sub_smul]
            norm_num
  rw [hdecomp]
  refine Matrix.posSemidef_sum _ ?_
  intro α hα
  have hproj :
      (fourierBasisProjector params α).PosSemidef := by
    simpa [fourierBasisProjector] using
      (Matrix.posSemidef_vecMulVec_self_star (fourierBasisState params α))
  have hmatrix :
      ((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) •
          fourierBasisProjector params α) =
        (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
          fourierBasisProjector params α) := by
    ext u v
    simp
  change
    ((((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
      fourierBasisProjector params α)).PosSemidef
  rw [← hmatrix]
  exact hproj.smul (hcoeff_nonneg α hα)

/-- The operator spectral gap inequality for the hypercube:
`(1 / (m M)) · P⊥ ≤ L`, with `M = q^m`. -/
lemma hypercubeSpectralGap_operator (params : Parameters) :
    ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params) ≤
      matrixLaplacianOperator params := by
  exact sub_nonneg.mp (hypercubeSpectralGap_operator_posSemidef params).nonneg

/-- Fourier-indexed spectral-gap conclusion supporting `cor:laplacian-spectral-gap`.

Paper origin: `references/ldt-paper/expansion.tex:102-109`.

The paper states this corollary as an ordered-spectrum assertion:
if `λ₁ ≤ λ₂ ≤ ... ≤ λ_M` are the eigenvalues of the Laplacian `L`, then
`λ₁ = 0` and `λ₂ = 1 / (mM)`.  In the finite Fourier formulation, this is the
assertion that the zero-frequency mode has eigenvalue `0`, every nonzero mode
has eigenvalue at least `1 / (mM)`, and a weight-one mode attains this value. -/
structure LaplacianSpectralGapConclusion (params : Parameters) : Prop where
  zeroEigenvalue : laplacianEigenvalue params (0 : Point params) = 0
  nonzeroEigenvalue_ge_gap :
    ∀ α : Point params, α ≠ 0 →
      hypercubeSpectralGap params ≤ laplacianEigenvalue params α
  gap_attained :
    ∃ α : Point params,
      α ≠ 0 ∧ laplacianEigenvalue params α = hypercubeSpectralGap params
  gap_eq :
    hypercubeSpectralGap params =
      1 / ((params.m : Error) * ((params.q ^ params.m : ℕ) : Error))















end MIPStarRE.LDT.ExpansionHypercubeGraph

end

end LIDT


