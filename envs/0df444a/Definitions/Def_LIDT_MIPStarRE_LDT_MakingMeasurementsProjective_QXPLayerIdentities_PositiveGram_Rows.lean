-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:15:47.450222+00:00
-- url     : https://prove2.me/theorems/59aafcd7-5c49-452b-8de0-b8f5a912beec
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayerIdentities / PositiveGram / Rows
-- statement:
--   This bundle constructs the normalized row matrices associated with positive Gram spectra in the QXP layer. It proves orthonormality of normalized eigenvector images, identifies the relevant eigenvector bases, and records the mixed Gram identities and dual positive-spectrum rows.
--
--   Principal definitions:
--   - `orthonormal_normalized_image_of_adjoint_comp_eigenvectors`: proves orthonormality of normalized adjoint-composed eigenvector images.
--   - `orthonormal_normalized_matrix_image_of_gram_eigenvectors`: gives the matrix form of that result.
--   - `toEuclideanLin_gram_eigenvectorBasis`: transports the Gram eigenbasis to the Euclidean linear map.
--   - `orthonormal_normalized_matrix_image_of_positive_gram_spectrum`: restricts the result to the positive spectrum.
--   - `normalizedMatrixImageRows`: forms the normalized image-row matrix.
--   - `positiveGramSpectrumImageRows`: forms the positive-spectrum image rows.
--   - `normalized_matrix_image_rows_transpose_mixed`: records the mixed Gram identity.
--   - `positiveGramSpectrumRightRows`: defines the corresponding right rows.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Rows.lean#L28-L554

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Rows.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Q/X/XHat/P identities and approximations

Late-stage algebraic identities and approximation lemmas for the paper's
`Q/X/XHat/P` intermediate layer.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- Normalizing the images of positive Gram eigenvectors gives an orthonormal
family.

This is the elementary singular-vector calculation underlying the rectangular
polar-decomposition route.  If `v_i` are orthonormal eigenvectors of `L†L` with
positive eigenvalues `λ_i`, then the vectors `λ_i^{-1/2} L v_i` are
orthonormal in the target Hilbert space. -/
theorem orthonormal_normalized_image_of_adjoint_comp_eigenvectors
    {κ E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]
    (L : E →ₗ[ℂ] F)
    (v : κ → E) (lam : κ → ℝ)
    (hv : Orthonormal ℂ v)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ, L.adjoint (L (v i)) = (lam i : ℂ) • v i) :
    Orthonormal ℂ
      (fun i : κ => ((1 / Real.sqrt (lam i) : ℝ) : ℂ) • L (v i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hinner_image :
      inner ℂ (L (v i)) (L (v j)) =
        (lam j : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    calc
      inner ℂ (L (v i)) (L (v j)) =
          inner ℂ (v i) (L.adjoint (L (v j))) := by
            rw [LinearMap.adjoint_inner_right]
      _ = inner ℂ (v i) ((lam j : ℂ) • v j) := by rw [heig j]
      _ = (lam j : ℂ) * (if i = j then (1 : ℂ) else 0) := by
            by_cases hij : i = j
            · subst i
              rw [inner_smul_right]
              simp only [inner_self_eq_norm_sq_to_K, hv.norm_eq_one j, one_pow,
                map_one, ite_true, mul_one]
            · rw [inner_smul_right]
              rw [orthonormal_iff_ite.mp hv i j]
  have hscale_mul :
      ((1 / Real.sqrt (lam j) : ℝ) : ℂ) *
          ((lam j : ℂ) * (if i = j then (1 : ℂ) else 0) *
            ((1 / Real.sqrt (lam i) : ℝ) : ℂ)) =
        if i = j then (1 : ℂ) else 0 := by
    by_cases hij : i = j
    · subst j
      have hsqrt_ne : (Real.sqrt (lam i) : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (hlam i))
      have hsqrt_neC : ((Real.sqrt (lam i) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hsqrt_ne
      have hlam_eq :
          (lam i : ℂ) =
            ((Real.sqrt (lam i) : ℝ) : ℂ) *
              ((Real.sqrt (lam i) : ℝ) : ℂ) := by
        have hsqrt_sq : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i := by
          rw [← sq, Real.sq_sqrt (le_of_lt (hlam i))]
        exact_mod_cast hsqrt_sq.symm
      simp only [ite_true, mul_one, one_div]
      rw [hlam_eq]
      simp only [Complex.ofReal_inv]
      calc
        ((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹ *
            (((Real.sqrt (lam i) : ℝ) : ℂ) *
              ((Real.sqrt (lam i) : ℝ) : ℂ) *
                ((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹) =
            (((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹ *
              ((Real.sqrt (lam i) : ℝ) : ℂ)) *
                (((Real.sqrt (lam i) : ℝ) : ℂ) *
                  ((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹) := by ring
        _ = 1 := by
          rw [inv_mul_cancel₀ hsqrt_neC, mul_inv_cancel₀ hsqrt_neC]
          simp
    · simp [hij]
  calc
    inner ℂ (((1 / Real.sqrt (lam i) : ℝ) : ℂ) • L (v i))
        (((1 / Real.sqrt (lam j) : ℝ) : ℂ) • L (v j)) =
        ((1 / Real.sqrt (lam j) : ℝ) : ℂ) *
          (inner ℂ (L (v i)) (L (v j)) *
            ((1 / Real.sqrt (lam i) : ℝ) : ℂ)) := by
          simp
    _ = ((1 / Real.sqrt (lam j) : ℝ) : ℂ) *
          ((lam j : ℂ) * (if i = j then (1 : ℂ) else 0) *
            ((1 / Real.sqrt (lam i) : ℝ) : ℂ)) := by rw [hinner_image]
    _ = if i = j then (1 : ℂ) else 0 := hscale_mul

/-- Matrix form of
`orthonormal_normalized_image_of_adjoint_comp_eigenvectors`.

For a rectangular matrix `X`, orthonormal eigenvectors of the Gram operator
`Xᴴ * X` with positive eigenvalues yield orthonormal normalized images under
`X`.  This is the first local linear-algebra step toward constructing the
rectangular polar coisometry required for the QXP `Xhat` layer. -/
theorem orthonormal_normalized_matrix_image_of_gram_eigenvectors
    {κ μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ)
    (hv : Orthonormal ℂ v)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ,
      Matrix.toEuclideanLin (Xᴴ * X) (v i) = (lam i : ℂ) • v i) :
    Orthonormal ℂ
      (fun i : κ =>
        ((1 / Real.sqrt (lam i) : ℝ) : ℂ) • Matrix.toEuclideanLin X (v i)) := by
  refine orthonormal_normalized_image_of_adjoint_comp_eigenvectors
    (Matrix.toEuclideanLin X) v lam hv hlam ?_
  intro i
  change ((Matrix.toEuclideanLin X).adjoint.comp (Matrix.toEuclideanLin X)) (v i) =
    (lam i : ℂ) • v i
  rw [← Matrix.toEuclideanLin_conjTranspose_mul_self X]
  exact heig i

/-- The eigenvector basis of a Hermitian Gram operator remains an eigenvector
family after the Gram operator is written as `Xᴴ * X`. -/
private theorem toEuclideanLin_gram_eigenvectorBasis
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) (i : ι) :
    Matrix.toEuclideanLin (Xᴴ * X) (hQ.eigenvectorBasis i) =
      (hQ.eigenvalues i : ℂ) • hQ.eigenvectorBasis i := by
  rw [hgram]
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
    congrArg (fun v : ι → ℂ => WithLp.toLp 2 v) (hQ.mulVec_eigenvectorBasis i)

/-- Spectral form of `orthonormal_normalized_matrix_image_of_gram_eigenvectors`.

After the right Gram matrix of `X` has been identified with a Hermitian
operator `Q`, its positive spectral subspace gives an orthonormal family of
normalized images under `X`.  This is the form used when the rectangular polar
construction is indexed by the positive spectrum of the total `Q` operator. -/
theorem orthonormal_normalized_matrix_image_of_positive_gram_spectrum
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    Orthonormal ℂ
      (fun i : {i : ι // 0 < hQ.eigenvalues i} =>
        ((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
          Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1)) := by
  refine orthonormal_normalized_matrix_image_of_gram_eigenvectors X
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvectorBasis i.1)
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvalues i.1)
    ?_ ?_ ?_
  · simpa [Function.comp_def] using
      hQ.eigenvectorBasis.orthonormal.comp
        (fun i : {i : ι // 0 < hQ.eigenvalues i} => i.1)
        (fun _i _j h => Subtype.ext h)
  · exact fun i => i.2
  · intro i
    exact toEuclideanLin_gram_eigenvectorBasis X Q hQ hgram i.1

/-- The matrix whose rows are the normalized images of a prescribed Gram
eigenvector family. -/
noncomputable def normalizedMatrixImageRows
    {κ μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ) :
    Matrix κ μ ℂ :=
  Matrix.of fun i r =>
    (((1 / Real.sqrt (lam i) : ℝ) : ℂ) • Matrix.toEuclideanLin X (v i)) r

/-- The matrix of normalized images indexed by the positive spectrum of a
Hermitian Gram operator. -/
noncomputable def positiveGramSpectrumImageRows
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) :
    Matrix {i : ι // 0 < hQ.eigenvalues i} μ ℂ :=
  normalizedMatrixImageRows X
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvectorBasis i.1)
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvalues i.1)



/-- The transpose of the normalized-image row matrix satisfies the mixed
Gram identity on the chosen eigenvector family.

This is the finite-dimensional calculation
\[
  X^\dagger(\lambda_i^{-1/2}Xv_i)=\lambda_i^{1/2}v_i,
\]
recorded as a matrix identity with one column for each eigenvector. -/
theorem normalized_matrix_image_rows_transpose_mixed
    {κ μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ,
      Matrix.toEuclideanLin (Xᴴ * X) (v i) = (lam i : ℂ) • v i) :
    Xᴴ * (normalizedMatrixImageRows X v lam)ᵀ =
      Matrix.of fun j i => ((Real.sqrt (lam i) : ℝ) : ℂ) * v i j := by
  ext j i
  have hcoord :
      Matrix.toEuclideanLin (Xᴴ * X) (v i) j = (lam i : ℂ) * v i j := by
    simpa [Pi.smul_apply] using
      congrArg (fun w : EuclideanSpace ℂ ι => w j) (heig i)
  have hsqrt_ne : ((Real.sqrt (lam i) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hlam i)))
  have hlam_eq :
      (lam i : ℂ) =
        ((Real.sqrt (lam i) : ℝ) : ℂ) *
          ((Real.sqrt (lam i) : ℝ) : ℂ) := by
    have hsqrt_sq : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i := by
      rw [← sq, Real.sq_sqrt (le_of_lt (hlam i))]
    exact_mod_cast hsqrt_sq.symm
  calc
    (Xᴴ * (normalizedMatrixImageRows X v lam)ᵀ) j i =
        ((1 / Real.sqrt (lam i) : ℝ) : ℂ) *
          Matrix.toEuclideanLin (Xᴴ * X) (v i) j := by
          simp only [one_div, Complex.ofReal_inv, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
            normalizedMatrixImageRows, Matrix.mul_apply, Matrix.transpose_apply,
            Matrix.conjTranspose_apply, Matrix.of_apply]
          rw [← Matrix.mulVec_mulVec]
          simp only [Matrix.mulVec, dotProduct, RCLike.star_def, PiLp.smul_apply,
            Matrix.ofLp_toLpLin, Matrix.toLin'_apply, smul_eq_mul, Matrix.conjTranspose_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r _hr
          ring
    _ = ((1 / Real.sqrt (lam i) : ℝ) : ℂ) * ((lam i : ℂ) * v i j) := by
          rw [hcoord]
    _ = ((Real.sqrt (lam i) : ℝ) : ℂ) * v i j := by
          rw [hlam_eq]
          rw [one_div, Complex.ofReal_inv]
          field_simp [hsqrt_ne]

/-- Spectral form of `normalized_matrix_image_rows_transpose_mixed`.

On the positive spectral part of the Gram operator, the adjoint of `X` sends
the normalized image of an eigenvector back to the eigenvector multiplied by the
positive square root of its eigenvalue.  This is the matrix identity which
records the nonzero singular values in the rectangular polar construction. -/
theorem positive_gram_spectrum_image_rows_transpose_mixed
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ =
      Matrix.of fun j i =>
        ((Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) *
          hQ.eigenvectorBasis i.1 j := by
  exact normalized_matrix_image_rows_transpose_mixed X
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvectorBasis i.1)
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvalues i.1)
    (fun i => i.2)
    (fun i => toEuclideanLin_gram_eigenvectorBasis X Q hQ hgram i.1)

/-- Spectral expansion of the CFC square root of a positive Hermitian matrix.

This is the square-root analogue of the Hermitian spectral expansion.  It is
used below to compare the mixed product produced by the positive Gram-image
columns with the operator `CFC.sqrt Q` on the whole ambient space, including
the zero eigenspace. -/
lemma sqrt_eq_sum_sqrt_eigenvalues_vecMulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian)
    (hQ_pos : Q.PosSemidef) :
    CFC.sqrt Q =
      ∑ i : ι, (((Real.sqrt (hQ.eigenvalues i) : ℝ) : ℂ) •
        Matrix.vecMulVec ((hQ.eigenvectorBasis i).ofLp)
          (star ((hQ.eigenvectorBasis i).ofLp))) := by
  classical
  calc
    CFC.sqrt Q = hQ.cfc Real.sqrt := by
      rw [CFC.sqrt_eq_real_sqrt Q (ha := hQ_pos.nonneg),
        cfcₙ_eq_cfc (hf0 := by simp), hQ.cfc_eq]
    _ = ∑ i : ι, (((Real.sqrt (hQ.eigenvalues i) : ℝ) : ℂ) •
          Matrix.vecMulVec ((hQ.eigenvectorBasis i).ofLp)
            (star ((hQ.eigenvectorBasis i).ofLp))) := by
        ext r c
        simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
          Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply,
          Matrix.IsHermitian.eigenvectorUnitary_apply]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [Matrix.smul_apply, Matrix.vecMulVec_apply, mul_assoc, mul_comm]

/-- Rows dual to the positive Gram eigenvectors.

Multiplying the positive mixed columns by this matrix sums those columns
against the conjugate eigenvector coordinates.  Thus the product is the
spectral expansion of the square root of the Gram operator. -/
noncomputable def positiveGramSpectrumRightRows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) :
    Matrix {i : ι // 0 < hQ.eigenvalues i} ι ℂ :=
  Matrix.of fun i j => star (hQ.eigenvectorBasis i.1 j)

/-- The conjugate eigenvector rows over the positive Gram spectrum are
orthonormal.

This is the right-singular-vector companion to the normalized image-row
coisometry.  It is independent of the matrix `X`; it uses only the
orthonormality of the Hermitian eigenvector basis for `Q`. -/
theorem positive_gram_spectrum_right_rows_mul_conjTranspose
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) :
    positiveGramSpectrumRightRows Q hQ *
        (positiveGramSpectrumRightRows Q hQ)ᴴ =
      (1 : Matrix {i : ι // 0 < hQ.eigenvalues i}
        {i : ι // 0 < hQ.eigenvalues i} ℂ) := by
  classical
  ext i j
  have horth := orthonormal_iff_ite.mp hQ.eigenvectorBasis.orthonormal i.1 j.1
  simp only [positiveGramSpectrumRightRows, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, star_star, Matrix.one_apply]
  calc
    ∑ k : ι, star (hQ.eigenvectorBasis i.1 k) * hQ.eigenvectorBasis j.1 k =
        inner ℂ (hQ.eigenvectorBasis i.1) (hQ.eigenvectorBasis j.1) := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    _ = if i.1 = j.1 then (1 : ℂ) else 0 := horth
    _ = if i = j then (1 : ℂ) else 0 := by
      by_cases hij : i = j
      · simp [hij]
      · have hval : i.1 ≠ j.1 := by
          intro h
          exact hij (Subtype.ext h)
        simp [hij, hval]

/-- The positive Gram-image rows recover the square root of the Gram operator.

The identity
`Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ` records the positive spectral
columns `sqrt(λ_i) v_i`.  Multiplying by the conjugate eigenvector rows gives
the spectral expansion of `CFC.sqrt Q`; the zero eigenspace contributes nothing
because `Q` is positive semidefinite. -/
theorem positive_gram_spectrum_image_rows_mixed_eq_sqrt
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q) :
    Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ *
        positiveGramSpectrumRightRows Q hQ =
      CFC.sqrt Q := by
  classical
  have hmixed := positive_gram_spectrum_image_rows_transpose_mixed X Q hQ hgram
  have hsqrt := sqrt_eq_sum_sqrt_eigenvalues_vecMulVec Q hQ hQ_pos
  ext r c
  have hsqrt_entry := congrFun (congrFun hsqrt r) c
  rw [hmixed]
  simp only [Complex.coe_smul, Matrix.sum_apply, RCLike.star_def,
    positiveGramSpectrumRightRows, Matrix.mul_apply, Matrix.of_apply] at hsqrt_entry ⊢
  rw [hsqrt_entry]
  let coeff : ι → ℂ := fun i =>
    ((Real.sqrt (hQ.eigenvalues i) : ℝ) : ℂ) *
      hQ.eigenvectorBasis i r * star (hQ.eigenvectorBasis i c)
  have hzero :
      ∀ i : {i : ι // ¬ 0 < hQ.eigenvalues i}, coeff i.1 = 0 := by
    intro i
    have hnonneg : 0 ≤ hQ.eigenvalues i.1 := hQ_pos.eigenvalues_nonneg i.1
    have hle : hQ.eigenvalues i.1 ≤ 0 := le_of_not_gt i.2
    have hLam : hQ.eigenvalues i.1 = 0 := le_antisymm hle hnonneg
    simp [coeff, hLam]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (p := fun i : ι => 0 < hQ.eigenvalues i)
      coeff
  have hpositive_sum : (∑ i : {i : ι // 0 < hQ.eigenvalues i}, coeff i.1) =
      ∑ i : ι, coeff i := by
    rw [← hsplit]
    simp [hzero]
  simpa [coeff, Matrix.vecMulVec, mul_assoc] using hpositive_sum

/-- Zero Gram eigenvectors are killed by the rectangular matrix.

If `Q = Xᴴ * X` is positive semidefinite and an eigenvalue of `Q` is not
strictly positive, then it is zero.  The corresponding eigenvector therefore
lies in the kernel of `X`.  This is the algebraic reason why the arbitrary
completion directions in the rectangular polar construction do not contribute
to the mixed product `Xᴴ * Xhat`. -/
theorem matrix_image_eq_zero_of_nonpositive_gram_eigenvalue
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (i : ι) (hi : ¬ 0 < hQ.eigenvalues i) :
    Matrix.toEuclideanLin X (hQ.eigenvectorBasis i) = 0 := by
  let L := Matrix.toEuclideanLin X
  have hnonneg : 0 ≤ hQ.eigenvalues i := hQ_pos.eigenvalues_nonneg i
  have hle : hQ.eigenvalues i ≤ 0 := le_of_not_gt hi
  have hLam : hQ.eigenvalues i = 0 := le_antisymm hle hnonneg
  have heig := toEuclideanLin_gram_eigenvectorBasis X Q hQ hgram i
  have hadj : L.adjoint (L (hQ.eigenvectorBasis i)) = 0 := by
    change ((Matrix.toEuclideanLin X).adjoint.comp (Matrix.toEuclideanLin X))
        (hQ.eigenvectorBasis i) = 0
    rw [← Matrix.toEuclideanLin_conjTranspose_mul_self X, heig, hLam]
    simp
  have hinner : inner ℂ (L (hQ.eigenvectorBasis i)) (L (hQ.eigenvectorBasis i)) = 0 := by
    calc
      inner ℂ (L (hQ.eigenvectorBasis i)) (L (hQ.eigenvectorBasis i)) =
          inner ℂ (hQ.eigenvectorBasis i) (L.adjoint (L (hQ.eigenvectorBasis i))) := by
            rw [LinearMap.adjoint_inner_right]
      _ = 0 := by rw [hadj, inner_zero_right]
  exact inner_self_eq_zero.mp hinner

/-- Vectors orthogonal to the positive Gram images are killed by `X†`.

The proof tests the adjoint vector against the complete eigenvector basis of
`Q = Xᴴ * X`.  Positive eigenvectors are handled by the normalized-image
orthogonality assumption, while non-positive eigenvectors are killed by `X`
itself.  This is the kernel statement needed when completing the positive
left singular-vector rows to a full unitary. -/
theorem adjoint_image_eq_zero_of_orthogonal_positive_gram_images
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (y : EuclideanSpace ℂ μ)
    (hy : ∀ i : {i : ι // 0 < hQ.eigenvalues i},
      inner ℂ
        (((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
          Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1))
        y = 0) :
    (Matrix.toEuclideanLin X).adjoint y = 0 := by
  classical
  let L := Matrix.toEuclideanLin X
  apply hQ.eigenvectorBasis.repr.injective
  ext j
  simp only [LinearIsometryEquiv.map_zero, OrthonormalBasis.repr_apply_apply]
  by_cases hj : 0 < hQ.eigenvalues j
  · let jp : {i : ι // 0 < hQ.eigenvalues i} := ⟨j, hj⟩
    have hsqrt_ne : ((Real.sqrt (hQ.eigenvalues j) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hj))
    have hscale :
        ((Real.sqrt (hQ.eigenvalues j) : ℝ) : ℂ) *
            ((1 / Real.sqrt (hQ.eigenvalues j) : ℝ) : ℂ) = 1 := by
      rw [one_div, Complex.ofReal_inv, mul_inv_cancel₀ hsqrt_ne]
    have himage :
        L (hQ.eigenvectorBasis j) =
          ((Real.sqrt (hQ.eigenvalues j) : ℝ) : ℂ) •
            (((1 / Real.sqrt (hQ.eigenvalues j) : ℝ) : ℂ) •
              L (hQ.eigenvectorBasis j)) := by
      rw [smul_smul, hscale, one_smul]
    have hinner_image : inner ℂ (L (hQ.eigenvectorBasis j)) y = 0 := by
      have hhy :
          inner ℂ
            (((1 / Real.sqrt (hQ.eigenvalues j) : ℝ) : ℂ) •
              L (hQ.eigenvectorBasis j)) y = 0 := by
        simpa [jp, L] using hy jp
      rw [himage]
      rw [inner_smul_left, hhy, mul_zero]
    calc
      inner ℂ (hQ.eigenvectorBasis j) ((Matrix.toEuclideanLin X).adjoint y) =
          inner ℂ (L (hQ.eigenvectorBasis j)) y := by
            rw [LinearMap.adjoint_inner_right]
      _ = 0 := hinner_image
  · have hzero := matrix_image_eq_zero_of_nonpositive_gram_eigenvalue X Q
      hQ hQ_pos hgram j hj
    calc
      inner ℂ (hQ.eigenvectorBasis j) ((Matrix.toEuclideanLin X).adjoint y) =
          inner ℂ (L (hQ.eigenvectorBasis j)) y := by
            rw [LinearMap.adjoint_inner_right]
      _ = 0 := by rw [hzero, inner_zero_left]



/-- The strictly positive Gram spectrum has cardinality at most the row
dimension of the rectangular matrix.

The proof uses the normalized-image orthonormal family above: an orthonormal
family in `EuclideanSpace ℂ μ` is linearly independent, so its index set cannot
be larger than the dimension of that space. -/
theorem positive_gram_spectrum_card_le_rows
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    Fintype.card {i : ι // 0 < hQ.eigenvalues i} ≤ Fintype.card μ := by
  have horth :
      Orthonormal ℂ
        (fun i : {i : ι // 0 < hQ.eigenvalues i} =>
          ((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
            Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1)) :=
    orthonormal_normalized_matrix_image_of_positive_gram_spectrum X Q hQ hgram
  have hcard :=
    (Orthonormal.linearIndependent horth).fintype_card_le_finrank
  simpa using hcard


end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


