-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:19:38.862984+00:00
-- url     : https://prove2.me/theorems/46a24f5b-57ae-4385-9722-487341f6671a
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayerIdentities / PositiveGram / Completion
-- statement:
--   This bundle provides completion results for positive-Gram row families in the QXP projectivization layer. It extends orthonormal families to unitary rows or rectangular coisometries and records the annihilation property of completion rows outside the positive Gram spectrum.
--
--   Principal definitions:
--   - `exists_orthonormalBasis_extension_of_embedding`: extends an embedded orthonormal family to a basis.
--   - `exists_unitaryGroup_rows_extending_orthonormal`: realizes prescribed orthonormal rows inside a square unitary matrix.
--   - `exists_unitaryGroup_with_positive_gram_spectrum_rows`: embeds positive-Gram image rows into a unitary matrix.
--   - `exists_unitaryGroup_with_positive_gram_spectrum_rows_of_card`: gives the cardinality-explicit version.
--   - `exists_rectangular_coisometry_extending_orthonormal_rows`: extends rows to a rectangular coisometry.
--   - `exists_rectangular_coisometry_with_positive_gram_spectrum_right_rows`: extends positive-Gram right singular rows.
--   - `transpose_unitaryGroup_mul_rectangular_coisometry`: preserves coisometry under the stated unitary multiplication.
--   - `adjoint_image_eq_zero_of_unitary_positive_gram_completion_row`: shows completion rows outside the spectrum are killed by the adjoint.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Completion.lean#L24-L414

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Completion.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
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
# Section 5 — Positive-Gram completion

Completion and polar-extension lemmas for the positive spectral rows of a
right Gram operator.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- Extend an orthonormal family along an embedding into the ambient row index
set.

This is the finite-dimensional basis-extension step used in the rectangular
polar-decomposition construction: after choosing distinct row indices for the
prescribed vectors, the family can be completed to an orthonormal basis of the
whole row space. -/
private theorem exists_orthonormalBasis_extension_of_embedding
    {κ μ : Type*} [Fintype μ]
    (row : κ → EuclideanSpace ℂ μ)
    (hrow : Orthonormal ℂ row)
    (e : κ ↪ μ) :
    ∃ b : OrthonormalBasis μ ℂ (EuclideanSpace ℂ μ),
      ∀ i : κ, b (e i) = row i := by
  classical
  let invRange : Set.range e → κ := (Equiv.ofInjective e e.injective).symm
  let rowFull : μ → EuclideanSpace ℂ μ := fun j =>
    if hj : j ∈ Set.range e then row (invRange ⟨j, hj⟩) else 0
  have hrowFull : ∀ i : κ, rowFull (e i) = row i := by
    intro i
    simp [rowFull, invRange, Equiv.ofInjective_symm_apply]
  have horthRange : Orthonormal ℂ ((Set.range e).domRestrict rowFull) := by
    have hcomp : Orthonormal ℂ (fun x : Set.range e => row (invRange x)) :=
      hrow.comp invRange (Equiv.injective _)
    convert hcomp with x
    change rowFull x = row (invRange x)
    change (if hj : (x : μ) ∈ Set.range e then row (invRange ⟨x, hj⟩) else 0) =
      row (invRange x)
    rw [dif_pos x.2]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ μ) (ι := μ)
      (card_ι := by simp) (v := rowFull) (s := Set.range e) horthRange
  refine ⟨b, fun i => ?_⟩
  rw [hb (e i) ⟨i, rfl⟩, hrowFull i]

/-- A square unitary group element whose selected rows are a prescribed
orthonormal family.

The row equations are stated pointwise so that later matrix calculations can
rewrite entries without unfolding the chosen orthonormal basis. -/
theorem exists_unitaryGroup_rows_extending_orthonormal
    {κ μ : Type*} [Fintype μ] [DecidableEq μ]
    (row : κ → EuclideanSpace ℂ μ)
    (hrow : Orthonormal ℂ row)
    (e : κ ↪ μ) :
    ∃ U : Matrix.unitaryGroup μ ℂ,
      ∀ (i : κ) (r : μ), (U : Matrix μ μ ℂ) (e i) r = row i r := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_of_embedding row hrow e
  let Umat : Matrix μ μ ℂ := Matrix.of fun i r => b i r
  have hleft : Umat * Umatᴴ = (1 : Matrix μ μ ℂ) := by
    simpa [Umat] using
      Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
        (fun i : μ => b i) b.orthonormal
  let U : Matrix.unitaryGroup μ ℂ := ⟨Umat, (Matrix.mem_unitaryGroup_iff).2 hleft⟩
  refine ⟨U, ?_⟩
  intro i r
  simp [U, Umat, hb i]

/-- The positive Gram image rows can be embedded into a square unitary group
element.

The hypothesis `e` chooses distinct row positions for the strictly positive
eigenvalues of the Gram operator.  The theorem then completes the corresponding
normalized image rows to a unitary element on the row space.  This is the
basis-extension ingredient needed to turn the positive spectral part into the
left unitary factor of the rectangular polar construction. -/
theorem exists_unitaryGroup_with_positive_gram_spectrum_rows
    {μ ι : Type*}
    [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ) :
    ∃ U : Matrix.unitaryGroup μ ℂ,
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
        (U : Matrix μ μ ℂ) (e i) r =
          positiveGramSpectrumImageRows X Q hQ i r := by
  classical
  let row : {i : ι // 0 < hQ.eigenvalues i} → EuclideanSpace ℂ μ := fun i =>
    ((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
      Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1)
  obtain ⟨U, hrows⟩ :=
    exists_unitaryGroup_rows_extending_orthonormal row
      (orthonormal_normalized_matrix_image_of_positive_gram_spectrum X Q hQ hgram) e
  refine ⟨U, ?_⟩
  intro i r
  simpa [row, positiveGramSpectrumImageRows, normalizedMatrixImageRows] using
    hrows i r

/-- Existential form of
`exists_unitaryGroup_with_positive_gram_spectrum_rows`.

The normalized positive Gram image rows have cardinality at most the row
dimension, so one may choose distinct row positions and then extend those rows
to a square unitary group element. -/
theorem exists_unitaryGroup_with_positive_gram_spectrum_rows_of_card
    {μ ι : Type*}
    [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    ∃ e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ,
      ∃ U : Matrix.unitaryGroup μ ℂ,
        ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
          (U : Matrix μ μ ℂ) (e i) r =
            positiveGramSpectrumImageRows X Q hQ i r := by
  classical
  have hcard :
      Fintype.card {i : ι // 0 < hQ.eigenvalues i} ≤ Fintype.card μ :=
    positive_gram_spectrum_card_le_rows X Q hQ hgram
  let e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  exact ⟨e, exists_unitaryGroup_with_positive_gram_spectrum_rows X Q hQ hgram e⟩

/-- Extend an orthonormal row family to a rectangular coisometry.

The embedding `e : κ ↪ μ` specifies the rows of the rectangular matrix which
must agree with the prescribed family.  The dimension hypothesis
`Fintype.card μ ≤ Fintype.card ν` supplies enough room to complete these rows
to an orthonormal family indexed by all of `μ`. -/
theorem exists_rectangular_coisometry_extending_orthonormal_rows
    {κ μ ν : Type*} [Fintype μ] [DecidableEq μ] [Fintype ν]
    (row : κ → EuclideanSpace ℂ ν)
    (hrow : Orthonormal ℂ row)
    (e : κ ↪ μ)
    (hcard : Fintype.card μ ≤ Fintype.card ν) :
    ∃ W : Matrix μ ν ℂ,
      W * Wᴴ = (1 : Matrix μ μ ℂ) ∧
        ∀ (i : κ) (r : ν), W (e i) r = row i r := by
  classical
  let f : μ ↪ ν := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let fe : κ ↪ ν := e.trans f
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_of_embedding row hrow fe
  let W : Matrix μ ν ℂ := Matrix.of fun i r => b (f i) r
  have hleft : W * Wᴴ = (1 : Matrix μ μ ℂ) := by
    simpa [W] using
      Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
        (fun i : μ => b (f i)) (b.orthonormal.comp f f.injective)
  refine ⟨W, hleft, ?_⟩
  intro i r
  change (b (f (e i))) r = row i r
  rw [show f (e i) = fe i from rfl, hb i]

/-- Extend the positive Gram right-singular rows to a rectangular coisometry.

The selected rows are the conjugate eigenvector rows of the right Gram
operator.  The cardinality hypothesis is the rectangular dimension condition:
there must be enough columns to complete the prescribed rows to an
orthonormal row family indexed by the auxiliary row space. -/
theorem exists_rectangular_coisometry_with_positive_gram_spectrum_right_rows
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (hcard : Fintype.card μ ≤ Fintype.card ι) :
    ∃ W : Matrix μ ι ℂ,
      W * Wᴴ = (1 : Matrix μ μ ℂ) ∧
        ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι),
          W (e i) r = positiveGramSpectrumRightRows Q hQ i r := by
  classical
  let row : {i : ι // 0 < hQ.eigenvalues i} → EuclideanSpace ℂ ι := fun i =>
    WithLp.toLp 2 fun r : ι => positiveGramSpectrumRightRows Q hQ i r
  have hrow : Orthonormal ℂ row := by
    rw [orthonormal_iff_ite]
    intro i j
    have hright := positive_gram_spectrum_right_rows_mul_conjTranspose Q hQ
    have hentry := congrFun (congrFun hright j) i
    have hone :
        (1 : Matrix {i : ι // 0 < hQ.eigenvalues i}
          {i : ι // 0 < hQ.eigenvalues i} ℂ) j i =
          if i = j then (1 : ℂ) else 0 := by
      by_cases hij : i = j
      · subst j
        simp
      · have hji : j ≠ i := fun h => hij h.symm
        simp [hij, hji]
    simpa [row, Matrix.mul_apply, Matrix.conjTranspose_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm, eq_comm, hone] using hentry
  obtain ⟨W, hW, hrows⟩ :=
    exists_rectangular_coisometry_extending_orthonormal_rows row hrow e hcard
  exact ⟨W, hW, by simpa [row] using hrows⟩

/-- Left multiplication by the transpose of a unitary group element preserves
row coisometries.

This is the coisometry half of the polar-extension calculation for the
candidate `Xhat = Uᵀ W`: the rectangular factor `W` has orthonormal rows, and
the square factor `U` merely changes the orthonormal basis of the row space. -/
theorem transpose_unitaryGroup_mul_rectangular_coisometry
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    (U : Matrix.unitaryGroup μ ℂ) (W : Matrix μ ι ℂ)
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ)) :
    ((U : Matrix μ μ ℂ)ᵀ * W) * ((U : Matrix μ μ ℂ)ᵀ * W)ᴴ =
      (1 : Matrix μ μ ℂ) := by
  have hU_right : (U : Matrix μ μ ℂ)ᴴ * (U : Matrix μ μ ℂ) =
      (1 : Matrix μ μ ℂ) :=
    Unitary.coe_star_mul_self U
  have hU_transpose :
      (U : Matrix μ μ ℂ)ᵀ * ((U : Matrix μ μ ℂ)ᵀ)ᴴ =
        (1 : Matrix μ μ ℂ) := by
    rw [show ((U : Matrix μ μ ℂ)ᵀ)ᴴ = ((U : Matrix μ μ ℂ)ᴴ)ᵀ from rfl,
      ← Matrix.transpose_mul, hU_right, Matrix.transpose_one]
  calc
    ((U : Matrix μ μ ℂ)ᵀ * W) * ((U : Matrix μ μ ℂ)ᵀ * W)ᴴ =
        (U : Matrix μ μ ℂ)ᵀ * (W * Wᴴ) * ((U : Matrix μ μ ℂ)ᵀ)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          simp [Matrix.mul_assoc]
    _ = (U : Matrix μ μ ℂ)ᵀ * ((U : Matrix μ μ ℂ)ᵀ)ᴴ := by
          rw [hW, Matrix.mul_one]
    _ = 1 := hU_transpose

/-- Completion rows of the left unitary outside the positive Gram spectrum are
killed by `X†`.

The selected rows of `U` are the normalized positive images of the Gram
eigenvectors.  If a row index is not one of the selected positive spectral
indices, the row-orthogonality of `U` makes that row orthogonal to all positive
Gram images.  The adjoint-kernel lemma then gives the stated vanishing. -/
theorem adjoint_image_eq_zero_of_unitary_positive_gram_completion_row
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix μ μ ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hU_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
      U (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (a : μ) (ha : a ∉ Set.range e) :
    (Matrix.toEuclideanLin X).adjoint (WithLp.toLp 2 fun r : μ => U a r) = 0 := by
  refine adjoint_image_eq_zero_of_orthogonal_positive_gram_images X Q hQ hQ_pos
    hgram (WithLp.toLp 2 fun r : μ => U a r) ?_
  intro i
  have hae : a ≠ e i := by
    intro h
    exact ha ⟨i, h.symm⟩
  have hentry := congrFun (congrFun hU_left a) (e i)
  have hentry_zero :
      ∑ r : μ, U a r * star (U (e i) r) = 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hae] using hentry
  change inner ℂ
      (WithLp.toLp 2 fun r : μ => positiveGramSpectrumImageRows X Q hQ i r)
      (WithLp.toLp 2 fun r : μ => U a r) = 0
  simpa [hU_rows i, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    using hentry_zero

/-- The selected columns of `X† Uᵀ` are the positive Gram-image mixed columns.

If the selected rows of `U` are the normalized images of the positive Gram
eigenvectors, then multiplying by `X†` and transposing `U` recovers precisely
the column matrix `X† Rᵀ`, where `R` is the positive Gram-image row matrix. -/
theorem positive_gram_selected_left_unitary_mixed_column
    {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix μ μ ℂ)
    (hU_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
      U (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι) :
    (Xᴴ * Uᵀ) r (e i) =
      (Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ) r i := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, hU_rows i]

/-- The complementary columns of `X† Uᵀ` vanish.

This is the matrix-column form of
`adjoint_image_eq_zero_of_unitary_positive_gram_completion_row`.  It records
that the arbitrary rows used to complete the positive image rows to a full
unitary make no contribution after left multiplication by `X†`. -/
theorem positive_gram_completion_left_unitary_mixed_column_eq_zero
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix μ μ ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hU_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
      U (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (a : μ) (ha : a ∉ Set.range e) (r : ι) :
    (Xᴴ * Uᵀ) r a = 0 := by
  have hzero :=
    adjoint_image_eq_zero_of_unitary_positive_gram_completion_row X Q hQ hQ_pos
      hgram e U hU_left hU_rows a ha
  have hzero_lin :
      Matrix.toEuclideanLin Xᴴ (WithLp.toLp 2 fun r : μ => U a r) = 0 := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact hzero
  have hcoord := congrArg (fun y : EuclideanSpace ℂ ι => y r) hzero_lin
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct] using hcoord

/-- The polar-extension mixed product is the positive-spectrum mixed product.

The candidate `Xhat = Uᵀ W` has selected rows matching the positive left and
right singular rows.  After expanding the middle index, the selected part is
exactly the positive-spectrum square-root product, while every complementary
row is killed by `X†`. -/
theorem positive_gram_polar_extension_mixed_eq_positive_rows
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix μ μ ℂ) (W : Matrix μ ι ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hU_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
      U (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (hW_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι),
      W (e i) r = positiveGramSpectrumRightRows Q hQ i r) :
    Xᴴ * (Uᵀ * W) =
      Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ *
        positiveGramSpectrumRightRows Q hQ := by
  classical
  ext r c
  let term : μ → ℂ := fun a => (Xᴴ * Uᵀ) r a * W a c
  let : Fintype {a : μ // a ∈ Set.range e} :=
    Subtype.fintype (fun a : μ => a ∈ Set.range e)
  let : Fintype {a : μ // ¬ a ∈ Set.range e} :=
    Subtype.fintype (fun a : μ => ¬ a ∈ Set.range e)
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (p := fun a : μ => a ∈ Set.range e) term
  have hcomp : ∀ a : {a : μ // ¬ a ∈ Set.range e}, term a.1 = 0 := by
    intro a
    simp [term, positive_gram_completion_left_unitary_mixed_column_eq_zero X Q
      hQ hQ_pos hgram e U hU_left hU_rows a.1 a.2 r]
  let er :
      {i : ι // 0 < hQ.eigenvalues i} ≃ {a : μ // a ∈ Set.range e} :=
    Equiv.ofInjective e e.injective
  have hrange :
      (∑ a : {a : μ // a ∈ Set.range e}, term a.1) =
        ∑ i : {i : ι // 0 < hQ.eigenvalues i},
          (Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ) r i *
            positiveGramSpectrumRightRows Q hQ i c := by
    have hreindex :
        (∑ i : {i : ι // 0 < hQ.eigenvalues i}, term (e i)) =
          ∑ a : {a : μ // a ∈ Set.range e}, term a.1 := by
      exact Fintype.sum_equiv er (fun i => term (e i)) (fun a => term a.1)
        (fun _ => rfl)
    rw [← hreindex]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [term, positive_gram_selected_left_unitary_mixed_column X Q hQ e U
      hU_rows i r, hW_rows i c]
  have hsum :
      (∑ a : μ, term a) =
        ∑ i : {i : ι // 0 < hQ.eigenvalues i},
          (Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ) r i *
            positiveGramSpectrumRightRows Q hQ i c := by
    calc
      (∑ a : μ, term a) =
          (∑ a : {a : μ // a ∈ Set.range e}, term a.1) +
            ∑ a : {a : μ // ¬ a ∈ Set.range e}, term a.1 := hsplit.symm
      _ = ∑ a : {a : μ // a ∈ Set.range e}, term a.1 := by
            simp only [hcomp, Finset.sum_const_zero, add_zero]
      _ = ∑ i : {i : ι // 0 < hQ.eigenvalues i},
            (Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ) r i *
              positiveGramSpectrumRightRows Q hQ i c := hrange
  calc
    (Xᴴ * (Uᵀ * W)) r c = ((Xᴴ * Uᵀ) * W) r c := by
      rw [Matrix.mul_assoc]
    _ = ∑ a : μ, term a := by simp [term, Matrix.mul_apply]
    _ = ∑ i : {i : ι // 0 < hQ.eigenvalues i},
          (Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ) r i *
            positiveGramSpectrumRightRows Q hQ i c := hsum
    _ = (Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ *
          positiveGramSpectrumRightRows Q hQ) r c := by
        simp [Matrix.mul_apply]

/-- The polar-extension mixed product is the square root of the Gram operator.

This combines the finite-dimensional completion calculation for
`Xhat = Uᵀ W` with the positive-spectrum square-root identity. -/
theorem positive_gram_polar_extension_mixed_eq_sqrt_unitaryGroup
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix.unitaryGroup μ ℂ) (W : Matrix μ ι ℂ)
    (hU_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
      (U : Matrix μ μ ℂ) (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (hW_rows : ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι),
      W (e i) r = positiveGramSpectrumRightRows Q hQ i r) :
    Xᴴ * ((U : Matrix μ μ ℂ)ᵀ * W) = CFC.sqrt Q := by
  rw [positive_gram_polar_extension_mixed_eq_positive_rows X Q hQ hQ_pos
    hgram e (U : Matrix μ μ ℂ) W
    (Unitary.coe_mul_star_self U) hU_rows hW_rows]
  exact positive_gram_spectrum_image_rows_mixed_eq_sqrt X Q hQ hQ_pos hgram

end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


