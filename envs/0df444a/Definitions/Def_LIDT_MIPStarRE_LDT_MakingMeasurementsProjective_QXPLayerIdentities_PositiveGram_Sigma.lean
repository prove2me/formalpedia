-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:22:46.16979+00:00
-- url     : https://prove2.me/theorems/e94dcda9-0a3f-41bc-868f-696575b3e9f0
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayerIdentities / PositiveGram / Sigma
-- statement:
--   This bundle constructs the positive-Gram QXP layer on the finite $\sigma$ range. It gives an explicit polar extension from row-extension choices, proves existence of the XHat factor, specializes it to the $\sigma$ embedding, and builds the canonical QXP layer data.
--
--   Principal definitions:
--   - `xHat_of_positive_gram_spectrum_unitaryGroup_choices`: constructs XHat from chosen unitary row-extension data.
--   - `exists_xHat_of_positive_gram_spectrum`: proves existence of XHat from a positive Gram factorization.
--   - `exists_xHat_of_sigmaFinRangeEmbedding_positiveGram`: specializes the existence result to the $\sigma$ range embedding.
--   - `exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram`: constructs the $\sigma$-space QXP layer.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Sigma.lean#L26-L162

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Sigma.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
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
import Mathlib.Analysis.InnerProductSpace.GramMatrix
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
# Section 5 — Positive-Gram sigma-space specialization

Application of the positive-Gram polar construction to the canonical
sigma-space layer obtained from a rank-reduction witness.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- Explicit positive-Gram polar extension from chosen row-extension data with
the left factor represented as a unitary group element.

The existential construction of `Xhat` first chooses an embedding of the
positive spectral subspace into the auxiliary row space, then chooses a unitary
group element `U` extending the normalized image rows and a rectangular
coisometry `W` extending the right singular rows.  This theorem records the
deterministic matrix produced from those choices, namely `Uᵀ * W`, together
with the two QXP identities it satisfies.

The explicit form is useful when a later argument needs to impose additional
structure on the chosen rows, such as fresh option-completion row preservation
used to derive the QXP-internal comparison `Q_none ≤ P_none`. -/
theorem xHat_of_positive_gram_spectrum_unitaryGroup_choices
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix.unitaryGroup μ ℂ) (W : Matrix μ ι ℂ)
    (hU_rows :
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
        (U : Matrix μ μ ℂ) (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ))
    (hW_rows :
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι),
        W (e i) r = positiveGramSpectrumRightRows Q hQ i r) :
    ((U : Matrix μ μ ℂ)ᵀ * W) * ((U : Matrix μ μ ℂ)ᵀ * W)ᴴ =
        (1 : Matrix μ μ ℂ) ∧
      Xᴴ * ((U : Matrix μ μ ℂ)ᵀ * W) = CFC.sqrt Q := by
  constructor
  · exact transpose_unitaryGroup_mul_rectangular_coisometry U W hW
  · exact positive_gram_polar_extension_mixed_eq_sqrt_unitaryGroup X Q hQ hQ_pos
      hgram e U W hU_rows hW_rows

/-- Existence of the polar-extension `Xhat` from a positive Gram factorization.

If `Q = X†X` is positive semidefinite and the row dimension is at most the
column dimension, the positive spectral rows of `Q` determine a rectangular
coisometry `Xhat` satisfying the two primitive QXP identities:
`Xhat Xhat† = I` and `X† Xhat = sqrt Q`. -/
theorem exists_xHat_of_positive_gram_spectrum
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    [NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (hcard : Fintype.card μ ≤ Fintype.card ι) :
    ∃ xHat : Matrix μ ι ℂ,
      xHat * xHatᴴ = (1 : Matrix μ μ ℂ) ∧
        Xᴴ * xHat = CFC.sqrt Q := by
  classical
  obtain ⟨e, U, hU_rows⟩ :=
    exists_unitaryGroup_with_positive_gram_spectrum_rows_of_card X Q hQ hgram
  obtain ⟨W, hW, hW_rows⟩ :=
    exists_rectangular_coisometry_with_positive_gram_spectrum_right_rows Q hQ e hcard
  have hchoices := xHat_of_positive_gram_spectrum_unitaryGroup_choices
    X Q hQ hQ_pos hgram e U W hU_rows hW hW_rows
  refine ⟨(U : Matrix μ μ ℂ)ᵀ * W, ?_, ?_⟩
  · exact hchoices.1
  · exact hchoices.2

/-- Sigma-range specialization of the positive-Gram `Xhat` construction.

For a rank-reduction witness, the canonical sigma-space embedding satisfies
`X†X = Q`.  The stored total-rank bound supplies the rectangular dimension
hypothesis, so the positive-Gram construction produces the `Xhat` required by
the QXP data package. -/
theorem exists_xHat_of_sigmaFinRangeEmbedding_positiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))] :
    ∃ xHat : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ,
      xHat * xHatᴴ =
        (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier qLayer.q)) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
          CFC.sqrt (QTotal qLayer) := by
  classical
  let X : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ :=
    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective
  have hgram : Xᴴ * X = QTotal qLayer := by
    simpa [X, QTotal] using
      sigmaFinRangeEmbedding_gram_right qLayer.q hRank.projective hRank.sum_eq_total
  have hQ_pos : (QTotal qLayer).PosSemidef := by
    have hX_gram :
        Matrix.gram ℂ (fun j : ι => WithLp.toLp 2 fun r => X r j) = Xᴴ * X := by
      ext i j
      simp [Matrix.gram, Matrix.mul_apply, Matrix.conjTranspose_apply,
        EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
    rw [← hgram]
    rw [← hX_gram]
    exact Matrix.posSemidef_gram ℂ _
  have hQ : (QTotal qLayer).IsHermitian := hQ_pos.isHermitian
  have hcard :
      Fintype.card (sigmaRangeCarrier qLayer.q) ≤ Fintype.card ι := by
    exact hRank.toSigmaRangeQLayer.auxDim_le
  simpa [X] using
    exists_xHat_of_positive_gram_spectrum X (QTotal qLayer) hQ hQ_pos hgram hcard

/-- Produce the canonical sigma-space QXP layer from the positive-Gram `Xhat`.

This removes the last explicit `Xhat` input from the sigma-space constructor:
the rank-reduction witness supplies the projective `Q` layer and the
rectangular dimension bound, while
`exists_xHat_of_sigmaFinRangeEmbedding_positiveGram` supplies the coisometry
and mixed square-root identities. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))] :
    ∃ xHat : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ,
      xHat * xHatᴴ =
          (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier qLayer.q)) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
            CFC.sqrt (QTotal qLayer) ∧
          ∃ data : QXPLayerData Outcome ι,
            ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
              hq ▸ data.x =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
                hq ▸ data.xHat =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    xHat) := by
  obtain ⟨xHat, hxHat_coisometry, hxHat_mixed⟩ :=
    exists_xHat_of_sigmaFinRangeEmbedding_positiveGram hRank
  obtain ⟨data, hq, hx, hxHat⟩ :=
    exists_qxpLayerData_ofRankReductionSigmaRangeAndSvdIdentities hRank xHat
      hxHat_coisometry hxHat_mixed
  exact ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat⟩



end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


