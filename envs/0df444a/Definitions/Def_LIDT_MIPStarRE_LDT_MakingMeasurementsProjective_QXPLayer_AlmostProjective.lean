-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:09:37.153901+00:00
-- url     : https://prove2.me/theorems/91c9c7b2-984e-441f-bce9-5544afe23745
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayer / AlmostProjective
-- statement:
--   This bundle gives the operator-order almost-projectivity estimate for the rank-reduced Q family in the QXP projectivization layer. It is the input to the subsequent spectral repair.
--
--   Principal definitions:
--   - `qAlmostProjective`: Let $\psi$ be a quantum state, `A` a complete measurement, $\zeta$ satisfy `0 <= zeta <= 1/4`, and `data` be Q-layer data. If `RankReductionWitness psi A zeta data` holds, then
--     $$
--     \sum_a\bigl(Q_a Q_{\mathrm{total}} Q_a-Q_a\bigr)
--     \leq \bigl(4\,\operatorname{spectralTruncationError}(\zeta)\bigr) I.
--     $$
--     Here the inequality is operator order and the scalar is interpreted in the complex operator space. The witness supplies the rank-reduced projectivity and total-operator bounds needed for the estimate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/AlmostProjective.lean#L21-L97

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/AlmostProjective.lean by skeleton subtraction.
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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Q/X/XHat/P almost-projectivity

Almost-projective estimates for the rank-reduced `Q` family.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

/-- **`Q` is almost projective** (`lem:q-almost-projective`).

The rank-reduced family satisfies the operator inequality
`∑_a (Q_a Q Q_a - Q_a) ≤ 4√ζ · I`. -/
lemma qAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hζ : 0 ≤ ζ)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a)) ≤
        (((4 : Error) * spectralTruncationError ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  intro hRank
  let ε : Error := spectralTruncationError ζ
  let sandwiched : Outcome → MIPStarRE.Quantum.Op ι :=
    fun a => Qa data a * QTotal data * Qa data a
  have hsandwiched_le :
      ∀ a : Outcome, sandwiched a ≤ (((1 : Error) + 2 * ε) : ℂ) • Qa data a := by
    intro a
    have hQa_herm : (Qa data a)ᴴ = Qa data a := (hRank.projective a).isSelfAdjoint.isHermitian.eq
    have hQa_sq : Qa data a * Qa data a = Qa data a := (hRank.projective a).isIdempotentElem.eq
    calc
      sandwiched a = Qa data a * QTotal data * Qa data a := rfl
      _ ≤ Qa data a *
            ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) *
            Qa data a := by
              exact IsSelfAdjoint.conjugate_le_conjugate hRank.total_le hQa_herm
      _ = (((1 : Error) + 2 * ε) : ℂ) • Qa data a := by
            simp [hQa_sq]
  have hsum_le :
      (∑ a, sandwiched a) ≤ (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) := by
    calc
      (∑ a, sandwiched a) ≤ ∑ a, (((1 : Error) + 2 * ε) : ℂ) • Qa data a := by
        exact Finset.sum_le_sum fun a _ => hsandwiched_le a
      _ = (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) := by
        simpa using
          (Finset.smul_sum (s := Finset.univ) (r := (((1 : Error) + 2 * ε) : ℂ))
            (f := fun a : Outcome => Qa data a)).symm
  have hsub_le :
      (∑ a, sandwiched a) - ∑ a, Qa data a ≤
        (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) - ∑ a, Qa data a := by
    exact sub_le_sub_right hsum_le _
  have hε_nonneg : 0 ≤ ε := by
    simpa [ε] using spectralTruncationError_nonneg hζ
  have hcoeff :
      (2 * ε) * (1 + 2 * ε) ≤ 4 * ε := by
    have hε_half : ε ≤ 1 / (2 : Error) := spectralTruncationError_le_half ζ hζ hζ_small
    nlinarith
  have hscaled_total :
      (2 * ε) • QTotal data ≤
        (2 * ε) • ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) := by
    exact smul_le_smul_of_nonneg_left hRank.total_le (by nlinarith [hε_nonneg] : 0 ≤ 2 * ε)
  have hcoeff_op :
      (((2 * ε) * ((1 : Error) + 2 * ε)) : Error) • (1 : MIPStarRE.Quantum.Op ι) ≤
        ((4 : Error) * ε) • (1 : MIPStarRE.Quantum.Op ι) := by
    exact smul_le_smul_of_nonneg_right hcoeff zero_le_one
  calc
    (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a))
        = (∑ a, sandwiched a) - ∑ a, Qa data a := by
            simp [sandwiched, Finset.sum_sub_distrib]
    _ ≤ (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) - ∑ a, Qa data a := hsub_le
    _ = (2 * ε) • QTotal data := by
          rw [hRank.sum_eq_total]
          ext i j
          simp
          ring
    _ ≤ (2 * ε) • ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) := hscaled_total
    _ = ((2 * ε) * ((1 : Error) + 2 * ε)) • (1 : MIPStarRE.Quantum.Op ι) := by
          ext i j
          simp [mul_assoc]
    _ ≤ ((4 : Error) * ε) • (1 : MIPStarRE.Quantum.Op ι) := hcoeff_op
    _ = (((4 : Error) * spectralTruncationError ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
          ext i j
          simp [ε]


end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


