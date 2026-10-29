-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:07:02.934649+00:00
-- url     : https://prove2.me/theorems/3bc4cbe8-0a39-40b2-9749-a7bab6766007
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayer / QCompleteness
-- statement:
--   This bundle provides completeness estimates for the Q, X, XHat, and P layers of projectivization. A small truncation threshold controls the spectral error, and the resulting operators satisfy the required completeness relations.
--
--   Principal definitions:
--   - `spectralTruncationError_le_half`: bounds spectral truncation by one half under a quarter-error threshold.
--   - `spectralTruncationError_le_zetaQuarterRoot`: bounds truncation by the fourth-root error scale.
--   - `qCompleteness`: states completeness of the Q layer.
--   - `one_sub_spectralTruncationError_smul_le_sqrt`: bounds the scaled truncation complement by a square-root estimate.
--   - `sqrtQCompleteness`: states completeness of the square-root Q construction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/QCompleteness.lean#L22-L407

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/QCompleteness.lean by skeleton subtraction.
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
# Section 5 — Q/X/XHat/P q-completeness

Completeness estimates for the rank-reduced `Q` family in the paper's
`Q/X/XHat/P` intermediate layer.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

/-- Under the small-error hypothesis `ζ ≤ 1/4`, the truncation error is at most `1/2`. -/
lemma spectralTruncationError_le_half (ζ : Error)
    (_hζ : 0 ≤ ζ) (hζq : ζ ≤ 1 / (4 : Error)) :
    spectralTruncationError ζ ≤ 1 / (2 : Error) := by
  -- Scalar bookkeeping for `ζ ≤ 1/4`: `√ζ ≤ 1/2`.
  have hquarter : Real.sqrt (1 / (4 : Error)) = 1 / (2 : Error) := by norm_num
  have hsqrt : Real.sqrt ζ ≤ 1 / (2 : Error) := by
    exact hquarter ▸ Real.sqrt_le_sqrt hζq
  simpa [spectralTruncationError, Real.sqrt_eq_rpow] using hsqrt

/-- Under the small-error hypothesis `ζ ≤ 1/4`, the spectral truncation error
is bounded by the fourth-root error scale used in the `Q/X/XHat/P` layer. -/
lemma spectralTruncationError_le_zetaQuarterRoot (ζ : Error)
    (hζ : 0 ≤ ζ) (hζq : ζ ≤ 1 / (4 : Error)) :
    spectralTruncationError ζ ≤ zetaQuarterRoot ζ := by
  have hζ1 : ζ ≤ 1 := by linarith
  dsimp [spectralTruncationError, zetaQuarterRoot]
  exact Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 (by positivity)
    (by norm_num : (1 : Error) / 2 ≥ 1 / 4)

/-- **Completeness of `Q`** (`lem:Q-completeness`).

If `Q_a` is the rank-reduced family from `lem:projective-low-rank-sum`, then
its total operator `Q` has expectation at least `1 - 11 ζ^(1/4)`. -/
lemma qCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ := by
  intro hRank
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  let qMass : Error := ev ψ (QTotal data)
  let overlap : Error := ∑ a : Outcome, ev ψ (A.outcome a * Qa data a)
  have hsdd :
      qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) data.q ≤
        roundingToProjectiveError ζ := by
    simpa [SDDOpRel, sddErrorOp, avgOver, uniformDistribution, constOpFamily, qSDDOp]
      using hRank.closeness.squaredDistanceBound
  have hdiagA_nonneg : 0 ≤ diagA := by
    unfold diagA
    exact Finset.sum_nonneg fun a _ => by
      simpa [Measurement.outcome_hermitian] using ev_adjoint_self_nonneg ψ (A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using
      MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ A.toSubMeas
  have hsqrt_diagA_le_one : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have hdiagA_lb : 1 - 2 * ζ ≤ diagA := by
    have hsource := hRank.source_almost_projective
    have hsum :
        ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) = 1 - diagA := by
      calc
        ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
            = ∑ a, (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                exact ev_sub ψ (A.outcome a) (A.outcome a * A.outcome a)
        _ = (∑ a, ev ψ (A.outcome a)) - ∑ a, ev ψ (A.outcome a * A.outcome a) := by
              rw [Finset.sum_sub_distrib]
        _ = 1 - diagA := by
              rw [← ev_sum ψ A.outcome, A.sum_eq]
              simp [diagA, ev_one_of_isNormalized ψ hψ]
    linarith [hsource, hsum]
  have hqtotal_nonneg : 0 ≤ QTotal data := by
    rw [← hRank.sum_eq_total]
    exact Finset.sum_nonneg fun a _ => hRank.outcome_nonneg a
  have hq_nonneg : 0 ≤ qMass := by
    exact ev_nonneg_of_psd ψ (QTotal data) hqtotal_nonneg
  have hdiagQ_eq :
      ∑ a : Outcome, ev ψ (Qa data a * Qa data a) = qMass := by
    calc
      ∑ a : Outcome, ev ψ (Qa data a * Qa data a)
          = ∑ a : Outcome, ev ψ (Qa data a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [(hRank.projective a).isIdempotentElem.eq]
      _ = ev ψ (QTotal data) := by
            rw [← ev_sum ψ (Qa data), hRank.sum_eq_total]
  have hoverlap_le : overlap ≤ Real.sqrt diagA * Real.sqrt qMass := by
    have hoverlap_abs :
        |overlap| ≤ Real.sqrt diagA * Real.sqrt qMass := by
      calc
        |overlap|
            = |∑ a : Outcome, ev ψ (A.outcome a * Qa data a)| := by
                simp [overlap]
        _ ≤ ∑ a : Outcome, |ev ψ (A.outcome a * Qa data a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : Outcome,
              Real.sqrt (ev ψ (A.outcome a * A.outcome a)) *
                Real.sqrt (ev ψ (Qa data a * Qa data a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              simpa [Measurement.outcome_hermitian,
                (hRank.projective a).isSelfAdjoint.isHermitian.eq] using
                ev_abs_mul_le_sqrt ψ (A.outcome a) (Qa data a)
        _ ≤ Real.sqrt diagA *
              Real.sqrt (∑ a : Outcome, ev ψ (Qa data a * Qa data a)) := by
              simpa [diagA] using
                Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                  (f := fun a => ev ψ (A.outcome a * A.outcome a))
                  (g := fun a => ev ψ (Qa data a * Qa data a))
                  (fun a => by
                    simpa [Measurement.outcome_hermitian] using
                      ev_adjoint_self_nonneg ψ (A.outcome a))
                  (fun a => by
                    simpa [(hRank.projective a).isSelfAdjoint.isHermitian.eq] using
                      ev_adjoint_self_nonneg ψ (Qa data a))
        _ = Real.sqrt diagA * Real.sqrt qMass := by rw [hdiagQ_eq]
    exact (abs_le.mp hoverlap_abs).2
  have h_expand :
      qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) data.q =
        diagA + qMass - 2 * overlap := by
    unfold qSDDOp qSDDCore
    calc
      ∑ a, ev ψ ((A.outcome a - Qa data a)ᴴ * (A.outcome a - Qa data a))
        = ∑ a, (ev ψ (A.outcome a * A.outcome a) +
            ev ψ (Qa data a * Qa data a) -
            2 * ev ψ (A.outcome a * Qa data a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hcomm :
                  ev ψ (Qa data a * A.outcome a) =
                    ev ψ (A.outcome a * Qa data a) := by
                exact ev_mul_comm_of_psd ψ _ _ (hRank.outcome_nonneg a) (A.outcome_pos a)
              calc
                ev ψ ((A.outcome a - Qa data a)ᴴ * (A.outcome a - Qa data a))
                    = ev ψ ((A.outcome a * A.outcome a -
                        A.outcome a * Qa data a) -
                        (Qa data a * A.outcome a -
                          Qa data a * Qa data a)) := by
                          congr 1
                          simp [sub_mul, mul_sub, Measurement.outcome_hermitian,
                            (hRank.projective a).isSelfAdjoint.isHermitian.eq]
                          abel
                _ = ev ψ (A.outcome a * A.outcome a) -
                      ev ψ (A.outcome a * Qa data a) -
                      (ev ψ (Qa data a * A.outcome a) -
                        ev ψ (Qa data a * Qa data a)) := by
                        rw [ev_sub, ev_sub, ev_sub]
                _ = ev ψ (A.outcome a * A.outcome a) +
                      ev ψ (Qa data a * Qa data a) -
                      2 * ev ψ (A.outcome a * Qa data a) := by
                        rw [hcomm]
                        ring
      _ = (∑ a, ev ψ (A.outcome a * A.outcome a)) +
            (∑ a, ev ψ (Qa data a * Qa data a)) -
            2 * ∑ a, ev ψ (A.outcome a * Qa data a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = diagA + qMass - 2 * overlap := by
            simp [diagA, overlap, hdiagQ_eq]
  have hsq_gap :
      (Real.sqrt qMass - Real.sqrt diagA) ^ (2 : Nat) ≤
        roundingToProjectiveError ζ := by
    calc
      (Real.sqrt qMass - Real.sqrt diagA) ^ (2 : Nat)
          = qMass + diagA - 2 * (Real.sqrt diagA * Real.sqrt qMass) := by
              nlinarith [Real.sq_sqrt hq_nonneg, Real.sq_sqrt hdiagA_nonneg]
      _ ≤ qMass + diagA - 2 * overlap := by
            nlinarith [hoverlap_le]
      _ = qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι) data.q := by
            rw [h_expand]
            ring
      _ ≤ roundingToProjectiveError ζ := hsdd
  have hround_nonneg : 0 ≤ roundingToProjectiveError ζ := by
    dsimp [roundingToProjectiveError]
    exact mul_nonneg (by norm_num) (spectralTruncationError_nonneg hζ)
  have habs :
      |Real.sqrt qMass - Real.sqrt diagA| ≤ Real.sqrt (roundingToProjectiveError ζ) := by
    refine abs_le_of_sq_le_sq' ?_ (Real.sqrt_nonneg _) |>.2
    calc
      |Real.sqrt qMass - Real.sqrt diagA| ^ 2
          = (Real.sqrt qMass - Real.sqrt diagA) ^ (2 : Nat) := by
              rw [sq_abs]
      _ ≤ roundingToProjectiveError ζ := hsq_gap
      _ = (Real.sqrt (roundingToProjectiveError ζ)) ^ (2 : Nat) := by
            calc
              roundingToProjectiveError ζ
                  = Real.sqrt (roundingToProjectiveError ζ) *
                      Real.sqrt (roundingToProjectiveError ζ) := by
                        nlinarith [Real.sq_sqrt hround_nonneg]
              _ = (Real.sqrt (roundingToProjectiveError ζ)) ^ (2 : Nat) := by
                    simp [pow_two]
  have hsqrt_q_lb :
      Real.sqrt qMass ≥ Real.sqrt diagA - Real.sqrt (roundingToProjectiveError ζ) := by
    have hleft := (abs_le.mp habs).1
    linarith
  have hq_lb :
      qMass ≥ diagA - 2 * Real.sqrt (roundingToProjectiveError ζ) := by
    let s : Error := Real.sqrt (roundingToProjectiveError ζ)
    let x : Error := Real.sqrt qMass
    let y : Error := Real.sqrt diagA
    have hxy : x ≥ y - s := by
      dsimp [x, y, s]
      exact hsqrt_q_lb
    by_cases hys : y ≤ s
    · have htarget : diagA - 2 * Real.sqrt (roundingToProjectiveError ζ) ≤ 0 := by
        dsimp [y, s] at hys ⊢
        nlinarith [Real.sq_sqrt hdiagA_nonneg,
          Real.sqrt_nonneg diagA,
          Real.sqrt_nonneg (roundingToProjectiveError ζ),
          mul_nonneg (sub_nonneg.mpr hsqrt_diagA_le_one)
            (Real.sqrt_nonneg diagA)]
      linarith
    · have hs_le_y : s ≤ y := le_of_not_ge hys
      have hy_sub_nonneg : 0 ≤ y - s := by linarith
      have hx_sq_ge : x ^ (2 : Nat) ≥ (y - s) ^ (2 : Nat) := by
        nlinarith
      have hx_sq_ge' :
          qMass ≥ diagA -
            2 * Real.sqrt diagA * Real.sqrt (roundingToProjectiveError ζ) +
            roundingToProjectiveError ζ := by
        dsimp [x, y, s] at hx_sq_ge
        nlinarith [hx_sq_ge, Real.sq_sqrt hq_nonneg, Real.sq_sqrt hdiagA_nonneg,
          Real.sq_sqrt hround_nonneg]
      have hcross :
          2 * Real.sqrt diagA * Real.sqrt (roundingToProjectiveError ζ) ≤
            2 * Real.sqrt (roundingToProjectiveError ζ) := by
        have hmul :
            Real.sqrt diagA * Real.sqrt (roundingToProjectiveError ζ) ≤
              1 * Real.sqrt (roundingToProjectiveError ζ) := by
          exact mul_le_mul_of_nonneg_right hsqrt_diagA_le_one (Real.sqrt_nonneg _)
        nlinarith
      linarith [hx_sq_ge', hcross, hround_nonneg]
  have hzeta_term :
      2 * ζ ≤ 2 * zetaQuarterRoot ζ := by
    gcongr
    have hζ1 : ζ ≤ 1 := by linarith
    dsimp [zetaQuarterRoot]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 (by positivity)
        (by norm_num : (1 : Error) ≥ 1 / 4))
  have hround_term :
      2 * Real.sqrt (roundingToProjectiveError ζ) ≤ 8 * zetaQuarterRoot ζ := by
    have hsqrt_rpow :
        Real.sqrt (ζ ^ (1 / (2 : Error))) = zetaQuarterRoot ζ := by
      rw [Real.sqrt_eq_rpow, zetaQuarterRoot, ← Real.rpow_mul hζ]
      congr 1
      ring
    have hsqrt_eq :
        Real.sqrt (roundingToProjectiveError ζ) =
          Real.sqrt (12 : Error) * zetaQuarterRoot ζ := by
      dsimp [roundingToProjectiveError, spectralTruncationError]
      rw [Real.sqrt_mul (by positivity), hsqrt_rpow]
    have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := zetaQuarterRoot_nonneg hζ
    have hsqrt : Real.sqrt (12 : Error) ≤ 4 := by
      have hsq : (Real.sqrt (12 : Error)) ^ 2 ≤ (4 : Error) ^ 2 := by norm_num
      nlinarith [Real.sq_sqrt (show 0 ≤ (12 : Error) by positivity), hsq]
    have hsqrt_bound : Real.sqrt (roundingToProjectiveError ζ) ≤ 4 * zetaQuarterRoot ζ := by
      rw [hsqrt_eq]
      exact mul_le_mul_of_nonneg_right hsqrt hzqr_nonneg
    nlinarith
  calc
    ev ψ (QTotal data) = qMass := rfl
    _ ≥ diagA - 2 * Real.sqrt (roundingToProjectiveError ζ) := hq_lb
    _ ≥ (1 - 2 * ζ) - 2 * Real.sqrt (roundingToProjectiveError ζ) := by
          gcongr
    _ ≥ (1 - 2 * zetaQuarterRoot ζ) - 8 * zetaQuarterRoot ζ := by
          linarith
    _ = 1 - 10 * zetaQuarterRoot ζ := by ring
    _ ≥ 1 - 11 * zetaQuarterRoot ζ := by
          have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := by
            dsimp [zetaQuarterRoot]
            exact Real.rpow_nonneg hζ _
          linarith

private lemma one_sub_spectralTruncationError_smul_le_sqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : MIPStarRE.Quantum.Op ι) (ζ : Error)
    (hQ_nonneg : 0 ≤ Q)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error))
    (hQ_le : Q ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
        (1 : MIPStarRE.Quantum.Op ι)) :
    (((1 : Error) - spectralTruncationError ζ) : ℂ) • Q ≤ CFC.sqrt Q := by
  let ε : Error := spectralTruncationError ζ
  have hε_nonneg : 0 ≤ ε := by
    simpa [ε] using spectralTruncationError_nonneg hζ
  have hε_half : ε ≤ 1 / (2 : Error) :=
    spectralTruncationError_le_half ζ hζ hζ_small
  let c : NNReal := ⟨1 - ε, by linarith⟩
  let b : NNReal := ⟨1 + 2 * ε, by positivity⟩
  have hspec_le : ∀ x, x ∈ spectrum NNReal Q → x ≤ b := by
    have hle : Q ≤ (algebraMap NNReal (MIPStarRE.Quantum.Op ι)) b := by
      rw [Algebra.algebraMap_eq_smul_one]
      have hb_real : (b : Error) = 1 + 2 * ε := by
        exact NNReal.coe_mk (1 + 2 * ε) (by positivity)
      change Q ≤ (((b : Error) : ℂ) • (1 : MIPStarRE.Quantum.Op ι))
      rw [hb_real]
      simpa [ε] using hQ_le
    rw [← cfc_id' NNReal Q (ha := hQ_nonneg),
      ← cfc_const (R := NNReal) b Q (ha := hQ_nonneg),
      cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg hQ_nonneg)
        (ha := hQ_nonneg)] at hle
    exact hle
  have hc_cast : (c : ℂ) = (((1 : Error) - ε) : ℂ) := by
    have hc_real : (c : Error) = 1 - ε := by
      exact NNReal.coe_mk (1 - ε) (by linarith)
    simpa using congrArg (fun r : Error => (r : ℂ)) hc_real
  rw [← hc_cast]
  change c • Q ≤ CFC.sqrt Q
  rw [CFC.sqrt_eq_cfc]
  rw [← cfc_const_mul_id (R := NNReal) c Q (ha := hQ_nonneg)]
  rw [cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg hQ_nonneg)
    (ha := hQ_nonneg)]
  intro x hx
  have hxb : (x : Error) ≤ 1 + 2 * ε := by
    have := hspec_le x hx
    exact_mod_cast this
  have hx_nonneg : 0 ≤ (x : Error) := by exact_mod_cast x.2
  have hsq :
      ((c : Error) * (x : Error)) ^ (2 : Nat) ≤
        (Real.sqrt (x : Error)) ^ (2 : Nat) := by
    rw [Real.sq_sqrt hx_nonneg]
    have hc_val : (c : Error) = 1 - ε := rfl
    rw [hc_val]
    have hx_sq_le :
        (x : Error) ^ (2 : Nat) ≤ (1 + 2 * ε) * (x : Error) := by
      nlinarith [mul_le_mul_of_nonneg_right hxb hx_nonneg]
    have hcoeff : (1 - ε) ^ (2 : Nat) * (1 + 2 * ε) ≤ 1 := by
      nlinarith [sq_nonneg ε, hε_nonneg, hε_half]
    have hmain :
        (1 - ε) ^ (2 : Nat) * ((x : Error) ^ (2 : Nat)) ≤ (x : Error) := by
      nlinarith [mul_le_mul_of_nonneg_left hx_sq_le (sq_nonneg (1 - ε)),
        mul_le_mul_of_nonneg_right hcoeff hx_nonneg]
    nlinarith
  have hreal : (c : Error) * (x : Error) ≤ Real.sqrt (x : Error) := by
    exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
  exact NNReal.coe_le_coe.mp (by simpa [NNReal.coe_mul] using hreal)

/-- **Completeness of `sqrt Q`** (`lem:sqrt-Q-completeness`).

The square root of the total operator `Q` remains almost complete on `ψ`. -/
lemma sqrtQCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      ev ψ (CFC.sqrt (QTotal data)) ≥ 1 - 12 * zetaQuarterRoot ζ := by
  intro hRank
  let ε : Error := spectralTruncationError ζ
  have hε_nonneg : 0 ≤ ε := by
    simpa [ε] using spectralTruncationError_nonneg hζ
  have hε_half : ε ≤ 1 / (2 : Error) :=
    spectralTruncationError_le_half ζ hζ hζ_small
  have hqtotal_nonneg : 0 ≤ QTotal data := by
    rw [← hRank.sum_eq_total]
    exact Finset.sum_nonneg fun a _ => hRank.outcome_nonneg a
  have hsqrt_lower :
      (((1 : Error) - ε) : ℂ) • QTotal data ≤ CFC.sqrt (QTotal data) := by
    simpa [ε] using
      one_sub_spectralTruncationError_smul_le_sqrt
        (QTotal data) ζ hqtotal_nonneg hζ hζ_small hRank.total_le
  have hev_lower :
      (1 - ε) * ev ψ (QTotal data) ≤ ev ψ (CFC.sqrt (QTotal data)) := by
    calc
      (1 - ε) * ev ψ (QTotal data)
          = ev ψ ((((1 : Error) - ε) : ℂ) • QTotal data) := by
              simpa [Complex.ofReal_sub] using
                (ev_scale ψ (1 - ε) (QTotal data)).symm
      _ ≤ ev ψ (CFC.sqrt (QTotal data)) := ev_mono ψ _ _ hsqrt_lower
  have hq_complete :
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ :=
    qCompleteness ψ A ζ data hψ hζ hζ_small hRank
  have hε_le_zqr : ε ≤ zetaQuarterRoot ζ := by
    simpa [ε] using spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := zetaQuarterRoot_nonneg hζ
  have hscaled :
      (1 - ε) * (1 - 11 * zetaQuarterRoot ζ) ≤
        (1 - ε) * ev ψ (QTotal data) := by
    exact mul_le_mul_of_nonneg_left hq_complete (by nlinarith)
  calc
    ev ψ (CFC.sqrt (QTotal data))
        ≥ (1 - ε) * ev ψ (QTotal data) := hev_lower
    _ ≥ (1 - ε) * (1 - 11 * zetaQuarterRoot ζ) := hscaled
    _ ≥ 1 - 12 * zetaQuarterRoot ζ := by
          nlinarith [hε_le_zqr, hε_nonneg, hzqr_nonneg]


end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


