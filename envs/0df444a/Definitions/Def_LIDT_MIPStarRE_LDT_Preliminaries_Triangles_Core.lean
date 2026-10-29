-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:47:39.835071+00:00
-- url     : https://prove2.me/theorems/f7279587-52df-4a72-8910-913249d24876
-- title:
--   LIDT definitions: LDT / Preliminaries / Triangles / Core
-- statement:
--   This bundle supplies atomic distance and averaging inequalities used to combine local consistency estimates. It gives symmetry, max-zero control, square-root averaging, a right-match estimate, and a right-register substitution bound for submeasurements.
--
--   Principal definitions:
--   - `qSDD_symm`: symmetry of question-level state-dependent distance.
--   - `sddRel_symm`: symmetry of the state-dependent distance relation.
--   - `max_zero_add_le`: the bound obtained when a scalar is added inside `max 0`.
--   - `avgOver_abs_le_sqrt_of_pointwise_nonneg`: an average absolute-value bound from pointwise square-root bounds and nonnegativity.
--   - `right_match_gap_abs_le_sqrt_qSDD`: the right-match gap bounded by the square root of question-level distance.
--   - `triangleSub_right_subMeas_totalGap`: the right-register substitution estimate with the total-overlap displacement made explicit.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/Triangles/Core.lean#L21-L815

-- Generated from MIPStarRE/LDT/Preliminaries/Triangles/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Triangle Inequalities for State-Dependent Distance: Core

This module contains the main triangle-substitution estimates for approximate
measurements.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Symmetry of the question-level state-dependent distance. -/
lemma qSDD_symm
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qSDD ψ A B = qSDD ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDD qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change
    ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

/-- Symmetry of the state-dependent distance relation. -/
lemma sddRel_symm
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 A B δ →
      SDDRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddError, qSDD_symm] using h





/-! ### Elementary max bound -/

/-- Adding `y` inside `max 0` changes the value by at most `|y|`. -/
lemma max_zero_add_le (x y : Error) :
    max 0 (x + y) ≤ max 0 x + |y| := by
  by_cases hxy : x + y < 0
  · rw [max_eq_left_of_lt hxy]
    positivity
  · have hxy' : 0 ≤ x + y := le_of_not_gt hxy
    rw [max_eq_right hxy']
    have hx : x ≤ max 0 x := le_max_right _ _
    have hy : y ≤ |y| := le_abs_self y
    linarith

 lemma avgOver_abs_le_sqrt_of_pointwise_nonneg
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (f g : Question → Error)
    (hfg : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q) :
    avgOver 𝒟 (fun q => |f q|) ≤ Real.sqrt (avgOver 𝒟 g) := by
  have havg_nonneg : 0 ≤ avgOver 𝒟 (fun q => |f q|) :=
    avgOver_nonneg 𝒟 (fun q => |f q|) (fun q => abs_nonneg (f q))
  have havg_abs :
      |avgOver 𝒟 (fun q => |f q|)| ≤ Real.sqrt (avgOver 𝒟 g) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => |f q|)
        g
        (fun q => by
          simpa [abs_of_nonneg (abs_nonneg (f q))] using hfg q)
        hg
        h𝒟
  simpa [abs_of_nonneg havg_nonneg] using havg_abs





/-! ### Right-register variant of `triangleSub` -/

 lemma right_match_gap_abs_le_sqrt_qSDD
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B D : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * D.outcome a)| ≤
      Real.sqrt (qSDD ψ B D) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))| ≤
        Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := by
    calc
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))|
        ≤ Real.sqrt
            (∑ a : Outcome, ev ψ (A.outcome a * (A.outcome a)ᴴ)) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ ((B.outcome a - D.outcome a)ᴴ *
                  (B.outcome a - D.outcome a))) := by
              simpa using
                sum_ev_mul_le_sqrt ψ
                  (fun a => A.outcome a)
                  (fun a => B.outcome a - D.outcome a)
      _ = Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := by
            simp [diagA, qSDD, qSDDCore, SubMeas.outcome_hermitian]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))| ≤
        Real.sqrt (qSDD ψ B D) := by
    calc
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))|
        ≤ Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := haux
      _ ≤ 1 * Real.sqrt (qSDD ψ B D) := by
            exact mul_le_mul_of_nonneg_right hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ B D) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    (∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * D.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (A.outcome a * D.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [(ev_sub ψ (A.outcome a * B.outcome a)
            (A.outcome a * D.outcome a)).symm]
          simp [mul_sub]





/-- Right-register substitution for submeasurements, with the total-overlap
displacement stated explicitly.

For complete right-register measurements the total-overlap term
`ev ψ (A_total ⊗ B_total)` is independent of the right family.  For general
submeasurements this term may change.  The lemma therefore separates the usual
state-dependent-distance contribution from the averaged displacement of the
right total operator. -/
theorem triangleSub_right_subMeas_totalGap
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B D : IdxSubMeas Question Outcome ι) (δ ε η : Error)
    (hAB : ConsRel ψ 𝒟 A B δ)
    (hBD : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight B)
      (IdxSubMeas.liftRight D) ε)
    (hTotal :
      avgOver 𝒟 (fun q =>
        |ev ψ (leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((D q).total)) -
          ev ψ (leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((B q).total))|) ≤ η) :
    ConsRel ψ 𝒟 A D (δ + Real.sqrt ε + η) := by
  let AL : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftLeft A
  let BR : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftRight B
  let DR : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftRight D
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
  let totalB : Question → Error := fun q =>
    ev ψ ((AL q).total * (BR q).total)
  let totalD : Question → Error := fun q =>
    ev ψ ((AL q).total * (DR q).total)
  let sdd : Question → Error := fun q =>
    qSDD ψ (BR q) (DR q)
  let matchGap : Question → Error := fun q => matchB q - matchD q
  let totalGap : Question → Error := fun q => totalD q - totalB q
  rcases hAB with ⟨hAB⟩
  rw [bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hmatchGap_pointwise : ∀ q, |matchGap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [matchGap, matchB, matchD, sdd] using
      right_match_gap_abs_le_sqrt_qSDD ψ hψ (AL q) (BR q) (DR q)
  have hmatchGap_avg_abs :
      avgOver 𝒟 (fun q => |matchGap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 matchGap sdd
        hmatchGap_pointwise
        (fun q => qSDD_nonneg ψ (BR q) (DR q))
  have htotalGap_avg_abs :
      avgOver 𝒟 (fun q => |totalGap q|) ≤ η := by
    simpa [totalGap, totalD, totalB, AL, BR, DR, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight] using hTotal
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (AL q) (DR q) ≤
        qConsDefect ψ (AL q) (BR q) + |matchGap q| + |totalGap q| := by
    intro q
    have hdefB :
        qConsDefect ψ (AL q) (BR q) = max 0 (totalB q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [totalB, matchB]
    have hdefD :
        qConsDefect ψ (AL q) (DR q) = max 0 (totalD q - matchD q) := by
      unfold qConsDefect qMatchMass
      dsimp [totalD, matchD]
    calc
      qConsDefect ψ (AL q) (DR q)
        = max 0 (((totalB q - matchB q) + matchGap q) + totalGap q) := by
            rw [hdefD]
            dsimp [matchGap, totalGap]
            ring_nf
      _ ≤ max 0 ((totalB q - matchB q) + matchGap q) + |totalGap q| := by
            exact max_zero_add_le _ _
      _ ≤ (max 0 (totalB q - matchB q) + |matchGap q|) + |totalGap q| := by
            linarith [max_zero_add_le (totalB q - matchB q) (matchGap q)]
      _ = qConsDefect ψ (AL q) (BR q) + |matchGap q| + |totalGap q| := by
            rw [hdefB]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (DR q))
      ≤ avgOver 𝒟
          (fun q => qConsDefect ψ (AL q) (BR q) + |matchGap q| + |totalGap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = (avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q)) +
          avgOver 𝒟 (fun q => |matchGap q|)) +
          avgOver 𝒟 (fun q => |totalGap q|) := by
            rw [avgOver_add, avgOver_add]
    _ ≤ (δ + Real.sqrt (avgOver 𝒟 sdd)) + η := by
          exact add_le_add (add_le_add hAB hmatchGap_avg_abs) htotalGap_avg_abs
    _ ≤ (δ + Real.sqrt ε) + η := by
          have hsqrt_sdd_le :
              Real.sqrt (avgOver 𝒟 sdd) ≤ Real.sqrt ε := by
            exact Real.sqrt_le_sqrt (by simpa [sdd, BR, DR] using hBD)
          linarith
    _ = δ + Real.sqrt ε + η := by ring




end MIPStarRE.LDT.Preliminaries

end

end LIDT


