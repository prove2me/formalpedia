-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:35:48.67699+00:00
-- url     : https://prove2.me/theorems/42aca3ef-cad1-4378-9096-a0f71a552162
-- title:
--   LIDT definitions: LDT / Preliminaries / ComparisonCore
-- statement:
--   This bundle collects the core monotonicity, consistency, postprocessing, and operator-order comparisons used by the preliminary lemmas. It converts consistency to squared distance, preserves or improves defects under postprocessing, and supplies the positive sandwich monotonicity needed for later estimates.
--
--   Principal definitions:
--   - `mono`: monotonicity of the consistency relation in its error parameter.
--   - `questionSDD_le_two_questionConsistency`: bounds squared distance by twice question consistency.
--   - `simeqToApprox`: converts symmetric closeness to the approximation relation.
--   - `ev_leftTensor_mul_rightTensor_nonneg`: records nonnegativity of the mixed tensor expectation.
--   - `qMatchMass_leftRight_postprocess_ge`: bounds match mass after left and right postprocessing.
--   - `qBipartiteSSCDefect_postprocess_le`: shows postprocessing does not increase bipartite SSC defect.
--   - `consRelDataProcessing_questionDependent`: gives question-dependent consistency data processing.
--   - `conjTranspose_mul_mono`: proves Loewner monotonicity under a conjugate-transpose sandwich.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean#L19-L660

-- Generated from MIPStarRE/LDT/Preliminaries/ComparisonCore.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
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

/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.ConsRel

/-- Monotonicity of `ConsRel` in the allowed error parameter. -/
lemma mono {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    {ψ : QuantumState (ιA × ιB)} {𝒟 : Distribution Question}
    {A : IdxSubMeas Question Outcome ιA}
    {B : IdxSubMeas Question Outcome ιB}
    {δ δ' : Error} (hδ : δ ≤ δ') :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟 A B δ →
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟 A B δ' := by
  intro h
  exact ⟨le_trans h.offDiagonalBound hδ⟩

end MIPStarRE.LDT.ConsRel

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT





/-- Atomic mathematical fact: for a full measurement, the squared-distance defect
is at most `2 * qConsDefect`. -/
 lemma questionSDD_le_two_questionConsistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : Measurement Outcome ι) :
    qSDD ψ A.toSubMeas B.toSubMeas ≤
      2 * qConsDefect ψ A.toSubMeas B.toSubMeas := by
  have hA_sq_sum_le : ∑ a, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ 1 := by
    calc
      ∑ a, ev ψ (A.outcome a * A.outcome a)
        ≤ ∑ a, ev ψ (A.outcome a) := by
            exact Finset.sum_le_sum fun a _ =>
              ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (A.outcome_pos a)
                  (Measurement.outcome_le_one A a)
      _ = ev ψ 1 := by
            rw [← ev_sum ψ A.outcome, A.sum_eq]
  have hB_sq_sum_le : ∑ a, ev ψ (B.outcome a * B.outcome a) ≤ ev ψ 1 := by
    calc
      ∑ a, ev ψ (B.outcome a * B.outcome a)
        ≤ ∑ a, ev ψ (B.outcome a) := by
            exact Finset.sum_le_sum fun a _ =>
              ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (B.outcome_pos a)
                  (Measurement.outcome_le_one B a)
      _ = ev ψ 1 := by
            rw [← ev_sum ψ B.outcome, B.sum_eq]
  have h_expand : ∀ a,
      ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)) =
        ev ψ (A.outcome a * A.outcome a) +
          ev ψ (B.outcome a * B.outcome a) -
          2 * ev ψ (A.outcome a * B.outcome a) := by
    intro a
    have hcomm :
        ev ψ (B.outcome a * A.outcome a) =
          ev ψ (A.outcome a * B.outcome a) :=
      ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
    calc
      ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
        = ev ψ ((A.outcome a * A.outcome a - A.outcome a * B.outcome a) -
            (B.outcome a * A.outcome a - B.outcome a * B.outcome a)) := by
              congr 1
              simp [sub_mul, mul_sub, Measurement.outcome_hermitian]
              abel
      _ = ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a) -
            (ev ψ (B.outcome a * A.outcome a) -
              ev ψ (B.outcome a * B.outcome a)) := by
              rw [ev_sub, ev_sub, ev_sub]
      _ = ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a) := by
              rw [hcomm]
              ring
  have hbound :
      qSDD ψ A.toSubMeas B.toSubMeas ≤
        2 * (ev ψ (A.total * B.total) -
          qMatchMass ψ A.toSubMeas B.toSubMeas) := by
    unfold qSDD qSDDCore qMatchMass
    calc
      ∑ a, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
        = ∑ a, (ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact h_expand a
      _ = (∑ a, ev ψ (A.outcome a * A.outcome a)) +
            (∑ a, ev ψ (B.outcome a * B.outcome a)) -
            2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ev ψ 1 + ev ψ 1 - 2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
              linarith
      _ = 2 * (ev ψ (A.total * B.total) -
            ∑ a, ev ψ (A.outcome a * B.outcome a)) := by
              simp [A.total_eq_one, B.total_eq_one]
              ring
  have hinner_nonneg :
      0 ≤ ev ψ (A.total * B.total) -
        qMatchMass ψ A.toSubMeas B.toSubMeas := by
    have hnonneg := qSDD_nonneg ψ A.toSubMeas B.toSubMeas
    linarith
  unfold qConsDefect
  rw [max_eq_right hinner_nonneg]
  exact hbound

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) :
    ConsRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      BipartiteSDDRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
        (2 * δ) := by
  intro ⟨hcons⟩
  rw [bipartiteConsError_eq_consError_placed] at hcons
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDD ψ
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
      ≤ avgOver 𝒟
          (fun q =>
            2 * qConsDefect ψ
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let A' : Measurement Outcome (ι × ι) :=
            leftLiftedMeasurement (ιB := ι) (A q)
          let B' : Measurement Outcome (ι × ι) :=
            rightLiftedMeasurement (ιA := ι) (B q)
          simpa [A', B', leftLiftedMeasurement, rightLiftedMeasurement,
            IdxSubMeas.liftLeft, IdxSubMeas.liftRight, SubMeas.liftLeft, SubMeas.liftRight,
            leftPlacedSubMeas, rightPlacedSubMeas, IdxMeas.toIdxSubMeas] using
            questionSDD_le_two_questionConsistency ψ A' B'
    _ = 2 * avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          rw [avgOver_const_mul]
    _ ≤ 2 * δ := by
          exact mul_le_mul_of_nonneg_left hcons (by norm_num)



lemma ev_leftTensor_mul_rightTensor_nonneg
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    {X : MIPStarRE.Quantum.Op ιA} {Y : MIPStarRE.Quantum.Op ιB}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ ev ψ (leftTensor (ι₂ := ιB) X * rightTensor (ι₁ := ιA) Y) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact _root_.LIDT.MIPStarRE.LDT.ev_nonneg_of_psd ψ (_root_.LIDT.MIPStarRE.LDT.opTensor X Y) (_root_.LIDT.MIPStarRE.LDT.opTensor_nonneg hX hY)

lemma qMatchMass_leftRight_postprocess_ge {α β : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qMatchMass ψ
        (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
        (rightPlacedSubMeas (ιA := ιA) (postprocess B f)) ≥
      qMatchMass ψ
        (leftPlacedSubMeas (ιB := ιB) A)
        (rightPlacedSubMeas (ιA := ιA) B) := by
  classical
  let fiber : β → Finset α := fun b => Finset.univ.filter fun a => f a = b
  let diagTerm : α → Error := fun a =>
    ev ψ
      (leftTensor (ι₂ := ιB) (A.outcome a) *
        rightTensor (ι₁ := ιA) (B.outcome a))
  let pairTerm : α → α → Error := fun a a' =>
    ev ψ
      (leftTensor (ι₂ := ιB) (A.outcome a) *
        rightTensor (ι₁ := ιA) (B.outcome a'))
  let fiberDiag : β → Error := fun b => (fiber b).sum diagTerm
  let fiberPair : β → Error := fun b => (fiber b).sum fun a => (fiber b).sum fun a' => pairTerm a a'
  have hdiag_le (b : β) : fiberDiag b ≤ fiberPair b := by
    dsimp [fiberDiag, fiberPair]
    refine Finset.sum_le_sum ?_
    intro a ha
    exact Finset.single_le_sum
      (fun a' ha' =>
        ev_leftTensor_mul_rightTensor_nonneg ψ (A.outcome_pos a) (B.outcome_pos a'))
      ha
  have hfiber_expand (b : β) :
      ev ψ
        (((fiber b).sum fun a => leftTensor (ι₂ := ιB) (A.outcome a)) *
          ((fiber b).sum fun a => rightTensor (ι₁ := ιA) (B.outcome a))) =
      fiberPair b := by
    dsimp [fiberPair]
    rw [Matrix.sum_mul, ev_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Matrix.mul_sum, ev_finset_sum]
  calc
    qMatchMass ψ
        (leftPlacedSubMeas (ιB := ιB) A)
        (rightPlacedSubMeas (ιA := ιA) B)
      = ∑ b : β, fiberDiag b := by
          dsimp [fiberDiag, diagTerm, fiber]
          unfold qMatchMass leftPlacedSubMeas rightPlacedSubMeas
          symm
          exact Finset.sum_fiberwise Finset.univ f
            (fun a =>
              ev ψ
                (leftTensor (ι₂ := ιB) (A.outcome a) *
                  rightTensor (ι₁ := ιA) (B.outcome a)))
    _ ≤ ∑ b : β, fiberPair b := by
          refine Finset.sum_le_sum ?_
          intro b _
          exact hdiag_le b
    _ = qMatchMass ψ
          (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
          (rightPlacedSubMeas (ιA := ιA) (postprocess B f)) := by
          dsimp [fiberPair, pairTerm, fiber]
          unfold qMatchMass leftPlacedSubMeas rightPlacedSubMeas postprocess
          refine Finset.sum_congr rfl ?_
          intro b _
          symm
          calc
            ev ψ
                (leftTensor (ι₂ := ιB)
                    (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) *
                  rightTensor (ι₁ := ιA)
                    (∑ a ∈ Finset.univ.filter (fun a => f a = b), B.outcome a))
              =
                ev ψ
                  (((Finset.univ.filter (fun a => f a = b)).sum fun a =>
                      leftTensor (ι₂ := ιB) (A.outcome a)) *
                    ((Finset.univ.filter (fun a => f a = b)).sum fun a =>
                      rightTensor (ι₁ := ιA) (B.outcome a))) := by
                    rw [← leftTensor_finset_sum (ι₂ := ιB)
                      (Finset.univ.filter (fun a => f a = b)) (fun a => A.outcome a)]
                    rw [← rightTensor_finset_sum (ι₁ := ιA)
                      (Finset.univ.filter (fun a => f a = b)) (fun a => B.outcome a)]
            _ = fiberPair b := hfiber_expand b

/-- Postprocessing can only decrease the bipartite strong self-consistency
defect: the total mass is preserved while the diagonal overlap term can only
increase. -/
lemma qBipartiteSSCDefect_postprocess_le {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (M : SubMeas α ι) (f : α → β) :
    qBipartiteSSCDefect ψ (postprocess M f) ≤ qBipartiteSSCDefect ψ M := by
  have hmatch :
      qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) (postprocess M f))
          (rightPlacedSubMeas (ιA := ι) (postprocess M f)) ≥
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) M)
          (rightPlacedSubMeas (ιA := ι) M) :=
    qMatchMass_leftRight_postprocess_ge ψ M M f
  have hsub :
      ev ψ (leftTensor (ι₂ := ι) M.total) -
          qMatchMass ψ
            (leftPlacedSubMeas (ιB := ι) (postprocess M f))
            (rightPlacedSubMeas (ιA := ι) (postprocess M f))
        ≤
      ev ψ (leftTensor (ι₂ := ι) M.total) -
          qMatchMass ψ
            (leftPlacedSubMeas (ιB := ι) M)
            (rightPlacedSubMeas (ιA := ι) M) := by
    linarith
  have hmass_post :
      ev ψ (leftTensor (ι₂ := ι) (postprocess M f).total) =
        ev ψ (leftTensor (ι₂ := ι) M.total) := by
    simp [postprocess_total]
  have hmatch_post :
      qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) (postprocess M f))
          (rightPlacedSubMeas (ιA := ι) (postprocess M f)) =
        ∑ b : β,
          ev ψ
            (opTensor
              ((postprocess M f).outcome b)
              ((postprocess M f).outcome b)) := by
    simp [qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
      leftTensor_mul_rightTensor_eq_opTensor]
  have hmatch_orig :
      qMatchMass ψ
          (leftPlacedSubMeas (ιB := ι) M)
          (rightPlacedSubMeas (ιA := ι) M) =
        ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    simp [qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
      leftTensor_mul_rightTensor_eq_opTensor]
  have hsub' :
      ev ψ (leftTensor (ι₂ := ι) M.total) -
          ∑ b : β,
            ev ψ
              (opTensor
                ((postprocess M f).outcome b)
                ((postprocess M f).outcome b))
        ≤
      ev ψ (leftTensor (ι₂ := ι) M.total) -
          ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    rw [← hmatch_post, ← hmatch_orig]
    exact hsub
  change
      max 0
          (ev ψ (leftTensor (ι₂ := ι) (postprocess M f).total) -
            ∑ b : β,
              ev ψ
                (opTensor
                  ((postprocess M f).outcome b)
                  ((postprocess M f).outcome b)))
        ≤
      max 0
          (ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : α, ev ψ (opTensor (M.outcome a) (M.outcome a)))
  rw [hmass_post]
  exact max_le_max le_rfl hsub'

private lemma qConsDefect_leftRight_postprocess_le {α β : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qConsDefect ψ
        (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
        (rightPlacedSubMeas (ιA := ιA) (postprocess B f))
      ≤
    qConsDefect ψ
        (leftPlacedSubMeas (ιB := ιB) A)
        (rightPlacedSubMeas (ιA := ιA) B) := by
  have hmatch :=
    qMatchMass_leftRight_postprocess_ge ψ A B f
  have hsub :
      ev ψ
          ((leftPlacedSubMeas (ιB := ιB) A).total *
            (rightPlacedSubMeas (ιA := ιA) B).total) -
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
          (rightPlacedSubMeas (ιA := ιA) (postprocess B f))
      ≤
      ev ψ
          ((leftPlacedSubMeas (ιB := ιB) A).total *
            (rightPlacedSubMeas (ιA := ιA) B).total) -
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ιB) A)
          (rightPlacedSubMeas (ιA := ιA) B) := by
    linarith
  unfold qConsDefect
  have htotal :
      ev ψ
          ((leftPlacedSubMeas (ιB := ιB) (postprocess A f)).total *
            (rightPlacedSubMeas (ιA := ιA) (postprocess B f)).total) =
        ev ψ
          ((leftPlacedSubMeas (ιB := ιB) A).total *
            (rightPlacedSubMeas (ιA := ιA) B).total) := by
    simp [leftPlacedSubMeas, rightPlacedSubMeas, postprocess_total]
  rw [htotal]
  exact max_le_max le_rfl hsub





/-- Question-dependent postprocessing preserves bipartite consistency. -/
theorem consRelDataProcessing_questionDependent {Question α β : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question α ιA) (B : IdxSubMeas Question α ιB) (δ : Error)
    (f : Question → α → β) :
    ConsRel ψ 𝒟 A B δ →
      ConsRel ψ 𝒟
        (fun q => postprocess (A q) (f q))
        (fun q => postprocess (B q) (f q)) δ := by
  intro ⟨hcons⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed] at hcons ⊢
  unfold consError at *
  calc
    avgOver 𝒟
        (fun q =>
          qConsDefect ψ
            (leftPlacedSubMeas (ιB := ιB) (postprocess (A q) (f q)))
            (rightPlacedSubMeas (ιA := ιA) (postprocess (B q) (f q))))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              (leftPlacedSubMeas (ιB := ιB) (A q))
              (rightPlacedSubMeas (ιA := ιA) (B q))) := by
          apply avgOver_mono
          intro q
          exact qConsDefect_leftRight_postprocess_le ψ (A q) (B q) (f q)
    _ ≤ δ := hcons







/-- Loewner-order monotonicity of the matrix sandwich `Zᴴ * X * Z`.
If `X ≤ Y` then `Zᴴ * X * Z ≤ Zᴴ * Y * Z`. -/
lemma conjTranspose_mul_mono
    {ι : Type*} [Fintype ι]
    {X Y Z : MIPStarRE.Quantum.Op ι}
    (hXY : X ≤ Y) :
    Zᴴ * X * Z ≤ Zᴴ * Y * Z := by
  apply sub_nonneg.mp
  have hnonneg : 0 ≤ Zᴴ * (Y - X) * Z := by
    simpa [Matrix.star_eq_conjTranspose] using
      star_left_conjugate_nonneg (sub_nonneg.mpr hXY) Z
  simpa [mul_sub, sub_mul, Matrix.conjTranspose_conjTranspose, mul_assoc] using hnonneg


end MIPStarRE.LDT.Preliminaries

end

end LIDT


