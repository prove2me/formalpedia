-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:37:36.541545+00:00
-- url     : https://prove2.me/theorems/bdd1d0af-6374-427b-b5e7-a10a684369fa
-- title:
--   LIDT definitions: LDT / Preliminaries / DistanceBounds
-- statement:
--   This bundle provides triangle, monotonicity, and Cauchy-Schwarz interfaces for state-dependent distances. It includes question-level and operator-family relations together with the raw approximate-error estimate used by switch-sandwich arguments.
--
--   Principal definitions:
--   - `questionSDD_triangle`: gives the parallelogram-style triangle inequality for question distance.
--   - `questionSDD_triangle_three`: gives the three-step question-level triangle inequality.
--   - `stateDependentDistanceRel_triangle`: gives the relation-level state-dependent triangle inequality.
--   - `stateDependentDistanceRel_triangle_three`: gives the three-step relation-level triangle inequality.
--   - `stateDependentDistanceRel_mono`: proves monotonicity when the error parameter increases.
--   - `cabApproxDelta_raw`: supplies the raw Cauchy-Schwarz approximate-error estimate.
--   - `questionSDDOp_triangle`: gives the operator-family parallelogram inequality.
--   - `stateDependentDistanceOpRel_triangle`: gives the operator-family relation triangle inequality.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/DistanceBounds.lean#L21-L386

-- Generated from MIPStarRE/LDT/Preliminaries/DistanceBounds.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
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
# Preliminary comparison theorems: distance bounds

Triangle-inequality style bounds for `SDDRel` and `SDDOpRel`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Infrastructure: triangle inequality for `SDDRel` -/

/-- Atomic mathematical fact: the parallelogram-style inequality for `qSDD`. -/
lemma questionSDD_triangle {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B C : SubMeas Outcome ι) :
    qSDD ψ A C ≤
      2 * (qSDD ψ A B +
           qSDD ψ B C) := by
  let ev' (X Y : MIPStarRE.Quantum.Op ι) := ev ψ ((X - Y)ᴴ * (X - Y))
  have pointwise_outcome : ∀ a, ev' (A.outcome a) (C.outcome a) ≤
      2 * (ev' (A.outcome a) (B.outcome a) +
           ev' (B.outcome a) (C.outcome a)) :=
    fun a => ev_diff_triangle ψ _ _ _
  unfold qSDD qSDDCore
  have h1 : ∑ a : Outcome, ev' (A.outcome a) (C.outcome a) ≤
      ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                 ev' (B.outcome a) (C.outcome a))) :=
    Finset.sum_le_sum (fun a _ => pointwise_outcome a)
  have h2 : ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                        ev' (B.outcome a) (C.outcome a))) =
      2 * (∑ a : Outcome, ev' (A.outcome a) (B.outcome a) +
           ∑ a : Outcome, ev' (B.outcome a) (C.outcome a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

/-- Atomic mathematical fact: the three-step triangle inequality for `qSDD`.

This is the `k = 3` instance of `prop:triangle-inequality-for-approx_delta`,
with the sharp paper constant `3 * (δ₁ + δ₂ + δ₃)`. -/
lemma questionSDD_triangle_three {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B C D : SubMeas Outcome ι) :
    qSDD ψ A D ≤ 3 * (qSDD ψ A B + qSDD ψ B C + qSDD ψ C D) := by
  let ev' (X Y : MIPStarRE.Quantum.Op ι) := ev ψ ((X - Y)ᴴ * (X - Y))
  have pointwise_outcome : ∀ a, ev' (A.outcome a) (D.outcome a) ≤
      3 * (ev' (A.outcome a) (B.outcome a) +
        ev' (B.outcome a) (C.outcome a) +
        ev' (C.outcome a) (D.outcome a)) :=
    fun a => ev_diff_triangle_three ψ _ _ _ _
  unfold qSDD qSDDCore
  have h1 : ∑ a : Outcome, ev' (A.outcome a) (D.outcome a) ≤
      ∑ a : Outcome, 3 * (ev' (A.outcome a) (B.outcome a) +
        ev' (B.outcome a) (C.outcome a) +
        ev' (C.outcome a) (D.outcome a)) :=
    Finset.sum_le_sum (fun a _ => pointwise_outcome a)
  have h2 : ∑ a : Outcome, 3 * (ev' (A.outcome a) (B.outcome a) +
        ev' (B.outcome a) (C.outcome a) +
        ev' (C.outcome a) (D.outcome a)) =
      3 * (∑ a : Outcome, ev' (A.outcome a) (B.outcome a) +
        ∑ a : Outcome, ev' (B.outcome a) (C.outcome a) +
        ∑ a : Outcome, ev' (C.outcome a) (D.outcome a)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.mul_sum]
  exact le_trans h1 (le_of_eq h2)

/-- Triangle inequality for state-dependent distance. -/
lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
    SDDRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  unfold sddError at *
  calc avgOver 𝒟
        (fun q => qSDD ψ (A q) (C q))
      ≤ avgOver 𝒟
          (fun q => 2 * (qSDD ψ (A q) (B q) +
                         qSDD ψ (B q) (C q))) := by
        apply avgOver_mono
        intro q
        exact questionSDD_triangle ψ (A q) (B q) (C q)
    _ = 2 * avgOver 𝒟
          (fun q => qSDD ψ (A q) (B q) +
                     qSDD ψ (B q) (C q)) := by
        rw [avgOver_const_mul]
    _ = 2 * (avgOver 𝒟
              (fun q => qSDD ψ (A q) (B q)) +
             avgOver 𝒟
              (fun q => qSDD ψ (B q) (C q))) := by
        rw [avgOver_add]
    _ ≤ 2 * (δ₁ + δ₂) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add h₁ h₂

/-- Three-step triangle inequality for state-dependent distance. -/
lemma stateDependentDistanceRel_triangle_three {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C D : IdxSubMeas Question Outcome ι) (δ₁ δ₂ δ₃ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
    SDDRel ψ 𝒟 C D δ₃ →
    SDDRel ψ 𝒟 A D (3 * (δ₁ + δ₂ + δ₃)) := by
  intro hAB hBC hCD
  constructor
  calc
    sddError ψ 𝒟 A D
        = avgOver 𝒟 (fun q => qSDD ψ (A q) (D q)) := rfl
    _ ≤ avgOver 𝒟 (fun q =>
          3 * (qSDD ψ (A q) (B q) + qSDD ψ (B q) (C q) +
            qSDD ψ (C q) (D q))) := by
          apply avgOver_mono
          exact fun _ => questionSDD_triangle_three ψ _ _ _ _
    _ = 3 * (sddError ψ 𝒟 A B + sddError ψ 𝒟 B C +
          sddError ψ 𝒟 C D) := by
          simp [sddError, avgOver_const_mul, avgOver_add, add_assoc]
    _ ≤ 3 * (δ₁ + δ₂ + δ₃) := by
          have hAB' := hAB.squaredDistanceBound
          have hBC' := hBC.squaredDistanceBound
          have hCD' := hCD.squaredDistanceBound
          linarith

/-- Monotonicity: if `SDDRel` holds for `δ`, it holds for any `δ' ≥ δ`. -/
lemma stateDependentDistanceRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDRel ψ 𝒟 A B δ →
    SDDRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩

lemma questionCabApproxDelta
    {Outcome Aux : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [Fintype Aux]
    (ψ : QuantumState ι)
    (A B : OpFamily Outcome ι)
    (C : Outcome → Aux → MIPStarRE.Quantum.Op ι)
    (hC : ∀ a, ∑ b : Aux, (C a b)ᴴ * C a b ≤ 1) :
    qSDDOp ψ
        ({ outcome := fun ab : Outcome × Aux =>
             C ab.1 ab.2 * A.outcome ab.1
           total := ∑ ab : Outcome × Aux,
             C ab.1 ab.2 * A.outcome ab.1
         } : OpFamily (Outcome × Aux) ι)
        ({ outcome := fun ab : Outcome × Aux =>
             C ab.1 ab.2 * B.outcome ab.1
           total := ∑ ab : Outcome × Aux,
             C ab.1 ab.2 * B.outcome ab.1
         } : OpFamily (Outcome × Aux) ι) ≤
      qSDDOp ψ A B := by
  let D : Outcome → MIPStarRE.Quantum.Op ι :=
    fun a => A.outcome a - B.outcome a
  let CA : OpFamily (Outcome × Aux) ι :=
    { outcome := fun ab => C ab.1 ab.2 * A.outcome ab.1
      total := ∑ ab : Outcome × Aux,
        C ab.1 ab.2 * A.outcome ab.1 }
  let CB : OpFamily (Outcome × Aux) ι :=
    { outcome := fun ab => C ab.1 ab.2 * B.outcome ab.1
      total := ∑ ab : Outcome × Aux,
        C ab.1 ab.2 * B.outcome ab.1 }
  have hpointwise (a : Outcome) :
      ∑ b : Aux, ev ψ (((C a b * D a)ᴴ) * (C a b * D a)) ≤
        ev ψ ((D a)ᴴ * D a) := by
    calc
      ∑ b : Aux, ev ψ (((C a b * D a)ᴴ) * (C a b * D a))
        = ∑ b : Aux, ev ψ ((D a)ᴴ * ((C a b)ᴴ * C a b) * D a) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = ev ψ (∑ b : Aux, (D a)ᴴ * ((C a b)ᴴ * C a b) * D a) := by
            rw [← ev_finset_sum]
      _ = ev ψ ((D a)ᴴ * (∑ b : Aux, (C a b)ᴴ * C a b) * D a) := by
            congr 1
            rw [← Finset.sum_mul, ← Matrix.mul_sum]
      _ ≤ ev ψ ((D a)ᴴ * 1 * D a) := by
            exact ev_mono ψ _ _ (conjTranspose_mul_mono (Z := D a) (hC a))
      _ = ev ψ ((D a)ᴴ * D a) := by simp
  have hrewrite :
      qSDDOp ψ CA CB =
        ∑ a : Outcome, ∑ b : Aux,
          ev ψ (((C a b * D a)ᴴ) * (C a b * D a)) := by
    unfold CA CB qSDDOp qSDDCore
    simpa [D, mul_sub] using
      (Fintype.sum_prod_type' (f := fun a b =>
        ev ψ (((C a b * D a)ᴴ) * (C a b * D a))))
  calc
    qSDDOp ψ CA CB
      = ∑ a : Outcome, ∑ b : Aux,
          ev ψ (((C a b * D a)ᴴ) * (C a b * D a)) := hrewrite
    _ ≤ ∑ a : Outcome, ev ψ ((D a)ᴴ * D a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact hpointwise a
    _ = qSDDOp ψ A B := by
          unfold qSDDOp qSDDCore
          simp [D]

/-- `prop:cab-approx-delta`. -/
theorem cabApproxDelta_raw
    {Question Outcome Aux : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [Fintype Aux]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι)
    (C : (q : Question) → Outcome → Aux → MIPStarRE.Quantum.Op ι)
    (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
    (∀ q a, ∑ b : Aux, (C q a b)ᴴ * C q a b ≤ 1) →
    SDDOpRel ψ 𝒟
      (fun q => ({
        outcome := fun ab : Outcome × Aux =>
          C q ab.1 ab.2 * (A q).outcome ab.1
        total := ∑ ab : Outcome × Aux,
          C q ab.1 ab.2 * (A q).outcome ab.1
      } : OpFamily (Outcome × Aux) ι))
      (fun q => ({
        outcome := fun ab : Outcome × Aux =>
          C q ab.1 ab.2 * (B q).outcome ab.1
        total := ∑ ab : Outcome × Aux,
          C q ab.1 ab.2 * (B q).outcome ab.1
      } : OpFamily (Outcome × Aux) ι))
      δ := by
  intro ⟨hAB⟩ hC
  exact ⟨by
    unfold sddErrorOp at *
    calc
      avgOver 𝒟
          (fun q =>
            qSDDOp ψ
              ({ outcome := fun ab : Outcome × Aux =>
                   C q ab.1 ab.2 * (A q).outcome ab.1
                 total := ∑ ab : Outcome × Aux,
                   C q ab.1 ab.2 * (A q).outcome ab.1
               } : OpFamily (Outcome × Aux) ι)
              ({ outcome := fun ab : Outcome × Aux =>
                   C q ab.1 ab.2 * (B q).outcome ab.1
                 total := ∑ ab : Outcome × Aux,
                   C q ab.1 ab.2 * (B q).outcome ab.1
               } : OpFamily (Outcome × Aux) ι))
        ≤ avgOver 𝒟
            (fun q => qSDDOp ψ (A q) (B q)) := by
              apply avgOver_mono
              intro q
              exact questionCabApproxDelta ψ (A q) (B q) (C q) (hC q)
      _ ≤ δ := hAB⟩

/-! ### Infrastructure: triangle inequality for `SDDOpRel` -/



/-- Atomic mathematical fact: the parallelogram-style inequality for `qSDDOp`. -/
private lemma questionSDDOp_triangle
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B C : OpFamily Outcome ι) :
    qSDDOp ψ A C ≤ 2 * (qSDDOp ψ A B + qSDDOp ψ B C) := by
  let ev' (X Y : MIPStarRE.Quantum.Op ι) := ev ψ ((X - Y)ᴴ * (X - Y))
  have pointwise_outcome : ∀ a, ev' (A.outcome a) (C.outcome a) ≤
      2 * (ev' (A.outcome a) (B.outcome a) +
           ev' (B.outcome a) (C.outcome a)) :=
    fun a => ev_diff_triangle ψ _ _ _
  unfold qSDDOp qSDDCore
  have h1 : ∑ a : Outcome, ev' (A.outcome a) (C.outcome a) ≤
      ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                 ev' (B.outcome a) (C.outcome a))) :=
    Finset.sum_le_sum fun a _ => pointwise_outcome a
  have h2 : ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                        ev' (B.outcome a) (C.outcome a))) =
      2 * (∑ a : Outcome, ev' (A.outcome a) (B.outcome a) +
           ∑ a : Outcome, ev' (B.outcome a) (C.outcome a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

/-- Triangle inequality for operator-family state-dependent distance. -/
lemma stateDependentDistanceOpRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDOpRel ψ 𝒟 A B δ₁ →
    SDDOpRel ψ 𝒟 B C δ₂ →
    SDDOpRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟 (fun q => qSDDOp ψ (A q) (C q))
      ≤ avgOver 𝒟
          (fun q => 2 * (qSDDOp ψ (A q) (B q) + qSDDOp ψ (B q) (C q))) := by
            apply avgOver_mono
            intro q
            exact questionSDDOp_triangle ψ (A q) (B q) (C q)
    _ = 2 * avgOver 𝒟
          (fun q => qSDDOp ψ (A q) (B q) + qSDDOp ψ (B q) (C q)) := by
            rw [avgOver_const_mul]
    _ = 2 * (avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) +
          avgOver 𝒟 (fun q => qSDDOp ψ (B q) (C q))) := by
            rw [avgOver_add]
    _ ≤ 2 * (δ₁ + δ₂) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact add_le_add h₁ h₂

/-- Monotonicity of `SDDOpRel` in the error bound. -/
lemma stateDependentDistanceOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDOpRel ψ 𝒟 A B δ →
    SDDOpRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩



/-- Transport a local raw-operator state-dependent distance estimate to the
left tensor factor of a bipartite state.

The hypothesis `hev` is the defining marginal identity for the left register:
expectations of local operators in `φ` agree with expectations of their
left-tensor placements in `ψ`.  Under this identity, the squared-distance
defect of two local raw operator families is exactly the squared-distance
defect of their left placements. -/
lemma sddOpRel_leftPlaced_of_ev_eq
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (φ : QuantumState ιA)
    (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ιA) (δ : Error)
    (hev : ∀ X : MIPStarRE.Quantum.Op ιA,
      ev ψ (leftTensor (ι₂ := ιB) X) = ev φ X) :
    SDDOpRel φ 𝒟 A B δ →
    SDDOpRel ψ 𝒟
      (fun q => OpFamily.leftPlacedOpFamily (ιB := ιB) (A q))
      (fun q => OpFamily.leftPlacedOpFamily (ιB := ιB) (B q)) δ := by
  intro ⟨hAB⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            (OpFamily.leftPlacedOpFamily (ιB := ιB) (A q))
            (OpFamily.leftPlacedOpFamily (ιB := ιB) (B q)))
      = avgOver 𝒟 (fun q => qSDDOp φ (A q) (B q)) := by
          refine avgOver_congr 𝒟 _ _ ?_
          intro q
          unfold qSDDOp qSDDCore
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [OpFamily.leftPlacedOpFamily, leftTensor_sub,
            leftTensor_mul_leftTensor, hev]
    _ ≤ δ := hAB


end MIPStarRE.LDT.Preliminaries

end

end LIDT


