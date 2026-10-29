-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:47:03.777057+00:00
-- url     : https://prove2.me/theorems/bc2f3f56-b4e6-4e59-b4bf-fee585fab149
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / Averaging
-- statement:
--   This bundle supplies averaging lemmas that turn pointwise operator and polynomial bounds into bounds for uniform families. It is used to pass from local estimates to qSDD or expectation estimates after averaging over answers and polynomial samples.
--
--   Principal definitions:
--   - `ev_uniformAverage_sq_le_avg`: bounds the expectation of a squared uniform average by the average of squared expectations.
--   - `qSDD_unit_family_of_average_le_avg`: lifts an averaged pointwise estimate to a qSDD bound for a unit-valued family.
--   - `sddRel_unit_family_of_pointwise`: converts pointwise deviation bounds into an SDD relation.
--   - `avgOver_polynomialDistribution_le_of_pointwise`: averages a pointwise polynomial bound over the uniform polynomial distribution.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean#L18-L258

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-! ## Uniform averaging infrastructure -/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

private lemma ev_uniformAverage_sq_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (D : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
      ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
        averageOperatorOverDistribution (uniformDistribution α) D)
      ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
  let c : Error := 1 / (Fintype.card α : Error)
  let S : MIPStarRE.Quantum.Op ι :=
    averageOperatorOverDistribution (uniformDistribution α) D
  let x : α → Error := fun a => ev ψ ((D a)ᴴ * D a)
  have hc_nonneg : 0 ≤ c := by
    positivity
  have hx_nonneg : ∀ a, 0 ≤ x a := by
    intro a
    exact ev_adjoint_self_nonneg ψ (D a)
  have hcard : (Fintype.card α : Error) ≠ 0 := by
    positivity
  have hsumc : ∑ a : α, c = 1 := by
    unfold c
    calc
      ∑ a : α, (1 / (Fintype.card α : Error))
          = (Fintype.card α : Error) * (1 / (Fintype.card α : Error)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            field_simp [hcard]
  have h_expand :
      ev ψ (Sᴴ * S)
        = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
    have hSsum : S = ∑ a : α, c • D a := by
      ext i j
      simp [S, c, averageOperatorOverDistribution, uniformDistribution]
    have hconj :
        (∑ a : α, c • D a)ᴴ = ∑ a : α, c • (D a)ᴴ := by
      simpa using
        (Matrix.conjTranspose_sum (s := Finset.univ)
          (M := fun a : α => c • D a))
    calc
      ev ψ (Sᴴ * S)
        = ev ψ (((∑ a : α, c • D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hSsum]
      _ = ev ψ ((∑ a : α, c • (D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hconj]
      _ = ev ψ (∑ b : α, ∑ a : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Matrix.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
      _ = ev ψ (∑ a : α, ∑ b : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Finset.sum_comm]
      _ = ∑ a : α, ∑ b : α, ev ψ ((c • (D a)ᴴ) * (c • D b)) := by
            rw [ev_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sum]
      _ = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [show ((c • (D a)ᴴ) * (c • D b)) =
                c • (c • ((D a)ᴴ * D b)) by
                  rw [smul_mul_assoc, mul_smul_comm]]
            rw [show c • (c • ((D a)ᴴ * D b)) =
                ((c : ℂ) • ((c : ℂ) • ((D a)ᴴ * D b))) by rfl]
            rw [ev_scale, ev_scale]
  have h_bound :
      ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b))
        ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := by
    refine Finset.sum_le_sum ?_
    intro a _
    refine Finset.sum_le_sum ?_
    intro b _
    have hab :
        ev ψ ((D a)ᴴ * D b) ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
      calc
        ev ψ ((D a)ᴴ * D b) ≤ |ev ψ ((D a)ᴴ * D b)| := le_abs_self _
        _ ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
              simpa [x] using ev_abs_mul_le_sqrt ψ ((D a)ᴴ) (D b)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hab hc_nonneg) hc_nonneg
  let s : Error := ∑ a : α, c * Real.sqrt (x a)
  have hs_square :
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) = s * s := by
    unfold s
    calc
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b)))
        = ∑ a : α, (c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
      _ = (∑ a : α, c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            rw [← Finset.sum_mul]
      _ = s * s := by
            rfl
  have hs_le :
      s ≤ Real.sqrt (avgOver (uniformDistribution α) x) := by
    have hs_raw :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c
          ≤ Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => c * x a) (g := fun _ => c)
              (fun a => mul_nonneg hc_nonneg (hx_nonneg a))
              (fun _ => hc_nonneg)
    have hs_lhs :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c = s := by
      unfold s
      refine Finset.sum_congr rfl ?_
      intro a _
      calc
        Real.sqrt (c * x a) * Real.sqrt c
          = Real.sqrt c * Real.sqrt (x a) * Real.sqrt c := by
              rw [Real.sqrt_mul hc_nonneg (x a)]
        _ = (Real.sqrt c * Real.sqrt c) * Real.sqrt (x a) := by
              ring
        _ = c * Real.sqrt (x a) := by
              rw [show Real.sqrt c * Real.sqrt c = c by
                nlinarith [Real.sq_sqrt hc_nonneg]]
    have hs_rhs :
        Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) =
          Real.sqrt (avgOver (uniformDistribution α) x) := by
      rw [hsumc, Real.sqrt_one, mul_one]
      simp [avgOver, uniformDistribution, c]
    rw [hs_lhs, hs_rhs] at hs_raw
    exact hs_raw
  have hs_nonneg : 0 ≤ s := by
    unfold s
    exact Finset.sum_nonneg fun a _ => mul_nonneg hc_nonneg (Real.sqrt_nonneg _)
  have havg_nonneg : 0 ≤ avgOver (uniformDistribution α) x := by
    exact avgOver_nonneg _ _ hx_nonneg
  calc
    ev ψ (Sᴴ * S)
      = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := h_expand
    _ ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := h_bound
    _ = s * s := hs_square
    _ ≤ avgOver (uniformDistribution α) x := by
          nlinarith [hs_nonneg, hs_le, Real.sq_sqrt havg_nonneg]

private lemma qSDD_unit_family_of_average_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (MA MB : SubMeas Unit ι)
    (A B : α → MIPStarRE.Quantum.Op ι)
    (hMA :
      MA.outcome () = averageOperatorOverDistribution (uniformDistribution α) A)
    (hMB :
      MB.outcome () = averageOperatorOverDistribution (uniformDistribution α) B) :
    qSDD ψ MA MB
      ≤ avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
  let D : α → MIPStarRE.Quantum.Op ι := fun a => A a - B a
  have havg_sub :
      averageOperatorOverDistribution (uniformDistribution α) A -
          averageOperatorOverDistribution (uniformDistribution α) B =
        averageOperatorOverDistribution (uniformDistribution α) D := by
    simp [D, averageOperatorOverDistribution,
      uniformDistribution, Finset.sum_sub_distrib, smul_sub]
  calc
    qSDD ψ MA MB
      = ev ψ
          (((averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)ᴴ) *
            (averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)) := by
              unfold qSDD qSDDCore
              simp [hMA, hMB]
    _ = ev ψ
          ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
            averageOperatorOverDistribution (uniformDistribution α) D) := by
          rw [havg_sub]
    _ ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
          exact ev_uniformAverage_sq_le_avg ψ D
    _ = avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
          rfl

/-- Lift pointwise operator deviation bounds to an `SDDRel` bound for
unit-valued averaged families. -/
lemma sddRel_unit_family_of_pointwise
    {Question α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (MA MB : Question → SubMeas Unit ι)
    (A B : Question → α → MIPStarRE.Quantum.Op ι)
    (hMA :
      ∀ q, (MA q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => A q a))
    (hMB :
      ∀ q, (MB q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => B q a))
    (δ : Error)
    (hpoint :
      ∀ a, avgOver 𝒟 (fun q => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a))) ≤ δ) :
    SDDRel ψ 𝒟 MA MB δ := by
  refine ⟨?_⟩
  unfold sddError
  calc
    avgOver 𝒟 (fun q => qSDD ψ (MA q) (MB q))
      ≤ avgOver 𝒟
          (fun q =>
            avgOver (uniformDistribution α)
              (fun a => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))) := by
              apply avgOver_mono
              intro q
              exact qSDD_unit_family_of_average_le_avg ψ
                (MA q) (MB q) (fun a => A q a) (fun a => B q a) (hMA q) (hMB q)
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver 𝒟 (fun q => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))) := by
            exact avgOver_comm 𝒟 (uniformDistribution α)
              (fun q a => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))
    _ ≤ avgOver (uniformDistribution α) (fun _ => δ) := by
          apply avgOver_mono
          intro a
          exact hpoint a
    _ = δ := by
          simp [avgOver, uniformDistribution]

/-! ## Averaging and local-to-global helpers -/

/-- Average a pointwise polynomial bound over the uniform polynomial distribution. -/
lemma avgOver_polynomialDistribution_le_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (f : Polynomial params → Error)
    (δ : Error)
    (hpoint : ∀ g : Polynomial params, f g ≤ δ) :
    avgOver (polynomialDistribution params) f ≤ δ := by
  calc
    avgOver (polynomialDistribution params) f
      ≤ avgOver (polynomialDistribution params) (fun _ => δ) := by
        apply avgOver_mono
        intro g
        exact hpoint g
    _ = δ := by
      simp [polynomialDistribution, avgOver, uniformDistribution]

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


