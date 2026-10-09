-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MarkedTensorComparison_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MarkedTensorComparison_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:21:56.196807+00:00
-- url     : https://prove2.me/theorems/2612ef3c-65b9-4445-a70a-ac2e41a15e83
-- title:
--   FLT.Assumptions.MazurProof.N13MarkedTensorComparison source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MarkedTensorComparison

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MarkedTensorComparison
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralPrincipalComparison_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MarkedEffectiveData_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

For the actual marked effective data constructed in this series, equality
of the generic class sums produces an integral two-chart tensor comparison.
No integral comparison, global specialization, branch compatibility, or
special additive law is assumed.
-/

namespace MazurProof.N13MarkedTensorComparison

noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair N13IntegralPrincipalComparison
open scoped nonZeroDivisors
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing

abbrev tensor := N13TwoChartLineTensor.tensor

theorem genericIdealUnit_tensor (L M : Line) :
    genericIdealUnit (tensor L M) = genericIdealUnit L * genericIdealUnit M := by
  apply Units.ext
  simp only [coe_genericIdealUnit, N13TwoChartLineTensor.tensor_affineIdeal,
    Ideal.map_mul, FractionalIdeal.coeIdeal_mul, Units.val_mul]

/-- Extract the actual affine principal multiplier and its positive order
from equality in the existing oriented quotient. -/
theorem exists_multiplier_of_class_sum_eq
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (D₀ D₁ D₂ D₃ : Data)
    (hraw₀ : genericRaw D₀.charts D₀.infinityOrder = SexticMumford.semiMumfordRaw Model E₀)
    (hraw₁ : genericRaw D₁.charts D₁.infinityOrder = SexticMumford.semiMumfordRaw Model E₁)
    (hraw₂ : genericRaw D₂.charts D₂.infinityOrder = SexticMumford.semiMumfordRaw Model E₂)
    (hraw₃ : genericRaw D₃.charts D₃.infinityOrder = SexticMumford.semiMumfordRaw Model E₃)
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    ∃ f : Fˣ,
      SexticMumford.mumfordIdealUnit Model E₀ * SexticMumford.mumfordIdealUnit Model E₁ *
          toPrincipalIdeal R F f =
        SexticMumford.mumfordIdealUnit Model E₂ * SexticMumford.mumfordIdealUnit Model E₃ ∧
      E₀.nInf + E₁.nInf +
          Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
        E₂.nInf + E₃.nInf := by
  let q := QuotientGroup.mk'
    (SexticMumford.principalOriented Model (N13Infinity.positiveInfinityOrder Q₂)).range
  have hq : q (SexticMumford.semiMumfordRaw Model E₀ * SexticMumford.semiMumfordRaw Model E₁) =
      q (SexticMumford.semiMumfordRaw Model E₂ * SexticMumford.semiMumfordRaw Model E₃) := by
    change q (genericRaw D₀.charts D₀.infinityOrder) * q (genericRaw D₁.charts D₁.infinityOrder) =
      q (genericRaw D₂.charts D₂.infinityOrder) * q (genericRaw D₃.charts D₃.infinityOrder) at hclass
    rw [hraw₀, hraw₁, hraw₂, hraw₃] at hclass
    simpa only [map_mul] using hclass
  change QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ at hq
  rw [QuotientGroup.mk'_eq_mk'] at hq
  obtain ⟨z, hz, hmul⟩ := hq
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hz
  refine ⟨f, congrArg Prod.fst hmul, ?_⟩
  have hi := congrArg
    (fun z : SexticMumford.OrientedFrac Model => Multiplicative.toAdd z.2) hmul
  change ((E₀.nInf - 1) + (E₁.nInf - 1)) +
      Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder Q₂).ordPlus f) =
    (E₂.nInf - 1) + (E₃.nInf - 1) at hi
  omega

/-- The central tensor-normalization construction for the marked effective
representatives. All four regular functions, nonzero reductions, both ideal
equations, and the single common overlap fraction are constructed. -/
theorem exists_integral_tensor_comparison
    (E₀ E₁ E₂ E₃ : N13Mumford.SemiMumford Q₂)
    (h₀ : EffectiveChamber E₀) (h₁ : EffectiveChamber E₁)
    (h₂ : EffectiveChamber E₂) (h₃ : EffectiveChamber E₃)
    (D₀ D₁ D₂ D₃ : Data)
    (hraw₀ : genericRaw D₀.charts D₀.infinityOrder = SexticMumford.semiMumfordRaw Model E₀)
    (hraw₁ : genericRaw D₁.charts D₁.infinityOrder = SexticMumford.semiMumfordRaw Model E₁)
    (hraw₂ : genericRaw D₂.charts D₂.infinityOrder = SexticMumford.semiMumfordRaw Model E₂)
    (hraw₃ : genericRaw D₃.charts D₃.infinityOrder = SexticMumford.semiMumfordRaw Model E₃)
    (hs₀ : AffineVerticallySaturated D₀.charts) (hs₁ : AffineVerticallySaturated D₁.charts)
    (hs₂ : AffineVerticallySaturated D₂.charts) (hs₃ : AffineVerticallySaturated D₃.charts)
    (hm₀ : HasInfinityMultiplicities D₀.charts (positiveMultiplicity E₀) (negativeMultiplicity E₀))
    (hm₁ : HasInfinityMultiplicities D₁.charts (positiveMultiplicity E₁) (negativeMultiplicity E₁))
    (hm₂ : HasInfinityMultiplicities D₂.charts (positiveMultiplicity E₂) (negativeMultiplicity E₂))
    (hm₃ : HasInfinityMultiplicities D₃.charts (positiveMultiplicity E₃) (negativeMultiplicity E₃))
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)) := by
  obtain ⟨f, hprincipal, horientation⟩ := exists_multiplier_of_class_sum_eq
    E₀ E₁ E₂ E₃ D₀ D₁ D₂ D₃ hraw₀ hraw₁ hraw₂ hraw₃ hclass
  obtain ⟨n, m, a, b, ha, hb, hf⟩ :=
    N13PrimitiveVerticalPresentation.exists_affine_primitive_fraction_presentation (f : F) f.ne_zero
  obtain ⟨c, d, hc, hd, hcross⟩ :=
    N13PrimitiveChartTransport.exists_common_primitive_presentation a b ha hb
  have hb0 : b ≠ 0 := fun h => hb (by simp [h])
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hd0 : d ≠ 0 := fun h => hd (by simp [h])
  have hf' : 2 ^ m * (f : F) * algebraMap A F b = 2 ^ n * algebraMap A F a := by
    simpa only [map_ofNat] using hf
  have hgeneric : genericIdealUnit (tensor D₀.charts D₁.charts) * toPrincipalIdeal R F f =
      genericIdealUnit (tensor D₂.charts D₃.charts) := by
    rw [genericIdealUnit_tensor, genericIdealUnit_tensor]
    have hu₀ := congrArg Prod.fst hraw₀
    have hu₁ := congrArg Prod.fst hraw₁
    have hu₂ := congrArg Prod.fst hraw₂
    have hu₃ := congrArg Prod.fst hraw₃
    change genericIdealUnit D₀.charts = SexticMumford.mumfordIdealUnit Model E₀ at hu₀
    change genericIdealUnit D₁.charts = SexticMumford.mumfordIdealUnit Model E₁ at hu₁
    change genericIdealUnit D₂.charts = SexticMumford.mumfordIdealUnit Model E₂ at hu₂
    change genericIdealUnit D₃.charts = SexticMumford.mumfordIdealUnit Model E₃ at hu₃
    rw [hu₀, hu₁, hu₂, hu₃]
    exact hprincipal
  have haffine := N13PrimitiveAffineComparison.integral_cleared_equation
    (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)
    (N13QuadraticTwoChartSpreadSaturation.affineVerticallySaturated_tensor _ _ hs₀ hs₁)
    (N13QuadraticTwoChartSpreadSaturation.affineVerticallySaturated_tensor _ _ hs₂ hs₃)
    f n m a b ha hb hf' hgeneric
  obtain ⟨hplus, hminus⟩ := tensor_branch_ideal_equations
    E₀ E₁ E₂ E₃ h₀ h₁ h₂ h₃ D₀.charts D₁.charts D₂.charts D₃.charts
    hm₀ hm₁ hm₂ hm₃ f n m a b c d hb0 hc0 hd0 hf' hcross hprincipal horientation
  have htensor (D E : Data) :
      Ideal.map N13IntegralInfinityReduction.reduceCoordinate (tensor D.charts E.charts).infinityIdeal ≠ ⊥ := by
    rw [N13TwoChartLineTensor.tensor_infinityIdeal, Ideal.map_mul]
    intro h
    rcases Ideal.mul_eq_bot.mp h with hD | hE
    · exact data_infinity_reduction_ne_bot D hD
    · exact data_infinity_reduction_ne_bot E hE
  have hinfinity := integral_infinity_cleared_equation
    (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)
    a b c d hb0 hc hd (htensor D₀ D₁) (htensor D₂ D₃)
    haffine hcross hplus hminus
  exact ⟨{
    aNum := a
    aDen := b
    iNum := c
    iDen := d
    aNum_ne := ha
    aDen_ne := hb
    iNum_ne := hc
    iDen_ne := hd
    affine_eq := haffine
    infinity_eq := hinfinity
    overlap_eq := hcross }⟩

end
end MazurProof.N13MarkedTensorComparison


