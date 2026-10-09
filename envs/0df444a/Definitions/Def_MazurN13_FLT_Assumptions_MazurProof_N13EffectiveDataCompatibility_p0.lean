-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EffectiveDataCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13EffectiveDataCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:27:54.094331+00:00
-- url     : https://prove2.me/theorems/963364c7-d410-44b1-b28a-730db0856b5f
-- title:
--   FLT.Assumptions.MazurProof.N13EffectiveDataCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13EffectiveDataCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13EffectiveDataCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MarkedTensorComparison_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBaseChange_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordInfinityBalance_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

The proved raw, effective, saturated, and actual-branch properties are
packaged together without adding a comparison assumption. Equal generic
classes of certified data give an integral comparison. Every rational class
has such data, and the resulting choice already has integral tensor
comparisons. The three exact calibrations and named-point compatibility are
the remaining GlobalExistenceTarget assembly.
-/

namespace MazurProof.N13EffectiveDataCompatibility

noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance instAlgebraAR : Algebra A R := N13IntegralFractionalHull.integralToRational.toAlgebra
local instance instIsFractionRingAF : IsFractionRing A F := N13IntegralFractionalHull.functionField_isFractionRing

/-- Only the geometric properties already constructed for the same Data.
In particular, neither a principal comparison nor additivity is a field. -/
def Certified (D : Data) : Prop :=
  ∃ E : N13Mumford.SemiMumford Q₂,
    EffectiveChamber E ∧
    genericRaw D.charts D.infinityOrder = SexticMumford.semiMumfordRaw Model E ∧
    AffineVerticallySaturated D.charts ∧
    HasInfinityMultiplicities D.charts (positiveMultiplicity E) (negativeMultiplicity E)

private theorem cancel_invertible_ideal
    {T K : Type*} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K]
    (I J U : Ideal T) (hU : IsUnit (U : FractionalIdeal T⁰ K))
    (h : I * U = J * U) : I = J := by
  obtain ⟨u, hu⟩ := hU
  apply FractionalIdeal.coeIdeal_injective (K := K)
  have he := congrArg (fun V : Ideal T => (V : FractionalIdeal T⁰ K)) h
  simp only [FractionalIdeal.coeIdeal_mul] at he
  rw [← hu] at he
  have hm := congrArg (fun V : FractionalIdeal T⁰ K => V * (↑(u⁻¹) : FractionalIdeal T⁰ K)) he
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hm

def cancel_tensor_right (L M U : Line)
    (h : N13CoherentChartComparison.IntegralComparison (tensor L U) (tensor M U)) :
    N13CoherentChartComparison.IntegralComparison L M where
  aNum := h.aNum
  aDen := h.aDen
  iNum := h.iNum
  iDen := h.iDen
  aNum_ne := h.aNum_ne
  aDen_ne := h.aDen_ne
  iNum_ne := h.iNum_ne
  iDen_ne := h.iDen_ne
  affine_eq := cancel_invertible_ideal (K := F) _ _ U.affineIdeal U.affine_isUnit
    (by simpa only [N13TwoChartLineTensor.tensor_affineIdeal, mul_assoc] using h.affine_eq)
  infinity_eq := cancel_invertible_ideal (K := N13IntegralInfinityPointSpread.FunctionField)
    _ _ U.infinityIdeal U.infinity_isUnit
    (by simpa only [N13TwoChartLineTensor.tensor_infinityIdeal, mul_assoc] using h.infinity_eq)
  overlap_eq := h.overlap_eq

theorem tensor_comparison_of_class_sum_eq
    (D₀ D₁ D₂ D₃ : Data)
    (h₀ : Certified D₀) (h₁ : Certified D₁) (h₂ : Certified D₂) (h₃ : Certified D₃)
    (hclass : D₀.toGenericPic + D₁.toGenericPic = D₂.toGenericPic + D₃.toGenericPic) :
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (tensor D₀.charts D₁.charts) (tensor D₂.charts D₃.charts)) := by
  obtain ⟨E₀, hc₀, hr₀, hs₀, hm₀⟩ := h₀
  obtain ⟨E₁, hc₁, hr₁, hs₁, hm₁⟩ := h₁
  obtain ⟨E₂, hc₂, hr₂, hs₂, hm₂⟩ := h₂
  obtain ⟨E₃, hc₃, hr₃, hs₃, hm₃⟩ := h₃
  exact exists_integral_tensor_comparison E₀ E₁ E₂ E₃ hc₀ hc₁ hc₂ hc₃
    D₀ D₁ D₂ D₃ hr₀ hr₁ hr₂ hr₃ hs₀ hs₁ hs₂ hs₃ hm₀ hm₁ hm₂ hm₃ hclass

theorem comparison_of_generic_eq (D E : Data) (hD : Certified D) (hE : Certified E)
    (heq : D.toGenericPic = E.toGenericPic) :
    Nonempty (N13CoherentChartComparison.IntegralComparison D.charts E.charts) := by
  obtain ⟨h⟩ := tensor_comparison_of_class_sum_eq D D E D hD hD hE hD
    (by rw [heq])
  exact ⟨cancel_tensor_right D.charts E.charts D.charts h⟩

abbrev G := N13RationalPointEndgame.G

theorem exists_certified_realization (P : G) :
    ∃ D : Data, Certified D ∧ D.toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P := by
  obtain ⟨D, hD⟩ := N13MumfordInfinityBalance.classOf_surjective P
  let M := D.mapCoeffs (M' := N13Mumford.model N13InfinityBaseChange.Q₂)
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (by simpa only [N13Mumford.model_f] using
      N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)
  obtain ⟨W, hraw, hgeneric, hs, hm⟩ := N13MarkedEffectiveData.exists_marked_repaired_data M
  refine ⟨W, ⟨repair M, repair_effective M, hraw, hs, hm⟩, ?_⟩
  rw [hgeneric]
  change SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂)
      (D.mapCoeffs N13InfinityBaseChange.ratToQ₂
        N13InfinityBaseChange.ratToQ₂_injective
        (N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)) = _
  rw [← N13InfinityBaseChange.picMapRatToQ₂_classOf, hD]

def chooseUncalibrated (P : G) : Data := Classical.choose (exists_certified_realization P)

theorem chooseUncalibrated_certified (P : G) : Certified (chooseUncalibrated P) :=
  (Classical.choose_spec (exists_certified_realization P)).1

theorem chooseUncalibrated_generic (P : G) :
    (chooseUncalibrated P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P :=
  (Classical.choose_spec (exists_certified_realization P)).2

theorem chooseUncalibrated_tensor_comparisons (P Q : G) :
    Nonempty (N13CoherentChartComparison.IntegralComparison
      (tensor (chooseUncalibrated P).charts (chooseUncalibrated Q).charts)
      (tensor (chooseUncalibrated (P + Q)).charts (chooseUncalibrated 0).charts)) := by
  apply tensor_comparison_of_class_sum_eq _ _ _ _
    (chooseUncalibrated_certified P) (chooseUncalibrated_certified Q)
    (chooseUncalibrated_certified (P + Q)) (chooseUncalibrated_certified 0)
  simp only [chooseUncalibrated_generic, map_add, map_zero, add_zero]

end
end MazurProof.N13EffectiveDataCompatibility


