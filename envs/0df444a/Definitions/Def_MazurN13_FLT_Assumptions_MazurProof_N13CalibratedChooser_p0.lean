-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CalibratedChooser_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CalibratedChooser_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:37:25.255989+00:00
-- url     : https://prove2.me/theorems/b9045db2-bd45-4513-a4ba-359d227d0237
-- title:
--   FLT.Assumptions.MazurProof.N13CalibratedChooser source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CalibratedChooser

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CalibratedChooser
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13PointDataCertificates_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CoherentChooserSpecification_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SmallMumfordRigidity_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Construct the exact calibrated Chooser from the actual marked effective
realizations and the proved integral comparisons. In particular the inverse
infinity value is the required existing C+A datum, with raw mark -2 and
actual branch multiplicities (0,0). GlobalExistenceTarget is unchanged.
-/

namespace MazurProof.N13CalibratedChooser

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Polynomial N13EffectiveDataCompatibility N13EffectiveInfinityRepair
open N13InfinityChartMarking N13TwoChartPicardRealization N13PointDataCertificates
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def caMumford : N13Mumford.Mumford Q₂ where
  u := X * (X + 1)
  v := 1
  nInf := 0
  u_monic := by monicity!
  deg_u := by compute_degree!
  v_reduced := by
    have h2 : (X * (X + 1) : Q₂[X]).natDegree = 2 := by compute_degree!
    have hne : (X * (X + 1) : Q₂[X]) ≠ 0 := by
      intro h; rw [h, natDegree_zero] at h2; exact absurd h2 (by norm_num)
    rw [Polynomial.mod_eq_self_iff hne, degree_one, degree_eq_natDegree hne, h2]
    exact_mod_cast (by norm_num : (0 : ℕ) < 2)
  curve_dvd := by
    refine ⟨X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X + 2, ?_⟩
    change N13Mumford.f Q₂ - (1 : Q₂[X]) ^ 2 = _
    unfold N13Mumford.f
    ring
  infinity_bound := by
    rw [add_zero]
    compute_degree!

def caSemi : N13Mumford.SemiMumford Q₂ := { caMumford.toSemi with nInf := -1 }

theorem ca_degree : caMumford.u.natDegree = 2 := by
  change (X * (X + 1) : Q₂[X]).natDegree = 2
  compute_degree!

theorem caLine_map :
    Ideal.map N13IntegralFractionalHull.integralToRational
        N13InverseInfinityWitness.caLine.affineIdeal =
      SexticMumford.mumfordIdeal Model caSemi.u caSemi.v := by
  change Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic
    (N13QuadraticTwoChartSpread.pairLine _ _ _ _ _ _).affineIdeal = _
  rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
    N13TwoChartLineTensor.pointY_goodY, N13TwoChartLineTensor.pointY_goodY]
  simpa [caMumford, caSemi] using
    N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
      caMumford ca_degree (0 : Q₂) (-1) (by simp [caMumford]) (by norm_num)

set_option maxHeartbeats 800000 in
theorem inverseInfinity_certified : Certified N13InverseInfinityWitness.inverseInfinityData := by
  have hd : caSemi.u.natDegree = 2 := ca_degree
  have hn : caSemi.nInf = -1 := rfl
  refine ⟨caSemi, ?_, ?_,
    N13InverseInfinityWitness.inverseInfinityData_affineVerticallySaturated, ?_⟩
  · simp [EffectiveChamber, hd, hn]
  · exact N13EffectiveGraphData.raw_eq_of_map_and_mark caSemi
      N13InverseInfinityWitness.inverseInfinityData caLine_map
      (by show (-2 : ℤ) = -1 - 1; norm_num)
  · have hm := pairLine_marked (0 : Q₂) (N13TwoChartLineTensor.goodY 0 1)
        (-1) (N13TwoChartLineTensor.goodY (-1) 1)
        N13InverseInfinityData.curve_zero N13InverseInfinityData.curve_negOne
    have hp : positiveMultiplicity caSemi = 0 := by
      simp [positiveMultiplicity, hn]
    have hq : negativeMultiplicity caSemi = 0 := by
      simp [negativeMultiplicity, hd, hn]
    rw [hp, hq]
    change HasInfinityMultiplicities N13InverseInfinityWitness.caLine 0 0
    exact hm

abbrev tClass : G := N13Arithmetic.AJ13 N13Arithmetic.T

private theorem tClass_eq_classOf : tClass =
    SexticMumford.classOf (N13Mumford.model ℚ) (N13Infinity.positiveInfinityOrder ℚ)
      (SexticMumford.infinityMinusMumford (N13Mumford.model ℚ)) := rfl

theorem tClass_ne_zero : tClass ≠ 0 := by
  intro h
  rw [tClass_eq_classOf, ← SexticMumford.classOf_zero] at h
  have he := N13SmallMumfordRigidity.classOf_injective ℚ h
  have hn := congrArg (fun D : N13Mumford.Mumford ℚ => D.nInf) he
  norm_num [SexticMumford.infinityMinusMumford, SexticMumford.zero] at hn

theorem neg_tClass_ne_tClass : -tClass ≠ tClass := by
  intro h
  rw [← N13Arithmetic.classOf_opposite_eq_neg_AJ13_T, tClass_eq_classOf] at h
  have he := N13SmallMumfordRigidity.classOf_injective ℚ h
  have hn := congrArg (fun D : N13Mumford.Mumford ℚ => D.nInf) he
  norm_num [N13Arithmetic.oppositeInfinityMumford, SexticMumford.infinityMinusMumford] at hn

theorem infinityPlus_generic : N13InfinityPointPicardRealization.infinityPlusData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂ (0 : G) := by
  rw [N13InfinityPointPicardRealization.infinityPlusData_toGenericPic,
    SexticMumford.classOf_zero, map_zero]

private theorem mumford_ext {D E : SexticMumford.Mumford Model}
    (hu : D.u = E.u) (hv : D.v = E.v) (hn : D.nInf = E.nInf) : D = E := by
  cases D
  cases E
  simp_all

theorem infinityMinus_generic : N13InfinityPointPicardRealization.infinityMinusData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂ tClass := by
  rw [N13InfinityPointPicardRealization.infinityMinusData_toGenericPic,
    tClass_eq_classOf, N13InfinityBaseChange.picMapRatToQ₂_classOf]
  congr 1
  apply mumford_ext <;>
    simp [SexticMumford.infinityMinusMumford]

theorem inverseInfinity_generic : N13InverseInfinityWitness.inverseInfinityData.toGenericPic =
    N13InfinityBaseChange.picMapRatToQ₂ (-tClass) := by
  rw [N13InverseInfinityWitness.inverseInfinityData_toGenericPic_eq_opposite]
  have hm := N13InfinityBaseChange.picMapRatToQ₂_classOf (N13Arithmetic.oppositeInfinityMumford ℚ)
  rw [N13Arithmetic.classOf_opposite_eq_neg_AJ13_T] at hm
  rw [hm]
  exact congrArg (SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂))
    N13InverseInfinityWitness.mapQ₂_oppositeInfinity.symm

def choose (P : G) : Data := by
  classical
  exact
    if P = 0 then N13InfinityPointPicardRealization.infinityPlusData
    else if P = tClass then N13InfinityPointPicardRealization.infinityMinusData
    else if P = -tClass then N13InverseInfinityWitness.inverseInfinityData
    else chooseUncalibrated P

theorem choose_certified (P : G) : Certified (choose P) := by
  unfold choose
  split
  · exact infinityPlus_certified
  · split
    · exact infinityMinus_certified
    · split
      · exact inverseInfinity_certified
      · exact chooseUncalibrated_certified P

theorem choose_generic (P : G) :
    (choose P).toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P := by
  unfold choose
  split
  · rename_i h; subst P; exact infinityPlus_generic
  · split
    · rename_i h; subst P; exact infinityMinus_generic
    · split
      · rename_i h; subst P; exact inverseInfinity_generic
      · exact chooseUncalibrated_generic P

@[simp] theorem choose_zero : choose 0 = N13InfinityPointPicardRealization.infinityPlusData := by
  simp [choose]

@[simp] theorem choose_tClass : choose tClass = N13InfinityPointPicardRealization.infinityMinusData := by
  simp [choose, tClass_ne_zero]

@[simp] theorem choose_neg_tClass : choose (-tClass) = N13InverseInfinityWitness.inverseInfinityData := by
  simp [choose, neg_ne_zero.mpr tClass_ne_zero, neg_tClass_ne_tClass]

def chooser : N13CoherentChooserSpecification.Chooser where
  choose := choose
  generic_eq := choose_generic
  saturated P := by
    obtain ⟨E, _, _, hs, _⟩ := choose_certified P
    exact hs
  point_compatible P := by
    apply comparison_of_generic_eq _ _ (choose_certified _) (rationalPoint_certified P)
    rw [choose_generic, (N13RationalCurvePointPicardRealization.data P).generic_eq]

theorem chooser_tensor_comparisons : N13CoherentChooserSpecification.HasIntegralTensorComparisons chooser := by
  intro P Q
  apply tensor_comparison_of_class_sum_eq _ _ _ _
    (choose_certified P) (choose_certified Q) (choose_certified (P + Q)) (choose_certified 0)
  simp only [choose_generic, map_add, map_zero, add_zero]

/-- Exact existing target, with no additional compatibility assumptions. -/
theorem globalExistenceTarget : N13CoherentChooserSpecification.GlobalExistenceTarget := by
  refine ⟨chooser, chooser_tensor_comparisons, ?_, ?_, ?_⟩
  · exact choose_zero
  · exact choose_tClass
  · exact choose_neg_tClass

end
end MazurProof.N13CalibratedChooser


