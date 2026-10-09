-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MarkedEffectiveData_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MarkedEffectiveData_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:44:43.911378+00:00
-- url     : https://prove2.me/theorems/c670b332-0bcd-4929-b9bb-3f09f86fb2a4
-- title:
--   FLT.Assumptions.MazurProof.N13MarkedEffectiveData source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MarkedEffectiveData

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MarkedEffectiveData
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MarkedQuadraticExistence_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

The explicit effective-chart constructors now retain actual generic
infinity multiplicities on their same witness. Integral principal extension
and global chooser compatibility are not proved here.
-/
namespace MazurProof.N13MarkedEffectiveData
noncomputable section
open Polynomial N13InfinityChartMarking
open N13TwoChartPicardRealization N13EffectiveInfinityRepair N13EffectiveGraphData
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem infinityPairData_multiplicities (b c : Bool) :
    HasInfinityMultiplicities (infinityPairData b c).charts
      ((if b then 1 else 0) + (if c then 1 else 0))
      ((if b then 0 else 1) + (if c then 0 else 1)) := by
  cases b <;> cases c
  · exact hasInfinityMultiplicities_tensor _ _ 0 1 0 1
      infinityMinusLine_marked infinityMinusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 0 1 1 0
      infinityMinusLine_marked infinityPlusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 1 0 0 1
      infinityPlusLine_marked infinityMinusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 1 0 1 0
      infinityPlusLine_marked infinityPlusLine_marked

theorem anchoredPointData_multiplicities
    (x y : Q₂) (h : N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    HasInfinityMultiplicities (anchoredPointData x y h b).charts
      (if b then 1 else 0) (if b then 0 else 1) := by
  cases b
  · exact hasInfinityMultiplicities_tensor _ _ 0 0 0 1
      (affinePointLine_marked x y h) infinityMinusLine_marked
  · exact hasInfinityMultiplicities_tensor _ _ 0 0 1 0
      (affinePointLine_marked x y h) infinityPlusLine_marked

theorem exists_effective_data_marked
    (E : N13Mumford.SemiMumford Q₂) (hE : EffectiveChamber E) :
    ∃ R : Data, genericRaw R.charts R.infinityOrder =
        SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model E ∧
      AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts (positiveMultiplicity E) (negativeMultiplicity E) := by
  have hd := hE.1
  interval_cases he : E.u.natDegree
  · have hu : E.u = 1 := Polynomial.eq_one_of_monic_natDegree_zero E.u_monic he
    have hv : E.v = 0 := by
      have hh := E.v_reduced
      rw [hu] at hh
      simpa using hh.symm
    have hnlo := hE.2.1
    have hnhi : E.nInf ≤ 1 - (E.u.natDegree : ℤ) := by have := hE.2.2; omega
    rw [he] at hnhi
    norm_num at hnhi
    have hm (b c : Bool) :
        Ideal.map N13IntegralFractionalHull.integralToRational
            (infinityPairData b c).charts.affineIdeal =
          SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v := by
      rw [infinityPairData_affineIdeal, Ideal.map_top, hu, hv]
      exact (SexticMumford.zero_mumfordIdeal N13TwoChartPicardRealization.Model).symm
    interval_cases hn : E.nInf
    · refine ⟨infinityPairData false false, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _, ?_⟩
      · change (-2 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          infinityPairData_multiplicities false false
    · refine ⟨infinityPairData false true, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _, ?_⟩
      · change (-1 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          infinityPairData_multiplicities false true
    · refine ⟨infinityPairData true true, raw_eq_of_map_and_mark E _ (hm _ _) ?_,
        infinityPairData_saturated _ _, ?_⟩
      · change (0 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          infinityPairData_multiplicities true true
  · let D := balancedGraph E hE.1
    obtain ⟨x, y, hc, hD⟩ :=
      SexticMumford.exists_affinePoint_of_natDegree_eq_one
        N13TwoChartPicardRealization.Model D he rfl
    have hu : E.u = X - C x := congrArg (fun D => D.u) hD
    have hv : E.v = C y := congrArg (fun D => D.v) hD
    let hg := N13TwoChartLineTensor.goodY_onCurve x y hc
    have hm (b : Bool) :
        Ideal.map N13IntegralFractionalHull.integralToRational
            (anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg b).charts.affineIdeal =
          SexticMumford.mumfordIdeal N13TwoChartPicardRealization.Model E.u E.v := by
      rw [anchoredPointData_map_affineIdeal, N13TwoChartLineTensor.pointY_goodY, hu, hv]
    have hnlo := hE.2.1
    have hnhi : E.nInf ≤ 1 - (E.u.natDegree : ℤ) := by have := hE.2.2; omega
    rw [he] at hnhi
    norm_num at hnhi
    interval_cases hn : E.nInf
    · refine ⟨anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg false,
        raw_eq_of_map_and_mark E _ (hm _) ?_, anchoredPointData_saturated _ _ _ _, ?_⟩
      · change (-2 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          anchoredPointData_multiplicities x (N13TwoChartLineTensor.goodY x y) hg false
    · refine ⟨anchoredPointData x (N13TwoChartLineTensor.goodY x y) hg true,
        raw_eq_of_map_and_mark E _ (hm _) ?_, anchoredPointData_saturated _ _ _ _, ?_⟩
      · change (-1 : ℤ) = E.nInf - 1
        omega
      · simpa [positiveMultiplicity, negativeMultiplicity, he, hn] using
          anchoredPointData_multiplicities x (N13TwoChartLineTensor.goodY x y) hg true
  · let D := balancedGraph E hE.1
    obtain ⟨R, hraw, _, hs, hmarked⟩ := N13MarkedQuadraticExistence.exists_saturated_data D he
    have hm := map_affineIdeal_eq_of_genericRaw_eq_mumfordRaw R.charts R.infinityOrder D hraw
    refine ⟨withMark R (E.nInf - 1), raw_eq_of_map_and_mark E _ hm rfl, hs, ?_⟩
    have hn : E.nInf = -1 := by
      have hlo := hE.2.1
      have hhi := hE.2.2
      rw [he] at hhi
      omega
    simpa [positiveMultiplicity, negativeMultiplicity, withMark, he, hn] using hmarked


theorem exists_marked_repaired_data (D : N13Mumford.Mumford Q₂) :
    ∃ R : Data,
      genericRaw R.charts R.infinityOrder =
        SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model (repair D) ∧
      R.toGenericPic = SexticMumford.classOf N13TwoChartPicardRealization.Model
        (N13Infinity.positiveInfinityOrder Q₂) D ∧
      AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts
        (positiveMultiplicity (repair D)) (negativeMultiplicity (repair D)) := by
  obtain ⟨R, hraw, hs, hm⟩ := exists_effective_data_marked (repair D) (repair_effective D)
  refine ⟨R, hraw, ?_, hs, hm⟩
  change genericClass R.charts R.infinityOrder = _
  unfold genericClass
  rw [hraw]
  exact repair_class D

end
end MazurProof.N13MarkedEffectiveData


