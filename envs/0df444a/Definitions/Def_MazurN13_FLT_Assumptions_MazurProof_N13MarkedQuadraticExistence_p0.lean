-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MarkedQuadraticExistence_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MarkedQuadraticExistence_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:41:44.051015+00:00
-- url     : https://prove2.me/theorems/f8587920-f881-4131-9e26-a59fb3b356ec
-- title:
--   FLT.Assumptions.MazurProof.N13MarkedQuadraticExistence source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MarkedQuadraticExistence

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MarkedQuadraticExistence
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityChartMarking_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Retain the infinity-marking certificate on the same quadratic witness.
The case constructions are the pinned finite, split and reciprocal source
proofs, augmented by the actual branch-ideal proofs; no existing file changes.
This supplies no integral principal-comparison or global chooser theorem.
-/
namespace MazurProof.N13MarkedQuadraticExistence
noncomputable section
open Polynomial N13InfinityChartMarking
open N13SplitQuadraticPicardRealization N13SplitQuadraticSpecialRestriction
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev Q₂ := N13TwoChartPicardRealization.Q₂
abbrev Model := N13TwoChartPicardRealization.Model

theorem exists_saturated_data_of_finite
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite N13FiniteAffineTwoChart.R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  let L :=
    N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
      D.toSemi hdeg hfinite
  obtain ⟨Δ, hrestrict⟩ :=
    N13FiniteQuadraticSpecialRestriction.exists_specialDivisor_of_finiteQuadratic
        D.toSemi hdeg hfinite
  have haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal :=
    congrArg (fun C => C.affineIdeal) hrestrict
  have hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal :=
    congrArg (fun C => C.infinityIdeal) hrestrict
  have hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
    exact
      N13FiniteAffineTwoChart.map_finiteQuadraticTwoChartLine_affineIdeal
          D.toSemi hdeg hfinite
  let R :=
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization
      D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
          D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
          D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity
        (N13QuadraticPicardRealization.finiteQuadraticTwoChartLine_affineVerticallySaturated
          D hdeg hfinite)
  · exact finiteQuadraticLine_marked D.toSemi hdeg hfinite

theorem ReciprocalGraphClosure.exists_saturated_data
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    {a b : N13IrreducibleQuadraticSpread.R₂}
    (E : N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  have huMonic : E.data.u.Monic := by
    rw [E.data_u]
    exact
      N13ReciprocalQuadraticReflection.integralReciprocal_monic
        a b
  have huDegree : E.data.u.natDegree = 2 := by
    rw [E.data_u]
    exact
      N13ReciprocalQuadraticReflection.integralReciprocal_natDegree
        a b
  let L :=
    N13IntegralInfinityGraphTwoChart.twoChartLine
      E.data (by omega) E.v_degree E.w_degree huMonic.ne_zero
  let Dbar :=
    N13SpecialInfinityGraphDivisor.reduceGraphData E.data huMonic
  let hDbarDegree :=
    N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
      E.data huMonic huDegree
  let Δ :=
    N13SpecialInfinityGraphDivisor.graphDivisor
      Dbar hDbarDegree
  have hrestrict :
      N13TwoChartSpecialRestriction.restrict L =
        N13SpecialDivisorCharts.ofDivisor Δ := by
    simpa [L, Dbar, hDbarDegree, Δ] using
      (N13IntegralInfinityGraphSpecialRestriction.restrict_twoChartLine
        E.data huMonic huDegree E.v_degree E.w_degree)
  have haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal :=
    congrArg (fun C => C.affineIdeal) hrestrict
  have hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal :=
    congrArg (fun C => C.infinityIdeal) hrestrict
  have hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal
          N13IrreducibleQuadraticSpread.Model D.u D.v := by
    change
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityGraphTwoChart.affineIdeal E.data) =
        SexticMumford.mumfordIdeal
          N13IrreducibleQuadraticSpread.Model D.u D.v
    apply
      N13IntegralInfinityGraphTwoChart.map_affineIdeal_eq_mumfordIdeal
        E.data D.toSemi ((D.u.coeff 0)⁻¹)
    · exact inv_ne_zero h0
    · change
        N13TwoAdicCoordinateBaseChange.mapPoly
            (E.data.u.reflect 2) =
          C ((D.u.coeff 0)⁻¹) * D.u
      rw [E.data_u]
      exact
        N13ReciprocalQuadraticReflection.mapPoly_reflect_integralReciprocal
          D hdeg h0 a b hm
    · exact E.generic_ordinate
  let R :=
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization
      D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity
        (N13ReciprocalGraphPicardRealization.ReciprocalGraphClosure.twoChartLine_affineVerticallySaturated E)
  · exact infinityGraphLine_marked E.data (by omega) E.v_degree E.w_degree huMonic.ne_zero
      (by rw [E.data_u]; exact reciprocal_constant_nonzero D a b h0 hm)

theorem verticalGraph_exists_saturated_data
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    {a b : N13IrreducibleQuadraticSpread.R₂}
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹))
    (E : N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hmDegree : E.m.natDegree = 2)
    (hI :
      N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  let u :=
    N13ReciprocalQuadraticReflection.integralReciprocal a b
  have hu : u.Monic :=
    N13ReciprocalQuadraticReflection.integralReciprocal_monic a b
  have huDegree : u.natDegree = 2 :=
    N13ReciprocalQuadraticReflection.integralReciprocal_natDegree a b
  have huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal := by
    rw [← hI]
    exact
      N13ReciprocalInfinityContraction.reciprocal_mem_integralInfinityIdeal
        D hdeg h0 a b hm
  let L :=
    N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
      u E hu huDegree hmDegree huMem
  obtain ⟨Δ, hrestrict⟩ :=
    N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor
      u E hu huDegree hmDegree huMem
  have haffine :
      (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal :=
    congrArg (fun C => C.affineIdeal) hrestrict
  have hinfinity :
      (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal :=
    congrArg (fun C => C.infinityIdeal) hrestrict
  have hmap :
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal
          N13IrreducibleQuadraticSpread.Model D.u D.v := by
    change
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralInfinityVerticalGraphTwoChart.affineIdeal u E) =
        N13ReciprocalInfinityContraction.genericIdeal D
    rw [←
        N13IntegralInfinityVerticalGraphContraction.contractIdeal_eq_affineIdeal
          D hdeg h0 u E hu huDegree hmDegree huMem hI,
      N13IntegralModelContraction.map_contractIdeal]
  let R :=
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization
      D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity
        (N13ReciprocalVerticalGraphPicardRealization.verticalGraph_twoChartLine_affineVerticallySaturated
          hdeg h0 u E hu huDegree hmDegree huMem hI)
  · exact infinityVerticalGraphLine_marked u E hu huDegree hmDegree huMem
      (reciprocal_constant_nonzero D a b h0 hm)

theorem exists_reciprocal_saturated_data
    (D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 +
          C (a : N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : N13IrreducibleQuadraticSpread.Q₂) :
        N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw
          N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          N13IrreducibleQuadraticSpread.Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  rcases
      N13IrreducibleQuadraticSpread.exists_reciprocalGraphClosure_or_verticalGraph
        D hdeg h0 a b hm with
    hhorizontal | ⟨E, hmDegree, hI⟩
  · obtain ⟨E⟩ := hhorizontal
    exact
      ReciprocalGraphClosure.exists_saturated_data
        E hdeg h0 hm
  · exact
      verticalGraph_exists_saturated_data
        hdeg h0 hm E hmDegree hI

theorem exists_saturated_data_of_irreducible
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  rcases
      N13IrreducibleQuadraticFinite.contractQuotient_finite_or_integral_reciprocal
          D hdeg hirr with
    hfinite | ⟨h0, a, b, hm⟩
  · exact exists_saturated_data_of_finite D hdeg hfinite
  · exact
      exists_reciprocal_saturated_data
        D hdeg h0 a b hm

theorem exists_saturated_twoChartLine_and_specialDivisor_of_distinct_split
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x₁) *
      (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal ∧
        N13TwoChartPicardRealization.AffineVerticallySaturated L ∧
        HasInfinityMultiplicities L 0 0 := by
  obtain ⟨hsextic₁, hsextic₂⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x₁ x₂ hfactor
  let y₁ :=
    N13TwoChartLineTensor.goodY x₁ (D.v.eval x₁)
  let y₂ :=
    N13TwoChartLineTensor.goodY x₂ (D.v.eval x₂)
  have hcurve₁ :
      N13GoodModelTwo.AffineEquation x₁ y₁ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₁ (D.v.eval x₁) hsextic₁
  have hcurve₂ :
      N13GoodModelTwo.AffineEquation x₂ y₂ :=
    N13TwoChartLineTensor.goodY_onCurve
      x₂ (D.v.eval x₂) hsextic₂
  let L :=
    N13QuadraticTwoChartSpread.pairLine
      x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  let Δ :=
    reducedPairDivisor x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  refine ⟨L, Δ, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [L]
    rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
      N13TwoChartLineTensor.pointY_goodY,
      N13TwoChartLineTensor.pointY_goodY,
      N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
        D hdeg x₁ x₂ hfactor hneq]
  · exact
      restrict_pairLine_affineIdeal
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact
      restrict_pairLine_infinityIdeal
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact
      N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated
        x₁ y₁ x₂ y₂ hcurve₁ hcurve₂
  · exact pairLine_marked x₁ y₁ x₂ y₂ hcurve₁ hcurve₂

theorem exists_saturated_data_of_distinct_split
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity, hsaturated, hmarked⟩ :=
    exists_saturated_twoChartLine_and_specialDivisor_of_distinct_split
      D hdeg x₁ x₂ hfactor hneq
  let R :=
    dataOfSpecialRealization D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity hsaturated
  · exact hmarked

theorem exists_saturated_twoChartLine_and_specialDivisor_of_repeated_root
    (D : SexticMumford.Mumford N13QuadraticTwoChartSpread.Model)
    (x : Q₂)
    (hfactor : D.u = (Polynomial.X - Polynomial.C x) ^ 2) :
    ∃ L : N13QuadraticTwoChartSpread.TwoChartLine,
      ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal
            N13QuadraticTwoChartSpread.Model D.u D.v ∧
        (N13TwoChartSpecialRestriction.restrict L).affineIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal ∧
        (N13TwoChartSpecialRestriction.restrict L).infinityIdeal =
          (N13SpecialDivisorCharts.ofDivisor Δ).infinityIdeal ∧
        N13TwoChartPicardRealization.AffineVerticallySaturated L ∧
        HasInfinityMultiplicities L 0 0 := by
  have hfactorMul :
      D.u = (Polynomial.X - Polynomial.C x) *
        (Polynomial.X - Polynomial.C x) := by
    simpa only [pow_two] using hfactor
  obtain ⟨hsextic, _⟩ :=
    N13TwoChartLineTensor.mumford_eval_onCurve_of_split
      D x x hfactorMul
  let y :=
    N13TwoChartLineTensor.goodY x (D.v.eval x)
  have hcurve :
      N13GoodModelTwo.AffineEquation x y :=
    N13TwoChartLineTensor.goodY_onCurve
      x (D.v.eval x) hsextic
  let L :=
    N13QuadraticTwoChartSpread.pairLine
      x y x y hcurve hcurve
  let Δ :=
    reducedPairDivisor x y x y hcurve hcurve
  refine ⟨L, Δ, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [L]
    rw [N13QuadraticTwoChartSpread.map_pairLine_affineIdeal,
      N13TwoChartLineTensor.pointY_goodY, ← pow_two,
      N13RepeatedRootSpread.pointIdeal_sq_eq_mumfordIdeal_of_square
        N13QuadraticTwoChartSpread.Model D x hfactor]
  · exact
      restrict_pairLine_affineIdeal
        x y x y hcurve hcurve
  · exact
      restrict_pairLine_infinityIdeal
        x y x y hcurve hcurve
  · exact
      N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated
        x y x y hcurve hcurve
  · exact pairLine_marked x y x y hcurve hcurve

theorem exists_saturated_data_of_repeated_root
    (D : SexticMumford.Mumford Model)
    (x : N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x) ^ 2) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder
            N13TwoChartPicardRealization.Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  obtain ⟨L, Δ, hmap, haffine, hinfinity, hsaturated, hmarked⟩ :=
    exists_saturated_twoChartLine_and_specialDivisor_of_repeated_root
      D x hfactor
  let R :=
    dataOfSpecialRealization D L Δ haffine hinfinity
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact
      dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity hsaturated
  · exact hmarked

theorem exists_saturated_data
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2) :
    ∃ R : N13TwoChartPicardRealization.Data,
      N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        SexticMumford.mumfordRaw Model D ∧
      R.toGenericPic =
        SexticMumford.classOf
          Model
          (N13Infinity.positiveInfinityOrder Q₂)
          D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts 0 0 := by
  by_cases hirr : Irreducible D.u
  · exact exists_saturated_data_of_irreducible D hdeg hirr
  obtain ⟨c₁, c₂, hc₀, hc₁⟩ :=
    (D.u_monic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp
      hirr
  let x₁ : Q₂ := -c₁
  let x₂ : Q₂ := -c₂
  have hfactor :
      D.u = (X - C x₁) * (X - C x₂) := by
    have hc₂ : D.u.coeff 2 = 1 := by
      calc
        D.u.coeff 2 = D.u.coeff D.u.natDegree :=
          congrArg D.u.coeff hdeg.symm
        _ = 1 := D.u_monic.coeff_natDegree
    simp only [x₁, x₂, C_neg, sub_neg_eq_add]
    rw [D.u.as_sum_range_C_mul_X_pow, hdeg,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, hc₂, hc₀, hc₁, C_mul, C_add, C_1]
    ring
  by_cases hneq : x₁ ≠ x₂
  · exact
      exists_saturated_data_of_distinct_split
        D hdeg x₁ x₂ hfactor hneq
  · have heq : x₂ = x₁ := by
      apply not_ne_iff.mp
      exact fun h ↦ hneq h.symm
    have hfactorSquare :
        D.u = (X - C x₁) ^ 2 := by
      rw [heq] at hfactor
      simpa only [pow_two] using hfactor
    exact
      exists_saturated_data_of_repeated_root
        D x₁ hfactorSquare

end
end MazurProof.N13MarkedQuadraticExistence


