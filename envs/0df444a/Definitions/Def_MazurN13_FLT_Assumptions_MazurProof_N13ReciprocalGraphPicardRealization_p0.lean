-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalGraphPicardRealization_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalGraphPicardRealization_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:14:17.904419+00:00
-- url     : https://prove2.me/theorems/890d1a1a-df51-4717-a9c0-f3863caa5c00
-- title:
--   FLT.Assumptions.MazurProof.N13ReciprocalGraphPicardRealization source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ReciprocalGraphPicardRealization

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ReciprocalGraphPicardRealization
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSpecialRestriction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSaturation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticSpread_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SplitQuadraticPicardRealization_p0

set_option autoImplicit false




/-!
# Picard realization of reciprocal horizontal N13 graphs

The direct-kernel horizontal branch of an irreducible quadratic supplies a
monic integral graph on the infinity chart.  Its weighted two-chart line
has the prescribed generic Mumford ideal, while its reduction is the
canonical chart pair of the completed special root divisor.  This file
packages those two exact comparisons as two-fibre Picard data without
forgetting either boundary chart.
-/

open Polynomial

namespace MazurProof.N13ReciprocalGraphPicardRealization

noncomputable section

/-- The proper line attached to a recovered horizontal reciprocal graph is
vertically saturated on the affine chart.  Reflection of its monic
quadratic infinity graph has a torsion-free integral quotient, as proved by
the infinity-graph saturation theorem. -/
theorem ReciprocalGraphClosure.twoChartLine_affineVerticallySaturated
    {D : SexticMumford.Mumford
      N13IrreducibleQuadraticSpread.Model}
    {a b : N13IrreducibleQuadraticSpread.R₂}
    (E : N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13IntegralInfinityGraphTwoChart.twoChartLine
        E.data (by
          rw [E.data_u]
          exact
            (N13ReciprocalQuadraticReflection.integralReciprocal_natDegree
              a b).le) E.v_degree E.w_degree (by
          rw [E.data_u]
          exact
            (N13ReciprocalQuadraticReflection.integralReciprocal_monic
              a b).ne_zero)) := by
  have huMonic : E.data.u.Monic := by
    rw [E.data_u]
    exact
      N13ReciprocalQuadraticReflection.integralReciprocal_monic a b
  have huDegree : E.data.u.natDegree = 2 := by
    rw [E.data_u]
    exact
      N13ReciprocalQuadraticReflection.integralReciprocal_natDegree a b
  intro r hr z hz
  change
    algebraMap N13IntegralModelContraction.R₂
        N13IntegralModelContraction.IntegralRing r * z ∈
      N13IntegralInfinityGraphTwoChart.affineIdeal E.data at hz
  change z ∈ N13IntegralInfinityGraphTwoChart.affineIdeal E.data
  exact
    N13IntegralInfinityGraphSaturation.affineIdeal_scalarSaturated
      E.data huMonic huDegree E.v_degree r hr z hz

/-- A recovered reciprocal horizontal graph realizes the original generic
quadratic class and a literal effective degree-two divisor on the special
fibre. -/
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
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts := by
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
  refine ⟨R, ?_, ?_, ?_⟩
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
        D L Δ haffine hinfinity hmap
  · exact
      N13SplitQuadraticPicardRealization.dataOfSpecialRealization_affineVerticallySaturated
        D L Δ haffine hinfinity
        (ReciprocalGraphClosure.twoChartLine_affineVerticallySaturated E)

/-- Forgetting vertical saturation recovers the original reciprocal
horizontal realization interface. -/
theorem ReciprocalGraphClosure.exists_data
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
          D := by
  obtain ⟨R, hraw, hgeneric, _⟩ :=
    ReciprocalGraphClosure.exists_saturated_data E hdeg h0 hm
  exact ⟨R, hraw, hgeneric⟩

end

end MazurProof.N13ReciprocalGraphPicardRealization


