-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticSpread_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticSpread_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:50:38.93783+00:00
-- url     : https://prove2.me/theorems/18fa3367-cfa1-4b58-9ff7-6d754a496c27
-- title:
--   FLT.Assumptions.MazurProof.N13IrreducibleQuadraticSpread source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IrreducibleQuadraticSpread

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IrreducibleQuadraticSpread
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteContractIdealInvertible_p2
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticFinite_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSaturation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphContraction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalInfinityContraction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalQuadraticReflection_p0

set_option autoImplicit false




/-!
# Proper spreads for irreducible N13 quadratics

An irreducible quadratic Mumford graph lies in one of the two ordinary
proper charts.  In the finite branch, a monic equation in the finite
quotient patches the canonical affine contraction across the infinity
uniformizer.  In the escaping branch, the literal integral reciprocal
equation gives a horizontal or vertical infinity graph.  Both cases now
produce an invertible two-chart line with the exact generic graph ideal.
-/

open Polynomial

namespace MazurProof.N13IrreducibleQuadraticSpread

noncomputable section

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model

abbrev InfinityGraphData : Type :=
  N13IntegralInfinityGraphTwoChart.GraphData

abbrev TwoChartLine : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine

/-- The exact remaining datum on the reciprocal chart.  Its horizontal
equation is the integral reciprocal quadratic, its other two equations
have the weighted bounds needed for two-chart reflection, and its reflected
ordinate cuts out the original generic Mumford graph. -/
structure ReciprocalGraphClosure
    (D : SexticMumford.Mumford Model)
    (a b : R₂) where
  data : InfinityGraphData
  data_u :
    data.u =
      N13ReciprocalQuadraticReflection.integralReciprocal a b
  v_degree : data.v.natDegree ≤ 3
  w_degree : data.w.natDegree ≤ 4
  generic_ordinate :
    D.u ∣
      N13GoodSexticMumfordTransport.completedGraph
          (N13TwoAdicCoordinateBaseChange.mapPoly
            (N13IntegralInfinityGraphTwoChart.affineV data)) -
        D.v

/-- The canonical direct-kernel construction closes the horizontal
reciprocal branch outright.  Its only alternative is the literal vertical
rank-two graph on the infinity chart. -/
theorem exists_reciprocalGraphClosure_or_verticalGraph
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    Nonempty (ReciprocalGraphClosure D a b) ∨
      (∃ E :
          N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
        E.m.natDegree = 2 ∧
        N13ReciprocalInfinityContraction.integralInfinityIdeal
            D hdeg h0 =
          E.ideal) := by
  rcases
      N13ReciprocalInfinityContraction.exists_horizontal_or_vertical_recovery
        D hdeg h0 a b hm with
    ⟨E, hu, _huMonic, _huDegree, hvDegree, hwDegree, _hI,
      hordinate⟩ |
    hvertical
  · left
    exact
      ⟨{
        data := E
        data_u := hu
        v_degree := hvDegree.trans (by omega)
        w_degree := hwDegree
        generic_ordinate := hordinate
      }⟩
  · exact Or.inr hvertical

/-- An irreducible quadratic graph already has an invertible affine
divisorial spread unless its reciprocal monic equation is integral on the
infinity chart. -/
theorem divisorialHull_isUnit_or_integral_reciprocal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      (D.u.coeff 0 ≠ 0 ∧
        ∃ a b : R₂,
          (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (D.u.coeff 1 / D.u.coeff 0) * X +
              C ((D.u.coeff 0)⁻¹)) := by
  rcases
      N13IrreducibleQuadraticFinite.contractQuotient_finite_or_integral_reciprocal
        D hdeg hirr with hfinite | hreciprocal
  · exact Or.inl
      (N13FiniteContractIdealInvertible.divisorialHull_graphIdeal_isUnit_of_finite_quadratic
        D.toSemi hdeg hfinite)
  · exact Or.inr hreciprocal

/-- In the escaping branch, the integral reciprocal equation already has
the correct affine weighted horizontal closure: after coefficient
extension it is the original Mumford equation multiplied by the inverse
constant term. -/
theorem divisorialHull_isUnit_or_reciprocal_closure
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      ∃ a b : R₂,
        let m :=
          N13ReciprocalQuadraticReflection.integralReciprocal a b
        m.Monic ∧
          m.natDegree = 2 ∧
          N13TwoAdicCoordinateBaseChange.mapPoly (m.reflect 2) =
            C ((D.u.coeff 0)⁻¹) * D.u := by
  rcases
      divisorialHull_isUnit_or_integral_reciprocal
        D hdeg hirr with hunit | hreciprocal
  · exact Or.inl hunit
  · right
    obtain ⟨h0, a, b, hm⟩ := hreciprocal
    refine ⟨a, b, ?_, ?_, ?_⟩
    · exact
        N13ReciprocalQuadraticReflection.integralReciprocal_monic
          a b
    · exact
        N13ReciprocalQuadraticReflection.integralReciprocal_natDegree
          a b
    · exact
        N13ReciprocalQuadraticReflection.mapPoly_reflect_integralReciprocal
          D hdeg h0 a b hm

/-- A recovered reciprocal semigraph gives an invertible two-chart line
whose affine generic fibre is exactly the original Mumford graph. -/
theorem ReciprocalGraphClosure.exists_twoChartLine
    {D : SexticMumford.Mumford Model}
    {a b : R₂}
    (E : ReciprocalGraphClosure D a b)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
  have huDegree : E.data.u.natDegree ≤ 2 := by
    rw [E.data_u,
      N13ReciprocalQuadraticReflection.integralReciprocal_natDegree]
  have huNonzero : E.data.u ≠ 0 := by
    rw [E.data_u]
    exact
      (N13ReciprocalQuadraticReflection.integralReciprocal_monic
        a b).ne_zero
  let L :=
    N13IntegralInfinityGraphTwoChart.twoChartLine
      E.data huDegree E.v_degree E.w_degree huNonzero
  refine ⟨L, ?_⟩
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13IntegralInfinityGraphTwoChart.affineIdeal E.data) =
      SexticMumford.mumfordIdeal Model D.u D.v
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

/-- The direct reciprocal-kernel construction always supplies a proper
two-chart spread of the original quadratic Mumford graph.  The recovered
rank-two quotient may use either the horizontal basis `{1,t}` or the
vertical basis `{1,v}`; the two recovery theorems now package both cases
with the same exact generic-ideal conclusion. -/
theorem exists_reciprocal_twoChartLine
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
  rcases
      exists_reciprocalGraphClosure_or_verticalGraph
        D hdeg h0 a b hm with
    hhorizontal | ⟨E, hmDegree, hI⟩
  · obtain ⟨E⟩ := hhorizontal
    exact E.exists_twoChartLine hdeg h0 hm
  · let u :=
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
    obtain ⟨L, _hInfinity, hGeneric⟩ :=
      N13IntegralInfinityVerticalGraphContraction.exists_twoChartLine
        D hdeg h0 u E hu huDegree hmDegree huMem hI
    exact ⟨L, hGeneric⟩

/-- Every irreducible quadratic graph is now covered by one of the two
explicit integral models needed downstream: a finite affine divisorial
spread, or a proper two-chart line with the exact generic graph ideal.
No reciprocal-chart recovery hypothesis remains in this dichotomy. -/
theorem divisorialHull_isUnit_or_exists_twoChartLine
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      ∃ L : TwoChartLine,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal Model D.u D.v := by
  rcases
      divisorialHull_isUnit_or_integral_reciprocal
        D hdeg hirr with
    hfinite | ⟨h0, a, b, hm⟩
  · exact Or.inl hfinite
  · exact Or.inr
      (exists_reciprocal_twoChartLine D hdeg h0 a b hm)

/-- Every irreducible quadratic Mumford graph has a proper integral
two-chart spread.  Finite affine support is closed by contraction through
the ordinary overlap; escaping support is closed by the reciprocal
horizontal-or-vertical recovery. -/
theorem exists_twoChartLine
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    ∃ L : TwoChartLine,
      Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          L.affineIdeal =
        SexticMumford.mumfordIdeal Model D.u D.v := by
  rcases
      N13IrreducibleQuadraticFinite.contractQuotient_finite_or_integral_reciprocal
        D hdeg hirr with
    hfinite | ⟨h0, a, b, hm⟩
  · let L :=
      N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
        D.toSemi hdeg hfinite
    refine ⟨L, ?_⟩
    exact
      N13FiniteAffineTwoChart.map_finiteQuadraticTwoChartLine_affineIdeal
        D.toSemi hdeg hfinite
  · exact exists_reciprocal_twoChartLine D hdeg h0 a b hm

/-- A recovered reciprocal semigraph is not merely an arbitrary
two-chart lattice: its reflected affine ideal is vertically saturated,
so it is the canonical contraction of the original generic graph. -/
theorem ReciprocalGraphClosure.divisorialHull_isUnit
    {D : SexticMumford.Mumford Model}
    {a b : R₂}
    (E : ReciprocalGraphClosure D a b)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) := by
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
  apply
    N13IntegralInfinityGraphSaturation.divisorialHull_isUnit_of_reciprocalGraph
        (N13CanonicalContractionQuotient.graphIdeal D.toSemi)
        E.data huMonic huDegree E.v_degree E.w_degree
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

/-- The irreducible quadratic branch is therefore closed by exactly one
reciprocal-chart recovery statement.  No affine factoriality or special
Picard-class hypothesis remains in this interface. -/
theorem divisorialHull_isUnit_or_has_reciprocalGraphLine
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u)
    (recover :
      ∀ a b : R₂,
        (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (D.u.coeff 1 / D.u.coeff 0) * X +
              C ((D.u.coeff 0)⁻¹) →
          ReciprocalGraphClosure D a b) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      ∃ L : TwoChartLine,
        Ideal.map
            N13TwoAdicCoordinateBaseChange.integralToSextic
            L.affineIdeal =
          SexticMumford.mumfordIdeal Model D.u D.v := by
  rcases
      divisorialHull_isUnit_or_integral_reciprocal
        D hdeg hirr with hunit | ⟨h0, a, b, hm⟩
  · exact Or.inl hunit
  · exact Or.inr
      ((recover a b hm).exists_twoChartLine hdeg h0 hm)

/-- The reciprocal recovery hypothesis closes the irreducible quadratic
branch completely: both the finite and escaping cases have invertible
canonical divisorial spread. -/
theorem divisorialHull_isUnit_of_reciprocalGraphRecovery
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u)
    (recover :
      ∀ a b : R₂,
        (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (D.u.coeff 1 / D.u.coeff 0) * X +
              C ((D.u.coeff 0)⁻¹) →
          ReciprocalGraphClosure D a b) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) := by
  rcases
      divisorialHull_isUnit_or_integral_reciprocal
        D hdeg hirr with hunit | ⟨h0, a, b, hm⟩
  · exact hunit
  · exact (recover a b hm).divisorialHull_isUnit hdeg h0 hm

/-- The unconditional direct-kernel construction reduces the entire
irreducible quadratic case to the vertical infinity-graph alternative. -/
theorem divisorialHull_isUnit_or_verticalGraph
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    IsUnit
        (N13IntegralFractionalHull.divisorialHull
          (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      ∃ a b : R₂,
        ∃ h0 : D.u.coeff 0 ≠ 0,
        (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
          X ^ 2 +
            C (D.u.coeff 1 / D.u.coeff 0) * X +
            C ((D.u.coeff 0)⁻¹) ∧
        ∃ E :
            N13IntegralInfinityVerticalGraphJacobian.VerticalGraph,
          E.m.natDegree = 2 ∧
          N13ReciprocalInfinityContraction.integralInfinityIdeal
              D hdeg h0 =
            E.ideal := by
  rcases
      divisorialHull_isUnit_or_integral_reciprocal
        D hdeg hirr with
    hunit | ⟨h0, a, b, hm⟩
  · exact Or.inl hunit
  · rcases
      exists_reciprocalGraphClosure_or_verticalGraph
        D hdeg h0 a b hm with
      hclosure | hvertical
    · obtain ⟨E⟩ := hclosure
      exact Or.inl (E.divisorialHull_isUnit hdeg h0 hm)
    · exact Or.inr ⟨a, b, h0, hm, hvertical⟩

/-- Every irreducible quadratic Mumford graph has an invertible canonical
divisorial spread; the direct-kernel vertical alternative is closed by its
three-generated affine contraction. -/
theorem divisorialHull_isUnit
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull
        (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) := by
  rcases
      divisorialHull_isUnit_or_verticalGraph D hdeg hirr with
    hunit | ⟨a, b, h0, hm, E, hmDegree, hI⟩
  · exact hunit
  · exact
      N13IntegralInfinityVerticalGraphContraction.divisorialHull_isUnit
        D hdeg h0 a b hm E hmDegree hI

end

end MazurProof.N13IrreducibleQuadraticSpread


