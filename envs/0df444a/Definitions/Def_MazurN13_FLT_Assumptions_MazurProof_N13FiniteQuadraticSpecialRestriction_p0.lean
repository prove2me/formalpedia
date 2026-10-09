-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteQuadraticSpecialRestriction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FiniteQuadraticSpecialRestriction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:43:21.823377+00:00
-- url     : https://prove2.me/theorems/9b122515-9428-4ccd-961d-c19275265dfd
-- title:
--   FLT.Assumptions.MazurProof.N13FiniteQuadraticSpecialRestriction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FiniteQuadraticSpecialRestriction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FiniteQuadraticSpecialRestriction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ContractQuotientXYBasis_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoSemiGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineVerticalGraph_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinitySaturation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuadraticGraphRegularity_p0

set_option autoImplicit false




/-!
# Special restriction of finite irreducible N13 quadratics

A finite canonical contraction is finite flat of rank two.  The existing
coordinate-basis theorem chooses either the literal basis `{1,x}` or
`{1,y}`.  The first basis recovers an integral horizontal semigraph; the
second recovers an integral vertical graph.

After reduction, a horizontal graph gives its canonical special root
divisor.  A vertical graph has reduced slope zero or one: slope zero gives
the canonical two-sheet fibre over `x=a`, while slope one translates to a
horizontal graph.  In every case the reduced affine ideal is canonical.
The reflected monic equation makes `t` invertible modulo the source
infinity closure, and the same property holds for the target finite
divisor.  Infinity-chart saturation therefore upgrades the affine equality
to equality of the complete chart pair.
-/

open Module
open Polynomial

namespace MazurProof.N13FiniteQuadraticSpecialRestriction

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The two-adic coefficient ring. -/
abbrev R₂ :=
  N13IntegralModelContraction.R₂

/-- The special residue field. -/
abbrev K :=
  N13GoodCoordinateRingTwo.K

/-- The integral affine coordinate ring. -/
abbrev IntegralRing :=
  N13IntegralModelContraction.IntegralRing

/-- The generic sextic model. -/
abbrev Model :=
  N13CanonicalContractionQuotient.Model

/-- Integral vertical graph data recovered from a `{1,y}` basis. -/
abbrev VerticalGraph :=
  N13RankTwoVerticalGraphRecovery.VerticalGraph

/-- Reduction commutes with evaluation at the integral affine ordinate
class `y`. -/
theorem reduce_aeval_integralY (p : R₂[X]) :
    N13GeneralizedMumfordReduction.reduceCoordinate
        (aeval N13ConcreteGraphRecovery.integralY p) =
      aeval N13GoodCoordinateRingTwo.yClass
        (N13GeneralizedMumfordReduction.reducePoly p) := by
  change
    N13GeneralizedMumfordReduction.reduceCoordinate
        (aeval N13GeneralizedMumfordIntegral.yClass p) =
      aeval N13GoodCoordinateRingTwo.yClass
        (N13GeneralizedMumfordReduction.reducePoly p)
  have h :=
    Polynomial.map_aeval_eq_aeval_map
      (R := R₂)
      (S := IntegralRing)
      (T := K)
      (U := N13GeneralizedMumfordReduction.SpecialRing)
      (φ := N13GeneralizedMumfordReduction.reduceBase)
      (ψ := N13GeneralizedMumfordReduction.reduceCoordinate)
      (by
        ext r
        change
          N13GoodCoordinateRingTwo.xClass
              (C (N13GeneralizedMumfordReduction.reduceBase r)) =
            N13GeneralizedMumfordReduction.reduceCoordinate
              (N13GeneralizedMumfordIntegral.xClass (C r))
        rw [N13GeneralizedMumfordReduction.reduce_xClass]
        simp [N13GeneralizedMumfordReduction.reducePoly])
      p N13GeneralizedMumfordIntegral.yClass
  rw [N13GeneralizedMumfordReduction.reduce_yClass] at h
  simpa only [
    N13GeneralizedMumfordReduction.reducePoly_apply] using h

/-- Coefficient reduction commutes with the vertical substitution equation
on the affine chart. -/
theorem reduce_verticalCurve
    (s : R₂[X]) :
    N13GeneralizedMumfordReduction.reducePoly
        (N13RankTwoVerticalGraphRecovery.verticalCurve s) =
      N13SpecialAffineVerticalGraph.verticalCurve
        (N13GeneralizedMumfordReduction.reducePoly s) := by
  rw [N13RankTwoVerticalGraphRecovery.verticalCurve,
    N13SpecialAffineVerticalGraph.verticalCurve]
  change
    (X ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly.comp s * X -
        N13GeneralizedMumfordIntegral.rhsPoly.comp s).map
          N13GeneralizedMumfordReduction.reduceBase =
      _
  simp only [Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_comp]
  rw [show
      N13GeneralizedMumfordIntegral.hPoly.map
          N13GeneralizedMumfordReduction.reduceBase =
        N13GoodCoordinateRingTwo.hPoly from
      N13GeneralizedMumfordReduction.reduce_hPoly,
    show
      N13GeneralizedMumfordIntegral.rhsPoly.map
          N13GeneralizedMumfordReduction.reduceBase =
        N13GoodCoordinateRingTwo.rhsPoly from
      N13GeneralizedMumfordReduction.reduce_rhsPoly]
  rfl

/-- The recovered integral vertical factorization reduces to the
corresponding special factorization. -/
theorem reduced_vertical_curve_eq
    (E : VerticalGraph) :
    N13SpecialAffineVerticalGraph.verticalCurve
          (C (N13GeneralizedMumfordReduction.reduceBase E.a) +
            C (N13GeneralizedMumfordReduction.reduceBase E.c) * X) =
      N13GeneralizedMumfordReduction.reducePoly E.m *
        N13GeneralizedMumfordReduction.reducePoly E.w := by
  have h :=
    congrArg
      N13GeneralizedMumfordReduction.reducePoly E.curve_eq
  rw [reduce_verticalCurve] at h
  simpa [N13RankTwoVerticalGraphRecovery.VerticalGraph.s,
    N13GeneralizedMumfordReduction.reducePoly] using h

/-- The reduced vertical quadratic remains monic. -/
theorem reduced_vertical_m_monic
    (E : VerticalGraph) :
    (N13GeneralizedMumfordReduction.reducePoly E.m).Monic :=
  E.m_monic.map N13GeneralizedMumfordReduction.reduceBase

/-- A monic recovered vertical quadratic retains degree two after
reduction. -/
theorem reduced_vertical_m_natDegree
    (E : VerticalGraph)
    (hdeg : E.m.natDegree = 2) :
    (N13GeneralizedMumfordReduction.reducePoly E.m).natDegree = 2 := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    E.m_monic.natDegree_map, hdeg]

/-- Reducing a recovered integral vertical ideal gives its literal special
vertical graph ideal. -/
theorem map_verticalIdeal
    (E : VerticalGraph) :
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate E.ideal =
      N13SpecialAffineVerticalGraph.verticalIdeal
        (N13GeneralizedMumfordReduction.reducePoly E.m)
        (N13GeneralizedMumfordReduction.reduceBase E.a)
        (N13GeneralizedMumfordReduction.reduceBase E.c) := by
  rw [N13RankTwoVerticalGraphRecovery.VerticalGraph.ideal,
    N13SpecialAffineVerticalGraph.verticalIdeal,
    Ideal.map_span, Set.image_pair]
  simp only [map_sub, reduce_aeval_integralY]
  congr 2
  simp [N13RankTwoVerticalGraphRecovery.VerticalGraph.s,
    N13GeneralizedMumfordReduction.reducePoly,
    N13CanonicalContractionQuotient.integralX]

/-- The reduced infinity closure of a finite affine ideal is
`t`-saturated. -/
theorem finiteLine_infinity_tUnitMod
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    N13SpecialInfinitySaturation.TUnitMod
      (N13TwoChartSpecialRestriction.restrict
        (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
          D hdeg hfinite)).infinityIdeal := by
  apply
    N13SpecialInfinitySaturation.map_reduceCoordinate_tUnitMod
  exact
    N13FiniteAffineTwoChart.infinityClosure_tUnitMod_of_finite
      (N13FiniteAffineTwoChart.finiteAffineIdeal D) hfinite

/-- A finite quadratic canonical contraction restricts to the complete
canonical chart pair of a literal effective degree-two special divisor. -/
theorem exists_specialDivisor_of_finiteQuadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (N13FiniteAffineTwoChart.AffineCurve ⧸
          N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    ∃ Δ : N13SpecialDivisorCharts.EffectiveDivisorTwo,
      N13TwoChartSpecialRestriction.restrict
          (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine
            D hdeg hfinite) =
        N13SpecialDivisorCharts.ofDivisor Δ := by
  rcases
      N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
        D hdeg hfinite with hx | hy
  · obtain ⟨b, hb⟩ := hx
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13TwoFiberNoEscape.pairFamily
            1
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13CanonicalContractionQuotient.integralX) := by
      simpa [N13FiniteFlatBasisLift.oneX,
        N13TwoFiberNoEscape.pairFamily] using hb
    obtain ⟨E, hEdeg, hI⟩ :=
      N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
        D b hb'
    let Ebar :=
      N13SpecialQuadraticGraphRegularity.reduceSemiMumford E hEdeg
    let hEbarDeg :=
      N13SpecialQuadraticGraphRegularity.reduceSemiMumford_u_natDegree
        E hEdeg
    let Δ :=
      N13SpecialGraphDivisor.graphDivisor Ebar hEbarDeg
    refine ⟨Δ, ?_⟩
    apply
      N13SpecialInfinitySaturation.chartPair_eq_of_affineIdeal_eq
    · exact finiteLine_infinity_tUnitMod D hdeg hfinite
    · exact
        N13SpecialInfinitySaturation.graphDivisor_infinity_tUnitMod
          Ebar hEbarDeg
    · change
        Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
            (N13FiniteAffineTwoChart.finiteAffineIdeal D) =
          (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal
      rw [N13FiniteAffineTwoChart.finiteAffineIdeal, hI]
      exact
        N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal
          E hEdeg
  · obtain ⟨b, hb⟩ := hy
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13FiniteFlatBasisLift.oneX
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13ConcreteGraphRecovery.integralY) := by
      simpa [N13ContractQuotientXYBasis.integralY,
        N13ConcreteGraphRecovery.integralY] using hb
    obtain ⟨E, hmDegree, hI⟩ :=
      N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
        D b hb'
    rcases
        N13GoodModelTwo.fixedTwo_eq_zero_or_one
          (N13GeneralizedMumfordReduction.reduceBase E.c)
          (ZMod.pow_card
            (N13GeneralizedMumfordReduction.reduceBase E.c)) with hc | hc
    · let Δ :=
        N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl
            (N13GeneralizedMumfordReduction.reduceBase E.a))
      refine ⟨Δ, ?_⟩
      apply
        N13SpecialInfinitySaturation.chartPair_eq_of_affineIdeal_eq
      · exact finiteLine_infinity_tUnitMod D hdeg hfinite
      · exact
          N13SpecialInfinitySaturation.canonicalDivisor_infinity_tUnitMod
            (N13GeneralizedMumfordReduction.reduceBase E.a)
      · change
          Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
              (N13FiniteAffineTwoChart.finiteAffineIdeal D) =
            (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal
        rw [N13FiniteAffineTwoChart.finiteAffineIdeal, hI,
          map_verticalIdeal, hc,
          N13SpecialAffineVerticalGraph.verticalIdeal_eq_span_of_slope_zero
              (N13GeneralizedMumfordReduction.reducePoly E.m)
              (N13GeneralizedMumfordReduction.reducePoly E.w)
              (N13GeneralizedMumfordReduction.reduceBase E.a)
              (reduced_vertical_m_monic E)
              (reduced_vertical_m_natDegree E hmDegree)
              (by
                simpa [hc] using reduced_vertical_curve_eq E),
          N13SpecialVerticalDivisorCharts.canonicalDivisor_affineIdeal]
    · let mbar :=
        N13GeneralizedMumfordReduction.reducePoly E.m
      let wbar :=
        N13GeneralizedMumfordReduction.reducePoly E.w
      let abar :=
        N13GeneralizedMumfordReduction.reduceBase E.a
      let hcurve :
          N13SpecialAffineVerticalGraph.verticalCurve
              (C abar + X) =
            mbar * wbar := by
        simpa [mbar, wbar, abar, hc] using
          reduced_vertical_curve_eq E
      let Ebar :=
        N13SpecialAffineVerticalGraph.horizontalGraph
          mbar wbar abar (reduced_vertical_m_monic E)
            (reduced_vertical_m_natDegree E hmDegree) hcurve
      let hEbarDeg :=
        N13SpecialAffineVerticalGraph.horizontalGraph_u_natDegree
          mbar wbar abar (reduced_vertical_m_monic E)
            (reduced_vertical_m_natDegree E hmDegree) hcurve
      let Δ :=
        N13SpecialGraphDivisor.graphDivisor Ebar hEbarDeg
      refine ⟨Δ, ?_⟩
      apply
        N13SpecialInfinitySaturation.chartPair_eq_of_affineIdeal_eq
      · exact finiteLine_infinity_tUnitMod D hdeg hfinite
      · exact
          N13SpecialInfinitySaturation.graphDivisor_infinity_tUnitMod
            Ebar hEbarDeg
      · change
          Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
              (N13FiniteAffineTwoChart.finiteAffineIdeal D) =
            (N13SpecialDivisorCharts.ofDivisor Δ).affineIdeal
        rw [N13FiniteAffineTwoChart.finiteAffineIdeal, hI,
          map_verticalIdeal, hc,
          N13SpecialAffineVerticalGraph.verticalIdeal_eq_mumfordIdeal_of_slope_one,
          N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal]
        rfl

end

end MazurProof.N13FiniteQuadraticSpecialRestriction


