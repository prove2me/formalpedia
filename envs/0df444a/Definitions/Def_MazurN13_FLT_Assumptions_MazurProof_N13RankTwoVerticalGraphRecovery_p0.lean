-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalGraphRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalGraphRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:07:27.433679+00:00
-- url     : https://prove2.me/theorems/14391fde-0bd4-4893-b05c-a3973f28d4e8
-- title:
--   FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConcreteGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteFlatBasisLift_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalIdealRecovery_p0

set_option autoImplicit false




open Module
open Polynomial

/-!
# Vertical graph recovery from a `{1,y}` basis

A rank-two quotient basis `{1,y}` recovers a monic quadratic relation
`m(y)` and a linear equation `x=a+cy`.  Substituting the latter into the
integral curve equation shows that the vertical curve polynomial factors
as `m*w`.
-/

namespace MazurProof.N13RankTwoVerticalGraphRecovery

noncomputable section

abbrev R₂ : Type := N13ConcreteGraphRecovery.R₂
abbrev IntegralRing : Type :=
  N13ConcreteGraphRecovery.IntegralRing
abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model

def verticalCurve (s : R₂[X]) : R₂[X] :=
  X ^ 2 +
    (N13GeneralizedMumfordIntegral.hPoly (R := R₂)).comp s * X -
    (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)).comp s

structure VerticalGraph where
  m : R₂[X]
  a : R₂
  c : R₂
  w : R₂[X]
  m_monic : m.Monic
  curve_eq :
    verticalCurve (C a + C c * X) = m * w

namespace VerticalGraph

def s (E : VerticalGraph) : R₂[X] :=
  C E.a + C E.c * X

def ideal (E : VerticalGraph) : Ideal IntegralRing :=
  Ideal.span
    ({aeval N13ConcreteGraphRecovery.integralY E.m,
      N13CanonicalContractionQuotient.integralX -
        aeval N13ConcreteGraphRecovery.integralY E.s} :
      Set IntegralRing)

end VerticalGraph

theorem quotient_aeval_integralY
    (I : Ideal IntegralRing) (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13ConcreteGraphRecovery.integralY) p =
      Ideal.Quotient.mk I
        (aeval N13ConcreteGraphRecovery.integralY p) := by
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := R₂) (S := IntegralRing) (T := R₂)
      (U := IntegralRing ⧸ I)
      (φ := RingHom.id R₂)
      (ψ := Ideal.Quotient.mk I)
      (by ext; simp) p
      N13ConcreteGraphRecovery.integralY).symm

theorem exists_verticalGraph_of_basis
    (D : SexticMumford.SemiMumford Model)
    (b : Basis (Fin 2) R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D)))
    (hb :
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13ConcreteGraphRecovery.integralY)) :
    ∃ E : VerticalGraph,
      E.m.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        E.ideal := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let xbar : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let ybar : B :=
    Ideal.Quotient.mk I
      N13ConcreteGraphRecovery.integralY
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX] using h
  have hb1 : b 1 = ybar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX, ybar, I] using h
  letI : Module.Free R₂ B :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ B :=
    Module.Finite.of_basis b
  letI : Nontrivial B :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hx⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
      ybar xbar b hb0 hb1
  let m : R₂[X] :=
    (Algebra.lmul R₂ B ybar).charpoly
  let s : R₂[X] :=
    C a + C c * X
  have hmMonic : m.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x ybar
  have hmDegree : m.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      ybar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval ybar : R₂[X] →ₐ[R₂] B).toRingHom) =
        Ideal.span ({m} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
        ybar b hb0 hb1
  have hxs : xbar = aeval ybar s := by
    calc
      xbar =
          algebraMap R₂ B a +
            algebraMap R₂ B c * ybar := hx
      _ = aeval ybar s := by simp [s]
  have hnormal :
      N13RankTwoVerticalIdealRecovery.HasVerticalPolynomialNormalForm
        (R := R₂)
        N13ConcreteGraphRecovery.integralY
        N13CanonicalContractionQuotient.integralX s :=
    N13RankTwoVerticalIdealRecovery.verticalNormalForm_of_rankTwoPolynomialNormalForm
      N13CanonicalContractionQuotient.integralX
      N13ConcreteGraphRecovery.integralY
      N13ConcreteGraphRecovery.integral_rankTwoPolynomialNormalForm
      s
  have hI :=
    N13RankTwoVerticalIdealRecovery.ideal_eq_span_vertical
      (R := R₂)
      N13ConcreteGraphRecovery.integralY
      N13CanonicalContractionQuotient.integralX
      I m s hnormal hker hxs
  have hverticalEval :
      aeval ybar (verticalCurve s) = 0 := by
    simp only [verticalCurve, map_sub, map_add, map_mul,
      map_pow, aeval_X, aeval_comp]
    rw [← hxs,
      N13ConcreteGraphRecovery.quotient_aeval_integralX,
      N13ConcreteGraphRecovery.quotient_aeval_integralX]
    change
      Ideal.Quotient.mk I
          (N13ConcreteGraphRecovery.integralY ^ 2) +
        Ideal.Quotient.mk I
            (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) *
          Ideal.Quotient.mk I
            N13ConcreteGraphRecovery.integralY -
        Ideal.Quotient.mk I
          (N13GeneralizedMumfordIntegral.xClass
            (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
        0
    have hcurve :=
      N13GeneralizedMumfordIntegral.yClass_relation (R := R₂)
    have hcurveQ :
        Ideal.Quotient.mk I
              ((N13GeneralizedMumfordIntegral.yClass (R := R₂)) ^ 2) +
            Ideal.Quotient.mk I
                (N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) *
              Ideal.Quotient.mk I
                (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
          Ideal.Quotient.mk I
            (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) := by
      simpa only [map_add, map_mul] using
        congrArg (Ideal.Quotient.mk I) hcurve
    exact sub_eq_zero.mpr
      (by
        simpa only [N13ConcreteGraphRecovery.integralY] using
          hcurveQ)
  have hverticalKer :
      verticalCurve s ∈
        RingHom.ker
          ((aeval ybar : R₂[X] →ₐ[R₂] B).toRingHom) :=
    RingHom.mem_ker.mpr hverticalEval
  rw [hker, Ideal.mem_span_singleton] at hverticalKer
  obtain ⟨w, hw⟩ := hverticalKer
  have hcurve :
      verticalCurve s = m * w := hw
  let E : VerticalGraph :=
    { m := m
      a := a
      c := c
      w := w
      m_monic := hmMonic
      curve_eq := by simpa [s] using hcurve }
  refine ⟨E, hmDegree, ?_⟩
  simpa [VerticalGraph.ideal, VerticalGraph.s, E, s] using hI

end

end MazurProof.N13RankTwoVerticalGraphRecovery


