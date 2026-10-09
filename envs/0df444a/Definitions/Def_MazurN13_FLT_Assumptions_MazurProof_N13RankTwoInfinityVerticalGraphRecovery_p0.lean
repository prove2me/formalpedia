-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoInfinityVerticalGraphRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RankTwoInfinityVerticalGraphRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T18:54:59.777524+00:00
-- url     : https://prove2.me/theorems/636fa263-971a-42bf-9b9b-92520d11f073
-- title:
--   FLT.Assumptions.MazurProof.N13RankTwoInfinityVerticalGraphRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RankTwoInfinityVerticalGraphRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoInfinityVerticalGraphRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteFlatBasisLift_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityVerticalGraphJacobian_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoVerticalIdealRecovery_p0

set_option autoImplicit false




/-!
# Rank-two vertical recovery on the N13 infinity chart

The ordinary infinity ring has the polynomial normal form
`p(t) + q(t)v`.  If a quotient has literal two-adic basis `{1,v}`, then
multiplication by `v` recovers a monic quadratic `m(v)` and the class of
`t` is a linear polynomial `a+cv`.  The generic vertical ideal-recovery
theorem identifies the original ideal with this graph, while the curve
equation supplies its complementary factor.
-/

open Module
open Polynomial

namespace MazurProof.N13RankTwoInfinityVerticalGraphRecovery

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev VerticalGraph : Type :=
  N13IntegralInfinityVerticalGraphJacobian.VerticalGraph

theorem aeval_tClass
    (p : R₂[X]) :
    aeval N13IntegralInfinityChart.tClass p =
      N13IntegralInfinityReduction.integralBaseClass p := by
  let f : R₂[X] →+* InfinityCurve :=
    (aeval N13IntegralInfinityChart.tClass).toRingHom
  let g : R₂[X] →+* InfinityCurve :=
    algebraMap R₂[X] InfinityCurve
  have hfg : f = g := by
    ext r
    · dsimp only [f, g]
      change
        (aeval N13IntegralInfinityChart.tClass :
          R₂[X] →ₐ[R₂] InfinityCurve) (C r) =
        algebraMap R₂[X] InfinityCurve (C r)
      rw [Polynomial.aeval_C]
      exact
        IsScalarTower.algebraMap_apply
          R₂ R₂[X] InfinityCurve r
    · dsimp only [f, g]
      change
        (aeval N13IntegralInfinityChart.tClass :
          R₂[X] →ₐ[R₂] InfinityCurve) X =
        algebraMap R₂[X] InfinityCurve X
      rw [aeval_X]
      rfl
  exact DFunLike.congr_fun hfg p

/-- The ordinary infinity coordinate ring has the generic polynomial
normal form required by both horizontal and vertical ideal recovery. -/
theorem rankTwoPolynomialNormalForm :
    N13RankTwoIdealRecovery.HasRankTwoPolynomialNormalForm
      (R := R₂)
      N13IntegralInfinityChart.tClass
      N13IntegralInfinityChart.vClass := by
  intro z
  refine
    ⟨N13IntegralInfinityReduction.integralCoeff0 z,
      N13IntegralInfinityReduction.integralCoeffV z, ?_⟩
  rw [aeval_tClass, aeval_tClass]
  exact N13IntegralInfinityReduction.integral_recompose z |>.symm

theorem quotient_aeval_vClass
    (I : Ideal InfinityCurve)
    (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13IntegralInfinityChart.vClass) p =
      Ideal.Quotient.mk I
        (aeval N13IntegralInfinityChart.vClass p) := by
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := R₂) (S := InfinityCurve) (T := R₂)
      (U := InfinityCurve ⧸ I)
      (φ := RingHom.id R₂)
      (ψ := Ideal.Quotient.mk I)
      (by ext; simp) p
      N13IntegralInfinityChart.vClass).symm

/-- A literal quotient basis `{1,v}` recovers an exact integral vertical
graph on the infinity chart. -/
theorem exists_verticalGraph_of_basis
    (I : Ideal InfinityCurve)
    (b : Basis (Fin 2) R₂ (InfinityCurve ⧸ I))
    (hb :
      (b : Fin 2 → InfinityCurve ⧸ I) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.vClass)) :
    ∃ E : VerticalGraph,
      E.m.natDegree = 2 ∧ I = E.ideal := by
  let tbar : InfinityCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13IntegralInfinityChart.tClass
  let vbar : InfinityCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13IntegralInfinityChart.vClass
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX] using h
  have hb1 : b 1 = vbar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX, vbar] using h
  letI : Module.Free R₂ (InfinityCurve ⧸ I) :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ (InfinityCurve ⧸ I) :=
    Module.Finite.of_basis b
  letI : Nontrivial (InfinityCurve ⧸ I) :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, ht⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
      vbar tbar b hb0 hb1
  let m : R₂[X] :=
    (Algebra.lmul R₂ (InfinityCurve ⧸ I) vbar).charpoly
  let s : R₂[X] :=
    C a + C c * X
  have hmMonic : m.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x vbar
  have hmDegree : m.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      vbar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval vbar : R₂[X] →ₐ[R₂]
            InfinityCurve ⧸ I).toRingHom) =
        Ideal.span ({m} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
        vbar b hb0 hb1
  have hts : tbar = aeval vbar s := by
    calc
      tbar =
          algebraMap R₂ (InfinityCurve ⧸ I) a +
            algebraMap R₂ (InfinityCurve ⧸ I) c * vbar := ht
      _ = aeval vbar s := by simp [s]
  have hnormal :
      N13RankTwoVerticalIdealRecovery.HasVerticalPolynomialNormalForm
        (R := R₂)
        N13IntegralInfinityChart.vClass
        N13IntegralInfinityChart.tClass s :=
    N13RankTwoVerticalIdealRecovery.verticalNormalForm_of_rankTwoPolynomialNormalForm
      N13IntegralInfinityChart.tClass
      N13IntegralInfinityChart.vClass
      rankTwoPolynomialNormalForm s
  have hI :=
    N13RankTwoVerticalIdealRecovery.ideal_eq_span_vertical
      (R := R₂)
      N13IntegralInfinityChart.vClass
      N13IntegralInfinityChart.tClass
      I m s hnormal hker hts
  have hverticalEval :
      aeval vbar
          (N13IntegralInfinityVerticalGraphJacobian.verticalCurve s) =
        0 := by
    simp only [N13IntegralInfinityVerticalGraphJacobian.verticalCurve,
      map_sub, map_add, map_mul, map_pow,
      aeval_X, aeval_comp]
    rw [← hts]
    have hcurve :=
      congrArg (Ideal.Quotient.mk I)
        N13IntegralInfinityVerticalGraphJacobian.curve_eval
    change
      (Ideal.Quotient.mk I
          N13IntegralInfinityChart.vClass) ^ 2 +
          (1 +
              (Ideal.Quotient.mk I
                N13IntegralInfinityChart.tClass) ^ 2 +
              (Ideal.Quotient.mk I
                N13IntegralInfinityChart.tClass) ^ 3) *
            (Ideal.Quotient.mk I
              N13IntegralInfinityChart.vClass) -
          (Ideal.Quotient.mk I
              N13IntegralInfinityChart.tClass +
            (Ideal.Quotient.mk I
              N13IntegralInfinityChart.tClass) ^ 2) =
        0 at hcurve
    simpa [N13IntegralInfinityChart.hBase,
      N13IntegralInfinityChart.rhsBase, tbar, vbar] using hcurve
  have hverticalKer :
      N13IntegralInfinityVerticalGraphJacobian.verticalCurve s ∈
        RingHom.ker
          ((aeval vbar : R₂[X] →ₐ[R₂]
            InfinityCurve ⧸ I).toRingHom) :=
    RingHom.mem_ker.mpr hverticalEval
  rw [hker, Ideal.mem_span_singleton] at hverticalKer
  obtain ⟨w, hw⟩ := hverticalKer
  let E :
      N13IntegralInfinityVerticalGraphJacobian.VerticalGraph :=
    { m := m
      a := a
      c := c
      w := w
      m_monic := hmMonic
      curve_eq := by simpa [s] using hw }
  refine ⟨E, hmDegree, ?_⟩
  simpa [
    N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal,
    N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityGraphJacobian.yClass,
    N13IntegralInfinityPointSpread.yClass,
    E, s] using hI

end

end MazurProof.N13RankTwoInfinityVerticalGraphRecovery


