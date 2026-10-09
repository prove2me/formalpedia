-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoInfinityGraphRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RankTwoInfinityGraphRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:09:43.031989+00:00
-- url     : https://prove2.me/theorems/c45df49e-ba16-4344-a0e9-18ac77930985
-- title:
--   FLT.Assumptions.MazurProof.N13RankTwoInfinityGraphRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RankTwoInfinityGraphRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoInfinityGraphRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoInfinityVerticalGraphRecovery_p0

set_option autoImplicit false




/-!
# Rank-two horizontal recovery on the N13 infinity chart

A quotient basis `{1,t}` recovers a monic quadratic horizontal relation
and a linear ordinate.  The infinity curve equation then supplies the
Cantor quotient, so the original ideal is literally a bounded integral
infinity semigraph.
-/

open Module
open Polynomial

namespace MazurProof.N13RankTwoInfinityGraphRecovery

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralInfinityChart.R₂

abbrev InfinityCurve : Type :=
  N13IntegralInfinityChart.InfinityCurve

abbrev GraphData : Type :=
  N13IntegralInfinityGraphTwoChart.GraphData

/-- A literal quotient basis `{1,t}` recovers a bounded monic quadratic
semigraph and identifies the original infinity ideal with its graph ideal. -/
theorem exists_graphData_of_basis
    (I : Ideal InfinityCurve)
    (b : Basis (Fin 2) R₂ (InfinityCurve ⧸ I))
    (hb :
      (b : Fin 2 → InfinityCurve ⧸ I) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.tClass)) :
    ∃ E : GraphData,
      E.u.Monic ∧
      E.u.natDegree = 2 ∧
      E.v.natDegree ≤ 1 ∧
      E.w.natDegree ≤ 4 ∧
      I = N13IntegralInfinityGraphTwoChart.infinityIdeal E := by
  let tbar : InfinityCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13IntegralInfinityChart.tClass
  let vbar : InfinityCurve ⧸ I :=
    Ideal.Quotient.mk I
      N13IntegralInfinityChart.vClass
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX] using h
  have hb1 : b 1 = tbar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX, tbar] using h
  letI : Module.Free R₂ (InfinityCurve ⧸ I) :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ (InfinityCurve ⧸ I) :=
    Module.Finite.of_basis b
  letI : Nontrivial (InfinityCurve ⧸ I) :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hv⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
      tbar vbar b hb0 hb1
  let u : R₂[X] :=
    (Algebra.lmul R₂ (InfinityCurve ⧸ I) tbar).charpoly
  let v : R₂[X] :=
    C a + C c * X
  have huMonic : u.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x tbar
  have huDegree : u.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      tbar b hb0 hb1
  have hvDegree : v.natDegree ≤ 1 := by
    dsimp only [v]
    compute_degree <;> norm_num
  have hker :
      RingHom.ker
          ((aeval tbar : R₂[X] →ₐ[R₂]
            InfinityCurve ⧸ I).toRingHom) =
        Ideal.span ({u} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
        tbar b hb0 hb1
  have hvv : vbar = aeval tbar v := by
    calc
      vbar =
          algebraMap R₂ (InfinityCurve ⧸ I) a +
            algebraMap R₂ (InfinityCurve ⧸ I) c * tbar := hv
      _ = aeval tbar v := by simp [v]
  have hI :=
    N13RankTwoIdealRecovery.ideal_eq_span_aeval_y_sub
      (R := R₂)
      N13IntegralInfinityChart.tClass
      N13IntegralInfinityChart.vClass
      I u v
      N13RankTwoInfinityVerticalGraphRecovery.rankTwoPolynomialNormalForm
      hker hvv
  let residual : R₂[X] :=
    v ^ 2 +
      N13IntegralInfinityChart.hBase * v -
      N13IntegralInfinityChart.rhsBase
  have hresDegree : residual.natDegree ≤ 4 := by
    dsimp only [residual, v,
      N13IntegralInfinityChart.hBase,
      N13IntegralInfinityChart.rhsBase]
    compute_degree <;> norm_num
  have hresEval :
      aeval tbar residual = 0 := by
    have hcurve :=
      congrArg (Ideal.Quotient.mk I)
        N13IntegralInfinityVerticalGraphJacobian.curve_eval
    change
      vbar ^ 2 +
          (1 + tbar ^ 2 + tbar ^ 3) * vbar -
          (tbar + tbar ^ 2) =
        0 at hcurve
    rw [hvv] at hcurve
    simpa [residual, N13IntegralInfinityChart.hBase,
      N13IntegralInfinityChart.rhsBase] using hcurve
  have hresKer :
      residual ∈
        RingHom.ker
          ((aeval tbar : R₂[X] →ₐ[R₂]
            InfinityCurve ⧸ I).toRingHom) :=
    RingHom.mem_ker.mpr hresEval
  rw [hker, Ideal.mem_span_singleton] at hresKer
  obtain ⟨w, hw⟩ := hresKer
  have hcurve :
      v ^ 2 +
          N13IntegralInfinityChart.hBase * v -
          N13IntegralInfinityChart.rhsBase =
        u * w := by
    simpa [residual] using hw
  have hwDegree : w.natDegree ≤ 4 := by
    by_cases hw0 : w = 0
    · simp [hw0]
    · rw [show residual = u * w by
          simpa [residual] using hcurve,
        natDegree_mul huMonic.ne_zero hw0,
        huDegree] at hresDegree
      omega
  let E : GraphData :=
    { u := u
      v := v
      w := w
      curve_eq := hcurve }
  refine
    ⟨E, huMonic, huDegree, hvDegree, hwDegree, ?_⟩
  simpa [N13IntegralInfinityGraphTwoChart.infinityIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass,
    N13IntegralInfinityGraphJacobian.xClassHom,
    N13IntegralInfinityGraphJacobian.yClass,
    N13IntegralInfinityPointSpread.xClassHom,
    N13IntegralInfinityPointSpread.yClass,
    N13IntegralInfinityReduction.integralBaseClass,
    N13RankTwoInfinityVerticalGraphRecovery.aeval_tClass,
    E] using hI

/-- The horizontal basis branch already produces an actual two-chart line,
with the recovered infinity ideal as its infinity component. -/
theorem exists_twoChartLine_of_basis
    (I : Ideal InfinityCurve)
    (b : Basis (Fin 2) R₂ (InfinityCurve ⧸ I))
    (hb :
      (b : Fin 2 → InfinityCurve ⧸ I) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk I
            N13IntegralInfinityChart.tClass)) :
    ∃ L : N13IntegralInfinityPointSpread.TwoChartLine,
      I = L.infinityIdeal := by
  obtain ⟨E, huMonic, huDegree, hvDegree, hwDegree, hI⟩ :=
    exists_graphData_of_basis I b hb
  have huDegreeLe : E.u.natDegree ≤ 2 := by
    omega
  have hvDegreeLe : E.v.natDegree ≤ 3 := by
    omega
  let L :=
    N13IntegralInfinityGraphTwoChart.twoChartLine
      E huDegreeLe hvDegreeLe hwDegree huMonic.ne_zero
  exact ⟨L, hI⟩

end

end MazurProof.N13RankTwoInfinityGraphRecovery


