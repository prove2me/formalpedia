-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoSemiGraphRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RankTwoSemiGraphRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:05:27.012611+00:00
-- url     : https://prove2.me/theorems/2e0e9d0b-c4ed-4a55-99fc-a484d4129c68
-- title:
--   FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConcreteGraphRecovery_p0

set_option autoImplicit false




/-!
# Recovering an integral semigraph from a rank-two quotient basis

The graph-recovery algebra does not need a selected special divisor until
one asks for a particular vertical smoothness certificate.  A literal
integral quotient basis `{1,x}` already recovers a monic quadratic
generalized Mumford semigraph and identifies its graph ideal with the
canonical contraction.

This is the special-class-independent core needed for arbitrary proper
specialization.
-/

open Module
open Polynomial

namespace MazurProof.N13RankTwoSemiGraphRecovery

noncomputable section

abbrev R₂ : Type :=
  N13ConcreteGraphRecovery.R₂

abbrev IntegralRing : Type :=
  N13ConcreteGraphRecovery.IntegralRing

abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂

/-- A quotient basis `{1,x}` recovers the canonical contraction as a
literal integral monic quadratic graph ideal. -/
theorem exists_integral_semiGraph_of_basis
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
        N13TwoFiberNoEscape.pairFamily
          1
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13CanonicalContractionQuotient.integralX)) :
    ∃ E : SemiMumford₂,
      E.u.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) E.u E.v := by
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
    simpa [N13TwoFiberNoEscape.pairFamily] using h
  have hb1 : b 1 = xbar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily, xbar, I] using h
  letI : Module.Free R₂ B :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ B :=
    Module.Finite.of_basis b
  letI : Nontrivial B :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hy⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
      xbar ybar b hb0 hb1
  let u : R₂[X] :=
    (Algebra.lmul R₂ B xbar).charpoly
  let v : R₂[X] :=
    C a + C c * X
  have huMonic : u.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x xbar
  have huDegree : u.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      xbar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) =
        Ideal.span ({u} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
        xbar b hb0 hb1
  have hyv : ybar = aeval xbar v := by
    calc
      ybar =
          algebraMap R₂ B a +
            algebraMap R₂ B c * xbar := hy
      _ = aeval xbar v := by
        simp [v]
  have hI :=
    N13RankTwoIdealRecovery.ideal_eq_span_aeval_y_sub
      (R := R₂)
      N13CanonicalContractionQuotient.integralX
      N13ConcreteGraphRecovery.integralY I u v
      N13ConcreteGraphRecovery.integral_rankTwoPolynomialNormalForm
      hker hyv
  have hIgraph :
      I =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    simpa [N13GeneralizedMumfordIntegral.mumfordIdeal,
      N13GeneralizedMumfordIntegral.ySubClass,
      N13ConcreteGraphRecovery.integralY,
      N13ConcreteGraphRecovery.aeval_integralX] using hI
  let residual : R₂[X] :=
    v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
      N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)
  have hresGraph :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    have hyMem :
        N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v ∈
          N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v :=
      N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v
    have hprod :
        N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v *
            N13GeneralizedMumfordIntegral.ySubClass
              (R := R₂)
              (N13GeneralizedMumfordIntegral.conjugateV v) ∈
          N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v :=
      Ideal.mul_mem_right _ _ hyMem
    rw [N13GeneralizedMumfordIntegral.ySubClass_mul_conjugateV_raw]
      at hprod
    have hneg :=
      (N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) u v).neg_mem hprod
    simpa [residual] using hneg
  have hresI :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈ I := by
    rw [hIgraph]
    exact hresGraph
  have hresEval :
      aeval xbar residual = 0 := by
    rw [N13ConcreteGraphRecovery.quotient_aeval_integralX]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hresI
  have hresKer :
      residual ∈
        RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) :=
    RingHom.mem_ker.mpr hresEval
  rw [hker, Ideal.mem_span_singleton] at hresKer
  obtain ⟨w, hw⟩ := hresKer
  have hcurve :
      v ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
          u * w := by
    simpa [residual] using hw
  let E : SemiMumford₂ :=
    { u := u
      v := v
      w := w
      u_monic := huMonic
      curve_eq := hcurve }
  refine ⟨E, huDegree, ?_⟩
  exact hIgraph

end

end MazurProof.N13RankTwoSemiGraphRecovery


