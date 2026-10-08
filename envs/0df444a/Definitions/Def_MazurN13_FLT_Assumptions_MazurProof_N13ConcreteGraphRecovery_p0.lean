-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConcreteGraphRecovery_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ConcreteGraphRecovery_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:01:15.454018+00:00
-- url     : https://prove2.me/theorems/b3cc5c23-993c-475d-81f5-880bceabd16b
-- title:
--   FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RankTwoIdealRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberConcreteBasis_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelCompatibleGraphRecover_p0
import Mathlib.RingTheory.Polynomial.Resultant.Basic

set_option autoImplicit false




/-!
# Recovering the integral N13 graph from the concrete two-fibre basis

The literal basis `{1,x}` turns multiplication by `x` into a monic
characteristic polynomial of degree two.  Expressing the quotient class of
`y` in that basis then recovers the canonical contraction literally as a
generalized Mumford graph ideal.
-/

open Module
open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13ConcreteGraphRecovery

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

/-- Equal graph ideals with equal infinity multiplicity define the same
oriented Picard class.  This is the literal representative-level form of
the separatedness used below. -/
theorem semiMumfordClass_eq_of_graphIdeal_eq
    (D₁ D₂ : SexticMumford.SemiMumford Model)
    (hideal :
      N13CanonicalContractionQuotient.graphIdeal D₁ =
        N13CanonicalContractionQuotient.graphIdeal D₂)
    (hnInf : D₁.nInf = D₂.nInf) :
    SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D₁ =
      SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D₂ := by
  unfold SexticMumford.semiMumfordClass
  congr 2
  apply Prod.ext
  · apply Units.ext
    change
      (N13CanonicalContractionQuotient.graphIdeal D₁ :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model)) =
        (N13CanonicalContractionQuotient.graphIdeal D₂ :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model))
    exact congrArg
      (fun I : Ideal
          (SexticMumford.CoordinateRing Model) ↦
        (I :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model)))
      hideal
  · unfold SexticMumford.semiMumfordRaw
    rw [hnInf]

/-- The integral affine `y` coordinate. -/
def integralY : IntegralRing :=
  N13GeneralizedMumfordIntegral.yClass (R := R₂)

/-- Evaluation at the integral affine `x` coordinate is the coordinate
embedding of the polynomial subring. -/
@[simp] theorem aeval_integralX (p : R₂[X]) :
    aeval N13CanonicalContractionQuotient.integralX p =
      N13GeneralizedMumfordIntegral.xClass (R := R₂) p := by
  change
    aeval
        (algebraMap R₂[X] IntegralRing X) p =
      algebraMap R₂[X] IntegralRing p
  simpa using
    aeval_algebraMap_apply IntegralRing
      (X : R₂[X]) p

/-- Polynomial evaluation commutes with passage to any quotient of the
integral affine ring. -/
theorem quotient_aeval_integralX
    (I : Ideal IntegralRing) (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) p =
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) := by
  rw [← aeval_integralX]
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := R₂) (S := IntegralRing) (T := R₂)
      (U := IntegralRing ⧸ I)
      (φ := RingHom.id R₂)
      (ψ := Ideal.Quotient.mk I)
      (by ext; simp) p
      N13CanonicalContractionQuotient.integralX).symm

/-- The integral affine ring has polynomial normal form in `x,y`. -/
theorem integral_rankTwoPolynomialNormalForm :
    N13RankTwoIdealRecovery.HasRankTwoPolynomialNormalForm
      (R := R₂)
      N13CanonicalContractionQuotient.integralX integralY := by
  intro z
  refine
    ⟨N13GeneralizedMumfordIntegral.coeff0 z,
      N13GeneralizedMumfordIntegral.coeffY z, ?_⟩
  rw [aeval_integralX, aeval_integralX]
  exact
    (N13GeneralizedMumfordIntegral.recompose z).symm

/-- The remaining special-ideal equality forces the canonical contraction
to be a literal monic quadratic graph ideal. -/
theorem exists_integral_smoothGraph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ E : SmoothMumford₂,
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
    Ideal.Quotient.mk I integralY
  obtain ⟨b, hb⟩ :=
    N13TwoFiberConcreteBasis.exists_contractQuotient_basis
      D hdeg hmap
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
      integralY I u v
      integral_rankTwoPolynomialNormalForm hker hyv
  have hIgraph :
      I =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    simpa [N13GeneralizedMumfordIntegral.mumfordIdeal,
      N13GeneralizedMumfordIntegral.ySubClass,
      integralY,
      aeval_integralX] using hI
  have hvDegree : v.natDegree ≤ 1 := by
    unfold v
    compute_degree
  let residual : R₂[X] :=
    v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
      N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)
  have hresGraph :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    have hy :
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
      Ideal.mul_mem_right _ _ hy
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
    rw [quotient_aeval_integralX]
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
  have hmapGraph :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v) =
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hIgraph]
    exact hmap
  have hspecialGraph :
      N13GoodCoordinateRingTwo.mumfordIdeal
          (N13GeneralizedMumfordReduction.reducePoly u)
          (N13GeneralizedMumfordReduction.reducePoly v) =
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← N13GeneralizedMumfordReduction.map_mumfordIdeal]
    exact hmapGraph
  have hxmem :
      N13GoodCoordinateRingTwo.xClass
          (N13GeneralizedMumfordReduction.reducePoly u) ∈
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hspecialGraph]
    exact
      N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
        (N13GeneralizedMumfordReduction.reducePoly u)
        (N13GeneralizedMumfordReduction.reducePoly v)
  have hxker :
      N13GoodCoordinateRingTwo.xClass
          (N13GeneralizedMumfordReduction.reducePoly u) ∈
        RingHom.ker
          (N13GoodCoordinateRingTwo.mumfordEval
            N13SpecialQuotientBasis.specialData) := by
    rw [N13GoodCoordinateRingTwo.ker_mumfordEval]
    exact hxmem
  have hbaseDvdU :=
    RingHom.mem_ker.mp hxker
  rw [N13GoodCoordinateRingTwo.mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hbaseDvdU
  have hreduceU :
      N13GeneralizedMumfordReduction.reducePoly u =
        (X ^ 2 + X : N13GeneralizedMumfordReduction.K[X]) := by
    have huReduceMonic :
        (N13GeneralizedMumfordReduction.reducePoly u).Monic :=
      huMonic.map N13GeneralizedMumfordReduction.reduceBase
    have huReduceDegree :
        (N13GeneralizedMumfordReduction.reducePoly u).natDegree = 2 := by
      change
        (u.map N13GeneralizedMumfordReduction.reduceBase).natDegree = 2
      rw [huMonic.natDegree_map, huDegree]
    have heq :
        N13GeneralizedMumfordReduction.reducePoly u =
          N13SpecialQuotientBasis.specialData.u :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        N13SpecialQuotientBasis.specialData.u_monic
        huReduceMonic hbaseDvdU
        (by
          rw [huReduceDegree,
            N13SpecialQuotientBasis.specialData_u_natDegree])
    simpa only [N13SpecialQuotientBasis.specialData_u] using heq
  have hymem :
      N13GoodCoordinateRingTwo.ySubClass
          (N13GeneralizedMumfordReduction.reducePoly v) ∈
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hspecialGraph]
    exact
      N13GoodCoordinateRingTwo.ySubClass_mem_mumfordIdeal
        (N13GeneralizedMumfordReduction.reducePoly u)
        (N13GeneralizedMumfordReduction.reducePoly v)
  have hyker :
      N13GoodCoordinateRingTwo.ySubClass
          (N13GeneralizedMumfordReduction.reducePoly v) ∈
        RingHom.ker
          (N13GoodCoordinateRingTwo.mumfordEval
            N13SpecialQuotientBasis.specialData) := by
    rw [N13GoodCoordinateRingTwo.ker_mumfordEval]
    exact hymem
  have hyzero :=
    RingHom.mem_ker.mp hyker
  have hbaseDvdNegV :
      N13SpecialQuotientBasis.specialData.u ∣
        -N13GeneralizedMumfordReduction.reducePoly v := by
    simp only [N13GoodCoordinateRingTwo.ySubClass, map_sub,
      N13GoodCoordinateRingTwo.mumfordEval_yClass,
      N13GoodCoordinateRingTwo.mumfordEval_xClass,
      N13SpecialQuotientBasis.specialData_v, map_zero,
      zero_sub] at hyzero
    change
        Ideal.Quotient.mk
            (Ideal.span
              ({N13SpecialQuotientBasis.specialData.u} :
                Set N13GeneralizedMumfordReduction.K[X]))
            (-N13GeneralizedMumfordReduction.reducePoly v) =
          0 at hyzero
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hyzero)
  have hbaseDvdV :
      N13SpecialQuotientBasis.specialData.u ∣
        N13GeneralizedMumfordReduction.reducePoly v := by
    simpa only [dvd_neg] using hbaseDvdNegV
  have hreduceV :
      N13GeneralizedMumfordReduction.reducePoly v = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hbaseDvdV
    calc
      (N13GeneralizedMumfordReduction.reducePoly v).natDegree ≤
          v.natDegree :=
        Polynomial.natDegree_map_le
      _ ≤ 1 := hvDegree
      _ < 2 := by omega
      _ =
          N13SpecialQuotientBasis.specialData.u.natDegree :=
        N13SpecialQuotientBasis.specialData_u_natDegree.symm
  let g : R₂[X] :=
    2 * v +
      N13GeneralizedMumfordIntegral.hPoly (R := R₂)
  have hgMonic : g.Monic := by
    unfold g v N13GeneralizedMumfordIntegral.hPoly
    monicity <;> norm_num
  have hreduceG :
      N13GeneralizedMumfordReduction.reducePoly g =
        N13GoodCoordinateRingTwo.hPoly := by
    change
      g.map N13GeneralizedMumfordReduction.reduceBase =
        N13GoodCoordinateRingTwo.hPoly
    unfold g
    rw [Polynomial.map_add, Polynomial.map_mul]
    have htwoPoly :
        (2 : N13GeneralizedMumfordReduction.K[X]) = 0 :=
      CharP.cast_eq_zero
        (N13GeneralizedMumfordReduction.K[X]) 2
    rw [show
        (2 : R₂[X]).map
            N13GeneralizedMumfordReduction.reduceBase =
          (2 : N13GeneralizedMumfordReduction.K[X]) by simp,
      htwoPoly, zero_mul, zero_add]
    exact N13GeneralizedMumfordReduction.reduce_hPoly
  have hcoprimeSpecial :
      IsCoprime
        (N13GeneralizedMumfordReduction.reducePoly u)
        (N13GeneralizedMumfordReduction.reducePoly g) := by
    rw [hreduceU, hreduceG]
    refine ⟨X - 1, 1, ?_⟩
    have htwoPoly :
        (2 : N13GeneralizedMumfordReduction.K[X]) = 0 :=
      CharP.cast_eq_zero
        (N13GeneralizedMumfordReduction.K[X]) 2
    calc
      (X - 1) * (X ^ 2 + X) +
          1 * N13GoodCoordinateRingTwo.hPoly =
        2 * X ^ 3 + 1 := by
          simp only [N13GoodCoordinateRingTwo.hPoly]
          ring
      _ = 1 := by rw [htwoPoly, zero_mul, zero_add]
  have hresultantSpecialUnit :
      IsUnit
        ((N13GeneralizedMumfordReduction.reducePoly u).resultant
          (N13GeneralizedMumfordReduction.reducePoly g)) :=
    (Polynomial.isUnit_resultant_iff_isCoprime
      (huMonic.map
        N13GeneralizedMumfordReduction.reduceBase)).2
      hcoprimeSpecial
  have hresultantMap :
      (N13GeneralizedMumfordReduction.reducePoly u).resultant
          (N13GeneralizedMumfordReduction.reducePoly g) =
        N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g) := by
    change
      (u.map N13GeneralizedMumfordReduction.reduceBase).resultant
          (g.map N13GeneralizedMumfordReduction.reduceBase) =
        N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g)
    simpa only [
      huMonic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase,
      hgMonic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase] using
      Polynomial.resultant_map_map
        (f := u) (g := g)
        (m := u.natDegree) (n := g.natDegree)
        N13GeneralizedMumfordReduction.reduceBase
  have hresultantReduceUnit :
      IsUnit
        (N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g)) := by
    rw [← hresultantMap]
    exact hresultantSpecialUnit
  have hresultantReduceOne :
      N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g) = 1 := by
    let z :=
      N13GeneralizedMumfordReduction.reduceBase
        (u.resultant g)
    have hzFixed : z ^ 2 = z :=
      ZMod.pow_card z
    rcases
        N13GoodModelTwo.fixedTwo_eq_zero_or_one z hzFixed with
      hz | hz
    · exact
        (hresultantReduceUnit.ne_zero hz).elim
    · exact hz
  have hresultantUnit :
      IsUnit (u.resultant g) :=
    N13TwoAdicAbelChartRecover.NearBaseMumford.isUnit_of_reduceBase_eq_one
      hresultantReduceOne
  have hcoprime :
      IsCoprime u g :=
    (Polynomial.isUnit_resultant_iff_isCoprime huMonic).1
      hresultantUnit
  obtain ⟨a', b', hab⟩ := hcoprime
  let E : SmoothMumford₂ :=
    { u := u
      v := v
      w := w
      u_monic := huMonic
      curve_eq := hcurve
      bezout := ⟨a', b', 0, by simpa [g] using hab⟩ }
  refine ⟨E, huDegree, ?_⟩
  exact hIgraph

/-- The strengthened recovery already lands in the two-disk chart.  It also
recovers the original generic sextic graph after coefficient extension, so
no separate representative-existence hypothesis remains after the mapped
special-ideal equality. -/
theorem exists_integral_diskGraph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ E : SmoothMumford₂,
      ∃ P : N13TwoAdicAbelChartData.DiskPair,
        E.u.natDegree = 2 ∧
        N13CanonicalContractionQuotient.graphIdeal D =
          N13IntegralGraphContraction.sexticIdeal E D.nInf ∧
        N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v =
          N13GeneralizedMumfordIntegral.mumfordIdeal P.u P.v := by
  obtain ⟨E, hEdeg, hE⟩ :=
    exists_integral_smoothGraph D hdeg hmap
  have hmapE :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) E.u E.v) =
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hE]
    exact hmap
  let P :=
    N13AbelCompatibleGraphRecover.recoveredDiskPairOfMappedSpecial
      E hEdeg hmapE
  have hEP :
      N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v =
        N13GeneralizedMumfordIntegral.mumfordIdeal P.u P.v :=
    N13AbelCompatibleGraphRecover.mumfordIdeal_eq_recoveredDiskPairOfMappedSpecial
      E hEdeg hmapE
  refine ⟨E, P, hEdeg, ?_, hEP⟩
  calc
    N13CanonicalContractionQuotient.graphIdeal D =
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) :=
      (N13IntegralModelContraction.map_contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal D)).symm
    _ =
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v) := by
      rw [hE]
    _ = N13IntegralGraphContraction.sexticIdeal E D.nInf :=
      N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        E D.nInf

/-- A balanced quadratic representative whose canonical contraction has the
selected special graph is represented by an actual pair in the two
distinguished residue disks. -/
theorem exists_diskPair_class_eq
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ P : N13TwoAdicAbelChartData.DiskPair,
      SexticMumford.classOf
          Model (N13Infinity.positiveInfinityOrder Q₂) D =
        N13TwoAdicAbelChartPic.DiskPair.pic P := by
  have hdeg : D.u.natDegree = 2 :=
    N13TwoFiberConcreteBasis.degree_eq_two_of_map_contractIdeal_eq_special
      D.toSemi (by simpa using D.deg_u) hmap
  have hnInfNat : D.nInf = 0 := by
    have hbound := D.infinity_bound
    omega
  have hnInf : D.toSemi.nInf = 0 := by
    simp [hnInfNat]
  obtain ⟨E, P, _hEdeg, hgraph, hEP⟩ :=
    exists_integral_diskGraph D.toSemi (by simpa using hdeg) hmap
  have hEPsextic :
      N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi E 0) =
        N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0) := by
    change
      SexticMumford.mumfordIdeal Model
          (N13TwoAdicMumfordTransport.sexticSemi E 0).u
          (N13TwoAdicMumfordTransport.sexticSemi E 0).v =
        SexticMumford.mumfordIdeal Model
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0).u
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0).v
    rw [
      ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        E 0,
      ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        P.smoothMumford 0]
    exact congrArg
      (Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic)
      hEP
  have hgraphDP :
      N13CanonicalContractionQuotient.graphIdeal D.toSemi =
        N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi := by
    calc
      N13CanonicalContractionQuotient.graphIdeal D.toSemi =
          N13IntegralGraphContraction.sexticIdeal
            E D.toSemi.nInf := hgraph
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi E 0) := by
        rw [hnInf]
        rfl
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0) := hEPsextic
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi := rfl
  refine ⟨P, ?_⟩
  rw [← SexticMumford.semiMumfordClass_toSemi]
  change
    SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D.toSemi =
      SexticMumford.classOf
        Model (N13Infinity.positiveInfinityOrder Q₂)
          (N13TwoAdicAbelChartPic.DiskPair.mumford P)
  rw [← SexticMumford.semiMumfordClass_toSemi]
  apply semiMumfordClass_eq_of_graphIdeal_eq
    D.toSemi
      (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi
      hgraphDP
  simp [hnInfNat]

/-- Compatibility wrapper retaining the earlier polynomial-level output. -/
theorem exists_integral_graph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ u v : R₂[X],
      u.Monic ∧
      u.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
  obtain ⟨E, hEdeg, hE⟩ :=
    exists_integral_smoothGraph D hdeg hmap
  exact ⟨E.u, E.v, E.u_monic, hEdeg, hE⟩

end

end MazurProof.N13ConcreteGraphRecovery


