-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalZeroCarrierDlog_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalZeroCarrierDlog_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:28:00.406323+00:00
-- url     : https://prove2.me/theorems/2c0bb7b2-481c-491f-bdc7-a0e812e94892
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianGlobalZeroCarrierDlog source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianGlobalZeroCarrierDlog

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianGlobalZeroCarrierDlog
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianDifferentSupport_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNormalizedSquareclassSeam_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCandidateDlog_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalReductionTwo_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianLowDegree_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitSquareclasses_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FakeDescentAssembly_p0

set_option autoImplicit false




/-!
# Global zero-carrier classes and the first ramified logarithm

The global factorization of a normalized N13 Kummer integer is an exact
identity

`x = ε * y²`

in the maximal order.  The same maximal order has an actual reduction to the
first ramified quotient at two.  Reducing the identity therefore shows that
the logarithm of `ε` vanishes: the square contributes twice its logarithm,
while `x` is the evaluation of a primitive polynomial of degree at most two
and hence has a constant nonzero first jet.

This aligns the global named-unit coordinates with the local logarithm
without a valuation case split or a finite candidate search.
-/

open Polynomial

namespace MazurProof.N13GaussianGlobalZeroCarrierDlog

noncomputable section

open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses

abbrev LowRep := N13LowDegreeKummerHom.LowRep
abbrev Oi := N13GlobalKummerIdealSquare.O
abbrev On := N13GaussianNamedUnitSquareclasses.O
abbrev Order := N13GaussianOrderTwo.Order
abbrev Z2 := N13GaussianOrderTwo.Z2
abbrev F8 := N13LocalDlogTwo.F8
abbrev JetUnit := (DualNumber F8)ˣ

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldLg :
    Field N13GaussianCubicField.L :=
  AdjoinRoot.instField

/-- The globally primitive integral Mumford polynomial, base-changed to
`ℤ₂`. -/
def globalPrimitiveZ2 (D : LowRep) : Z2[X] :=
  (N13GlobalKummerNormalization.primitiveNormalization D.toSemi.u).map
    (algebraMap ℤ Z2)

theorem globalPrimitiveZ2_natDegree_le (D : LowRep) :
    (globalPrimitiveZ2 D).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans
    (N13GlobalKummerNormalization.normalizedKummerInteger_degree D)

/-- Global primitivity prevents all coefficients from vanishing modulo two
after base change to `ℤ₂`. -/
theorem residuePolynomial_globalPrimitiveZ2_ne_zero (D : LowRep) :
    residuePolynomial (globalPrimitiveZ2 D) ≠ 0 := by
  let U : ℤ[X] :=
    N13GlobalKummerNormalization.primitiveNormalization D.toSemi.u
  intro hzero
  have hle :
      (globalPrimitiveZ2 D).contentIdeal ≤
        RingHom.ker PadicInt.toZMod := by
    rw [Polynomial.contentIdeal_def, Ideal.span_le]
    intro z hz
    obtain ⟨n, -, rfl⟩ :=
      Polynomial.mem_coeffs_iff.mp hz
    change
      PadicInt.toZMod ((globalPrimitiveZ2 D).coeff n) = 0
    have hcoeff :=
      congrArg (fun q : (ZMod 2)[X] => q.coeff n) hzero
    simpa [residuePolynomial] using hcoeff
  have hprimitive : U.IsPrimitive :=
    N13GlobalKummerNormalization.primitiveNormalization_isPrimitive
      D.toSemi.u
  have htopU : U.contentIdeal = ⊤ :=
    (Polynomial.isPrimitive_iff_contentIdeal_eq_top U).mp hprimitive
  have htop :
      (globalPrimitiveZ2 D).contentIdeal = ⊤ := by
    rw [globalPrimitiveZ2,
      Polynomial.contentIdeal_map_eq_map_contentIdeal, htopU,
      Ideal.map_top]
  rw [htop, PadicInt.ker_toZMod] at hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal Z2).ne_top
      (top_unique hle)

/-- The exact first jet of the globally primitive polynomial. -/
def globalPrimitiveJet (D : LowRep) : JetUnit :=
  lowDegreeJet
    (globalPrimitiveZ2 D)
    (residuePolynomial_globalPrimitiveZ2_ne_zero D)
    (Polynomial.natDegree_map_le.trans
      (globalPrimitiveZ2_natDegree_le D))

theorem dlog_globalPrimitiveJet (D : LowRep) :
    RamifiedDlog.dlog (globalPrimitiveJet D) = 0 :=
  dlog_lowDegreeJet _ _ _

/-! ## The global integral evaluation in the explicit order -/

/-- The two maximal-order presentations send an integral polynomial
evaluation to the same carrier in the Gaussian cubic field. -/
theorem normalizationOrderEquiv_integralEval
    (U : ℤ[X]) :
    N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
        (N13GlobalKummerNormalization.integralEval U) =
      relativeToRingOfIntegers
        (eval₂
          (algebraMap ℤ
            N13GaussianGlobalReductionTwo.RelativeO)
          relativeTheta U) := by
  apply NumberField.RingOfIntegers.ext
  have hfun :
      N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
          (N13GlobalKummerNormalization.integralEval U) =
        N13GlobalKummerPID.integralClosureEquivClassNumberOrder.toFun
          (N13GlobalKummerNormalization.integralEval U) := rfl
  rw [hfun, N13GlobalKummerPID.coe_integralClosureEquivClassNumberOrder,
    N13GlobalKummerNormalization.coe_integralEval]
  have hrelative
      (z : N13GaussianGlobalReductionTwo.RelativeO) :
      (((relativeToRingOfIntegers z : On)) :
          N13GaussianCubicField.L) =
        algebraMap
          N13GaussianGlobalReductionTwo.RelativeO
          N13GaussianCubicField.L z := by
    calc
      (((relativeToRingOfIntegers z : On)) :
          N13GaussianCubicField.L) =
          N13GaussianNamedUnitTransport.orderToGaussian
            (relativeToRingOfIntegers z) :=
        (N13GaussianNamedUnitTransport.orderToGaussian_apply _).symm
      _ =
          algebraMap
            N13GaussianGlobalReductionTwo.RelativeO
            N13GaussianCubicField.L z := by
        simp [N13GaussianNamedUnitTransport.orderToGaussian,
          relativeToRingOfIntegers]
  rw [hrelative]
  have hInt :
      (algebraMap
          N13GaussianGlobalReductionTwo.RelativeO
          N13GaussianCubicField.L).comp
          (algebraMap ℤ
            N13GaussianGlobalReductionTwo.RelativeO) =
        algebraMap ℤ N13GaussianCubicField.L :=
    RingHom.ext_int _ _
  symm
  calc
    algebraMap
          N13GaussianGlobalReductionTwo.RelativeO
          N13GaussianCubicField.L
          (eval₂
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO)
            relativeTheta U) =
        eval₂
          ((algebraMap
              N13GaussianGlobalReductionTwo.RelativeO
              N13GaussianCubicField.L).comp
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO))
          (algebraMap
            N13GaussianGlobalReductionTwo.RelativeO
            N13GaussianCubicField.L relativeTheta) U := by
      exact Polynomial.hom_eval₂ _ _ _ _
    _ =
        eval₂ (algebraMap ℤ N13GaussianCubicField.L)
          N13GaussianFieldEquiv.gaussianTheta U := by
      rw [hInt, N13GaussianNamedUnitTransport.map_relativeTheta]

/-- Hence the normalized global Kummer integer is literally the displayed
low-degree polynomial evaluation in the fixed integral order at two. -/
theorem ringOfIntegersToOrder_normalizedKummerInteger
    (D : LowRep) :
    ringOfIntegersToOrder
        (N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
          (N13GlobalKummerNormalization.normalizedKummerInteger D)) =
      thetaEval (globalPrimitiveZ2 D) := by
  rw [N13GlobalKummerNormalization.normalizedKummerInteger,
    normalizationOrderEquiv_integralEval,
    ringOfIntegersToOrder_relative]
  have hInt :
      relativeToOrder.comp
          (algebraMap ℤ
            N13GaussianGlobalReductionTwo.RelativeO) =
        (algebraMap Z2 Order).comp
          (algebraMap ℤ Z2) :=
    RingHom.ext_int _ _
  calc
    relativeToOrder
          (eval₂
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO)
            relativeTheta
            (N13GlobalKummerNormalization.primitiveNormalization
              D.toSemi.u)) =
        eval₂
          (relativeToOrder.comp
            (algebraMap ℤ
              N13GaussianGlobalReductionTwo.RelativeO))
          (relativeToOrder relativeTheta)
          (N13GlobalKummerNormalization.primitiveNormalization
            D.toSemi.u) := by
      exact Polynomial.hom_eval₂ _ _ _ _
    _ =
        eval₂
          ((algebraMap Z2 Order).comp (algebraMap ℤ Z2))
          N13GaussianOrderTwo.theta
          (N13GlobalKummerNormalization.primitiveNormalization
            D.toSemi.u) := by
      rw [hInt, relativeToOrder_theta]
    _ =
        eval₂ (algebraMap Z2 Order) N13GaussianOrderTwo.theta
          ((N13GlobalKummerNormalization.primitiveNormalization
            D.toSemi.u).map (algebraMap ℤ Z2)) := by
      rw [Polynomial.eval₂_map]
    _ = thetaEval (globalPrimitiveZ2 D) := rfl

theorem globalReduction_normalizedKummerInteger
    (D : LowRep) :
    globalReduction
        (N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
          (N13GlobalKummerNormalization.normalizedKummerInteger D)) =
      (globalPrimitiveJet D : DualNumber F8) := by
  change
    reduction
        (ringOfIntegersToOrder
          (N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
            (N13GlobalKummerNormalization.normalizedKummerInteger D))) =
      (globalPrimitiveJet D : DualNumber F8)
  rw [ringOfIntegersToOrder_normalizedKummerInteger]
  exact
    (lowDegreeJet_val
      (globalPrimitiveZ2 D)
      (residuePolynomial_globalPrimitiveZ2_ne_zero D)
      (Polynomial.natDegree_map_le.trans
        (globalPrimitiveZ2_natDegree_le D))).symm

/-! ## The same named-unit word globally and locally -/

/-- The unit in the factorization `x = ε y²` has zero first ramified
logarithm.  The proof is an identity of group homomorphisms: the primitive
left side has constant first jet and the square on the right contributes
twice its logarithm. -/
theorem factorizationUnit_dlog_eq_zero
    (D : LowRep)
    (ε : Oiˣ) (y : Oi)
    (hxy :
      N13GlobalKummerNormalization.normalizedKummerInteger D =
        (ε : Oi) * y ^ 2) :
    N13GaussianNamedUnitSquareclasses.globalDlogAdd
        (Additive.ofMul
          (Units.map
            N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
            ε)) = 0 := by
  let e :=
    N13GaussianNormalizationOrderTransport.normalizationOrderEquiv
  let εn : Onˣ := Units.map e.toMonoidHom ε
  let yn : On := e y
  have hxyOn :
      e (N13GlobalKummerNormalization.normalizedKummerInteger D) =
        (εn : On) * yn ^ 2 := by
    dsimp only [εn, yn]
    change
      e (N13GlobalKummerNormalization.normalizedKummerInteger D) =
        e (ε : Oi) * e y ^ 2
    simpa only [map_mul, map_pow] using congrArg e hxy
  have hxUnit :
      IsUnit
        (globalReduction
          (e
            (N13GlobalKummerNormalization.normalizedKummerInteger D))) := by
    rw [globalReduction_normalizedKummerInteger]
    exact (globalPrimitiveJet D).isUnit
  have hprod :
      IsUnit
        (globalReduction (εn : On) *
          globalReduction yn ^ 2) := by
    rw [← map_pow, ← map_mul, ← hxyOn]
    exact hxUnit
  have hynSq : IsUnit (globalReduction yn ^ 2) :=
    ((Commute.all
      (globalReduction (εn : On))
      (globalReduction yn ^ 2)).isUnit_mul_iff.mp hprod).2
  have hyn : IsUnit (globalReduction yn) :=
    (isUnit_pow_iff (by norm_num : 2 ≠ 0)).mp hynSq
  let yJet : JetUnit := hyn.unit
  let εJet : JetUnit := Units.map globalReduction.toMonoidHom εn
  have hyJet :
      (yJet : DualNumber F8) = globalReduction yn :=
    IsUnit.unit_spec _
  have hJet :
      globalPrimitiveJet D = εJet * yJet ^ 2 := by
    apply Units.ext
    change
      (globalPrimitiveJet D : DualNumber F8) =
        globalReduction (εn : On) *
          (yJet : DualNumber F8) ^ 2
    rw [hyJet, ← map_pow, ← map_mul, ← hxyOn,
      globalReduction_normalizedKummerInteger]
  have hdlog :=
    congrArg RamifiedDlog.dlog hJet
  have hεJet :
      RamifiedDlog.dlog εJet = 0 := by
    simpa only [dlog_globalPrimitiveJet,
      RamifiedDlog.dlog_mul, RamifiedDlog.dlog_sq,
      add_zero] using hdlog.symm
  exact hεJet

theorem exists_normalizedCandidate_dlog_zero
    (D : LowRep) :
    ∃ i j k : ZMod 2,
      ((N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit D :
          N13SexticSquareclass.SexticAlgebraˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
          N13CandidateCollapse.candidateClass i j k 0 ∧
        N13LocalDlogTwo.candidateDlog i j k 0 = 0 := by
  let x :=
    N13GlobalKummerNormalization.normalizedKummerInteger D
  have hx : x ≠ 0 :=
    N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D
  obtain ⟨ε, y, hxy⟩ :=
    N13GaussianDifferentSupport.normalizedKummerInteger_eq_unit_mul_sq D
  let εn : Onˣ :=
    Units.map
      N13GaussianNormalizationOrderTransport.normalizationOrderEquiv.toMonoidHom
      ε
  obtain ⟨i, j, k, η, hε⟩ :=
    N13GaussianNamedUnitSquareclasses.unit_modSq_decompose_named εn
  have hεzero :
      N13GaussianNamedUnitSquareclasses.globalDlogAdd
          (Additive.ofMul εn) = 0 := by
    exact factorizationUnit_dlog_eq_zero D ε y hxy
  have hnamedZero :
      N13GaussianNamedUnitSquareclasses.globalDlogAdd
          (Additive.ofMul
            (N13GaussianNamedUnitSquareclasses.namedWord
              (i, j, k))) = 0 := by
    rw [hε] at hεzero
    simpa only [N13GaussianNamedUnitSquareclasses.namedWord,
      ofMul_mul, map_add,
      N13GaussianNamedUnitSquareclasses.globalDlogAdd_sq,
      add_zero] using hεzero
  have hdlog :
      N13LocalDlogTwo.candidateDlog i j k 0 = 0 := by
    rw [N13GaussianNamedUnitSquareclasses.globalDlogAdd_namedWord] at hnamedZero
    simpa only [N13LocalDlogTwo.candidateDlog, map_zero,
      add_zero] using hnamedZero
  obtain ⟨s, hs⟩ :=
    N13GaussianNormalizationOrderTransport.exists_transportedUnit_mul_sq
      x hx ε y hxy
  have hεSextic :
      N13GaussianNamedUnitTransport.orderUnitsToSextic εn =
        N13CandidateCollapse.zetaUnit ^ i.val *
          N13CandidateCollapse.e1Unit ^ j.val *
          N13CandidateCollapse.e2Unit ^ k.val *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η) ^ 2 := by
    simpa only [map_mul, map_pow,
      N13GaussianNamedUnitTransport.orderUnitsToSextic_zeta,
      N13GaussianNamedUnitTransport.orderUnitsToSextic_e1,
      N13GaussianNamedUnitTransport.orderUnitsToSextic_e2] using
      congrArg
        N13GaussianNamedUnitTransport.orderUnitsToSextic hε
  have hunit :
      N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit D =
        N13CandidateCollapse.candidateUnit i j k 0 *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η * s) ^ 2 := by
    change
      N13GaussianNormalizationOrderTransport.unitOfNonzero x hx =
        N13CandidateCollapse.candidateUnit i j k 0 *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η * s) ^ 2
    rw [hs, hεSextic]
    simp only [N13CandidateCollapse.candidateUnit,
      ZMod.val_zero, pow_zero, mul_one, mul_pow]
    simp only [mul_comm]
    exact mul_left_comm _ _ _
  refine ⟨i, j, k, ?_, hdlog⟩
  rw [hunit]
  change
    ((N13CandidateCollapse.candidateUnit i j k 0 *
          (N13GaussianNamedUnitTransport.orderUnitsToSextic η * s) ^ 2 :
        N13SexticSquareclass.SexticAlgebraˣ) :
      FakeSquareClass.Target
        (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
      ((N13CandidateCollapse.candidateUnit i j k 0 :
          N13SexticSquareclass.SexticAlgebraˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13SexticSquareclass.SexticAlgebra))
  simp

/-- The same aligned coordinates represent the actual Mumford value; the
rational scalar separating it from the globally primitive value disappears
only after the local logarithm has already been proved from the integral
factorization. -/
theorem exists_actualCandidate_dlog_zero
    (D : LowRep) :
    ∃ i j k : ZMod 2,
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) :
          N13SexticSquareclass.SexticAlgebraˣ) :
        FakeSquareClass.Target
          (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
          N13CandidateCollapse.candidateClass i j k 0 ∧
        N13LocalDlogTwo.candidateDlog i j k 0 = 0 := by
  obtain ⟨i, j, k, hclass, hdlog⟩ :=
    exists_normalizedCandidate_dlog_zero D
  exact
    ⟨i, j, k,
      (N13GaussianNormalizedSquareclassSeam.normalizedIntegralUnit_fakeClass_eq_uThetaUnit
        D).symm.trans
          hclass,
      hdlog⟩

/-! ## Group-level capstone -/

/-- The actual structural Kummer homomorphism admits aligned zero-carrier
coordinates with vanishing first logarithm for every rational class. -/
def actualCandidateLocalization :
    N13FakeDescentAssembly.CandidateLocalization
      N13FakeDescentAssembly.actualKummer where
  exists_candidate P := by
    let D : LowRep :=
      N13LowDegreeKummerHom.representative P
    obtain ⟨i, j, k, hclass, hdlog⟩ :=
      exists_actualCandidate_dlog_zero D
    refine ⟨i, j, k, 0, ?_, hdlog⟩
    change
      Additive.ofMul
          (((N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) :
              N13SexticSquareclass.SexticAlgebraˣ)) :
            FakeSquareClass.Target
              (algebraMap ℚ N13SexticSquareclass.SexticAlgebra)) =
        Additive.ofMul
          (N13CandidateCollapse.candidateClass i j k 0)
    exact congrArg Additive.ofMul hclass

/-- The genuine N13 fake-Kummer homomorphism is unconditionally trivial. -/
theorem actualKummer_trivial :
    ∀ P : N13FakeDescentAssembly.G,
      N13FakeDescentAssembly.actualKummer P = 0 :=
  N13FakeDescentAssembly.actualKummer_trivial_of_candidateLocalization
    actualCandidateLocalization

end

end MazurProof.N13GaussianGlobalZeroCarrierDlog


