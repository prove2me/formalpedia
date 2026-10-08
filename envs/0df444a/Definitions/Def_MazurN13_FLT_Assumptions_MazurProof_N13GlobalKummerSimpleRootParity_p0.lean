-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerSimpleRootParity_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerSimpleRootParity_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:04:16.939267+00:00
-- url     : https://prove2.me/theorems/2756b000-4fc6-4dca-b4a0-4deab5e3d42e
-- title:
--   FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerIdealSquare_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeSimpleRoot_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0

set_option autoImplicit false




/-!
# Simple-root parity for normalized N13 Kummer values

This file maps the primitive global Mumford polynomial and its homogeneous
curve relation into the integer ring of a height-one completion.  Away from
the different, the sextic secant is a unit.  Hence whenever the quadratic
Mumford polynomial has a simple root modulo the prime, its normalized
Kummer value has even multiplicity.

The denominator-clearing scale is not inverted in the integer ring.  It is
absorbed into the square root only after passing to the completion field,
so no denominator prime is excluded.
-/

open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace MazurProof.N13GlobalKummerSimpleRootParity

noncomputable section

open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot

abbrev L : Type :=
  N13GlobalKummerIdealSquare.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

abbrev O : Type :=
  N13GlobalKummerIdealSquare.O

local instance dedekindO : IsDedekindDomain O :=
  integralClosure.isDedekindDomain ℤ ℚ L

local instance fractionRingOL : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ ℚ L O

local instance charZeroL : CharZero L :=
  charZero_of_injective_algebraMap
    (algebraMap ℚ L).injective

local instance charZeroCompletion
    (P : HeightOneSpectrum O) :
    CharZero (P.adicCompletion L) :=
  charZero_of_injective_algebraMap
    (algebraMap L (P.adicCompletion L)).injective

abbrev LocalIntegers
    (P : HeightOneSpectrum O) : Type :=
  P.adicCompletionIntegers L

/-- Map an integral polynomial into the integer ring of the completion. -/
def localPolynomial
    (P : HeightOneSpectrum O) (p : ℤ[X]) :
    (LocalIntegers P)[X] :=
  p.map (algebraMap ℤ (LocalIntegers P))

/-- The integral sextic branch point inside the local integer ring. -/
def localTheta
    (P : HeightOneSpectrum O) :
    LocalIntegers P :=
  algebraMap O (LocalIntegers P) integralTheta

/-- The local primitive quadratic attached to a low-degree representative. -/
def localU
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P
    (primitiveNormalization D.toSemi.u)

def localF
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P N13SexticIrreducible.fInt

def localV
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P (scaledIntegralMumford D).v

def localW
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (LocalIntegers P)[X] :=
  localPolynomial P (scaledIntegralMumford D).w

def localScale
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    LocalIntegers P :=
  algebraMap ℤ (LocalIntegers P)
    (scaledIntegralMumford D).scale

/-- Evaluation at the local branch point commutes with the map from the
global ring of integers. -/
theorem localPolynomial_eval_localTheta
    (P : HeightOneSpectrum O) (p : ℤ[X]) :
    (localPolynomial P p).eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (integralEval p) := by
  rw [localPolynomial, Polynomial.eval_map]
  change
    eval₂ (algebraMap ℤ (LocalIntegers P))
        (algebraMap O (LocalIntegers P) integralTheta) p =
      algebraMap O (LocalIntegers P)
        (eval₂ (algebraMap ℤ O) integralTheta p)
  have h :=
    (Polynomial.hom_eval₂ p
      (algebraMap ℤ O)
      (algebraMap O (LocalIntegers P))
      integralTheta).symm
  have hmaps :
      (algebraMap O (LocalIntegers P)).comp
          (algebraMap ℤ O) =
        algebraMap ℤ (LocalIntegers P) :=
    RingHom.ext_int _ _
  rw [← hmaps]
  exact h

theorem localU_eval_localTheta
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (normalizedKummerInteger D) := by
  exact localPolynomial_eval_localTheta P _

theorem localF_eval_localTheta
    (P : HeightOneSpectrum O) :
    (localF P).eval (localTheta P) = 0 := by
  rw [localF, localPolynomial_eval_localTheta]
  have hzero :
      integralEval N13SexticIrreducible.fInt = 0 :=
    integralTheta_root_fInt
  rw [hzero, map_zero]

/-- The local derivative is the image of the global different generator. -/
theorem localF_derivative_eval_localTheta
    (P : HeightOneSpectrum O) :
    (localF P).derivative.eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (integralEval
          N13SexticIrreducible.fInt.derivative) := by
  rw [localF, localPolynomial, derivative_map]
  exact localPolynomial_eval_localTheta P _

/-- The completion ideal lies over the original height-one prime. -/
theorem algebraMap_mem_completionIdeal_iff
    (P : HeightOneSpectrum O) (x : O) :
    algebraMap O (LocalIntegers P) x ∈
        P.completionIdeal L ↔
      x ∈ P.asIdeal := by
  change
    x ∈ Ideal.comap
        (algebraMap O (LocalIntegers P))
        (P.completionIdeal L) ↔
      x ∈ P.asIdeal
  have hover :
      Ideal.comap
          (algebraMap O (LocalIntegers P))
          (P.completionIdeal L) =
        P.asIdeal :=
    by
      simpa only [Ideal.under_def] using
        (inferInstance :
          (P.completionIdeal L).LiesOver P.asIdeal).over.symm
  rw [hover]

/-- An element avoiding the global prime maps to a local unit. -/
theorem localMap_isUnit_iff_not_mem
    (P : HeightOneSpectrum O) (x : O) :
    IsUnit (algebraMap O (LocalIntegers P) x) ↔
      x ∉ P.asIdeal := by
  have hmem :=
    algebraMap_mem_completionIdeal_iff P x
  have hnonunit :
      algebraMap O (LocalIntegers P) x ∈
          P.completionIdeal L ↔
        ¬ IsUnit
          (algebraMap O (LocalIntegers P) x) := by
    simp only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  tauto

/-- Away from the different, the local sextic derivative is a unit. -/
theorem localF_derivative_isUnit
    (P : HeightOneSpectrum O)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal) :
    IsUnit
      ((localF P).derivative.eval
        (localTheta P)) := by
  rw [localF_derivative_eval_localTheta]
  exact
    (localMap_isUnit_iff_not_mem P _).mpr
      hdifferent

theorem localU_natDegree_le
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans
    (normalizedKummerInteger_degree D)

/-- Global primitivity remains the statement that the local coefficients
generate the unit ideal. -/
theorem localU_contentIdeal_eq_top
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).contentIdeal = ⊤ := by
  rw [localU, localPolynomial,
    Polynomial.contentIdeal_map_eq_map_contentIdeal]
  have hprimitive :=
    primitiveNormalization_isPrimitive D.toSemi.u
  have htop :
      (primitiveNormalization D.toSemi.u).contentIdeal =
        ⊤ :=
    (Polynomial.isPrimitive_iff_contentIdeal_eq_top
      (primitiveNormalization D.toSemi.u)).mp
      hprimitive
  rw [htop, Ideal.map_top]

/-- The mapped homogeneous Mumford relation. -/
theorem local_relation
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    C (localScale D P ^ 2) * localF P -
        localV D P ^ 2 =
      localU D P * localW D P := by
  have h :=
    congrArg
      (Polynomial.map
        (algebraMap ℤ (LocalIntegers P)))
      (scaledCurve_relation D)
  simpa [scaledCurve, localScale, localF, localV,
    localU, localW, localPolynomial,
    Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C,
    map_pow] using h

theorem localScale_ne_zero
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    localScale D P ≠ 0 := by
  unfold localScale
  intro hzero
  apply (scaledIntegralMumford D).scale_ne_zero
  have hzero' :=
    congrArg
      (fun z : LocalIntegers P =>
        (z : P.adicCompletion L))
      hzero
  have hmaps :
      (algebraMap
          (LocalIntegers P)
          (P.adicCompletion L)).comp
          (algebraMap ℤ (LocalIntegers P)) =
        algebraMap ℤ (P.adicCompletion L) :=
    RingHom.ext_int _ _
  change
    ((algebraMap
        (LocalIntegers P)
        (P.adicCompletion L)).comp
      (algebraMap ℤ (LocalIntegers P)))
        (scaledIntegralMumford D).scale =
      0 at hzero'
  rw [hmaps] at hzero'
  apply
    (algebraMap ℤ
      (P.adicCompletion L)).injective_int
  simpa only [map_zero] using hzero'

/-- The normalized Kummer integer is nonzero. -/
theorem normalizedKummerInteger_ne_zero
    (D : N13LowDegreeKummerHom.LowRep) :
    normalizedKummerInteger D ≠ 0 := by
  obtain ⟨c, hc, hspec⟩ :=
    normalizedKummerInteger_spec D
  have hcL :
      algebraMap ℚ L c ≠ 0 :=
    by
      simpa only [map_zero] using
        (algebraMap ℚ L).injective.ne hc
  have hu :
      N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) ≠ 0 :=
    N13MumfordKummerValue.uTheta_ne_zero _
  have huL :
      N13GaussianFieldEquiv.sexticEquivGaussian
          (N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D)) ≠ 0 :=
    by
      simpa only [map_zero] using
        N13GaussianFieldEquiv.sexticEquivGaussian.injective.ne
          hu
  intro hzero
  have hprod :
      algebraMap ℚ L c *
          N13GaussianFieldEquiv.sexticEquivGaussian
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D)) =
        0 := by
    calc
      algebraMap ℚ L c *
            N13GaussianFieldEquiv.sexticEquivGaussian
              (N13MumfordKummerValue.uTheta
                (N13LowDegreeKummerHom.asMumford D)) =
          ((normalizedKummerInteger D : O) : L) :=
        hspec.symm
      _ = ((0 : O) : L) := by rw [hzero]
      _ = 0 := rfl
  exact (mul_ne_zero hcL huL) hprod

/-- For a nonzero integral generator, the fractional-ideal count is the
ordinary height-one multiplicity of its principal ideal. -/
theorem count_spanSingleton_eq_int_multiplicity
    (P : HeightOneSpectrum O)
    {x : O} (hx : x ≠ 0) :
    FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          ((x : O) : L)) =
      (multiplicity P.asIdeal
        (Ideal.span ({x} : Set O)) : ℤ) := by
  have hspan :
      Ideal.span ({x} : Set O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hx
  change
    FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          (algebraMap O L x)) =
      (multiplicity P.asIdeal
        (Ideal.span ({x} : Set O)) : ℤ)
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  rw [FractionalIdeal.count_coe L P hspan]
  norm_cast
  rw [Ideal.count_associates_factors_eq
      hspan P.isPrime P.ne_bot,
    P.count_normalizedFactors_eq_multiplicity hspan]

/-- In the nonsimple branch, local primitivity forces the leading
coefficient to be a unit.  This isolates the sole remaining local case. -/
theorem localU_coeff_two_isUnit_of_mem_nonsimple
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hmem :
      normalizedKummerInteger D ∈ P.asIdeal)
    (hnonsimple :
      ¬ IsUnit
        ((localU D P).derivative.eval
          (localTheta P))) :
    IsUnit ((localU D P).coeff 2) := by
  apply
    coeff_two_isUnit_of_content_top_small_nonsimple
      (localU D P)
      (localU_natDegree_le D P)
      (localU_contentIdeal_eq_top D P)
      (localTheta P)
  · rw [localU_eval_localTheta]
    exact
      (algebraMap_mem_completionIdeal_iff P _).mpr
        hmem
  · exact hnonsimple

/-- At every prime away from the different, the simple-root branch gives
even multiplicity of the normalized Kummer integer, with no condition on
the denominator-clearing scale. -/
theorem normalizedKummerInteger_multiplicity_even_of_simpleRoot
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hmem :
      normalizedKummerInteger D ∈ P.asIdeal)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal)
    (hsimple :
      IsUnit
        ((localU D P).derivative.eval
          (localTheta P))) :
    Even
      (multiplicity P.asIdeal
        (Ideal.span
          {normalizedKummerInteger D})) := by
  let a := (localU D P).coeff 2
  let b := (localU D P).coeff 1
  let c := (localU D P).coeff 0
  have hU :
      localU D P = quadratic a b c := by
    simpa only [a, b, c] using
      eq_quadratic_of_natDegree_le_two
        (localU D P)
        (localU_natDegree_le D P)
  have hsmall :
      a * localTheta P ^ 2 +
          b * localTheta P + c ∈
        P.completionIdeal L := by
    rw [← quadratic_eval, ← hU,
      localU_eval_localTheta]
    exact
      (algebraMap_mem_completionIdeal_iff P _).mpr
        hmem
  have hquadDeriv :
      IsUnit
        (2 * a * localTheta P + b) := by
    rw [← quadratic_derivative_eval,
      ← hU]
    exact hsimple
  have hglobal :
      algebraMap O (P.adicCompletion L)
          (normalizedKummerInteger D) =
        ((a * localTheta P ^ 2 +
              b * localTheta P + c :
            LocalIntegers P) :
          P.adicCompletion L) := by
    have heval :
        a * localTheta P ^ 2 +
              b * localTheta P + c =
          algebraMap O (LocalIntegers P)
            (normalizedKummerInteger D) := by
      rw [← quadratic_eval, ← hU,
        localU_eval_localTheta]
    change
      ((algebraMap O (LocalIntegers P)
          (normalizedKummerInteger D) :
        LocalIntegers P) :
          P.adicCompletion L) =
        ((a * localTheta P ^ 2 +
              b * localTheta P + c :
            LocalIntegers P) :
          P.adicCompletion L)
    exact
      congrArg
        (fun z : LocalIntegers P =>
          (z : P.adicCompletion L))
        heval.symm
  apply
    multiplicity_even_of_completion_quadratic_simpleRoot
      P
      (normalizedKummerInteger_ne_zero D)
      a b c (localTheta P) (localScale D P)
      (localF P) (localV D P) (localW D P)
      hglobal
      (localScale_ne_zero D P)
      hsmall hquadDeriv
      (localF_eval_localTheta P)
      (localF_derivative_isUnit P hdifferent)
      (by
        rw [← hU]
        exact local_relation D P)

/-- Fractional-ideal count form of the same result, matching the global
Kummer factorization interface. -/
theorem normalizedKummerInteger_count_even_of_simpleRoot
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hmem :
      normalizedKummerInteger D ∈ P.asIdeal)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal)
    (hsimple :
      IsUnit
        ((localU D P).derivative.eval
          (localTheta P))) :
    Even
      (FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) := by
  rw [count_spanSingleton_eq_int_multiplicity
    P (normalizedKummerInteger_ne_zero D)]
  exact
    (Int.even_coe_nat _).mpr
      (normalizedKummerInteger_multiplicity_even_of_simpleRoot
        D P hmem hdifferent hsimple)

end

end MazurProof.N13GlobalKummerSimpleRootParity


