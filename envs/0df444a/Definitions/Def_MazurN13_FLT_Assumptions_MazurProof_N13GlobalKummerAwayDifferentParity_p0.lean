-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerAwayDifferentParity_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerAwayDifferentParity_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:08:35.305168+00:00
-- url     : https://prove2.me/theorems/7503a21c-29b6-4093-9a04-ba92a17b0fc7
-- title:
--   FLT.Assumptions.MazurProof.N13GlobalKummerAwayDifferentParity source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GlobalKummerAwayDifferentParity

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GlobalKummerAwayDifferentParity
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerSimpleRootParity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuadraticAlgebraDoubleRoot_p0

set_option autoImplicit false




/-!
# Uniform N13 parity away from the different

The simple- and double-root principles together cover every primitive
quadratic at every height-one prime where the sextic is étale.  No
condition is imposed on the denominator-clearing scale.
-/

open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace MazurProof.N13GlobalKummerAwayDifferentParity

noncomputable section

open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
open N13GlobalKummerSimpleRootParity
open N13QuadraticAlgebraDoubleRoot

abbrev L : Type :=
  N13GlobalKummerSimpleRootParity.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

abbrev O : Type :=
  N13GlobalKummerSimpleRootParity.O

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

/-- The double-root branch has even multiplicity at every prime away from
the different. -/
theorem normalizedKummerInteger_multiplicity_even_of_doubleRoot
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hmem :
      normalizedKummerInteger D ∈ P.asIdeal)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal)
    (hnonsimple :
      ¬ IsUnit
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
  have ha : IsUnit a := by
    exact
      localU_coeff_two_isUnit_of_mem_nonsimple
        D P hmem hnonsimple
  have hsmall :
      a * localTheta P ^ 2 +
          b * localTheta P + c ∈
        P.completionIdeal L := by
    rw [← quadratic_eval, ← hU,
      localU_eval_localTheta]
    exact
      (algebraMap_mem_completionIdeal_iff P _).mpr
        hmem
  have hquadNonsimple :
      ¬ IsUnit
        (2 * a * localTheta P + b) := by
    rw [← quadratic_derivative_eval, ← hU]
    exact hnonsimple
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
    multiplicity_even_of_completion_quadratic_doubleRoot
      P
      (normalizedKummerInteger_ne_zero D)
      a b c (localTheta P) (localScale D P)
      (localF P) (localV D P) (localW D P)
      hglobal
      (localScale_ne_zero D P)
      ha hsmall hquadNonsimple
      (localF_eval_localTheta P)
      (localF_derivative_isUnit P hdifferent)
      (by
        rw [← hU]
        exact local_relation D P)

/-- At a prime away from the different, every normalized N13 Kummer
integer has even multiplicity. -/
theorem normalizedKummerInteger_multiplicity_even_of_not_mem_different
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal) :
    Even
      (multiplicity P.asIdeal
        (Ideal.span
          {normalizedKummerInteger D})) := by
  by_cases hmem :
      normalizedKummerInteger D ∈ P.asIdeal
  · by_cases hsimple :
        IsUnit
          ((localU D P).derivative.eval
            (localTheta P))
    · exact
        normalizedKummerInteger_multiplicity_even_of_simpleRoot
          D P hmem hdifferent hsimple
    · exact
        normalizedKummerInteger_multiplicity_even_of_doubleRoot
          D P hmem hdifferent hsimple
  · have hmult :
        multiplicity P.asIdeal
            (Ideal.span
              {normalizedKummerInteger D}) = 0 := by
      apply multiplicity_eq_zero.mpr
      exact
        (Ideal.dvd_span_singleton.not).mpr hmem
    rw [hmult]
    exact ⟨0, by simp⟩

/-- Fractional-ideal count form: all support away from the different has
even exponent, independently of the denominator-clearing scale. -/
theorem normalizedKummerInteger_count_even_of_not_mem_different
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal) :
    Even
      (FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) := by
  rw [count_spanSingleton_eq_int_multiplicity
    P (normalizedKummerInteger_ne_zero D)]
  exact
    (Int.even_coe_nat _).mpr
      (normalizedKummerInteger_multiplicity_even_of_not_mem_different
        D P hdifferent)

end

end MazurProof.N13GlobalKummerAwayDifferentParity


