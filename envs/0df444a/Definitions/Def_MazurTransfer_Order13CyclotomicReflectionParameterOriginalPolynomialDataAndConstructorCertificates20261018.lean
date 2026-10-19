-- Prove2me | Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
-- name    : MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T22:28:28.773355+00:00
-- url     : https://prove2.me/theorems/29e48224-6bcb-42c5-88d4-5adad776bfb3
-- title:
--   Original cyclotomic reflection parameter and literal polynomial certificates
-- statement:
--   The original cubic period and quadratic Gauss sum of a primitive thirteenth root construct the original reflection parameter. Fourteen complete original declaration types and seven whole values are checked, together with the original quadratic-thirteen polynomial constructor-helper proposition. Named downstream consumer: MazurTransfer.Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator. The accepted thirteenth-root cubic-period theorem is reused directly; the generator-orbit arithmetic remains separate.
-- source:
--   MazurTheorem Order13CyclotomicReflectionCoefficients, original polynomial data and the cyclotomicParameter record constructor with its immediate certificates; necessary original Order13ReflectionParameterArithmetic.quadratic_thirteen_certificate helper retained; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit polynomial certificates express the reflection
coefficients in a primitive thirteenth root of unity. Named downstream
consumer: the arithmetic13 character of the actual reflected fixed line.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
import Theorems.Thm_MazurTransfer_thirteenth_root_cubic_period
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
noncomputable section
universe u
namespace MazurTransfer.CyclotomicReflectionConstructorProofHelpers20261018
open Order13ReflectionSexticSymmetry
variable {K : Type u} [Field K]
theorem quadratic_thirteen_certificate (t : K) :
    (3 * t ^ 2 + 8 * t + 1) ^ 2 - 13 * reflectionScalar t =
      3 * (3 * t + 4) * reflectionCubic t := by
  dsimp [reflectionScalar, reflectionCubic]
  ring

end MazurTransfer.CyclotomicReflectionConstructorProofHelpers20261018
namespace MazurTransfer.Order13CyclotomicReflectionCoefficients
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open CyclotomicReflectionConstructorProofHelpers20261018
variable {K : Type u} [Field K]

def cyclotomicSum (z : K) : K :=
  1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7 + z ^ 8 + z ^ 9 + z ^ 10 + z ^ 11 + z ^ 12

def cubicPeriod (z : K) : K := z + z ^ 5 + z ^ 8 + z ^ 12 - 1

def quadraticGauss (z : K) : K :=
  z + z ^ 3 + z ^ 4 + z ^ 9 + z ^ 10 + z ^ 12 - z ^ 2 - z ^ 5 - z ^ 6 - z ^ 7 - z ^ 8 - z ^ 11

def cubicCertificate (z : K) : K :=
  z ^ 24 - z ^ 23 + 3 * z ^ 20 - 3 * z ^ 19 + 3 * z ^ 17 - 3 * z ^ 15 +
    9 * z ^ 13 - 7 * z ^ 12 - z ^ 11 + 2 * z ^ 10 + 6 * z ^ 9 - 7 * z ^ 8 +
    z ^ 7 + 6 * z ^ 6 - 4 * z ^ 5 - z ^ 4 + 5 * z ^ 2 - 5 * z + 1

def quadraticCertificate (z : K) : K :=
  z ^ 12 - 3 * z ^ 11 + 5 * z ^ 10 - 3 * z ^ 9 - 3 * z ^ 8 + 5 * z ^ 7 -
    3 * z ^ 6 - 3 * z ^ 5 + 5 * z ^ 4 - 3 * z ^ 3 + z ^ 2 + 13 * z - 13

theorem cubic_polynomial_certificate (z : K) :
    reflectionCubic (cubicPeriod z) = cubicCertificate z * cyclotomicSum z := by
  dsimp [reflectionCubic, cubicPeriod, cubicCertificate, cyclotomicSum]
  ring

theorem quadratic_polynomial_certificate (z : K) :
    quadraticGauss z ^ 2 - 13 = quadraticCertificate z * cyclotomicSum z := by
  dsimp [quadraticGauss, quadraticCertificate, cyclotomicSum]
  ring

theorem cyclotomicSum_eq_zero {z : K} (hz : IsPrimitiveRoot z 13) : cyclotomicSum z = 0 := by
  have h := hz.geom_sum_eq_zero (by decide : 1 < 13)
  simpa only [cyclotomicSum, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add] using h

theorem cubicPeriod_root {z : K} (hz : IsPrimitiveRoot z 13) : reflectionCubic (cubicPeriod z) = 0 := by
  exact MazurTransfer.thirteenth_root_cubic_period K z hz

theorem quadraticGauss_square {z : K} (hz : IsPrimitiveRoot z 13) : quadraticGauss z ^ 2 = 13 := by
  have h := quadratic_polynomial_certificate z
  rw [cyclotomicSum_eq_zero hz, mul_zero] at h
  exact sub_eq_zero.mp h

variable [CharZero K]

theorem quadraticGauss_ne_zero {z : K} (hz : IsPrimitiveRoot z 13) : quadraticGauss z ≠ 0 := by
  intro h
  have hs := quadraticGauss_square hz
  rw [h] at hs
  norm_num at hs

def reflectionS (z : K) : K :=
  (3 * cubicPeriod z ^ 2 + 8 * cubicPeriod z + 1) / quadraticGauss z

theorem reflectionS_square {z : K} (hz : IsPrimitiveRoot z 13) :
    reflectionS z ^ 2 = reflectionScalar (cubicPeriod z) := by
  have h := quadratic_thirteen_certificate (cubicPeriod z)
  rw [cubicPeriod_root hz, mul_zero] at h
  have hA := sub_eq_zero.mp h
  dsimp [reflectionS]
  rw [div_pow, quadraticGauss_square hz]
  apply (div_eq_iff (by norm_num : (13 : K) ≠ 0)).mpr
  rw [hA]
  ring

def cyclotomicParameter (z : K) (hz : IsPrimitiveRoot z 13) : ReflectionParameter K where
  t := cubicPeriod z
  s := reflectionS z
  cubic_eq_zero := cubicPeriod_root hz
  square_eq_scalar := reflectionS_square hz

end MazurTransfer.Order13CyclotomicReflectionCoefficients
#print axioms MazurTransfer.Order13CyclotomicReflectionCoefficients.cyclotomicParameter


