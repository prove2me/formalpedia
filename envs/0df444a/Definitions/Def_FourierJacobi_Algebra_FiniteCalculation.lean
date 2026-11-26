-- Prove2me | Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
-- name    : FourierJacobi_Algebra_FiniteCalculation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:16:20.615357+00:00
-- url     : https://prove2.me/theorems/9efc79de-0ed3-494c-87b7-a281cc368691
-- title:
--   Finite Calculation
-- statement:
--   Definitions and structural lemmas for Finite Calculation, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/FiniteCalculation.lean

import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
structure RegionRegular (t d U V : K) : Prop where
  p : 1 - d * V * t ≠ 0
  n : 1 - V * t / d ≠ 0
  e : 1 - V ^ 2 * t ^ 2 ≠ 0
  f : 1 - U * t ^ 2 ≠ 0
  g : 1 - U * t ^ 4 ≠ 0
structure FiniteRegular (t a b d : K) : Prop where
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  d_ne_zero : d ≠ 0
  a_ne_one : a - 1 ≠ 0
  b_ne_one : b - 1 ≠ 0
  a_ne_b : a - b ≠ 0
  ab_ne_one : a * b - 1 ≠ 0
  common : weylCommonDenominator t a b d ≠ 0
  rows : ∀ i, RegionRegular t d (weylU a b i) (weylV a b i)
def finiteCore (t a b d : K) : K :=
  (∑ i : Fin 8, weylWeights t a b i *
    (∑ j : Fin 50, regionTerms t d (weylU a b i) (weylV a b i) j)) / poincare t
end Algebra
end FourierJacobi


