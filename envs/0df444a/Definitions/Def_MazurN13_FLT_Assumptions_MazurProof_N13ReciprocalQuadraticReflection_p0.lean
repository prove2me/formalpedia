-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalQuadraticReflection_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13ReciprocalQuadraticReflection_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:06:40.579614+00:00
-- url     : https://prove2.me/theorems/2c429462-c871-42ca-a022-2dbd23f4f2df
-- title:
--   FLT.Assumptions.MazurProof.N13ReciprocalQuadraticReflection source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13ReciprocalQuadraticReflection

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13ReciprocalQuadraticReflection
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CanonicalContractionQuotient_p0

set_option autoImplicit false




/-!
# Reflection of the reciprocal N13 quadratic

For a monic quadratic

`u(X) = X² + u₁X + u₀`

with `u₀ ≠ 0`, its monic reciprocal equation is

`m(T) = T² + (u₁/u₀)T + u₀⁻¹`.

Reflecting `m` at weight two gives exactly `u₀⁻¹ u`.  Consequently an
integral reciprocal equation produces an integral affine weighted closure
whose generic horizontal generator differs from the original Mumford
generator by a nonzero scalar.  This is the horizontal equality needed in
the reciprocal two-chart branch.
-/

open Polynomial

namespace MazurProof.N13ReciprocalQuadraticReflection

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev Model : SexticMumford.Model Q₂ :=
  N13CanonicalContractionQuotient.Model

def integralReciprocal (a b : R₂) : R₂[X] :=
  X ^ 2 + C a * X + C b

theorem integralReciprocal_monic
    (a b : R₂) :
    (integralReciprocal a b).Monic := by
  unfold integralReciprocal
  monicity <;> norm_num

theorem integralReciprocal_natDegree
    (a b : R₂) :
    (integralReciprocal a b).natDegree = 2 := by
  unfold integralReciprocal
  compute_degree <;> norm_num

private theorem reflect_reciprocal_explicit
    (a b : Q₂) :
    (X ^ 2 + C a * X + C b : Q₂[X]).reflect 2 =
      1 + C a * X + C b * X ^ 2 := by
  rw [reflect_add, reflect_add]
  have hX2 :
      ((X : Q₂[X]) ^ 2).reflect 2 = 1 := by
    simpa using
      (reflect_monomial 2 2 (R := Q₂))
  have hCX :
      (C a * X : Q₂[X]).reflect 2 = C a * X := by
    simpa using
      (reflect_C_mul_X_pow (R := Q₂) 2 1 (c := a))
  rw [hX2, hCX, reflect_C]

/-- The weight-two reflection of the monic reciprocal is the original
quadratic multiplied by its inverse constant term. -/
theorem reflect_monic_reciprocal
    (u : Q₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2)
    (h0 : u.coeff 0 ≠ 0) :
    (X ^ 2 +
        C (u.coeff 1 / u.coeff 0) * X +
        C ((u.coeff 0)⁻¹) : Q₂[X]).reflect 2 =
      C ((u.coeff 0)⁻¹) * u := by
  rw [reflect_reciprocal_explicit,
    N13IrreducibleQuadraticChart.monic_quadratic_eq u hu hdeg]
  apply Polynomial.ext
  intro n
  simp only [coeff_add, coeff_one, coeff_C_mul_X,
    coeff_C_mul, coeff_X_pow, coeff_C]
  by_cases hn : n ≤ 2
  · interval_cases n
    · simp [h0]
    · simp [div_eq_mul_inv, mul_comm]
    · norm_num [coeff_X]
  · have hn2 : 2 < n := Nat.lt_of_not_ge hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2ne : n ≠ 2 := by omega
    rw [coeff_X_of_ne_one hn1]
    simp [hn0, hn2ne]

/-- If the reciprocal monic equation has integral coefficients, then the
generic fibre of its affine weighted closure is a nonzero scalar multiple
of the original Mumford horizontal equation. -/
theorem mapPoly_reflect_integralReciprocal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : R₂)
    (hm :
      (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    N13TwoAdicCoordinateBaseChange.mapPoly
        ((integralReciprocal a b).reflect 2) =
      C ((D.u.coeff 0)⁻¹) * D.u := by
  have hmMap :
      N13TwoAdicCoordinateBaseChange.mapPoly
          (integralReciprocal a b) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹) := by
    simpa [integralReciprocal,
      N13TwoAdicCoordinateBaseChange.mapPoly,
      N13TwoAdicCoordinateBaseChange.coeffMap,
      N13TwoAdicMumfordTransport.mapPoly,
      N13TwoAdicMumfordTransport.coeffMap] using hm
  change
    ((integralReciprocal a b).reflect 2).map
        N13TwoAdicCoordinateBaseChange.coeffMap =
      C ((D.u.coeff 0)⁻¹) * D.u
  rw [← Polynomial.reflect_map]
  change
    (N13TwoAdicCoordinateBaseChange.mapPoly
        (integralReciprocal a b)).reflect 2 =
      C ((D.u.coeff 0)⁻¹) * D.u
  rw [hmMap]
  exact
    reflect_monic_reciprocal
      D.u D.u_monic hdeg h0

end

end MazurProof.N13ReciprocalQuadraticReflection


