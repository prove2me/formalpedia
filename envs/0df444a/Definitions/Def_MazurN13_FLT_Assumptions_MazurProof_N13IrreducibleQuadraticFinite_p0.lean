-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticFinite_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticFinite_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:44:59.702967+00:00
-- url     : https://prove2.me/theorems/3a4c2643-2e75-4f42-963a-d9882f7445e1
-- title:
--   FLT.Assumptions.MazurProof.N13IrreducibleQuadraticFinite source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IrreducibleQuadraticFinite

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IrreducibleQuadraticFinite
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IrreducibleQuadraticChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityNormCarrier_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientVerticalFlatness_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CanonicalContractionQuotient_p0

set_option autoImplicit false




/-!
# Finiteness on the affine chart of an irreducible N13 quadratic

If the horizontal quadratic has integral affine coefficients, its monic
equation belongs to the canonical contraction.  The rank-two polynomial
normal form then makes the contracted quotient finite.  Vertical
saturation already makes the same quotient flat.

Combined with the proper-chart theorem, this leaves only the reciprocal
integral chart as the non-affine alternative.
-/

open Polynomial

namespace MazurProof.N13IrreducibleQuadraticFinite

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
  N13CanonicalContractionQuotient.Model

/-- An integral horizontal equation whose coefficient extension is the
generic Mumford equation belongs to the canonical contraction. -/
theorem xClass_mem_contract_of_mapPoly_eq_u
    (D : SexticMumford.SemiMumford Model)
    (m : R₂[X])
    (hm :
      N13TwoAdicCoordinateBaseChange.mapPoly m = D.u) :
    N13GeneralizedMumfordIntegral.xClass m ∈
      N13IntegralModelContraction.contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal D) := by
  change
    N13TwoAdicCoordinateBaseChange.integralToSextic
        (N13GeneralizedMumfordIntegral.xClass m) ∈
      N13CanonicalContractionQuotient.graphIdeal D
  rw [N13TwoAdicCoordinateBaseChange.integralToSextic,
    RingHom.comp_apply,
    N13TwoAdicCoordinateBaseChange.extend_xClass,
    N13GoodSexticCoordinateEquiv.toSextic_xClass,
    hm]
  exact
    SexticMumford.xClass_mem_mumfordIdeal
      Model D.u D.v

/-- A monic integral horizontal equation makes the canonical contracted
quotient finite over `ℤ₂`. -/
theorem contractQuotient_finite_of_integral_u
    (D : SexticMumford.SemiMumford Model)
    (m : R₂[X])
    (hmMonic : m.Monic)
    (hm :
      N13TwoAdicCoordinateBaseChange.mapPoly m = D.u) :
    Module.Finite R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D)) := by
  apply
    N13InfinityNormCarrier.quotient_finite_of_monic_xClass_mem
  · exact hmMonic
  · exact xClass_mem_contract_of_mapPoly_eq_u D m hm

/-- For an irreducible quadratic graph, either the canonical affine
quotient is finite or the reciprocal monic equation is literally integral
on the infinity chart. -/
theorem contractQuotient_finite_or_integral_reciprocal
    (D : SexticMumford.Mumford Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
    Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) ∨
      (D.u.coeff 0 ≠ 0 ∧
        ∃ a b : R₂,
          (X ^ 2 + C (a : Q₂) * X + C (b : Q₂) : Q₂[X]) =
            X ^ 2 +
              C (D.u.coeff 1 / D.u.coeff 0) * X +
              C ((D.u.coeff 0)⁻¹)) := by
  rcases
      N13IrreducibleQuadraticChart.irreducible_monic_quadratic_has_integral_chart
        D.u D.u_monic hdeg hirr with hAffine | hInfinity
  · left
    obtain ⟨a, b, hu⟩ := hAffine
    let m : R₂[X] := X ^ 2 + C a * X + C b
    apply contractQuotient_finite_of_integral_u D.toSemi m
    · dsimp [m]
      monicity <;> norm_num
    · simpa [m,
        N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hu.symm
  · exact Or.inr hInfinity

end

end MazurProof.N13IrreducibleQuadraticFinite


