-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicMumfordTransport_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicMumfordTransport_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:02:38.169261+00:00
-- url     : https://prove2.me/theorems/117bdda8-37e0-476c-9caa-3a2d4f131094
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicMumfordTransport
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodSexticMumfordTransport_p0
import Mathlib.NumberTheory.Padics.PadicIntegers

set_option autoImplicit false




/-!
# Transporting integral N13 Mumford data to the two-adic sextic model

Smooth generalized Mumford data over `ℤ₂` first extend coefficientwise to
`ℚ₂`.  Completion of the square then gives a standard reduced sextic
semirepresentative.  This file records that passage without choosing
coordinates or enumerating residue classes.
-/

open Polynomial

namespace MazurProof.N13TwoAdicMumfordTransport

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev Q₂ : Type :=
  ℚ_[2]

def coeffMap : R₂ →+* Q₂ :=
  algebraMap R₂ Q₂

def mapPoly : R₂[X] →+* Q₂[X] :=
  Polynomial.mapRingHom coeffMap

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) := by
  simp [mapPoly, coeffMap,
    N13GeneralizedMumfordIntegral.hPoly]

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) := by
  simp [mapPoly, coeffMap,
    N13GeneralizedMumfordIntegral.rhsPoly]

/-- Coefficient extension does not require the additional special-fibre
smoothness witness. -/
def baseChangeSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h

@[simp] theorem baseChangeSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).u = mapPoly D.u := rfl

@[simp] theorem baseChangeSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).v = mapPoly D.v := rfl

@[simp] theorem baseChangeSemi_w
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (baseChangeSemi D).w = mapPoly D.w := rfl

/-- Coefficient extension of an integral generalized Mumford datum. -/
def baseChange
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    N13GeneralizedMumfordIntegral.SemiMumford (R := Q₂) where
  u := mapPoly D.u
  v := mapPoly D.v
  w := mapPoly D.w
  u_monic := D.u_monic.map coeffMap
  curve_eq := by
    have h := congrArg mapPoly D.curve_eq
    simpa only [map_add, map_sub, map_mul, map_pow,
      mapPoly_hPoly, mapPoly_rhsPoly] using h

@[simp] theorem baseChange_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).u = mapPoly D.u := rfl

@[simp] theorem baseChange_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).v = mapPoly D.v := rfl

@[simp] theorem baseChange_w
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (baseChange D).w = mapPoly D.w := rfl

/-- The smoothness Bézout identity survives coefficient extension. -/
theorem baseChange_bezout
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    ∃ a b c : Q₂[X],
      a * (baseChange D).u +
          b * (2 * (baseChange D).v +
            N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) +
        c * (baseChange D).w = 1 := by
  obtain ⟨a, b, c, habc⟩ := D.bezout
  refine ⟨mapPoly a, mapPoly b, mapPoly c, ?_⟩
  have h := congrArg mapPoly habc
  simpa only [baseChange_u, baseChange_v, baseChange_w,
    map_add, map_mul, map_ofNat, map_one, mapPoly_hPoly] using h

/-- The standard reduced sextic semirepresentative attached to arbitrary
integral generalized Mumford data. -/
def sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChangeSemi D) nInf

@[simp] theorem sexticSemiOfSemi_u
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).u = mapPoly D.u := rfl

@[simp] theorem sexticSemiOfSemi_v
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl

@[simp] theorem sexticSemiOfSemi_nInf
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    (sexticSemiOfSemi D nInf).nInf = nInf := rfl

/-- Completion of the square transports every integral generalized graph
ideal, independently of a vertical Bézout witness. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChangeSemi D).u (baseChangeSemi D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemiOfSemi D nInf).u
        (sexticSemiOfSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChangeSemi D) nInf

/-- The standard reduced sextic semirepresentative over `ℚ₂`. -/
def sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    SexticMumford.SemiMumford
      (N13GoodSexticCoordinateEquiv.M (K := Q₂)) :=
  N13GoodSexticMumfordTransport.toSexticSemi
    (baseChange D) nInf

@[simp] theorem sexticSemi_u
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).u = mapPoly D.u := rfl

@[simp] theorem sexticSemi_v
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).v =
      N13GoodSexticMumfordTransport.reducedCompletedGraph
        (mapPoly D.u) (mapPoly D.v) := rfl

@[simp] theorem sexticSemi_nInf
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    (sexticSemi D nInf).nInf = nInf := rfl

/-- The two-adic sextic graph ideal is exactly the image of the generalized
graph ideal under completion of the square. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map
        (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂))
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (baseChange D).u (baseChange D).v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (sexticSemi D nInf).u
        (sexticSemi D nInf).v :=
  N13GoodSexticMumfordTransport.map_mumfordIdeal_toSexticSemi
    (baseChange D) nInf

end

end MazurProof.N13TwoAdicMumfordTransport


