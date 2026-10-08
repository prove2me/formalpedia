-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicCoordinateBaseChange_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicCoordinateBaseChange_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:05:15.694977+00:00
-- url     : https://prove2.me/theorems/da636d5c-a9ca-4b9d-9aa7-524a791ded3f
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicCoordinateBaseChange
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicMumfordTransport_p0

set_option autoImplicit false




/-!
# Base change of the N13 integral coordinate ring to `ℚ₂`

Coefficient extension from `ℤ₂` to `ℚ₂` induces a map between the two
generalized-hyperelliptic coordinate rings.  It carries an integral Mumford
graph ideal exactly onto the graph ideal obtained by coefficient extension.
Composing with completion of the square therefore sends the integral graph
directly to the standard sextic Mumford graph over `ℚ₂`.
-/

open Polynomial

namespace MazurProof.N13TwoAdicCoordinateBaseChange

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicMumfordTransport.R₂

abbrev Q₂ : Type :=
  N13TwoAdicMumfordTransport.Q₂

abbrev IntegralRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := R₂)

abbrev GoodRing : Type :=
  N13GeneralizedMumfordIntegral.CoordinateRing (R := Q₂)

def coeffMap : R₂ →+* Q₂ :=
  N13TwoAdicMumfordTransport.coeffMap

def mapPoly : R₂[X] →+* Q₂[X] :=
  N13TwoAdicMumfordTransport.mapPoly

@[simp] theorem mapPoly_apply (p : R₂[X]) :
    mapPoly p = p.map coeffMap := rfl

/-- Coefficient extension from `ℤ₂[X]` to `ℚ₂[X]` is faithful. -/
theorem mapPoly_injective : Function.Injective mapPoly :=
  Polynomial.map_injective coeffMap
    (IsFractionRing.injective R₂ Q₂)

@[simp] theorem mapPoly_hPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.hPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_hPoly

@[simp] theorem mapPoly_rhsPoly :
    mapPoly
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂) :=
  N13TwoAdicMumfordTransport.mapPoly_rhsPoly

theorem map_curvePoly :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly =
      N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul]
  change
    X ^ 2 +
          C (mapPoly
            (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) * X -
        C (mapPoly
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
      X ^ 2 +
          C (N13GeneralizedMumfordIntegral.hPoly (R := Q₂)) * X -
        C (N13GeneralizedMumfordIntegral.rhsPoly (R := Q₂))
  rw [mapPoly_hPoly, mapPoly_rhsPoly]

private theorem target_curve_dvd :
    N13GeneralizedMumfordIntegral.curvePoly (R := Q₂) ∣
      (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).map
        mapPoly := by
  rw [map_curvePoly]

/-- Coefficient extension on the affine coordinate ring of the good model. -/
def extendCoordinate : IntegralRing →+* GoodRing :=
  AdjoinRoot.map mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_xClass (p : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) =
      N13GeneralizedMumfordIntegral.xClass
        (R := Q₂) (mapPoly p) := by
  exact AdjoinRoot.map_of
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd p

@[simp] theorem extend_yClass :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
      N13GeneralizedMumfordIntegral.yClass (R := Q₂) := by
  exact AdjoinRoot.map_root
    mapPoly
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂))
    (N13GeneralizedMumfordIntegral.curvePoly (R := Q₂))
    target_curve_dvd

@[simp] theorem extend_ySubClass (v : R₂[X]) :
    extendCoordinate
        (N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v) =
      N13GeneralizedMumfordIntegral.ySubClass
        (R := Q₂) (mapPoly v) := by
  simp [N13GeneralizedMumfordIntegral.ySubClass]

/-- Coefficient extension preserves the `1`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeff0_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeff0
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeff0 z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp

/-- Coefficient extension preserves the `Y`-coordinate in the rank-two
presentation of the generalized coordinate ring. -/
@[simp] theorem coeffY_extendCoordinate (z : IntegralRing) :
    N13GeneralizedMumfordIntegral.coeffY
        (extendCoordinate z) =
      mapPoly (N13GeneralizedMumfordIntegral.coeffY z) := by
  rw [← N13GeneralizedMumfordIntegral.recompose z]
  simp

/-- Base change from the integral good model to its generic fibre loses no
functions.  This is the rank-two basis argument, not a localization
calculation in coordinates. -/
theorem extendCoordinate_injective :
    Function.Injective extendCoordinate := by
  intro z w h
  apply
    (N13GeneralizedMumfordIntegral.eq_iff_coeff z w).2
  constructor
  · apply mapPoly_injective
    simpa only [coeff0_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeff0 h
  · apply mapPoly_injective
    simpa only [coeffY_extendCoordinate] using congrArg
      N13GeneralizedMumfordIntegral.coeffY h

/-- Coefficient extension maps an integral graph ideal onto the
coefficient-extended graph ideal. -/
theorem map_mumfordIdeal (u v : R₂[X]) :
    Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := Q₂) (mapPoly u) (mapPoly v) := by
  rw [N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    Ideal.map_span, Set.image_pair, extend_xClass,
    extend_ySubClass]

/-- Extension followed by contraction fixes every integral generalized
Mumford graph.  The proof only uses monicity and coefficientwise
divisibility descent; no special-fibre smoothness witness is involved. -/
theorem comap_map_mumfordIdeal_semi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂) :
    (Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v)).comap extendCoordinate =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) D.u D.v := by
  ext z
  rw [Ideal.mem_comap, map_mumfordIdeal]
  change
    extendCoordinate z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13TwoAdicMumfordTransport.baseChangeSemi D).u
          (N13TwoAdicMumfordTransport.baseChangeSemi D).v ↔
      z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v
  rw [
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff
      (N13TwoAdicMumfordTransport.baseChangeSemi D),
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff D]
  simp only [N13TwoAdicMumfordTransport.baseChangeSemi_u,
    N13TwoAdicMumfordTransport.baseChangeSemi_v,
    coeff0_extendCoordinate, coeffY_extendCoordinate]
  change
    D.u.map coeffMap ∣
          (N13GeneralizedMumfordIntegral.coeff0 z).map coeffMap +
            (N13GeneralizedMumfordIntegral.coeffY z).map coeffMap *
              D.v.map coeffMap ↔
      D.u ∣
        N13GeneralizedMumfordIntegral.coeff0 z +
          N13GeneralizedMumfordIntegral.coeffY z * D.v
  rw [← Polynomial.map_mul, ← Polynomial.map_add]
  exact Polynomial.map_dvd_map coeffMap
    (IsFractionRing.injective R₂ Q₂) D.u_monic

/-- Extending a smooth integral graph to the generic fibre and contracting
it back recovers the original graph.  The reason is exactly that divisibility
by a monic polynomial descends along an injective coefficient map. -/
theorem comap_map_mumfordIdeal
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂) :
    (Ideal.map extendCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v)).comap extendCoordinate =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) D.u D.v := by
  ext z
  rw [Ideal.mem_comap, map_mumfordIdeal]
  change
    extendCoordinate z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13TwoAdicMumfordTransport.baseChange D).u
          (N13TwoAdicMumfordTransport.baseChange D).v ↔
      z ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          D.toSemiMumford.u D.toSemiMumford.v
  rw [
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff
      (N13TwoAdicMumfordTransport.baseChange D),
    N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff
      D.toSemiMumford]
  simp only [N13TwoAdicMumfordTransport.baseChange_u,
    N13TwoAdicMumfordTransport.baseChange_v,
    coeff0_extendCoordinate, coeffY_extendCoordinate]
  change
    D.u.map coeffMap ∣
          (N13GeneralizedMumfordIntegral.coeff0 z).map coeffMap +
            (N13GeneralizedMumfordIntegral.coeffY z).map coeffMap *
              D.v.map coeffMap ↔
      D.u ∣
        N13GeneralizedMumfordIntegral.coeff0 z +
          N13GeneralizedMumfordIntegral.coeffY z * D.v
  rw [← Polynomial.map_mul, ← Polynomial.map_add]
  exact Polynomial.map_dvd_map coeffMap
    (IsFractionRing.injective R₂ Q₂) D.u_monic

/-- Consequently coefficient extension is injective on smooth integral
Mumford graph ideals. -/
theorem map_mumfordIdeal_injective
    {D E : N13GeneralizedMumfordReduction.SmoothMumford₂}
    (h :
      Ideal.map extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) D.u D.v) =
        Ideal.map extendCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) E.u E.v)) :
    N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) E.u E.v := by
  rw [← comap_map_mumfordIdeal D,
    ← comap_map_mumfordIdeal E, h]

/-- The full integral-to-sextic coordinate map over `ℚ₂`. -/
def integralToSextic :
    IntegralRing →+*
      N13GoodSexticCoordinateEquiv.SexticRing (K := Q₂) :=
  (N13GoodSexticCoordinateEquiv.toSextic (K := Q₂)).comp
    extendCoordinate

/-- An integral smooth graph ideal becomes exactly the standard reduced
sextic Mumford graph attached by `sexticSemi`. -/
theorem map_mumfordIdeal_sexticSemi
    (D : N13GeneralizedMumfordReduction.SmoothMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi
      D nInf

/-- The same coordinate transport theorem for arbitrary integral
semigraphs. -/
theorem map_mumfordIdeal_sexticSemiOfSemi
    (D :
      N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (nInf : ℤ) :
    Ideal.map integralToSextic
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) D.u D.v) =
      SexticMumford.mumfordIdeal
        (N13GoodSexticCoordinateEquiv.M (K := Q₂))
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).u
        (N13TwoAdicMumfordTransport.sexticSemiOfSemi D nInf).v := by
  rw [integralToSextic, ← Ideal.map_map,
    map_mumfordIdeal]
  exact
    N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemiOfSemi
      D nInf

end

end MazurProof.N13TwoAdicCoordinateBaseChange


