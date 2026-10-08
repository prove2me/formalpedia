-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordOrientedBaseChange_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordOrientedBaseChange_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:24:20.202803+00:00
-- url     : https://prove2.me/theorems/0c05f30d-0fc8-4f88-81ed-7a25eee11e03
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBaseChange_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticOrientedPic_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0
import Mathlib.RingTheory.FractionalIdeal.Extended

set_option autoImplicit false




/-!
# Base change of oriented Picard classes for smooth sextics

An injective coefficient map carrying one sextic equation to another induces
maps on the affine coordinate rings, their fraction fields, and invertible
fractional ideals.  If the distinguished infinity orders are compatible,
the resulting map on oriented fractional ideals descends to an additive map
of the concrete oriented Picard groups.

The construction is algebraic: extension of fractional ideals and a quotient
universal property.  It does not use a relative Picard scheme.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford.OrientedBaseChange

noncomputable section

universe u v

variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}

/-- Coefficient extension on the polynomial base ring. -/
def mapPoly (ι : K →+* K') : K[X] →+* K'[X] :=
  Polynomial.mapRingHom ι

@[simp] theorem mapPoly_apply (ι : K →+* K') (p : K[X]) :
    mapPoly ι p = p.map ι := rfl

theorem map_curvePoly
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    (curvePoly M).map (mapPoly ι) = curvePoly M' := by
  simp [curvePoly, mapPoly, hM]

private theorem target_curve_dvd
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    curvePoly M' ∣ (curvePoly M).map (mapPoly ι) := by
  rw [map_curvePoly ι hM]

/-- Coefficient extension on the affine sextic coordinate ring. -/
def coordinateMap
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    CoordinateRing M →+* CoordinateRing M' :=
  AdjoinRoot.map (mapPoly ι) (curvePoly M) (curvePoly M')
    (target_curve_dvd ι hM)

@[simp] theorem coordinateMap_xClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (p : K[X]) :
    coordinateMap ι hM (xClass M p) =
      xClass M' (p.map ι) := by
  exact AdjoinRoot.map_of
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM) p

@[simp] theorem coordinateMap_yClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    coordinateMap ι hM (yClass M) = yClass M' := by
  exact AdjoinRoot.map_root
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM)

@[simp] private theorem coeff0_xClass_mul_yClass
    (N : Model K) (p : K[X]) :
    coeff0 N (xClass N p * yClass N) = 0 := by
  rw [show xClass N p =
    algebraMap K[X] (CoordinateRing N) p from rfl]
  rw [← Algebra.smul_def, map_smul, coeff0_yClass, smul_zero]

@[simp] private theorem coeffY_xClass_mul_yClass
    (N : Model K) (p : K[X]) :
    coeffY N (xClass N p * yClass N) = p := by
  rw [show xClass N p =
    algebraMap K[X] (CoordinateRing N) p from rfl]
  rw [← Algebra.smul_def, map_smul, coeffY_yClass, smul_eq_mul,
    mul_one]

@[simp] theorem coeff0_coordinateMap
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (z : CoordinateRing M) :
    coeff0 M' (coordinateMap ι hM z) =
      (coeff0 M z).map ι := by
  rw [← recompose M z]
  simp

@[simp] theorem coeffY_coordinateMap
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (z : CoordinateRing M) :
    coeffY M' (coordinateMap ι hM z) =
      (coeffY M z).map ι := by
  rw [← recompose M z]
  simp

/-- An injective coefficient map remains injective on the rank-two affine
coordinate ring. -/
theorem coordinateMap_injective
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    Function.Injective (coordinateMap ι hM) := by
  intro z w h
  apply (eq_iff_coeff M z w).2
  constructor
  · apply Polynomial.map_injective ι hι
    simpa only [coeff0_coordinateMap] using congrArg (coeff0 M') h
  · apply Polynomial.map_injective ι hι
    simpa only [coeffY_coordinateMap] using congrArg (coeffY M') h

/-- A nonzero element of the source coordinate ring stays nonzero after
coefficient extension. -/
theorem nonZeroDivisors_le_comap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    (CoordinateRing M)⁰ ≤
      Submonoid.comap (coordinateMap ι hM) (CoordinateRing M')⁰ := by
  intro z hz
  rw [mem_nonZeroDivisors_iff_ne_zero] at hz
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  simpa using (coordinateMap_injective ι hι hM).ne hz

/-- The induced map between the two fraction fields. -/
def functionMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    FunctionField M →+* FunctionField M' :=
  IsLocalization.map
    (M := (CoordinateRing M)⁰) (S := FunctionField M)
    (T := (CoordinateRing M')⁰) (FunctionField M')
    (coordinateMap ι hM) (nonZeroDivisors_le_comap ι hι hM)

@[simp] theorem functionMap_algebraMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (z : CoordinateRing M) :
    functionMap ι hι hM
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M') (FunctionField M')
        (coordinateMap ι hM z) := by
  exact IsLocalization.map_eq
    (nonZeroDivisors_le_comap ι hι hM) z

theorem functionMap_injective
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    Function.Injective (functionMap ι hι hM) :=
  (functionMap ι hι hM).injective

/-- Extension of fractional ideals along the affine coordinate-ring map. -/
def fractionalMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    FractionalIdeal (CoordinateRing M)⁰ (FunctionField M) →+*
      FractionalIdeal (CoordinateRing M')⁰ (FunctionField M') :=
  FractionalIdeal.extendedHom' (FunctionField M')
    (nonZeroDivisors_le_comap ι hι hM)

/-- Extension of invertible fractional ideals. -/
def invFracMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    InvFrac M →* InvFrac M' :=
  Units.map (fractionalMap ι hι hM).toMonoidHom

@[simp] theorem coe_invFracMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (I : InvFrac M) :
    ((invFracMap ι hι hM I : InvFrac M') :
        FractionalIdeal
          (CoordinateRing M')⁰ (FunctionField M')) =
      fractionalMap ι hι hM
        (I :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) :=
  rfl

/-- Extension of nonzero rational functions. -/
def functionUnitMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    (FunctionField M)ˣ →* (FunctionField M')ˣ :=
  Units.map (functionMap ι hι hM).toMonoidHom

/-- Compatibility required of the two chosen orders at infinity. -/
def InfinityCompatible
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M') : Prop :=
  ∀ α : (FunctionField M)ˣ,
    O'.ordPlus (functionUnitMap ι hι hM α) = O.ordPlus α

/-- Base change on the product of an invertible fractional ideal and its
integer infinity coordinate. -/
def orientedFracMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    OrientedFrac M →* OrientedFrac M' :=
  MonoidHom.prodMap (invFracMap ι hι hM)
    (MonoidHom.id (Multiplicative ℤ))

theorem invFracMap_toPrincipalIdeal
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (α : (FunctionField M)ˣ) :
    invFracMap ι hι hM
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α) =
      toPrincipalIdeal (CoordinateRing M') (FunctionField M')
        (functionUnitMap ι hι hM α) := by
  apply Units.ext
  simp only [invFracMap, functionUnitMap, Units.coe_map,
    coe_toPrincipalIdeal]
  change
    fractionalMap ι hι hM
        (FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (α : FunctionField M)) =
      FractionalIdeal.spanSingleton (CoordinateRing M')⁰
        (functionMap ι hι hM (α : FunctionField M))
  rw [fractionalMap, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_spanSingleton]
  rfl

theorem orientedFracMap_principalOriented
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O')
    (α : (FunctionField M)ˣ) :
    orientedFracMap ι hι hM (principalOriented M O α) =
      principalOriented M' O' (functionUnitMap ι hι hM α) := by
  apply Prod.ext
  · change
      invFracMap ι hι hM
          (toPrincipalIdeal (CoordinateRing M) (FunctionField M) α) =
        toPrincipalIdeal (CoordinateRing M') (FunctionField M')
          (functionUnitMap ι hι hM α)
    exact invFracMap_toPrincipalIdeal ι hι hM α
  · change
      O.ordPlus α =
        O'.ordPlus (functionUnitMap ι hι hM α)
    exact (hO α).symm

theorem principalRange_le_comap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O') :
    (principalOriented M O).range ≤
      Subgroup.comap (orientedFracMap ι hι hM)
        (principalOriented M' O').range := by
  intro z hz
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
  rw [Subgroup.mem_comap]
  exact MonoidHom.mem_range.mpr
    ⟨functionUnitMap ι hι hM α,
      (orientedFracMap_principalOriented ι hι hM O O' hO α).symm⟩

/-- The additive homomorphism on concrete oriented Picard groups induced by
coefficient extension. -/
def picMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O') :
    ConcretePic M O →+ ConcretePic M' O' :=
  MonoidHom.toAdditive <|
    QuotientGroup.map
      (principalOriented M O).range
      (principalOriented M' O').range
      (orientedFracMap ι hι hM)
      (principalRange_le_comap ι hι hM O O' hO)

@[simp] theorem coordinateMap_ySubClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (v : K[X]) :
    coordinateMap ι hM (ySubClass M v) =
      ySubClass M' (v.map ι) := by
  simp [ySubClass]

/-- A Mumford graph ideal extends to the coefficient-extended graph ideal. -/
theorem map_mumfordIdeal
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (u v : K[X]) :
    Ideal.map (coordinateMap ι hM) (mumfordIdeal M u v) =
      mumfordIdeal M' (u.map ι) (v.map ι) := by
  rw [mumfordIdeal, mumfordIdeal, Ideal.map_span, Set.image_pair,
    coordinateMap_xClass, coordinateMap_ySubClass]

/-- Fractional-ideal extension carries a literal Mumford graph ideal to
the coefficient-extended graph ideal. -/
theorem fractionalMap_coe_mumfordIdeal
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (u v : K[X]) :
    fractionalMap ι hι hM
        (mumfordIdeal M u v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M' (u.map ι) (v.map ι) :
        FractionalIdeal
          (CoordinateRing M')⁰ (FunctionField M')) := by
  calc
    fractionalMap ι hι hM
          (mumfordIdeal M u v :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) =
        (Ideal.map (coordinateMap ι hM)
            (mumfordIdeal M u v) :
          FractionalIdeal
            (CoordinateRing M')⁰ (FunctionField M')) :=
      FractionalIdeal.extended_coeIdeal_eq_map
        (FunctionField M')
        (nonZeroDivisors_le_comap ι hι hM)
        (mumfordIdeal M u v)
    _ = _ := by rw [map_mumfordIdeal]

theorem invFracMap_mumfordIdealUnit
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    invFracMap ι hι hM (mumfordIdealUnit M D.toSemi) =
      mumfordIdealUnit M' (D.mapCoeffs ι hι hM).toSemi := by
  apply Units.ext
  simp only [invFracMap, Units.coe_map, coe_mumfordIdealUnit]
  change
    (FractionalIdeal.extendedHom' (FunctionField M')
      (nonZeroDivisors_le_comap ι hι hM))
        (mumfordIdeal M D.u D.v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M'
          (D.u.map ι) (D.v.map ι) :
        FractionalIdeal (CoordinateRing M')⁰ (FunctionField M'))
  calc
    _ =
        (Ideal.map (coordinateMap ι hM)
            (mumfordIdeal M D.u D.v) :
          FractionalIdeal (CoordinateRing M')⁰ (FunctionField M')) :=
      FractionalIdeal.extended_coeIdeal_eq_map
        (FunctionField M')
        (nonZeroDivisors_le_comap ι hι hM)
        (mumfordIdeal M D.u D.v)
    _ = _ := by rw [map_mumfordIdeal]

theorem orientedFracMap_mumfordRaw
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    orientedFracMap ι hι hM (mumfordRaw M D) =
      mumfordRaw M' (D.mapCoeffs ι hι hM) := by
  apply Prod.ext
  · change
      invFracMap ι hι hM (mumfordIdealUnit M D.toSemi) =
        mumfordIdealUnit M' (D.mapCoeffs ι hι hM).toSemi
    exact invFracMap_mumfordIdealUnit ι hι hM D
  · rfl

/-- The quotient map sends the class of a Mumford graph to the class of its
coefficient extension. -/
@[simp] theorem picMap_classOf
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O')
    (D : Mumford M) :
    picMap ι hι hM O O' hO (classOf M O D) =
      classOf M' O' (D.mapCoeffs ι hι hM) := by
  change
    Additive.ofMul
        ((QuotientGroup.map
          (principalOriented M O).range
          (principalOriented M' O').range
          (orientedFracMap ι hι hM)
          (principalRange_le_comap ι hι hM O O' hO))
            (QuotientGroup.mk' (principalOriented M O).range
              (mumfordRaw M D))) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M' O').range
          (mumfordRaw M' (D.mapCoeffs ι hι hM)))
  rw [QuotientGroup.map_mk', orientedFracMap_mumfordRaw]
  rfl

end

end MazurProof.SexticMumford.OrientedBaseChange


