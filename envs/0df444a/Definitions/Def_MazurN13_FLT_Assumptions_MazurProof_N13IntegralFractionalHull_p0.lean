-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFractionalHull_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralFractionalHull_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:11:00.283665+00:00
-- url     : https://prove2.me/theorems/822c3e86-dec1-485c-83fd-b52f8a696f46
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralFractionalHull source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralFractionalHull

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralFractionalHull
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralModelContraction_p0
import Mathlib.RingTheory.FractionalIdeal.Extended

set_option autoImplicit false




/-!
# Divisorial hulls on the N13 integral model

The N13 generic affine ring is the vertical localization of its integral
good-model ring.  This file proves that the common function field is also the
fraction field of the integral model and that vertical extension commutes with
inverse fractional ideals.

The reverse inclusion is the substantive point: a fractional ideal over the
Noetherian integral model has finitely many generators, so one vertical scalar
clears all denominators of their products with a generic inverse section.
Consequently the divisorial double inverse of a contracted invertible generic
ideal has exactly the original generic fibre.  No affine generator or
principality assumption is used.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13IntegralFractionalHull

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev FunctionField : Type :=
  N13Mumford.FunctionField
    N13IntegralModelContraction.Q₂

def integralToRational : IntegralRing →+* RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  integralToRational.toAlgebra

theorem integralToRational_injective :
    Function.Injective integralToRational := by
  exact
    (N13GoodSexticCoordinateEquiv.coordinateRingEquiv
      (K := N13IntegralModelContraction.Q₂)).injective.comp
      N13TwoAdicCoordinateBaseChange.extendCoordinate_injective

local instance integralRingDomain : IsDomain IntegralRing :=
  integralToRational_injective.isDomain integralToRational

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

/-- The function field of the generic fibre is also the fraction field of
the integral model. -/
theorem functionField_isFractionRing :
    IsFractionRing IntegralRing FunctionField := by
  let M := N13IntegralModelContraction.verticalScalars
  let N := nonZeroDivisors RationalRing
  have hloc :
      IsLocalization
          (N.comap (algebraMap IntegralRing RationalRing))
          FunctionField :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M N FunctionField (fun x hx => by
        change x ∈ nonZeroDivisors RationalRing
        rw [mem_nonZeroDivisors_iff_ne_zero]
        exact hx.ne_zero)
  have hsub :
      N.comap (algebraMap IntegralRing RationalRing) =
        nonZeroDivisors IntegralRing := by
    ext a
    change
      integralToRational a ∈ nonZeroDivisors RationalRing ↔
        a ∈ nonZeroDivisors IntegralRing
    simp only [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using
      (integralToRational_injective.ne_iff
        (x := a) (y := 0))
  rw [hsub] at hloc
  exact hloc

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  functionField_isFractionRing

abbrev IntegralFractionalIdeal : Type :=
  FractionalIdeal IntegralRing⁰ FunctionField

abbrev RationalFractionalIdeal : Type :=
  FractionalIdeal RationalRing⁰ FunctionField

def nonZeroDivisors_le_comap :
    IntegralRing⁰ ≤
      RationalRing⁰.comap integralToRational :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    integralToRational integralToRational_injective

/-- Extension of fractional ideals from the integral model to its generic
affine coordinate ring. -/
def extendFractional :
    IntegralFractionalIdeal →+* RationalFractionalIdeal :=
  FractionalIdeal.extendedHom'
    FunctionField nonZeroDivisors_le_comap

/-- The induced self-map of the common function field is the identity. -/
theorem fractionFieldMap_eq_id :
    IsLocalization.map
        FunctionField integralToRational
        nonZeroDivisors_le_comap =
      RingHom.id FunctionField := by
  apply IsLocalization.ringHom_ext IntegralRing⁰
  apply DFunLike.ext _ _
  intro a
  change
    IsLocalization.map
        FunctionField integralToRational
        nonZeroDivisors_le_comap
        (algebraMap IntegralRing FunctionField a) =
      algebraMap IntegralRing FunctionField a
  rw [IsLocalization.map_eq]
  rfl

/-- The contracted generic ideal, regarded inside the common function
field. -/
def contractedFractional
    (J : Ideal RationalRing) :
    IntegralFractionalIdeal :=
  (N13IntegralModelContraction.contractIdeal J :
    IntegralFractionalIdeal)

/-- Extending the contracted fractional ideal recovers the original generic
ideal exactly. -/
theorem extendFractional_contracted
    (J : Ideal RationalRing) :
    extendFractional (contractedFractional J) =
      (J : RationalFractionalIdeal) := by
  rw [extendFractional, contractedFractional,
    FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map]
  unfold integralToRational
  rw [N13IntegralModelContraction.map_contractIdeal]

theorem mem_extendFractional_of_mem
    {I : IntegralFractionalIdeal} {x : FunctionField}
    (hx : x ∈ I) :
    x ∈ extendFractional I := by
  change
    x ∈ FractionalIdeal.extended
      FunctionField nonZeroDivisors_le_comap
        I
  rw [FractionalIdeal.mem_extended_iff]
  apply Submodule.subset_span
  refine ⟨x, hx, ?_⟩
  rw [fractionFieldMap_eq_id]
  rfl

theorem mem_generic_of_mem_contracted
    (J : Ideal RationalRing) {x : FunctionField}
    (hx : x ∈ contractedFractional J) :
    x ∈ (J : RationalFractionalIdeal) := by
  rw [← extendFractional_contracted J]
  exact mem_extendFractional_of_mem hx

theorem mem_rational_one_of_mem_integral_one
    {x : FunctionField}
    (hx : x ∈ (1 : IntegralFractionalIdeal)) :
    x ∈ (1 : RationalFractionalIdeal) := by
  obtain ⟨a, ha⟩ :=
    (FractionalIdeal.mem_one_iff IntegralRing⁰).mp hx
  apply (FractionalIdeal.mem_one_iff RationalRing⁰).mpr
  refine ⟨integralToRational a, ?_⟩
  change
    algebraMap RationalRing FunctionField
        (algebraMap IntegralRing RationalRing a) = x
  rw [← IsScalarTower.algebraMap_apply
    IntegralRing RationalRing FunctionField]
  exact ha

theorem contractedFractional_ne_zero
    {J : Ideal RationalRing} (hJ : J ≠ ⊥) :
    contractedFractional J ≠ 0 := by
  rw [contractedFractional,
    FractionalIdeal.coeIdeal_ne_zero]
  exact
    N13IntegralModelContraction.contractIdeal_ne_bot hJ

theorem contractedFractional_fg
    (J : Ideal RationalRing) :
    (contractedFractional J).coeToSubmodule.FG := by
  change
    (((N13IntegralModelContraction.contractIdeal J :
        Ideal IntegralRing) :
      IntegralFractionalIdeal).coeToSubmodule).FG
  rw [FractionalIdeal.coeIdeal_fg IntegralRing⁰
    (IsFractionRing.injective IntegralRing FunctionField)]
  exact IsNoetherian.noetherian _

theorem fractional_fg
    (I : IntegralFractionalIdeal) :
    I.coeToSubmodule.FG :=
  FractionalIdeal.fg_of_isNoetherianRing (le_refl IntegralRing⁰) I

/-- Extension of an inverse is contained in the inverse of the extension.
This direction does not use finite generation. -/
theorem extendFractional_inv_le
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    extendFractional I⁻¹ ≤
      (extendFractional I)⁻¹ := by
  have hExtended : extendFractional I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      FunctionField nonZeroDivisors_le_comap
        integralToRational_injective hI (by simp)
  intro z hz
  change
    z ∈ FractionalIdeal.extended
      FunctionField nonZeroDivisors_le_comap I⁻¹ at hz
  rw [FractionalIdeal.mem_extended_iff] at hz
  refine Submodule.span_induction
    (p := fun z _ => z ∈
      (extendFractional I)⁻¹)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨y, hy, rfl⟩
    rw [fractionFieldMap_eq_id]
    rw [FractionalIdeal.mem_inv_iff hExtended]
    intro x hx
    change
      x ∈ FractionalIdeal.extended
        FunctionField nonZeroDivisors_le_comap I at hx
    rw [FractionalIdeal.mem_extended_iff] at hx
    refine Submodule.span_induction
      (p := fun x _ => y * x ∈
        (1 : RationalFractionalIdeal))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      rw [fractionFieldMap_eq_id]
      apply mem_rational_one_of_mem_integral_one
      exact
        (FractionalIdeal.mem_inv_iff hI).mp hy a ha
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]
      exact
        ((1 : RationalFractionalIdeal) :
          Submodule RationalRing FunctionField).add_mem ha hb
    · intro a b _ hb
      have hsmul :=
        ((1 : RationalFractionalIdeal) :
          Submodule RationalRing FunctionField).smul_mem a hb
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hsmul
  · exact FractionalIdeal.zero_mem _
  · intro a b _ _ ha hb
    exact
      (((extendFractional I)⁻¹ :
        RationalFractionalIdeal) :
        Submodule RationalRing FunctionField).add_mem ha hb
  · intro a b _ hb
    exact
      (((extendFractional I)⁻¹ :
        RationalFractionalIdeal) :
        Submodule RationalRing FunctionField).smul_mem a hb

set_option maxHeartbeats 800000 in
/-- Finite generation supplies one common vertical denominator, giving the
reverse inclusion for inverse fractional ideals. -/
theorem inv_extendFractional_le
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    (extendFractional I)⁻¹ ≤
      extendFractional I⁻¹ := by
  have hExtended : extendFractional I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      FunctionField nonZeroDivisors_le_comap
        integralToRational_injective hI (by simp)
  obtain ⟨n, g, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (fractional_fg I)
  intro z hz
  have hgI (i : Fin n) : g i ∈ I := by
    change g i ∈ I.coeToSubmodule
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzg (i : Fin n) :
      z * g i ∈ (1 : RationalFractionalIdeal) := by
    exact
      (FractionalIdeal.mem_inv_iff hExtended).mp hz
        (g i) (mem_extendFractional_of_mem (hgI i))
  choose b hb using fun i =>
    (FractionalIdeal.mem_one_iff RationalRing⁰).mp (hzg i)
  obtain ⟨s, hs⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      N13IntegralModelContraction.verticalScalars b
  choose a ha using fun i => hs i
  have hszInv :
      (s : IntegralRing) • z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI]
    intro x hx
    change x ∈ I.coeToSubmodule at hx
    rw [← hspan] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        ((s : IntegralRing) • z) * x ∈
          (1 : IntegralFractionalIdeal))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      apply (FractionalIdeal.mem_one_iff IntegralRing⁰).mpr
      refine ⟨a i, ?_⟩
      calc
        algebraMap IntegralRing FunctionField (a i) =
            algebraMap RationalRing FunctionField
              (algebraMap IntegralRing RationalRing (a i)) := by
                rw [IsScalarTower.algebraMap_apply
                  IntegralRing RationalRing FunctionField]
        _ = algebraMap RationalRing FunctionField
              ((s : IntegralRing) • b i) := by rw [ha i]
        _ = (s : IntegralRing) •
              algebraMap RationalRing FunctionField (b i) := by
                simp only [Algebra.smul_def]
                rw [map_mul,
                  IsScalarTower.algebraMap_apply
                    IntegralRing RationalRing FunctionField]
        _ = (s : IntegralRing) • (z * g i) := by rw [hb i]
        _ = ((s : IntegralRing) • z) * g i := by
              simp [Algebra.smul_def, mul_assoc]
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact
        ((1 : IntegralFractionalIdeal) :
          Submodule IntegralRing FunctionField).add_mem hx hy
    · intro r x _ hx
      have hrx :=
        ((1 : IntegralFractionalIdeal) :
          Submodule IntegralRing FunctionField).smul_mem r hx
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hrx
  have hszExtended :
      (s : IntegralRing) • z ∈
        extendFractional I⁻¹ := by
    change
      (s : IntegralRing) • z ∈
        FractionalIdeal.extended
          FunctionField nonZeroDivisors_le_comap I⁻¹
    rw [FractionalIdeal.mem_extended_iff]
    apply Submodule.subset_span
    refine ⟨(s : IntegralRing) • z, hszInv, ?_⟩
    rw [fractionFieldMap_eq_id]
    rfl
  exact
    (IsLocalization.smul_mem_iff
      (R := IntegralRing) (R' := RationalRing)
      (N' :=
        (extendFractional I⁻¹ :
          Submodule RationalRing FunctionField))
      (s := s)).mp hszExtended

/-- Extension along the vertical localization commutes with inverse for every
nonzero fractional ideal of the Noetherian integral model. -/
theorem extendFractional_inv
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    extendFractional I⁻¹ =
      (extendFractional I)⁻¹ :=
  le_antisymm
    (extendFractional_inv_le hI)
    (inv_extendFractional_le hI)

theorem extendFractional_inv_contracted
    {J : Ideal RationalRing} (hJ : J ≠ ⊥) :
    extendFractional (contractedFractional J)⁻¹ =
      (J : RationalFractionalIdeal)⁻¹ := by
  rw [extendFractional_inv
    (contractedFractional_ne_zero hJ),
    extendFractional_contracted]

/-- The inverse of a nonzero fractional ideal is nonzero. -/
theorem fractional_inv_ne_zero
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    I⁻¹ ≠ 0 := by
  intro hzero
  have hden := FractionalIdeal.den_mem_inv hI
  rw [hzero, FractionalIdeal.mem_zero_iff] at hden
  exact
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      I.den.prop) hden

/-- The vertical generic-fibre functor preserves the divisorial double
inverse. -/
theorem extendFractional_inv_inv
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    extendFractional I⁻¹⁻¹ =
      (extendFractional I)⁻¹⁻¹ := by
  rw [extendFractional_inv (fractional_inv_ne_zero hI),
    extendFractional_inv hI]

/-- Every nonzero fractional ideal maps into its divisorial double inverse.
This is the algebraic evaluation map into the double dual. -/
theorem le_inv_inv
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    I ≤ I⁻¹⁻¹ := by
  have hInv : I⁻¹ ≠ 0 :=
    fractional_inv_ne_zero hI
  intro x hx
  rw [FractionalIdeal.mem_inv_iff hInv]
  intro y hy
  rw [mul_comm]
  exact
    (FractionalIdeal.mem_inv_iff hI).mp hy x hx

/-- Multiplier inverse is unchanged by taking the divisorial double inverse.
Equivalently, triple inverse equals single inverse for every nonzero
fractional ideal. -/
theorem inv_inv_inv
    {I : IntegralFractionalIdeal} (hI : I ≠ 0) :
    I⁻¹⁻¹⁻¹ = I⁻¹ := by
  have hInv : I⁻¹ ≠ 0 :=
    fractional_inv_ne_zero hI
  have hInvInv : I⁻¹⁻¹ ≠ 0 :=
    fractional_inv_ne_zero hInv
  apply le_antisymm
  · exact
      FractionalIdeal.inv_anti_mono
        hI hInvInv (le_inv_inv hI)
  · exact le_inv_inv hInv

/-- Divisorial/reflexive hull of the contracted ideal. -/
def divisorialHull
    (J : Ideal RationalRing) :
    IntegralFractionalIdeal :=
  (contractedFractional J)⁻¹⁻¹

/-- The multiplier inverse of the divisorial hull is already the multiplier
inverse of the original contracted ideal. -/
theorem divisorialHull_inv
    {J : Ideal RationalRing} (hJ : J ≠ ⊥) :
    (divisorialHull J)⁻¹ =
      (contractedFractional J)⁻¹ := by
  rw [divisorialHull,
    inv_inv_inv (contractedFractional_ne_zero hJ)]

theorem extendFractional_divisorialHull
    {J : Ideal RationalRing} (hJ : J ≠ ⊥) :
    extendFractional (divisorialHull J) =
      (J : RationalFractionalIdeal)⁻¹⁻¹ := by
  rw [divisorialHull,
    extendFractional_inv_inv
      (contractedFractional_ne_zero hJ),
    extendFractional_contracted]

/-- Double inverse fixes every invertible fractional ideal. -/
theorem inv_inv_eq_of_isUnit
    {I : RationalFractionalIdeal} (hI : IsUnit I) :
    I⁻¹⁻¹ = I := by
  have hmul : I * I⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      FunctionField).mpr hI
  exact
    (FractionalIdeal.right_inverse_eq
      FunctionField I⁻¹ I (by simpa [mul_comm] using hmul)).symm

theorem extendFractional_divisorialHull_eq
    {J : Ideal RationalRing} (hJ : J ≠ ⊥)
    (hUnit : IsUnit (J : RationalFractionalIdeal)) :
    extendFractional (divisorialHull J) =
      (J : RationalFractionalIdeal) := by
  rw [extendFractional_divisorialHull hJ,
    inv_inv_eq_of_isUnit hUnit]

/-- The divisorial hull attached to an integral oriented Mumford
representative has exactly the same generic finite ideal. -/
theorem orientedRep_divisorialHull_genericFiber
    (R : N13IntegralModelContraction.IntegralOrientedRep) :
    extendFractional (divisorialHull R.ideal) =
      (R.ideal : RationalFractionalIdeal) :=
  extendFractional_divisorialHull_eq
    (R.ideal_ne_bot (N13Mumford.model
      N13IntegralModelContraction.Q₂))
    (R.ideal_isUnit (N13Mumford.model
      N13IntegralModelContraction.Q₂))

theorem contractedFractional_le_divisorialHull
    {J : Ideal RationalRing} (hJ : J ≠ ⊥) :
    contractedFractional J ≤ divisorialHull J :=
  le_inv_inv (contractedFractional_ne_zero hJ)

theorem extended_mono
    {I L : IntegralFractionalIdeal} (hIL : I ≤ L) :
    extendFractional I ≤ extendFractional L := by
  intro x hx
  change
    x ∈ FractionalIdeal.extended
      FunctionField nonZeroDivisors_le_comap I at hx
  change
    x ∈ FractionalIdeal.extended
      FunctionField nonZeroDivisors_le_comap L
  rw [FractionalIdeal.mem_extended_iff] at hx ⊢
  exact Submodule.span_mono (Set.image_mono hIL) hx

/-- The evaluation map into the divisorial hull gives the easy generic-fibre
containment directly. -/
theorem genericIdeal_le_extended_divisorialHull
    {J : Ideal RationalRing} (hJ : J ≠ ⊥) :
    (J : RationalFractionalIdeal) ≤
      extendFractional (divisorialHull J) := by
  rw [← extendFractional_contracted J]
  exact
    extended_mono
      (contractedFractional_le_divisorialHull hJ)

/-- The integral defect ideal attached to a fractional ideal.  Its
fractional extension is the evaluation product `H * H⁻¹`, which lies in the
unit fractional ideal by definition of inverse. -/
def defectIdeal
    (H : IntegralFractionalIdeal) :
    Ideal IntegralRing :=
  Classical.choose
    (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
      (by
        simpa only [FractionalIdeal.inv_eq] using
          (FractionalIdeal.mul_one_div_le_one
            (I := H))))

theorem coe_defectIdeal
    (H : IntegralFractionalIdeal) :
    (defectIdeal H : IntegralFractionalIdeal) =
      H * H⁻¹ :=
  Classical.choose_spec
    (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
      (by
        simpa only [FractionalIdeal.inv_eq] using
          (FractionalIdeal.mul_one_div_le_one
            (I := H))))

/-- Generic-fibre invertibility forces the defect ideal to be generically
the unit ideal. -/
theorem map_defectIdeal_eq_top
    {H : IntegralFractionalIdeal}
    (hH : H ≠ 0)
    (hGeneric :
      IsUnit (extendFractional H)) :
    Ideal.map integralToRational (defectIdeal H) = ⊤ := by
  rw [← Ideal.one_eq_top]
  apply
    (FractionalIdeal.coeIdeal_eq_one
      (K := FunctionField)).mp
  change
    ((Ideal.map integralToRational (defectIdeal H) :
      Ideal RationalRing) : RationalFractionalIdeal) = 1
  calc
    ((Ideal.map integralToRational (defectIdeal H) :
        Ideal RationalRing) : RationalFractionalIdeal) =
        extendFractional
          (defectIdeal H : IntegralFractionalIdeal) := by
      rw [extendFractional,
        FractionalIdeal.extendedHom'_apply,
        FractionalIdeal.extended_coeIdeal_eq_map]
    _ = 1 := by
      rw [coe_defectIdeal, map_mul,
        extendFractional_inv hH]
      exact
        (FractionalIdeal.mul_inv_cancel_iff_isUnit
          FunctionField).mpr hGeneric

/-- Equality of the defect ideal with the unit ideal is exactly the desired
invertibility conclusion. -/
theorem isUnit_of_defectIdeal_eq_top
    {H : IntegralFractionalIdeal}
    (hDefect : defectIdeal H = ⊤) :
    IsUnit H := by
  apply
    (FractionalIdeal.mul_inv_cancel_iff_isUnit
      FunctionField).mp
  rw [← coe_defectIdeal H, hDefect]
  show
    ((⊤ : Ideal IntegralRing) :
      IntegralFractionalIdeal) = 1
  exact FractionalIdeal.coeIdeal_top IntegralRing⁰

end

end MazurProof.N13IntegralFractionalHull


