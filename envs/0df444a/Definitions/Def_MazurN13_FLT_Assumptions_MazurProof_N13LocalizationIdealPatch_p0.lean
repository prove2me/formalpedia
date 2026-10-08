-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalizationIdealPatch_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13LocalizationIdealPatch_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:32:25.475968+00:00
-- url     : https://prove2.me/theorems/a34c6abf-67fb-4bf2-9244-8fc35335ef45
-- title:
--   FLT.Assumptions.MazurProof.N13LocalizationIdealPatch source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13LocalizationIdealPatch

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LocalizationIdealPatch
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TraceGluing_p0
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Localization.Finiteness

set_option autoImplicit false




/-!
# Patching an invertible ideal across one principal localization

Let `B = A[f⁻¹]` and let `K` be the common fraction field.  For a finitely
generated fractional ideal, extension from `A` to `B` commutes with the
multiplier inverse: one power of `f` clears the finitely many denominators
that occur on a generating family.

Consequently, if an integral ideal becomes invertible over `B`, some power
of `f` belongs to `I I⁻¹`.  If `f` is already a unit modulo `I`, a finite
geometric series gives `1 ∈ I I⁻¹`, so `I` is invertible over `A`.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13LocalizationIdealPatch

noncomputable section

variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]

include B M

/-- Every element inverted in the domain localization is nonzero. -/
theorem submonoid_le_nonZeroDivisors :
    M ≤ A⁰ := by
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hzero
  have hunit := IsLocalization.map_units B ⟨x, hx⟩
  have hmapZero : algebraMap A B x = 0 := by
    rw [hzero, map_zero]
  exact hunit.ne_zero hmapZero

/-- The nonzero elements of `A` remain nonzero after localization in `B`. -/
def nonZeroDivisors_le_comap :
    A⁰ ≤ B⁰.comap (algebraMap A B) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
    (algebraMap A B)
      (IsLocalization.injective B
        (submonoid_le_nonZeroDivisors (A := A) (B := B) M))

/-- A fraction field of a localization is also a fraction field of the
original domain. -/
theorem fractionRing_of_localization_fractionRing
    [IsFractionRing B K] :
    IsFractionRing A K := by
  let N := nonZeroDivisors B
  have hloc :
      IsLocalization
          (N.comap (algebraMap A B))
          K :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M N K (fun x hx => by
        change x ∈ nonZeroDivisors B
        rw [mem_nonZeroDivisors_iff_ne_zero]
        exact hx.ne_zero)
  have hsub :
      N.comap (algebraMap A B) =
        nonZeroDivisors A := by
    ext a
    change
      algebraMap A B a ∈ nonZeroDivisors B ↔
        a ∈ nonZeroDivisors A
    simp only [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using
      ((IsLocalization.injective B
          (submonoid_le_nonZeroDivisors (A := A) (B := B) M)).ne_iff
        (x := a) (y := 0))
  rw [hsub] at hloc
  exact hloc

/-- Extending the kernel of a map across a localization gives the kernel
of any compatible map out of the localized ring. -/
theorem map_ker_eq_ker_of_isLocalization
    {C : Type*} [CommRing C]
    (f : A →+* C)
    (g : B →+* C)
    (hcomp :
      g.comp (algebraMap A B) = f) :
    Ideal.map (algebraMap A B) (RingHom.ker f) =
      RingHom.ker g := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change g (algebraMap A B a) = 0
    rw [← RingHom.comp_apply, hcomp, ha]
  · intro z hz
    obtain ⟨⟨a, s⟩, hzs⟩ := IsLocalization.surj M z
    have ha : a ∈ RingHom.ker f := by
      rw [RingHom.mem_ker]
      have hzero := congrArg g hzs
      rw [map_mul, RingHom.mem_ker.mp hz, zero_mul,
        ← RingHom.comp_apply, hcomp] at hzero
      exact hzero.symm
    have hma :
        algebraMap A B a ∈
          Ideal.map (algebraMap A B) (RingHom.ker f) :=
      Ideal.mem_map_of_mem (algebraMap A B) ha
    have hzsMem :
        z * algebraMap A B (s : A) ∈
          Ideal.map (algebraMap A B) (RingHom.ker f) := by
      rw [hzs]
      exact hma
    exact
      (Ideal.unit_mul_mem_iff_mem
        (Ideal.map (algebraMap A B) (RingHom.ker f))
        (IsLocalization.map_units B s)).mp
          (by simpa [mul_comm] using hzsMem)

variable [IsFractionRing A K] [IsFractionRing B K]

/-- Extension of fractional ideals to the principal localization. -/
def extendFractional :
    FractionalIdeal A⁰ K →+* FractionalIdeal B⁰ K :=
  FractionalIdeal.extendedHom'
    K (nonZeroDivisors_le_comap (A := A) (B := B) M)

/-- The induced endomorphism of the common fraction field is the identity. -/
theorem fractionFieldMap_eq_id :
    IsLocalization.map
        K (algebraMap A B)
        (nonZeroDivisors_le_comap (A := A) (B := B) M) =
      RingHom.id K := by
  apply IsLocalization.ringHom_ext A⁰
  apply DFunLike.ext _ _
  intro a
  change
    IsLocalization.map
        K (algebraMap A B)
        (nonZeroDivisors_le_comap (A := A) (B := B) M)
        (algebraMap A K a) =
      algebraMap A K a
  rw [IsLocalization.map_eq]
  exact (IsScalarTower.algebraMap_apply A B K a).symm

/-- Every section of a fractional ideal maps into its localization. -/
theorem mem_extendFractional_of_mem
    {I : FractionalIdeal A⁰ K} {x : K}
    (hx : x ∈ I) :
    x ∈ extendFractional (A := A) (B := B) (K := K) M I := by
  change
    x ∈ FractionalIdeal.extended
      K (nonZeroDivisors_le_comap (A := A) (B := B) M) I
  rw [FractionalIdeal.mem_extended_iff]
  apply Submodule.subset_span
  refine ⟨x, hx, ?_⟩
  rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
  rfl

/-- Extension of the multiplier inverse is contained in the inverse of
the extended fractional ideal. -/
theorem extendFractional_inv_le
    {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    extendFractional (A := A) (B := B) (K := K) M I⁻¹ ≤
      (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ := by
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      K (nonZeroDivisors_le_comap (A := A) (B := B) M)
        hAB hI (by simp)
  intro z hz
  change
    z ∈ FractionalIdeal.extended
      K (nonZeroDivisors_le_comap (A := A) (B := B) M) I⁻¹ at hz
  rw [FractionalIdeal.mem_extended_iff] at hz
  refine Submodule.span_induction
    (p := fun z _ =>
      z ∈
        (extendFractional (A := A) (B := B) (K := K) M I)⁻¹)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨y, hy, rfl⟩
    rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
    rw [FractionalIdeal.mem_inv_iff hExtended]
    intro x hx
    change
      x ∈ FractionalIdeal.extended
        K (nonZeroDivisors_le_comap (A := A) (B := B) M) I at hx
    rw [FractionalIdeal.mem_extended_iff] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        y * x ∈ (1 : FractionalIdeal B⁰ K))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
      obtain ⟨r, hr⟩ :=
        (FractionalIdeal.mem_one_iff A⁰).mp
          ((FractionalIdeal.mem_inv_iff hI).mp hy a ha)
      apply (FractionalIdeal.mem_one_iff B⁰).mpr
      refine ⟨algebraMap A B r, ?_⟩
      rw [← IsScalarTower.algebraMap_apply A B K]
      exact hr
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]
      exact
        ((1 : FractionalIdeal B⁰ K) :
          Submodule B K).add_mem ha hb
    · intro a b _ hb
      have hsmul :=
        ((1 : FractionalIdeal B⁰ K) :
          Submodule B K).smul_mem a hb
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hsmul
  · exact FractionalIdeal.zero_mem _
  · intro a b _ _ ha hb
    exact
      ((((extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :
          FractionalIdeal B⁰ K)) :
        Submodule B K).add_mem ha hb
  · intro a b _ hb
    exact
      ((((extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :
          FractionalIdeal B⁰ K)) :
        Submodule B K).smul_mem a hb

/-- Finite generation clears one common localization denominator and gives
the reverse inclusion for multiplier inverses. -/
theorem inv_extendFractional_le
    {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0)
    (hfg : I.coeToSubmodule.FG) :
    (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ ≤
      extendFractional (A := A) (B := B) (K := K) M I⁻¹ := by
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      K (nonZeroDivisors_le_comap (A := A) (B := B) M)
        hAB hI (by simp)
  obtain ⟨n, g, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hfg
  intro z hz
  have hgI (i : Fin n) : g i ∈ I := by
    change g i ∈ I.coeToSubmodule
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzg (i : Fin n) :
      z * g i ∈ (1 : FractionalIdeal B⁰ K) := by
    exact
      (FractionalIdeal.mem_inv_iff hExtended).mp hz
        (g i)
        (mem_extendFractional_of_mem
          (A := A) (B := B) (K := K) M (hgI i))
  choose b hb using fun i =>
    (FractionalIdeal.mem_one_iff B⁰).mp (hzg i)
  obtain ⟨s, hs⟩ :=
    IsLocalization.exist_integer_multiples_of_finite M b
  choose a ha using fun i => hs i
  have hszInv :
      (s : A) • z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI]
    intro x hx
    change x ∈ I.coeToSubmodule at hx
    rw [← hspan] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        ((s : A) • z) * x ∈
          (1 : FractionalIdeal A⁰ K))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      apply (FractionalIdeal.mem_one_iff A⁰).mpr
      refine ⟨a i, ?_⟩
      calc
        algebraMap A K (a i) =
            algebraMap B K (algebraMap A B (a i)) := by
              rw [IsScalarTower.algebraMap_apply A B K]
        _ = algebraMap B K ((s : A) • b i) := by rw [ha i]
        _ = (s : A) • algebraMap B K (b i) := by
              simp only [Algebra.smul_def]
              rw [map_mul,
                IsScalarTower.algebraMap_apply A B K]
        _ = (s : A) • (z * g i) := by rw [hb i]
        _ = ((s : A) • z) * g i := by
              simp [Algebra.smul_def, mul_assoc]
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact
        ((1 : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem hx hy
    · intro r x _ hx
      have hrx :=
        ((1 : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem r hx
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hrx
  have hszExtended :
      (s : A) • z ∈
        extendFractional (A := A) (B := B) (K := K) M I⁻¹ := by
    change
      (s : A) • z ∈
        FractionalIdeal.extended
          K (nonZeroDivisors_le_comap (A := A) (B := B) M) I⁻¹
    rw [FractionalIdeal.mem_extended_iff]
    apply Submodule.subset_span
    refine ⟨(s : A) • z, hszInv, ?_⟩
    rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
    rfl
  exact
    (IsLocalization.smul_mem_iff
      (R := A) (R' := B)
      (N' :=
        (extendFractional (A := A) (B := B) (K := K) M I⁻¹ :
          Submodule B K))
      (s := s)).mp hszExtended

/-- Extension through a localization commutes with multiplier inverse for
every nonzero finitely generated fractional ideal. -/
theorem extendFractional_inv
    {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0)
    (hfg : I.coeToSubmodule.FG) :
    extendFractional (A := A) (B := B) (K := K) M I⁻¹ =
      (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :=
  le_antisymm
    (extendFractional_inv_le (A := A) (B := B) (K := K) M hI)
    (inv_extendFractional_le
      (A := A) (B := B) (K := K) M hI hfg)

/-- If a finitely generated fractional ideal becomes invertible after
localization, one element of the localization submonoid lies in `I I⁻¹`. -/
theorem exists_submonoid_mem_mul_inv
    (I : FractionalIdeal A⁰ K)
    (hfg : I.coeToSubmodule.FG)
    (hlocal :
      IsUnit
        (extendFractional (A := A) (B := B) (K := K) M I)) :
    ∃ s : M, algebraMap A K (s : A) ∈ I * I⁻¹ := by
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    hlocal.ne_zero
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hI : I ≠ 0 := by
    intro hzero
    apply hExtended
    rw [hzero]
    exact map_zero
      (extendFractional (A := A) (B := B) (K := K) M)
  have hExtMul :
      extendFractional (A := A) (B := B) (K := K) M (I * I⁻¹) =
        1 := by
    rw [map_mul,
      extendFractional_inv
        (A := A) (B := B) (K := K) M hI hfg]
    exact
      (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hlocal
  have hone :
      (1 : K) ∈
        extendFractional (A := A) (B := B) (K := K) M (I * I⁻¹) := by
    rw [hExtMul]
    simp
  change
    (1 : K) ∈
      FractionalIdeal.extended
        K (nonZeroDivisors_le_comap (A := A) (B := B) M)
          (I * I⁻¹) at hone
  rw [FractionalIdeal.mem_extended_iff] at hone
  rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M] at hone
  have hone' :
      (1 : K) ∈
        Submodule.span B (I * I⁻¹ : Set K) := by
    simpa using hone
  obtain ⟨s, hs⟩ :=
    multiple_mem_span_of_mem_localization_span
      M B (I * I⁻¹ : Set K) (1 : K) hone'
  refine ⟨s, ?_⟩
  change
    s • (1 : K) ∈
      Submodule.span A
        ((((I * I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K)) : Set K) at hs
  rw [Submodule.span_eq] at hs
  change
    algebraMap A K (s : A) ∈
      ((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K)
  simpa only [Submonoid.smul_def, Algebra.smul_def, mul_one] using hs

omit M in
/-- An ideal that is invertible after localizing at powers of `f` is
already invertible when `f` is a unit modulo that ideal. -/
theorem ideal_isUnit_of_localized_isUnit
    (f : A)
    [IsLocalization (Submonoid.powers f) B]
    (I : Ideal A)
    (hfg : I.FG)
    (hmod : ∃ a : A, 1 - f * a ∈ I)
    (hlocal :
      IsUnit
        (extendFractional
          (A := A) (B := B) (K := K)
          (Submonoid.powers f)
          (I : FractionalIdeal A⁰ K))) :
    IsUnit (I : FractionalIdeal A⁰ K) := by
  let IF : FractionalIdeal A⁰ K :=
    (I : FractionalIdeal A⁰ K)
  have hfgF : IF.coeToSubmodule.FG := by
    change
      ((I : FractionalIdeal A⁰ K) :
        Submodule A K).FG
    rw [FractionalIdeal.coeIdeal_fg A⁰
      (IsFractionRing.injective A K)]
    exact hfg
  obtain ⟨s, hs⟩ :=
    exists_submonoid_mem_mul_inv
      (A := A) (B := B) (K := K)
      (Submonoid.powers f) IF hfgF hlocal
  obtain ⟨n, hn⟩ := s.2
  have hpow :
      ∃ n : ℕ,
        algebraMap A K (f ^ n) ∈ IF * IF⁻¹ := by
    refine ⟨n, ?_⟩
    simpa only [hn] using hs
  obtain ⟨a, ha⟩ := hmod
  have hmod' :
      ∃ a : A,
        algebraMap A K (1 - f * a) ∈ IF * IF⁻¹ := by
    refine ⟨a, ?_⟩
    exact
      FractionalIdeal.coe_ideal_le_self_mul_inv K I
        (FractionalIdeal.mem_coeIdeal_of_mem A⁰ ha)
  exact
    N13TraceGluing.isUnit_of_genericPower_and_modUniformizerTrace
      IF hpow hmod'

end

end MazurProof.N13LocalizationIdealPatch


