-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomain
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomain
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:11:21.941091+00:00
-- url     : https://prove2.me/theorems/94a2fc39-acef-5d3c-bf69-7648528b16d3
-- title:
--   Finite Integral Closure Of Ess Finite Type Int Domain
-- statement:
--   Definitions and structural lemmas for Finite Integral Closure Of Ess Finite Type Int Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteIntegralClosureOfEssFiniteTypeIntDomain.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory
theorem finite_integralClosure_of_isLocalization {R S L : Type*} [CommRing R] [CommRing S]
    [CommRing L] [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R L)
  let f : integralClosure R L → integralClosure S L := fun z => ⟨z, IsIntegral.tower_top z.2⟩
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (Rₘ := S) (y : L) y.2
  have key : ∀ z ∈ Submodule.span R (s : Set (integralClosure R L)),
      f z ∈ Submodule.span S (↑(s.image f) : Set (integralClosure S L)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
    | zero =>
      have : f 0 = 0 := rfl
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := rfl
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : f (a • x) = algebraMap R S a • f x := by
        apply Subtype.ext
        change a • (x : L) = algebraMap R S a • (x : L)
        rw [algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have hz : (⟨m • (y : L), hm⟩ : integralClosure R L) ∈ Submodule.span R (s : Set _) :=
    hs ▸ Submodule.mem_top
  have e : y = IsLocalization.mk' S (1 : R) m • f ⟨m • (y : L), hm⟩ := by
    apply Subtype.ext
    change (y : L) = IsLocalization.mk' S (1 : R) m • ((m : R) • (y : L))
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S L, ← mul_assoc,
      ← map_mul, IsLocalization.mk'_spec, map_one, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ hz)
theorem finite_integralClosure_of_essFiniteType_int :
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      Module.Finite D (integralClosure D (FractionRing D)) := by
  intro D _ _ _
  obtain ⟨S₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ D).mp inferInstance
  let K := FractionRing D
  have hinj : Function.Injective (algebraMap S₀ D) := Subtype.val_injective
  haveI hfr : IsFractionRing S₀ K := by
    have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M (nonZeroDivisors D) K
      (fun x hx => hx.mem_nonZeroDivisors)
    have e : (nonZeroDivisors D).comap (algebraMap S₀ D) = nonZeroDivisors S₀ := by
      ext x
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq]
      exact (map_eq_zero_iff _ hinj).not
    rw [e] at h
    exact h
  suffices h : Module.Finite S₀ (integralClosure S₀ K) from
    finite_integralClosure_of_isLocalization M
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | h0
  · haveI : Fact (ringChar D).Prime := ⟨hp⟩
    haveI : CharP D (ringChar D) := ringChar.charP D
    haveI : CharP S₀ (ringChar D) := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff D]⟩
    letI : Algebra (ZMod (ringChar D)) S₀ := (ZMod.castHom dvd_rfl S₀).toAlgebra
    haveI : Algebra.FiniteType (ZMod (ringChar D)) S₀ :=
      .of_restrictScalars_finiteType ℤ (ZMod (ringChar D)) S₀
    exact NormFin.finite_integralClosure_of_perfectField (ZMod (ringChar D)) S₀ K K
  · haveI : CharZero D := (CharP.ringChar_zero_iff_CharZero D).mp h0
    haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective D K)
    haveI : Algebra.EssFiniteType S₀ D := .of_isLocalization D M
    haveI : Algebra.EssFiniteType D K := .of_isLocalization K (nonZeroDivisors D)
    haveI : Algebra.EssFiniteType S₀ K := .comp S₀ D K
    exact finite_integralClosure_of_essFiniteType_field ℤ S₀ K
example : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    Module.Finite D (integralClosure D (FractionRing D)) := finite_integralClosure_of_essFiniteType_int
end GlobalTheory


