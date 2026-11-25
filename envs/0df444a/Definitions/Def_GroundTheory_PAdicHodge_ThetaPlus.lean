-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
-- name    : GroundTheory_PAdicHodge_ThetaPlus
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:47.72841+00:00
-- url     : https://prove2.me/theorems/9ac1a5d5-4cd7-5c79-8176-d5640d0d759a
-- title:
--   Theta Plus
-- statement:
--   Definitions and structural lemmas for Theta Plus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ThetaPlus.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mem_ker_fontaineTheta_isUnit_coeff_one
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_preTilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_wittVector_preTilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isPrincipal_ker_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_frobenius
import Theorems.Thm_GroundTheory_PAdicHodge_smodEq_span_singleton_pow_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Ideal WittVector IsLocalRing
section Abstract
variable {B : Type*} [CommRing B]
theorem ker_adicCompletion_evalₐ {A : Type*} [CommRing A] {I : Ideal A} (fg : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  have h1 : I ^ n ≤ (I ^ n • ⊤ : Ideal A) := by simp
  have h2 : (I ^ n • ⊤ : Ideal A) ≤ I ^ n := by simp
  trans x ∈ (AdicCompletion.eval I A n).ker
  · constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      rw [LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval I x h1]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hx
      simp [hx]
    · intro hx
      rw [LinearMap.mem_ker] at hx
      rw [RingHom.mem_ker]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x h2, hx, map_zero]
  · rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]
    rfl
theorem exists_eq_pow_mul_unit_of_isAdicComplete {π : B} [IsAdicComplete (span {π}) B]
    (hmax : (span {π}).IsMaximal) {x : B} (hx : x ≠ 0) : ∃ (n : ℕ) (u : Bˣ), x = π ^ n * u := by
  classical
  have := hmax
  have : IsLocalRing B := isLocalRing_of_isAdicComplete_maximal (span {π})
  have hm : maximalIdeal B = span {π} := (IsLocalRing.eq_maximalIdeal hmax).symm
  have hex : ∃ n, ¬ π ^ n ∣ x := by
    by_contra h
    push Not at h
    apply hx
    refine IsHausdorff.haus' (I := span {π}) x fun n => ?_
    rw [smodEq_span_singleton_pow_iff, sub_zero]
    exact h n
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    exact this (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hdvd : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    push Not at this
    exact this
  obtain ⟨u, rfl⟩ := hdvd
  have hu : IsUnit u := by
    by_contra hu
    have : u ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal u).mpr hu
    rw [hm, mem_span_singleton] at this
    obtain ⟨c, rfl⟩ := this
    have := Nat.find_spec hex
    rw [hk] at this
    exact this ⟨c, by rw [pow_succ]; ring⟩
  exact ⟨k, hu.unit, rfl⟩
theorem isDomain_of_isAdicComplete {π : B} [IsAdicComplete (span {π}) B]
    (hmax : (span {π}).IsMaximal) (hpow : ∀ n : ℕ, π ^ n ≠ 0) : IsDomain B := by
  have : Nontrivial B := ⟨⟨1, 0, by simpa using hpow 0⟩⟩
  have : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push Not at h
    obtain ⟨a, u, rfl⟩ := exists_eq_pow_mul_unit_of_isAdicComplete hmax h.1
    obtain ⟨b, v, rfl⟩ := exists_eq_pow_mul_unit_of_isAdicComplete hmax h.2
    apply hpow (a + b)
    have : π ^ (a + b) * ((u * v : Bˣ) : B) = 0 := by rw [Units.val_mul, ← hxy]; ring
    exact (Units.mul_left_eq_zero (u * v)).mp this
  exact NoZeroDivisors.to_isDomain B
theorem isDiscreteValuationRing_of_isAdicComplete {π : B} [IsAdicComplete (span {π}) B]
    (hmax : (span {π}).IsMaximal) (hpow : ∀ n : ℕ, π ^ n ≠ 0) :
    haveI := isDomain_of_isAdicComplete hmax hpow
    IsDiscreteValuationRing B ∧ Irreducible π := by
  have := isDomain_of_isAdicComplete hmax hpow
  have := hmax
  have : IsLocalRing B := isLocalRing_of_isAdicComplete_maximal (span {π})
  have hm : maximalIdeal B = span {π} := (IsLocalRing.eq_maximalIdeal hmax).symm
  have hπ0 : π ≠ 0 := by simpa using hpow 1
  have hnu : ¬ IsUnit π := by
    intro h
    exact hmax.ne_top (Ideal.span_singleton_eq_top.mpr h)
  have hirr : Irreducible π := by
    refine ⟨hnu, ?_⟩
    intro a b hab
    by_contra h
    push Not at h
    have ha : a ∈ span {π} := hm ▸ (IsLocalRing.mem_maximalIdeal a).mpr h.1
    have hb : b ∈ span {π} := hm ▸ (IsLocalRing.mem_maximalIdeal b).mpr h.2
    rw [mem_span_singleton] at ha hb
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := hb
    apply hnu
    have h1 : π * (1 - π * (c * d)) = 0 := by
      have : π = π * c * (π * d) := hab
      linear_combination this
    have h2 : 1 - π * (c * d) = 0 := (mul_eq_zero.mp h1).resolve_left hπ0
    exact isUnit_iff_exists_inv.mpr ⟨c * d, by linear_combination -h2⟩
  refine ⟨IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, ?_⟩, hirr⟩
  intro x hx
  obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit_of_isAdicComplete hmax hx
  exact ⟨n, u, rfl⟩
end Abstract
section General
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))
def toBDeRhamPlus : 𝔸 →+* BDeRhamPlus R p :=
  algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)
def wittToBDeRhamPlus : 𝕎R♭ →+* BDeRhamPlus R p :=
  (toBDeRhamPlus R p).comp (algebraMap 𝕎R♭ 𝔸)
def thetaBDeRhamPlus : BDeRhamPlus R p →+* Localization.Away (p : R) :=
  (RingHom.kerLift (fontaineThetaInvertP R p)).comp
    (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p))).toRingHom
@[simp]
theorem thetaBDeRhamPlus_toBDeRhamPlus (x : 𝔸) :
    thetaBDeRhamPlus R p (toBDeRhamPlus R p x) = fontaineThetaInvertP R p x :=
  rfl
@[simp]
theorem fontaineThetaInvertP_algebraMap (x : 𝕎R♭) :
    fontaineThetaInvertP R p (algebraMap 𝕎R♭ 𝔸 x) =
      algebraMap R (Localization.Away (p : R)) (fontaineTheta R p x) :=
  IsLocalization.lift_eq _ x
@[simp]
theorem thetaBDeRhamPlus_wittToBDeRhamPlus (x : 𝕎R♭) :
    thetaBDeRhamPlus R p (wittToBDeRhamPlus R p x) =
      algebraMap R (Localization.Away (p : R)) (fontaineTheta R p x) :=
  fontaineThetaInvertP_algebraMap R p x
theorem surjective_fontaineThetaInvertP (hθ : Function.Surjective (fontaineTheta R p)) :
    Function.Surjective (fontaineThetaInvertP R p) := by
  intro z
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : R)) z
  obtain ⟨w, rfl⟩ := hθ r
  refine ⟨IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)), ?_⟩
  symm
  have hpn : algebraMap R (Localization.Away (p : R)) ((p : R) ^ n) =
      fontaineThetaInvertP R p (algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ n)) := by
    rw [fontaineThetaInvertP_algebraMap]
    simp
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp only
  rw [hpn, ← map_mul, IsLocalization.mk'_spec, fontaineThetaInvertP_algebraMap]
theorem surjective_thetaBDeRhamPlus (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (thetaBDeRhamPlus R p) := by
  intro z
  obtain ⟨x, rfl⟩ := surjective_fontaineThetaInvertP R p (surjective_fontaineTheta hF) z
  exact ⟨toBDeRhamPlus R p x, rfl⟩
variable {R p}
theorem ker_fontaineThetaInvertP {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    RingHom.ker (fontaineThetaInvertP R p) = span {algebraMap 𝕎R♭ 𝔸 ξ} := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨⟨w, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎R♭)) z
    have h1 : algebraMap R (Localization.Away (p : R)) (fontaineTheta R p w) = 0 := by
      rw [← fontaineThetaInvertP_algebraMap,
        ← IsLocalization.mk'_spec 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)),
        map_mul, hz, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : R)) _ _).mp h1
    have h2 : (p : 𝕎R♭) ^ k * w ∈ span {ξ} := by
      rw [← hξ, RingHom.mem_ker, map_mul, map_pow, map_natCast]
      exact hk
    obtain ⟨c, hc⟩ := mem_span_singleton'.mp h2
    have hu : IsUnit (algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * (p : 𝕎R♭) ^ n)) :=
      IsLocalization.map_units 𝔸 (⟨_, mul_mem (pow_mem (Submonoid.mem_powers _) k)
        (pow_mem (Submonoid.mem_powers _) n)⟩ : Submonoid.powers (p : 𝕎R♭))
    rw [mem_span_singleton, ← hu.dvd_mul_right]
    refine ⟨algebraMap 𝕎R♭ 𝔸 c, ?_⟩
    calc IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)) *
          algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * (p : 𝕎R♭) ^ n)
        = algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k) *
          (IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)) *
            algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ n)) := by rw [map_mul]; ring
      _ = algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * w) := by rw [IsLocalization.mk'_spec, map_mul]
      _ = algebraMap 𝕎R♭ 𝔸 ξ * algebraMap 𝕎R♭ 𝔸 c := by rw [← hc, map_mul, mul_comm]
  · rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      fontaineThetaInvertP_algebraMap]
    have : ξ ∈ RingHom.ker (fontaineTheta R p) := hξ ▸ mem_span_singleton_self ξ
    rw [RingHom.mem_ker] at this
    rw [this, map_zero]
theorem fg_ker_fontaineThetaInvertP {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    (RingHom.ker (fontaineThetaInvertP R p)).FG :=
  ⟨{algebraMap 𝕎R♭ 𝔸 ξ}, by rw [ker_fontaineThetaInvertP hξ, Finset.coe_singleton]⟩
theorem ker_thetaBDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    RingHom.ker (thetaBDeRhamPlus R p) = span {wittToBDeRhamPlus R p ξ} := by
  have h := AdicCompletion.ker_evalOneₐ_eq_map _ (fg_ker_fontaineThetaInvertP hξ)
  have h' : span {wittToBDeRhamPlus R p ξ} =
      (RingHom.ker (fontaineThetaInvertP R p)).map (toBDeRhamPlus R p) := by
    rw [ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton]
    rfl
  rw [h']
  ext x
  have h2 : ∀ y : AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸,
      y ∈ (RingHom.ker (fontaineThetaInvertP R p)).map
        (algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)) ↔
        AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p)) y = 0 := fun y => by
    rw [← h, RingHom.mem_ker]
    rfl
  have hx : thetaBDeRhamPlus R p x = 0 ↔
      AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p)) x = 0 :=
    map_eq_zero_iff (RingHom.kerLift (fontaineThetaInvertP R p)) (RingHom.kerLift_injective _)
  exact (RingHom.mem_ker.trans hx).trans (h2 x).symm
theorem isAdicComplete_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    IsAdicComplete (span {wittToBDeRhamPlus R p ξ}) (BDeRhamPlus R p) := by
  have h := AdicCompletion.isAdicComplete_self _ (fg_ker_fontaineThetaInvertP hξ)
  have h' : span {wittToBDeRhamPlus R p ξ} =
      (RingHom.ker (fontaineThetaInvertP R p)).map (toBDeRhamPlus R p) := by
    rw [ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton]
    rfl
  rw [h']
  exact h
theorem toBDeRhamPlus_mem_span_pow_iff {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (a : 𝔸) (n : ℕ) :
    toBDeRhamPlus R p a ∈ span {wittToBDeRhamPlus R p ξ ^ n} ↔ algebraMap 𝕎R♭ 𝔸 ξ ^ n ∣ a := by
  have h := ker_adicCompletion_evalₐ (fg_ker_fontaineThetaInvertP hξ) n
  have h' : span {wittToBDeRhamPlus R p ξ ^ n} =
      (RingHom.ker (fontaineThetaInvertP R p) ^ n).map (toBDeRhamPlus R p) := by
    rw [ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, map_pow]
    rfl
  rw [h']
  have h2 : ∀ y : AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸,
      y ∈ (RingHom.ker (fontaineThetaInvertP R p) ^ n).map
        (algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)) ↔
        AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP R p)) n y = 0 := fun y => by
    rw [← h, RingHom.mem_ker]
    rfl
  refine (h2 (algebraMap 𝔸 _ a)).trans ?_
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem, ker_fontaineThetaInvertP hξ,
    Ideal.span_singleton_pow, mem_span_singleton]
omit [IsAdicComplete (span {(p : R)}) R] in

theorem eq_zero_of_algebraMap_mul_eq_zero {x : 𝕎R♭} (hx : x ∈ nonZeroDivisors 𝕎R♭) {y : 𝔸}
    (h : algebraMap 𝕎R♭ 𝔸 x * y = 0) : y = 0 := by
  obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎R♭)) y
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨m, mem_nonZeroDivisors_iff_left.mp hx _ ?_⟩
  rw [← hm]
  ring
end General
section DVR
variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))
theorem isMaximal_ker_thetaBDeRhamPlus (hF : Function.Surjective (frobenius (ModP R p) p))
    (hK : IsField (Localization.Away (p : R))) : (RingHom.ker (thetaBDeRhamPlus R p)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hK
    (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlus R p hF)).toMulEquiv)
theorem pow_wittToBDeRhamPlus_ne_zero [Nontrivial (Localization.Away (p : R))] {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭) (n : ℕ) :
    wittToBDeRhamPlus R p ξ ^ n ≠ 0 := by
  intro h0
  have hmem : toBDeRhamPlus R p (algebraMap 𝕎R♭ 𝔸 ξ ^ n) ∈
      span {wittToBDeRhamPlus R p ξ ^ (n + 1)} := by
    rw [map_pow]
    change wittToBDeRhamPlus R p ξ ^ n ∈ _
    rw [h0]
    exact zero_mem _
  rw [toBDeRhamPlus_mem_span_pow_iff hξ] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : algebraMap 𝕎R♭ 𝔸 (ξ ^ n) * (1 - algebraMap 𝕎R♭ 𝔸 ξ * c) = 0 := by
    rw [map_pow, mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← hc, sub_self]
  have h2 := eq_zero_of_algebraMap_mul_eq_zero (pow_mem hξ0 n) h1
  have hone : (1 : 𝔸) ∈ RingHom.ker (fontaineThetaInvertP R p) := by
    rw [ker_fontaineThetaInvertP hξ, mem_span_singleton]
    exact ⟨c, by linear_combination h2⟩
  rw [RingHom.mem_ker, map_one] at hone
  exact one_ne_zero hone
theorem isLocalRing_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    IsLocalRing (BDeRhamPlus R p) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have : (span {wittToBDeRhamPlus R p ξ}).IsMaximal :=
    ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK
  exact isLocalRing_of_isAdicComplete_maximal (span {wittToBDeRhamPlus R p ξ})
theorem isDomain_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭) (hF : Function.Surjective (frobenius (ModP R p) p))
    (hK : IsField (Localization.Away (p : R))) : IsDomain (BDeRhamPlus R p) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have := hK.nontrivial
  exact isDomain_of_isAdicComplete
    (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK)
    (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)
theorem isDiscreteValuationRing_bDeRhamPlus {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭)
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isDomain_bDeRhamPlus hξ hξ0 hF hK
    IsDiscreteValuationRing (BDeRhamPlus R p) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have := hK.nontrivial
  exact (isDiscreteValuationRing_of_isAdicComplete
    (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK)
    (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)).1
theorem maximalIdeal_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    maximalIdeal (BDeRhamPlus R p) = RingHom.ker (thetaBDeRhamPlus R p) :=
  haveI := isLocalRing_bDeRhamPlus hξ hF hK
  (IsLocalRing.eq_maximalIdeal (isMaximal_ker_thetaBDeRhamPlus hF hK)).symm
def residueFieldBDeRhamPlusEquiv {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    ResidueField (BDeRhamPlus R p) ≃+* Localization.Away (p : R) :=
  haveI := isLocalRing_bDeRhamPlus hξ hF hK
  (Ideal.quotEquivOfEq (maximalIdeal_bDeRhamPlus hξ hF hK)).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlus R p hF))
end DVR
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p
theorem isLocalization_away [CharZero K] : IsLocalization.Away (p : 𝒪) K := by
  rw [IsLocalization.Away, isLocalization_iff]
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpn : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, map_natCast]
    exact (isUnit_iff_ne_zero.mpr hp0).pow n
  · intro z
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖z‖ + 1)⁻¹ by positivity) hpn
    refine ⟨⟨⟨z * (p : K) ^ n, ?_⟩, ⟨(p : 𝒪) ^ n, n, rfl⟩⟩, ?_⟩
    · rw [mem_normInteger, norm_mul, norm_pow]
      have h1 : ‖z‖ * ‖(p : K)‖ ^ n ≤ ‖z‖ * (‖z‖ + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left hn.le (norm_nonneg z)
      have h2 : ‖z‖ * (‖z‖ + 1)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        linarith
      linarith
    · rfl
  · intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩
def awayEquiv [CharZero K] : Localization.Away (p : 𝒪) ≃ₐ[𝒪] K :=
  haveI := isLocalization_away (K := K) p
  IsLocalization.algEquiv (Submonoid.powers (p : 𝒪)) _ K
theorem isField_away [CharZero K] : IsField (Localization.Away (p : 𝒪)) :=
  MulEquiv.isField (Field.toIsField K) (awayEquiv (K := K) p).toMulEquiv
def thetaBDeRhamPlusField [CharZero K] : 𝔹 →+* K :=
  (awayEquiv (K := K) p).toRingEquiv.toRingHom.comp (thetaBDeRhamPlus 𝒪 p)
theorem surjective_thetaBDeRhamPlusField [CharZero K] :
    Function.Surjective (thetaBDeRhamPlusField (K := K) p) :=
  (awayEquiv (K := K) p).surjective.comp (surjective_thetaBDeRhamPlus 𝒪 p (surjective_frobenius p))
theorem ker_thetaBDeRhamPlusField [CharZero K] :
    RingHom.ker (thetaBDeRhamPlusField (K := K) p) = RingHom.ker (thetaBDeRhamPlus 𝒪 p) := by
  ext x
  simp only [RingHom.mem_ker, thetaBDeRhamPlusField, RingHom.comp_apply]
  exact map_eq_zero_iff _ (awayEquiv (K := K) p).injective
variable {p}
theorem mem_nonZeroDivisors_of_ker_eq_span {ξ : 𝕎𝒪♭} (hξ : RingHom.ker θ = span {ξ}) :
    ξ ∈ nonZeroDivisors 𝕎𝒪♭ := by
  have := isDomain_preTilt (K := K) p
  have := isDomain_wittVector_preTilt K p
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  obtain ⟨ξ₀, h₀, h1⟩ := exists_mem_ker_fontaineTheta_isUnit_coeff_one K p
  rw [hξ, h0, mem_span_singleton, zero_dvd_iff] at h₀
  rw [h₀, zero_coeff] at h1
  exact not_isUnit_zero h1
variable (K p) in

def kerThetaGenerator : 𝕎𝒪♭ :=
  haveI := isPrincipal_ker_fontaineTheta K p
  Submodule.IsPrincipal.generator (RingHom.ker θ)
variable (K p) in

theorem ker_fontaineTheta_eq_span_kerThetaGenerator : RingHom.ker θ = span {kerThetaGenerator K p} :=
  haveI := isPrincipal_ker_fontaineTheta K p
  (Submodule.IsPrincipal.span_singleton_generator (RingHom.ker θ)).symm
variable [CharZero K]
instance isDomain_bDeRhamPlus : IsDomain 𝔹 :=
  GroundTheory.PAdicHodge.isDomain_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
    (mem_nonZeroDivisors_of_ker_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p))
    (surjective_frobenius p) (isField_away p)
instance isDiscreteValuationRing_bDeRhamPlus : IsDiscreteValuationRing 𝔹 :=
  GroundTheory.PAdicHodge.isDiscreteValuationRing_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
    (mem_nonZeroDivisors_of_ker_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p))
    (surjective_frobenius p) (isField_away p)
theorem maximalIdeal_bDeRhamPlus :
    maximalIdeal 𝔹 = RingHom.ker (thetaBDeRhamPlusField (K := K) p) := by
  rw [ker_thetaBDeRhamPlusField]
  exact GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
    (surjective_frobenius p) (isField_away p)
def residueFieldBDeRhamPlusEquiv : ResidueField 𝔹 ≃+* K :=
  (Ideal.quotEquivOfEq (maximalIdeal_bDeRhamPlus (K := K) (p := p))).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlusField (K := K) p))
end IsPerfectoidField
end GroundTheory.PAdicHodge


