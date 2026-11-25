-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
-- name    : GroundTheory_PAdicHodge_BdRGalois
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:14.5664+00:00
-- url     : https://prove2.me/theorems/3a41c873-f4ed-4a60-a826-489942184560
-- title:
--   Bd RGalois
-- statement:
--   Definitions and structural lemmas for Bd RGalois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_gal_smul
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Ideal WittVector IsLocalRing
namespace GroundTheory.PAdicHodge
section AdicCompletion
variable {A : Type*} [CommRing A] (I : Ideal A)
theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := AdicCompletion.AdicCauchySequence.mk_eq_mk hle c
  rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at h
  exact h
end AdicCompletion
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
variable (K p) in

def evalB (n : ℕ) : 𝔹 →+* 𝔸 ⧸ J ^ n := (AdicCompletion.evalₐ J n).toRingHom
omit [CharZero K] in
theorem evalB_ext {x y : 𝔹} (h : ∀ n, evalB K p n x = evalB K p n y) : x = y :=
  AdicCompletion.ext_evalₐ h
end IsPerfectoidField
section Galois
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝒪" => normInteger ℂ_[p]
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger ℂ_[p]) p))
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
omit hp in
theorem isUnit_algebraMap_p_away [Fact p.Prime] :
    IsUnit ((algebraMap 𝕎𝒪♭ 𝔸) (p : 𝕎𝒪♭)) :=
  IsLocalization.Away.algebraMap_isUnit (S := 𝔸) (p : 𝕎𝒪♭)
theorem gal_smul_mem_ker_fontaineTheta (σ : Gal(PadicAlgCl p/K)) {w : 𝕎𝒪♭}
    (hw : w ∈ RingHom.ker θ) : σ • w ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker] at hw ⊢
  have h := AInf.fontaineTheta_gal_smul σ w
  rw [hw, ZeroMemClass.coe_zero, smul_zero] at h
  exact Subtype.ext h
def galAway (σ : Gal(PadicAlgCl p/K)) : 𝔸 →+* 𝔸 :=
  Localization.awayLift ((algebraMap 𝕎𝒪♭ 𝔸).comp (AInf.galMap σ)) (p : 𝕎𝒪♭)
    (by simpa using isUnit_algebraMap_p_away (p := p))
@[simp]
theorem galAway_algebraMap (σ : Gal(PadicAlgCl p/K)) (w : 𝕎𝒪♭) :
    galAway σ (algebraMap 𝕎𝒪♭ 𝔸 w) = algebraMap 𝕎𝒪♭ 𝔸 (σ • w) :=
  IsLocalization.Away.lift_eq (S := 𝔸) (p : 𝕎𝒪♭)
    (by simpa using isUnit_algebraMap_p_away (p := p)) w
theorem galAway_one : galAway (1 : Gal(PadicAlgCl p/K)) = RingHom.id 𝔸 :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : 𝕎𝒪♭)) (RingHom.ext fun w => by
    simp only [RingHom.comp_apply, galAway_algebraMap, one_smul, RingHom.id_apply])
theorem galAway_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galAway (σ * τ) = (galAway σ).comp (galAway τ) :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : 𝕎𝒪♭)) (RingHom.ext fun w => by
    simp only [RingHom.comp_apply, galAway_algebraMap, mul_smul])
theorem map_galAway_le (σ : Gal(PadicAlgCl p/K)) : Ideal.map (galAway σ) J ≤ J := by
  have hξ := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[p] p
  rw [ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff, galAway_algebraMap, SetLike.mem_coe]
  have h : σ • IsPerfectoidField.kerThetaGenerator ℂ_[p] p ∈ RingHom.ker θ :=
    gal_smul_mem_ker_fontaineTheta σ (hξ ▸ Ideal.mem_span_singleton_self _)
  rw [hξ, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  rw [hc, map_mul, Ideal.mem_span_singleton]
  exact dvd_mul_right _ _
theorem pow_le_comap_galAway (σ : Gal(PadicAlgCl p/K)) (n : ℕ) :
    J ^ n ≤ (J ^ n).comap (galAway σ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_galAway_le σ) n
def galQuot (σ : Gal(PadicAlgCl p/K)) (n : ℕ) : 𝔸 ⧸ J ^ n →+* 𝔸 ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) (galAway σ) (pow_le_comap_galAway σ n)
@[simp]
theorem galQuot_mk (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (a : 𝔸) :
    galQuot σ n (Ideal.Quotient.mk (J ^ n) a) = Ideal.Quotient.mk (J ^ n) (galAway σ a) :=
  Ideal.quotientMap_mk
theorem galQuot_one (n : ℕ) : galQuot (1 : Gal(PadicAlgCl p/K)) n = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk, galAway_one, RingHom.id_apply])
theorem galQuot_mul (σ τ : Gal(PadicAlgCl p/K)) (n : ℕ) :
    galQuot (σ * τ) n = (galQuot σ n).comp (galQuot τ n) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk, galAway_mul])
theorem factorPow_galQuot (σ : Gal(PadicAlgCl p/K)) {m n : ℕ} (hle : m ≤ n) (y : 𝔸 ⧸ J ^ n) :
    Ideal.Quotient.factorPow J hle (galQuot σ n y) = galQuot σ m (Ideal.Quotient.factorPow J hle y) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [galQuot_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
theorem galQuot_evalB_compat (σ : Gal(PadicAlgCl p/K)) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp ((galQuot σ n).comp (IsPerfectoidField.evalB ℂ_[p] p n)) =
      (galQuot σ m).comp (IsPerfectoidField.evalB ℂ_[p] p m) :=
  RingHom.ext fun x => by
    simp only [RingHom.comp_apply]
    rw [factorPow_galQuot]
    exact congrArg (galQuot σ m) (factorPow_evalₐ J hle x)
def galBdRHom (σ : Gal(PadicAlgCl p/K)) : 𝔹 →+* 𝔹 :=
  AdicCompletion.liftRingHom J (fun n => (galQuot σ n).comp (IsPerfectoidField.evalB ℂ_[p] p n))
    (galQuot_evalB_compat σ)
theorem evalB_galBdRHom (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (x : 𝔹) :
    IsPerfectoidField.evalB ℂ_[p] p n (galBdRHom σ x) =
      galQuot σ n (IsPerfectoidField.evalB ℂ_[p] p n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (galQuot_evalB_compat σ) n x
theorem galBdRHom_one : galBdRHom (1 : Gal(PadicAlgCl p/K)) = RingHom.id 𝔹 :=
  RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, galQuot_one, RingHom.id_apply, RingHom.id_apply]
theorem galBdRHom_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galBdRHom (σ * τ) = (galBdRHom σ).comp (galBdRHom τ) :=
  RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by
    rw [RingHom.comp_apply, evalB_galBdRHom, evalB_galBdRHom, evalB_galBdRHom, galQuot_mul,
      RingHom.comp_apply]
instance instMulSemiringActionBdR : MulSemiringAction Gal(PadicAlgCl p/K) 𝔹 where
  smul σ x := galBdRHom σ x
  one_smul x := by
    change galBdRHom 1 x = x
    rw [galBdRHom_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galBdRHom (σ * τ) x = galBdRHom σ (galBdRHom τ x)
    rw [galBdRHom_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galBdRHom σ)
  smul_add σ := map_add (galBdRHom σ)
  smul_one σ := map_one (galBdRHom σ)
  smul_mul σ := map_mul (galBdRHom σ)
def galBdR (σ : Gal(PadicAlgCl p/K)) : 𝔹 ≃+* 𝔹 :=
  MulSemiringAction.toRingEquiv Gal(PadicAlgCl p/K) 𝔹 σ
end Galois
end GroundTheory.PAdicHodge


