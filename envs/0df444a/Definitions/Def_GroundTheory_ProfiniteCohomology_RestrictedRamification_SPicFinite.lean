-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicFinite
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicFinite
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:12.298089+00:00
-- url     : https://prove2.me/theorems/d380eb05-8d6b-484f-8160-5195a2282bf7
-- title:
--   SPic Finite
-- statement:
--   Definitions and structural lemmas for SPic Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/SPicFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Theorems.Thm_GroundTheory_ProfCoh_divS_apply
import Theorems.Thm_GroundTheory_ProfCoh_ordAt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
variable {F : Type*} [Field F] [NumberField F]
noncomputable def integerUnit {a : 𝓞 F} (ha : a ≠ 0) : Fˣ :=
  Units.mk0 (algebraMap (𝓞 F) F a) (by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    exact ha)
theorem coe_integerUnit {a : 𝓞 F} (ha : a ≠ 0) : (integerUnit ha : F) = algebraMap (𝓞 F) F a :=
  rfl
theorem integerUnit_mul {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0) :
    integerUnit hab = integerUnit ha * integerUnit hb :=
  Units.ext (by simp [coe_integerUnit])
theorem integerUnit_pow {a : 𝓞 F} (ha : a ≠ 0) (k : ℕ) (hak : a ^ k ≠ 0) :
    integerUnit hak = integerUnit ha ^ k :=
  Units.ext (by simp [coe_integerUnit])
theorem ordAt_pow (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (k : ℕ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  simp only [ordAt, map_pow, toAdd_pow, nsmul_eq_mul]
  ring
theorem ordAt_integerUnit_eq_of_associated {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associated a b) (w : HeightOneSpectrum (𝓞 F)) :
    ordAt w (integerUnit ha) = ordAt w (integerUnit hb) := by
  obtain ⟨u, rfl⟩ := h
  have hu : integerUnit hb = integerUnit ha * Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u :=
    Units.ext (by simp [coe_integerUnit])
  rw [hu, ordAt_mul]
  simp [ordAt, valuation_of_unit_eq]
open scoped Classical in

theorem ordAt_placeUnit (v w : HeightOneSpectrum (𝓞 F)) :
    ordAt w (GroundTheory.Global.SUnit.placeUnit v) = if w = v then (classNumber F : ℤ) else 0 := by
  rw [ordAt, GroundTheory.Global.SUnit.valuationOfNeZero_placeUnit]
  split_ifs <;> simp
theorem placeUnit_eq_integerUnit (v : HeightOneSpectrum (𝓞 F)) :
    GroundTheory.Global.SUnit.placeUnit v =
      integerUnit (GroundTheory.Global.SUnit.exists_pow_classNumber_eq_span v).choose_spec.1 :=
  Units.ext rfl
def primeNZD (v : HeightOneSpectrum (𝓞 F)) : (Ideal (𝓞 F))⁰ :=
  ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
open scoped Classical in

theorem exists_ordAt_eq_of_mk0_eq {v p : HeightOneSpectrum (𝓞 F)}
    (h : ClassGroup.mk0 (primeNZD v) = ClassGroup.mk0 (primeNZD p)) :
    ∃ x : Fˣ, ∀ w, ordAt w x = (if w = v then 1 else 0) - (if w = p then 1 else 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  change Ideal.span {a} * v.asIdeal = Ideal.span {b} * p.asIdeal at hab
  set hF := classNumber F with hhF
  have hv := GroundTheory.Global.SUnit.exists_pow_classNumber_eq_span v
  have hp := GroundTheory.Global.SUnit.exists_pow_classNumber_eq_span p
  set πv := hv.choose
  set πp := hp.choose
  have hπv : πv ≠ 0 := hv.choose_spec.1
  have hπp : πp ≠ 0 := hp.choose_spec.1
  have hav : a ^ hF * πv ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) hπv
  have hbp : b ^ hF * πp ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) hπp
  have hspan : Ideal.span {a ^ hF * πv} = Ideal.span {b ^ hF * πp} := by
    have := congrArg (· ^ hF) hab
    simp only [mul_pow, Ideal.span_singleton_pow] at this
    rw [hv.choose_spec.2, hp.choose_spec.2, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton] at this
    exact this
  have hassoc := Ideal.span_singleton_eq_span_singleton.1 hspan
  refine ⟨integerUnit hb * (integerUnit ha)⁻¹, fun w => ?_⟩
  have key := ordAt_integerUnit_eq_of_associated hav hbp hassoc w
  rw [integerUnit_mul (pow_ne_zero _ ha) hπv hav, integerUnit_mul (pow_ne_zero _ hb) hπp hbp,
    integerUnit_pow ha hF (pow_ne_zero _ ha), integerUnit_pow hb hF (pow_ne_zero _ hb),
    ordAt_mul, ordAt_mul, ordAt_pow, ordAt_pow] at key
  have hv' : ordAt w (integerUnit hπv) = if w = v then (hF : ℤ) else 0 := by
    rw [← ordAt_placeUnit v w, placeUnit_eq_integerUnit]
  have hp' : ordAt w (integerUnit hπp) = if w = p then (hF : ℤ) else 0 := by
    rw [← ordAt_placeUnit p w, placeUnit_eq_integerUnit]
  rw [hv', hp'] at key
  have hh : (hF : ℤ) ≠ 0 := by exact_mod_cast classNumber_ne_zero F
  rw [ordAt_mul, ordAt_inv]
  apply mul_left_cancel₀ hh
  split_ifs at key ⊢ <;> linarith
variable (S : Set (HeightOneSpectrum (𝓞 F)))
theorem divS_placeUnit (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S (Additive.ofMul (GroundTheory.Global.SUnit.placeUnit v.1)) =
      (classNumber F : ℤ) • Finsupp.single v 1 := by
  classical
  ext w
  rw [divS_apply, toMul_ofMul, ordAt_placeUnit, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : w = v
  · subst h
    simp
  · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
    simp [h', Ne.symm h]
theorem classNumber_nsmul_sPic (c : sPic S) : classNumber F • c = 0 := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective (divS S).range c
  rw [← map_nsmul]
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  induction D using Finsupp.induction_linear with
  | zero => rw [smul_zero]; exact zero_mem _
  | add f g hf hg => rw [smul_add]; exact add_mem hf hg
  | single v m =>
    refine ⟨m • Additive.ofMul (GroundTheory.Global.SUnit.placeUnit v.1), ?_⟩
    rw [map_zsmul, divS_placeUnit]
    ext w
    by_cases hw : v = w <;> simp [hw]
    ring
open scoped Classical in

noncomputable def sPicGen (c : ClassGroup (𝓞 F)) : sPic S :=
  if h : ∃ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ClassGroup.mk0 (primeNZD v.1) = c then
    sPicMk S (Finsupp.single h.choose 1)
  else 0
theorem sPicMk_single_eq_sPicGen (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    sPicMk S (Finsupp.single v 1) = sPicGen S (ClassGroup.mk0 (primeNZD v.1)) := by
  classical
  have hex : ∃ u : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      ClassGroup.mk0 (primeNZD u.1) = ClassGroup.mk0 (primeNZD v.1) := ⟨v, rfl⟩
  rw [sPicGen, dif_pos hex]
  obtain ⟨x, hx⟩ := exists_ordAt_eq_of_mk0_eq hex.choose_spec.symm
  rw [← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).2 ⟨Additive.ofMul x, ?_⟩
  ext w
  rw [divS_apply, toMul_ofMul, hx, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have e1 : (w.1 = v.1) ↔ (v = w) := ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩
  have e2 : (w.1 = hex.choose.1) ↔ (hex.choose = w) := ⟨fun e => (Subtype.ext e).symm, fun e => by rw [e]⟩
  simp only [e1, e2]
theorem closure_range_sPicGen : AddSubgroup.closure (Set.range (sPicGen S)) = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective (divS S).range c
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | single v m =>
    rw [← Finsupp.smul_single_one, map_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ m
    change sPicMk S (Finsupp.single v 1) ∈ _
    rw [sPicMk_single_eq_sPicGen]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
instance finite_sPic : Finite (sPic S) := by
  have : AddGroup.FG (sPic S) :=
    AddGroup.fg_iff.2 ⟨_, closure_range_sPicGen S, Set.finite_range _⟩
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun c => ?_
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨classNumber F, classNumber_pos F,
    classNumber_nsmul_sPic S c⟩
end GroundTheory.ProfCoh


