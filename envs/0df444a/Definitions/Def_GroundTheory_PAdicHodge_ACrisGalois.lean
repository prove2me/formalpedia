-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
-- name    : GroundTheory_PAdicHodge_ACrisGalois
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:25.729716+00:00
-- url     : https://prove2.me/theorems/eb956a17-bae0-59df-b73a-ab549c10af43
-- title:
--   ACris Galois
-- statement:
--   Definitions and structural lemmas for ACris Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_gal_smul
import Theorems.Thm_GroundTheory_PAdicHodge_AdicCompletion_extendRingHom_of
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
namespace GroundTheory.PAdicHodge
section ExtGeneric
variable {A B : Type*} [CommRing A] [CommRing B]
theorem AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero {a : A} {b : B}
    (F : AdicCompletion (Ideal.span {a}) A →+* B)
    (hF : F (algebraMap A _ a) ∈ Ideal.span {b}) (n : ℕ) {z : AdicCompletion (Ideal.span {a}) A}
    (hz : AdicCompletion.evalₐ (Ideal.span {a}) n z = 0) :
    F z ∈ Ideal.span {b} ^ n := by
  have hz' : z ∈ (Ideal.span {a} ^ n).map (algebraMap A (AdicCompletion (Ideal.span {a}) A)) := by
    rw [← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _) n, RingHom.mem_ker]
    exact hz
  rw [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    at hz'
  obtain ⟨c, rfl⟩ := hz'
  rw [map_mul, map_pow, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hF n)
theorem AdicCompletion.ringHom_ext_span {a : A} {b : B} [IsHausdorff (Ideal.span {b}) B]
    {F G : AdicCompletion (Ideal.span {a}) A →+* B}
    (hF : F (algebraMap A _ a) ∈ Ideal.span {b}) (hG : G (algebraMap A _ a) ∈ Ideal.span {b})
    (h : ∀ y : A, F (algebraMap A _ y) = G (algebraMap A _ y)) : F = G := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {b})]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {a}) n x)
  have h1 : AdicCompletion.evalₐ (Ideal.span {a}) n
      (algebraMap A (AdicCompletion (Ideal.span {a}) A) y) = Ideal.Quotient.mk _ y := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.evalₐ_of]
  have hz : AdicCompletion.evalₐ (Ideal.span {a}) n
      (x - algebraMap A (AdicCompletion (Ideal.span {a}) A) y) = 0 := by
    rw [map_sub, h1, hy, sub_self]
  have e : F x - G x = F (x - algebraMap A _ y) - G (x - algebraMap A _ y) := by
    rw [map_sub, map_sub, h y]; ring
  rw [e]
  exact sub_mem (AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero F hF n hz)
    (AdicCompletion.map_mem_span_pow_of_evalₐ_eq_zero G hG n hz)
end ExtGeneric
namespace ACris
section Ext
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
theorem ringHom_ext {B : Type*} [CommRing B] [IsHausdorff (Ideal.span {(p : B)}) B]
    {F G : ACris K p →+* B}
    (h : ∀ y : ACrisZero K p, F (AdicCompletion.of _ _ y) = G (AdicCompletion.of _ _ y)) :
    F = G := by
  refine AdicCompletion.ringHom_ext_span (b := (p : B)) ?_ ?_ fun y => ?_
  · rw [map_natCast, map_natCast]; exact Ideal.mem_span_singleton_self _
  · rw [map_natCast, map_natCast]; exact Ideal.mem_span_singleton_self _
  · rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact h y
theorem span_p_le_comap_endo (f : ACrisZero K p →+* ACrisZero K p) :
    Ideal.span {(p : ACrisZero K p)} ≤ (Ideal.span {(p : ACris K p)}).comap
      ((algebraMap (ACrisZero K p) (ACris K p)).comp f) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _
def extendEndo (f : ACrisZero K p →+* ACrisZero K p) : ACris K p →+* ACris K p :=
  AdicCompletion.extendRingHom _ _ ((algebraMap (ACrisZero K p) (ACris K p)).comp f)
    (span_p_le_comap_endo f)
theorem extendEndo_of (f : ACrisZero K p →+* ACrisZero K p) (y : ACrisZero K p) :
    extendEndo f (AdicCompletion.of _ _ y) = AdicCompletion.of _ _ (f y) :=
  AdicCompletion.extendRingHom_of _ _ _ _ y
theorem extendEndo_id : extendEndo (RingHom.id (ACrisZero K p)) = RingHom.id (ACris K p) :=
  ringHom_ext fun y => by rw [extendEndo_of, RingHom.id_apply, RingHom.id_apply]
theorem extendEndo_comp (f g : ACrisZero K p →+* ACrisZero K p) :
    (extendEndo f).comp (extendEndo g) = extendEndo (f.comp g) :=
  ringHom_ext fun y => by
    rw [RingHom.comp_apply, extendEndo_of g y, extendEndo_of f (g y), extendEndo_of (f.comp g) y,
      RingHom.comp_apply]
end Ext
section Galois
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)
def galAway (σ : Gal(PadicAlgCl p/K)) : 𝔸 →+* 𝔸 :=
  Localization.awayLift ((algebraMap (AInf ℂ_[p] p) 𝔸).comp (AInf.galMap σ)) (p : AInf ℂ_[p] p)
    (by
      rw [RingHom.comp_apply, map_natCast (AInf.galMap σ)]
      exact IsLocalization.Away.algebraMap_isUnit (p : AInf ℂ_[p] p))
theorem galAway_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    galAway σ (algebraMap (AInf ℂ_[p] p) 𝔸 x) = algebraMap (AInf ℂ_[p] p) 𝔸 (σ • x) :=
  IsLocalization.lift_eq _ x
theorem galAway_one : galAway (1 : Gal(PadicAlgCl p/K)) = RingHom.id 𝔸 :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap, one_smul, RingHom.id_apply])
theorem galAway_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galAway (σ * τ) = (galAway σ).comp (galAway τ) :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap,
      galAway_algebraMap, galAway_algebraMap, mul_smul])
theorem galAway_dpow (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (x : AInf ℂ_[p] p) :
    galAway σ (dpow n x) = dpow n (σ • x) := by
  symm
  rw [dpow_eq_iff, ← map_natCast (galAway σ), ← map_mul, factorial_mul_dpow, map_pow,
    galAway_algebraMap]
theorem gal_smul_mem_ker (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ RingHom.ker θ) :
    σ • x ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker] at hx ⊢
  apply Subtype.ext
  rw [AInf.fontaineTheta_gal_smul, hx]
  simp
theorem galAway_mem (σ : Gal(PadicAlgCl p/K)) {y : 𝔸} (hy : y ∈ ACrisZero ℂ_[p] p) :
    galAway σ y ∈ ACrisZero ℂ_[p] p := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [galAway_dpow]
    exact dpow_mem (gal_smul_mem_ker σ hx) n
  | algebraMap r =>
    rw [galAway_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
def galZero (σ : Gal(PadicAlgCl p/K)) : ACrisZero ℂ_[p] p →+* ACrisZero ℂ_[p] p :=
  ((galAway σ).comp (ACrisZero ℂ_[p] p).val.toRingHom).codRestrict (ACrisZero ℂ_[p] p)
    fun y => galAway_mem σ y.2
instance instMulSemiringActionGalZero :
    MulSemiringAction Gal(PadicAlgCl p/K) (ACrisZero ℂ_[p] p) where
  smul σ y := galZero σ y
  one_smul y := Subtype.ext (by
    change galAway 1 (y : 𝔸) = y
    rw [galAway_one, RingHom.id_apply])
  mul_smul σ τ y := Subtype.ext (by
    change galAway (σ * τ) (y : 𝔸) = galAway σ (galAway τ y)
    rw [galAway_mul, RingHom.comp_apply])
  smul_zero σ := map_zero (galZero σ)
  smul_add σ := map_add (galZero σ)
  smul_one σ := map_one (galZero σ)
  smul_mul σ := map_mul (galZero σ)
theorem galZero_one : galZero (1 : Gal(PadicAlgCl p/K)) = RingHom.id (ACrisZero ℂ_[p] p) :=
  RingHom.ext fun y => one_smul Gal(PadicAlgCl p/K) y
theorem galZero_mul (σ τ : Gal(PadicAlgCl p/K)) : galZero (σ * τ) = (galZero σ).comp (galZero τ) :=
  RingHom.ext fun y => mul_smul σ τ y
def galCris (σ : Gal(PadicAlgCl p/K)) : ACris ℂ_[p] p →+* ACris ℂ_[p] p :=
  extendEndo (galZero σ)
theorem galCris_one : galCris (1 : Gal(PadicAlgCl p/K)) = RingHom.id (ACris ℂ_[p] p) := by
  rw [galCris, galZero_one, extendEndo_id]
theorem galCris_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galCris (σ * τ) = (galCris σ).comp (galCris τ) := by
  rw [galCris, galCris, galCris, galZero_mul, extendEndo_comp]
instance instMulSemiringActionGal : MulSemiringAction Gal(PadicAlgCl p/K) (ACris ℂ_[p] p) where
  smul σ x := galCris σ x
  one_smul x := by
    change galCris 1 x = x
    rw [galCris_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galCris (σ * τ) x = galCris σ (galCris τ x)
    rw [galCris_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galCris σ)
  smul_add σ := map_add (galCris σ)
  smul_one σ := map_one (galCris σ)
  smul_mul σ := map_mul (galCris σ)
end Galois
end ACris
end GroundTheory.PAdicHodge


