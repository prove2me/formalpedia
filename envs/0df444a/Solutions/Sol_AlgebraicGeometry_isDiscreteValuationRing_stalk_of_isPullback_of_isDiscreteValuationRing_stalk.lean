-- Prove2me | solution 1 for AlgebraicGeometry.isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c13a4971-2609-5f8e-b4ca-7eb9c909888b

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IsLocalRing CategoryTheory AlgebraicGeometry TensorProduct

namespace E137
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem stalk_level_localization_tensor
    {A₀ A₁ : Type} [CommRing A₀] [CommRing A₁] (ι : A₀ →+* A₁)
    {X₀ X₁ : Scheme.{0}} (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (g₁ : X₁ ⟶ X₀)
    (hsq : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι))) (x₁ : X₁) :
    letI : Algebra A₀ A₁ := ι.toAlgebra
    letI : Algebra A₀ (X₀.presheaf.stalk (g₁.base x₁)) :=
      ((X₀.presheaf.germ ⊤ (g₁.base x₁) trivial).hom.comp
        (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X₀.presheaf.stalk (g₁.base x₁)) ⊗[A₀] A₁)) (_ : 𝔮.IsPrime)
      (e : X₁.presheaf.stalk x₁ ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A₀) (S := A₀)
          (A := X₀.presheaf.stalk (g₁.base x₁)) (B := A₁)).toRingHom =
        IsLocalRing.maximalIdeal (X₀.presheaf.stalk (g₁.base x₁)) ∧
      (∀ s : X₀.presheaf.stalk (g₁.base x₁),
        e ((g₁.stalkMap x₁).hom s) =
          algebraMap ((X₀.presheaf.stalk (g₁.base x₁)) ⊗[A₀] A₁) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1)) ∧
      (∀ a : A₁,
        e ((X₁.presheaf.germ ⊤ x₁ trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a))) =
          algebraMap ((X₀.presheaf.stalk (g₁.base x₁)) ⊗[A₀] A₁) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A₀] a)) := by
  letI : Algebra A₀ A₁ := ι.toAlgebra
  obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : X₁ ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)),
      θ.hom ≫ pullback.fst _ _ = g₁ ∧ θ.hom ≫ pullback.snd _ _ = f₁ :=
    ⟨hsq.isoPullback, hsq.isoPullback_hom_fst, hsq.isoPullback_hom_snd⟩
  subst hθ₁ hθ₂
  obtain ⟨𝔮, h𝔮, eP, hcomap, hfst, hsnd⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
      X₀ toBase₀ A₁ (θ.hom.base x₁)

  let eθ : ↑((pullback toBase₀ (Spec.map (CommRingCat.ofHom ι))).presheaf.stalk (θ.hom.base x₁)) ≃+*
      ↑(X₁.presheaf.stalk x₁) := (asIso (θ.hom.stalkMap x₁)).commRingCatIsoToRingEquiv
  have heθ : ∀ t, eθ t = (θ.hom.stalkMap x₁).hom t := fun _ => rfl
  refine ⟨𝔮, h𝔮, eθ.symm.trans eP, hcomap, ?_, ?_⟩
  · intro s
    have h1 : eθ.symm (((θ.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap x₁).hom s) =
        ((pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (θ.hom.base x₁)).hom s := by
      rw [RingEquiv.symm_apply_eq, heθ, Scheme.Hom.stalkMap_comp]
      rfl
    rw [RingEquiv.trans_apply, h1]
    exact hfst s
  · intro a
    have key : (X₁.presheaf.germ ⊤ x₁ trivial).hom ((θ.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a)) =
        eθ (((pullback toBase₀ (Spec.map (CommRingCat.ofHom ι))).presheaf.germ ⊤ (θ.hom.base x₁) trivial).hom
          ((pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι))).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom a))) := by
      rw [heθ, Scheme.Hom.comp_appTop]
      exact (Scheme.Hom.germ_stalkMap_apply θ.hom ⊤ x₁ trivial _).symm
    rw [key, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    exact hsnd a

end E137

namespace KFGDL

theorem core
    {A₀ : Type*} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {A' : Type*} [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Algebra A₀ A']
    [IsLocalHom (algebraMap A₀ A')] (hinj : Function.Injective (algebraMap A₀ A'))
    (hres : Function.Surjective ((IsLocalRing.residue A').comp (algebraMap A₀ A')))
    {S₀ : Type*} [CommRing S₀] [IsDomain S₀] [IsDiscreteValuationRing S₀] [Algebra A₀ S₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (hS₀ : maximalIdeal S₀ = Ideal.span {algebraMap A₀ S₀ ϖ₀})
    (ϖ' : A') (hϖ' : maximalIdeal A' = Ideal.span {ϖ'})
    (𝔮 : Ideal (S₀ ⊗[A₀] A')) [𝔮.IsPrime] (hϖ'𝔮 : (1 : S₀) ⊗ₜ[A₀] ϖ' ∈ 𝔮)
    [IsNoetherianRing (Localization.AtPrime 𝔮)] :
    (∃ h : IsDomain (Localization.AtPrime 𝔮), @IsDiscreteValuationRing (Localization.AtPrime 𝔮) _ h) ∧
    maximalIdeal (Localization.AtPrime 𝔮) =
      Ideal.span {algebraMap (S₀ ⊗[A₀] A') (Localization.AtPrime 𝔮) ((1 : S₀) ⊗ₜ[A₀] ϖ')} := by
  classical
  let T := S₀ ⊗[A₀] A'
  let L := Localization.AtPrime 𝔮
  have hϖ'irr : Irreducible ϖ' := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mpr hϖ'
  have hϖ₀irrA : Irreducible ϖ₀ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hϖ₀
  have hϖ₀irrS : Irreducible (algebraMap A₀ S₀ ϖ₀) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hS₀
  have hϖ₀m' : algebraMap A₀ A' ϖ₀ ∈ maximalIdeal A' := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hϖ₀irrA.not_isUnit (IsLocalHom.map_nonunit _ hu)

  haveI : Module.IsTorsionFree A₀ A' := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  haveI : Module.Flat A₀ A' :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

  let M' : Ideal T := Ideal.span {(1 : S₀) ⊗ₜ[A₀] ϖ'}
  have happrox : ∀ t : T, ∃ s : S₀, t - s ⊗ₜ[A₀] (1 : A') ∈ M' := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul s a =>
      obtain ⟨a₀, ha₀⟩ := hres (IsLocalRing.residue A' a)
      simp only [RingHom.coe_comp, Function.comp_apply] at ha₀
      have hm : a - algebraMap A₀ A' a₀ ∈ maximalIdeal A' := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ha₀, sub_self]
      rw [hϖ', Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨a₀ • s, ?_⟩
      have e1 : (a₀ • s) ⊗ₜ[A₀] (1 : A') = s ⊗ₜ[A₀] (algebraMap A₀ A' a₀) := by
        rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      have e2 : s ⊗ₜ[A₀] a - s ⊗ₜ[A₀] (algebraMap A₀ A' a₀) = (s ⊗ₜ[A₀] c) * ((1 : S₀) ⊗ₜ[A₀] ϖ') := by
        rw [← TensorProduct.tmul_sub, hc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm c ϖ']
      rw [e1, e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    | add x y hx hy =>
      obtain ⟨s₁, h₁⟩ := hx
      obtain ⟨s₂, h₂⟩ := hy
      refine ⟨s₁ + s₂, ?_⟩
      have : x + y - (s₁ + s₂) ⊗ₜ[A₀] (1 : A') = (x - s₁ ⊗ₜ[A₀] 1) + (y - s₂ ⊗ₜ[A₀] 1) := by
        rw [TensorProduct.add_tmul]; abel
      rw [this]; exact Ideal.add_mem _ h₁ h₂

  have hM'le : M' ≤ 𝔮 := by rw [Ideal.span_singleton_le_iff_mem]; exact hϖ'𝔮
  have h𝔮eq : 𝔮 = M' := by
    refine le_antisymm ?_ hM'le
    intro t ht
    obtain ⟨s, hs⟩ := happrox t
    have h1 : s ⊗ₜ[A₀] (1 : A') ∈ 𝔮 := by
      have := Ideal.sub_mem _ ht (hM'le hs); rwa [sub_sub_cancel] at this
    have hsnu : ¬ IsUnit s := by
      intro hu
      apply ‹𝔮.IsPrime›.ne_top
      refine Ideal.eq_top_of_isUnit_mem _ h1 ?_
      have : s ⊗ₜ[A₀] (1 : A') = algebraMap S₀ T s := rfl
      rw [this]; exact hu.map _
    have hsm : s ∈ maximalIdeal S₀ := (IsLocalRing.mem_maximalIdeal _).mpr hsnu
    rw [hS₀, Ideal.mem_span_singleton] at hsm
    obtain ⟨s', rfl⟩ := hsm
    obtain ⟨c, hc⟩ : ∃ c, algebraMap A₀ A' ϖ₀ = ϖ' * c := by
      have := hϖ₀m'; rw [hϖ', Ideal.mem_span_singleton] at this; exact this
    have h2 : (algebraMap A₀ S₀ ϖ₀ * s') ⊗ₜ[A₀] (1 : A') ∈ M' := by
      have : (algebraMap A₀ S₀ ϖ₀ * s') ⊗ₜ[A₀] (1 : A') = (s' ⊗ₜ[A₀] c) * ((1 : S₀) ⊗ₜ[A₀] ϖ') := by
        rw [← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hc,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm c ϖ']
      rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have := Ideal.add_mem _ hs h2
    rwa [sub_add_cancel] at this

  let p : L := algebraMap T L ((1 : S₀) ⊗ₜ[A₀] ϖ')
  have hmLp : maximalIdeal L = Ideal.span {p} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, congrArg (Ideal.map (algebraMap T L)) h𝔮eq, Ideal.map_span,
      Set.image_singleton]

  obtain ⟨c, hc⟩ : ∃ c, algebraMap A₀ A' ϖ₀ = ϖ' * c := by
    have := hϖ₀m'; rw [hϖ', Ideal.mem_span_singleton] at this; exact this
  have hϖ₀T : ∀ n : ℕ, algebraMap S₀ T (algebraMap A₀ S₀ ϖ₀ ^ n) = ((1 : S₀) ⊗ₜ[A₀] c) ^ n * ((1 : S₀) ⊗ₜ[A₀] ϖ') ^ n := by
    intro n
    rw [map_pow, ← mul_pow]
    congr 1
    show (algebraMap A₀ S₀ ϖ₀) ⊗ₜ[A₀] (1 : A') = _
    rw [Algebra.algebraMap_eq_smul_one (A := S₀), TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, hc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm c ϖ']
  have hpn : ∀ n : ℕ, p ^ n ≠ 0 := by
    intro n hn
    have h0 : algebraMap T L (algebraMap S₀ T (algebraMap A₀ S₀ ϖ₀ ^ n)) = 0 := by
      rw [hϖ₀T, map_mul, map_pow, map_pow, show algebraMap T L ((1 : S₀) ⊗ₜ[A₀] ϖ') = p from rfl, hn, mul_zero]
    rw [IsLocalization.map_eq_zero_iff 𝔮.primeCompl] at h0
    obtain ⟨⟨u, hu⟩, hum⟩ := h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := T)
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ₀irrS.ne_zero))
    have : u = 0 := hreg (by
      show algebraMap A₀ S₀ ϖ₀ ^ n • u = algebraMap A₀ S₀ ϖ₀ ^ n • (0 : T)
      rw [smul_zero, Algebra.smul_def, mul_comm]; exact hum)
    exact hu (this.symm ▸ Ideal.zero_mem 𝔮)
  have hp0 : p ≠ 0 := by simpa using hpn 1
  have hpnu : ¬ IsUnit p := fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp (hmLp.symm ▸ Ideal.mem_span_singleton_self p) hu

  have hkrull : ⨅ n : ℕ, (Ideal.span {p}) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {p}) (fun h => hpnu (Ideal.span_singleton_eq_top.mp h))
  have hdec : ∀ a : L, a ≠ 0 → ∃ (m : ℕ) (u : L), IsUnit u ∧ a = p ^ m * u := by
    intro a ha
    have hex : ∃ n : ℕ, ¬ p ^ n ∣ a := by
      by_contra hall
      push_neg at hall
      apply ha
      have : a ∈ ⨅ n : ℕ, (Ideal.span {p}) ^ n := by
        rw [Submodule.mem_iInf]; intro n
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact hall n
      rwa [hkrull, Submodule.mem_bot] at this
    let k := Nat.find hex
    have hk : ¬ p ^ k ∣ a := Nat.find_spec hex
    have hk0 : k ≠ 0 := fun h => hk (by rw [h, pow_zero]; exact one_dvd a)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hdvd : p ^ m ∣ a := by
      have := Nat.find_min hex (show m < k by omega)
      push_neg at this; exact this
    obtain ⟨u, hu⟩ := hdvd
    refine ⟨m, u, ?_, hu⟩
    by_contra hnu
    have : u ∈ Ideal.span {p} := hmLp ▸ (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [Ideal.mem_span_singleton] at this
    obtain ⟨u', rfl⟩ := this
    exact hk (by rw [hm, pow_succ, hu]; exact mul_dvd_mul_left _ (dvd_mul_right _ _))
  haveI hLdom : IsDomain L := by
    haveI : NoZeroDivisors L := ⟨fun {a b} hab => by
      by_contra hne
      push_neg at hne
      obtain ⟨m, u, hu, rfl⟩ := hdec a hne.1
      obtain ⟨m', u', hu', rfl⟩ := hdec b hne.2
      apply hpn (m + m')
      have : p ^ (m + m') * (u * u') = 0 := by rw [← hab]; ring
      exact ((hu.mul hu').mul_left_eq_zero).mp this⟩
    exact NoZeroDivisors.to_isDomain L
  have hpirr : Irreducible p := by
    refine ⟨hpnu, fun a b hab => ?_⟩
    by_contra hnn
    push_neg at hnn
    have ha0 : a ≠ 0 := fun h => hp0 (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hp0 (by rw [hab, h, mul_zero])
    obtain ⟨m, u, hu, rfl⟩ := hdec a ha0
    obtain ⟨m', u', hu', rfl⟩ := hdec b hb0
    have hm1 : 1 ≤ m := by
      by_contra h; push_neg at h
      have : m = 0 := by omega
      subst this; exact hnn.1 (by simpa using hu)
    have hm1' : 1 ≤ m' := by
      by_contra h; push_neg at h
      have : m' = 0 := by omega
      subst this; exact hnn.2 (by simpa using hu')
    have hcalc : p = p * (p * (p ^ (m + m' - 2) * (u * u'))) := by
      have e : p ^ (m + m') = p * (p * p ^ (m + m' - 2)) := by
        rw [← pow_succ', ← pow_succ']; congr 1; omega
      calc p = p ^ m * u * (p ^ m' * u') := hab
        _ = p ^ (m + m') * (u * u') := by rw [pow_add]; ring
        _ = p * (p * (p ^ (m + m' - 2) * (u * u'))) := by rw [e]; ring
    have : p * (1 - p * (p ^ (m + m' - 2) * (u * u'))) = 0 := by
      rw [mul_sub, mul_one, sub_eq_zero]; exact hcalc
    rcases mul_eq_zero.mp this with h | h
    · exact hp0 h
    · rw [sub_eq_zero, eq_comm] at h
      exact hpnu (isUnit_iff_exists_inv.mpr ⟨_, h⟩)
  have hdvr : IsDiscreteValuationRing L :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨p, hpirr, fun {x} hx => by
        obtain ⟨m, u, hu, rfl⟩ := hdec x hx
        exact ⟨m, hu.unit, by rw [IsUnit.unit_spec]⟩⟩
  exact ⟨⟨hLdom, hdvr⟩, hmLp⟩

end KFGDL

theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    (ι₁' : A₀ →+* A₁) [IsLocalHom ι₁'] (hι₁' : Function.Injective ι₁')
    (hres₁ : Function.Surjective ((IsLocalRing.residue A₁).comp ι₁'))
    (ϖ₁ : A₁) (hϖ₁ : maximalIdeal A₁ = Ideal.span {ϖ₁})
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (g₁ : X₁ ⟶ X₀)
    (hsq : IsPullback g₁ f₁ toBase₀ (Spec.map (CommRingCat.ofHom ι₁')))
    (η₁ : X₁) (hη₁ : f₁.base η₁ = closedPoint A₁)
    [IsDiscreteValuationRing (X₀.presheaf.stalk (g₁.base η₁))]
    (h𝔪₀ : maximalIdeal (X₀.presheaf.stalk (g₁.base η₁)) =
      Ideal.span {(X₀.presheaf.germ ⊤ (g₁.base η₁) trivial).hom
        (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀))}) :
    ∃ (_ : IsDomain (X₁.presheaf.stalk η₁)),
      IsDiscreteValuationRing (X₁.presheaf.stalk η₁) ∧
      maximalIdeal (X₁.presheaf.stalk η₁) =
        Ideal.span {(X₁.presheaf.germ ⊤ η₁ trivial).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))} := by
  classical
  letI algA : Algebra A₀ A₁ := ι₁'.toAlgebra
  haveI hlocal : IsLocalHom (algebraMap A₀ A₁) := ‹IsLocalHom ι₁'›
  letI algO : Algebra A₀ (X₀.presheaf.stalk (g₁.base η₁)) :=
    ((X₀.presheaf.germ ⊤ (g₁.base η₁) trivial).hom.comp
      (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)).toAlgebra
  obtain ⟨𝔮, h𝔮p, eL, hcomap, hleft, hright⟩ :=
    E137.stalk_level_localization_tensor ι₁' toBase₀ f₁ g₁ hsq η₁
  haveI := h𝔮p
  have hUnit : ∀ y, IsUnit (eL y) ↔ IsUnit y :=
    fun y => ⟨fun h => by simpa using h.map eL.symm.toRingHom, fun h => h.map eL.toRingHom⟩

  have hc₁loc : ¬ IsUnit ((X₁.presheaf.germ ⊤ η₁ trivial).hom
      (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))) := by
    intro hu
    have hu2 : IsUnit ((f₁.stalkMap η₁).hom (((Spec (CommRingCat.of A₁)).presheaf.germ ⊤ (f₁.base η₁) trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁))) := by
      rw [Scheme.Hom.germ_stalkMap_apply f₁ ⊤ η₁ trivial]
      exact hu
    have hu' := isUnit_of_map_unit (f₁.stalkMap η₁).hom _ hu2
    letI algSt : Algebra A₁ ((Spec (CommRingCat.of A₁)).presheaf.stalk (f₁.base η₁)) :=
      (StructureSheaf.toStalk A₁ (f₁.base η₁)).hom.toAlgebra
    haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A₁)).presheaf.stalk (f₁.base η₁))
        (f₁.base η₁).asIdeal := StructureSheaf.IsLocalization.to_stalk A₁ (f₁.base η₁)
    have key : IsUnit (algebraMap A₁ ((Spec (CommRingCat.of A₁)).presheaf.stalk (f₁.base η₁)) ϖ₁) := hu'
    rw [IsLocalization.AtPrime.isUnit_to_map_iff ((Spec (CommRingCat.of A₁)).presheaf.stalk (f₁.base η₁))
      (f₁.base η₁).asIdeal ϖ₁] at key
    apply key
    show ϖ₁ ∈ (f₁.base η₁).asIdeal
    rw [hη₁]
    show ϖ₁ ∈ maximalIdeal A₁
    rw [hϖ₁]; exact Ideal.mem_span_singleton_self ϖ₁
  have h𝔮₁ : (1 : X₀.presheaf.stalk (g₁.base η₁)) ⊗ₜ[A₀] ϖ₁ ∈ 𝔮 := by
    by_contra hnot
    apply hc₁loc
    have hu : IsUnit (algebraMap _ (Localization.AtPrime 𝔮) ((1 : X₀.presheaf.stalk (g₁.base η₁)) ⊗ₜ[A₀] ϖ₁)) :=
      IsLocalization.map_units (Localization.AtPrime 𝔮) (⟨_, hnot⟩ : 𝔮.primeCompl)
    rw [← hright] at hu
    exact (hUnit _).mp hu

  haveI : LocallyOfFinitePresentation f₁ := MorphismProperty.of_isPullback hsq inferInstance
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  haveI : IsNoetherianRing (Localization.AtPrime 𝔮) := isNoetherianRing_of_ringEquiv _ eL

  obtain ⟨⟨hdom, hdvr⟩, hmL⟩ := KFGDL.core (A' := A₁) (S₀ := X₀.presheaf.stalk (g₁.base η₁))
    hι₁' hres₁ ϖ₀ hϖ₀ h𝔪₀ ϖ₁ hϖ₁ 𝔮 h𝔮₁

  haveI : IsDomain (X₁.presheaf.stalk η₁) := Function.Injective.isDomain eL.toRingHom eL.injective
  haveI : IsDiscreteValuationRing (X₁.presheaf.stalk η₁) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eL.symm
  refine ⟨inferInstance, inferInstance, ?_⟩
  have h1 : maximalIdeal (X₁.presheaf.stalk η₁) = Ideal.map eL.symm (maximalIdeal (Localization.AtPrime 𝔮)) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv eL.symm (p := maximalIdeal (Localization.AtPrime 𝔮)))).symm
  rw [h1, hmL, Ideal.map_span, Set.image_singleton, ← hright]
  show Ideal.span {eL.symm (eL _)} = _
  rw [RingEquiv.symm_apply_apply]

end S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_isDiscreteValuationRing_stalk_of_isPullback_of_isDiscreteValuationRing_stalk (solution)
