-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/acd62d22-82d3-54c3-b331-ef452cecf9a2

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TensorProduct

namespace FibreIdAux

theorem exists_sub_tmul_one_mem {A₀ A M : Type*} [CommRing A₀] [CommRing A] [CommRing M]
    [Algebra A₀ A] [Algebra A₀ M] (𝔪 : Ideal A)
    (hsurj : ∀ a : A, ∃ a₀ : A₀, a - algebraMap A₀ A a₀ ∈ 𝔪) (τ : M ⊗[A₀] A) :
    ∃ s : M, τ - s ⊗ₜ[A₀] (1 : A) ∈ Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (𝔪 : Set A)) := by
  induction τ using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s a =>
      obtain ⟨a₀, ha₀⟩ := hsurj a
      refine ⟨a₀ • s, ?_⟩
      have h1 : s ⊗ₜ[A₀] a - (a₀ • s) ⊗ₜ[A₀] (1 : A) = (s ⊗ₜ[A₀] (1 : A)) * ((1 : M) ⊗ₜ[A₀] (a - algebraMap A₀ A a₀)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub,
          Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ha₀, rfl⟩)
  | add τ₁ τ₂ ih₁ ih₂ =>
      obtain ⟨s₁, hs₁⟩ := ih₁
      obtain ⟨s₂, hs₂⟩ := ih₂
      refine ⟨s₁ + s₂, ?_⟩
      have : τ₁ + τ₂ - (s₁ + s₂) ⊗ₜ[A₀] (1 : A) = (τ₁ - s₁ ⊗ₜ[A₀] 1) + (τ₂ - s₂ ⊗ₜ[A₀] 1) := by
        rw [TensorProduct.add_tmul]; abel
      rw [this]
      exact Ideal.add_mem _ hs₁ hs₂

theorem le_of_comap_le {A₀ A M S : Type*} [CommRing A₀] [CommRing A] [CommRing M] [CommRing S]
    [Algebra A₀ A] [Algebra A₀ M] (𝔪 : Ideal A)
    (hsurj : ∀ a : A, ∃ a₀ : A₀, a - algebraMap A₀ A a₀ ∈ 𝔪)
    (𝔮 : Ideal (M ⊗[A₀] A)) [𝔮.IsPrime]
    (e : S ≃+* Localization.AtPrime 𝔮)
    (g : M →+* S) (hg : ∀ s : M, e (g s) = algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1))
    (c : A →+* S) (hc : ∀ a : A, e (c a) = algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A₀] a))
    (Q Q' : Ideal S) [Q'.IsPrime]
    (hQ : ∀ m ∈ 𝔪, c m ∈ Q) (hQ' : ∀ m ∈ 𝔪, c m ∈ Q')
    (hle : Q.comap g ≤ Q'.comap g) : Q ≤ Q' := by
  intro t ht

  obtain ⟨⟨τ, u⟩, hτ⟩ := IsLocalization.surj 𝔮.primeCompl (e t)
  obtain ⟨s, hs⟩ := exists_sub_tmul_one_mem (M := M) 𝔪 hsurj τ

  let ρ : M ⊗[A₀] A →+* S := e.symm.toRingHom.comp (algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮))
  have hρg : ∀ s : M, ρ (s ⊗ₜ[A₀] 1) = g s := fun s => by
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hg, RingEquiv.symm_apply_apply]
  have hρc : ∀ a : A, ρ (1 ⊗ₜ[A₀] a) = c a := fun a => by
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hc, RingEquiv.symm_apply_apply]
  have hJ : Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (𝔪 : Set A)) ≤ (Q ⊓ Q').comap ρ := by
    rw [Ideal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, hρc, Ideal.mem_inf]
    exact ⟨hQ m hm, hQ' m hm⟩
  have hdiff := hJ hs
  rw [Ideal.mem_comap, map_sub, hρg, Ideal.mem_inf] at hdiff

  have hρτ : ρ τ = t * e.symm (algebraMap _ _ (u : M ⊗[A₀] A)) := by
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hτ, map_mul, RingEquiv.symm_apply_apply]
  have hunit : IsUnit (e.symm (algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (u : M ⊗[A₀] A))) :=
    (IsLocalization.map_units (Localization.AtPrime 𝔮) u).map e.symm

  have hgsQ : g s ∈ Q := by
    have : ρ τ ∈ Q := by rw [hρτ]; exact Ideal.mul_mem_right _ _ ht
    have := Q.sub_mem this hdiff.1
    simpa using this
  have hgsQ' : g s ∈ Q' := hle hgsQ
  have hρτ' : ρ τ ∈ Q' := by
    have := Q'.add_mem hdiff.2 hgsQ'
    simpa using this
  rw [hρτ] at hρτ'
  exact ((Ideal.IsPrime.mem_or_mem ‹Q'.IsPrime› hρτ').resolve_right
    (fun h => (Ideal.IsPrime.ne_top ‹Q'.IsPrime›) (Ideal.eq_top_of_isUnit_mem _ h hunit)))

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

end FibreIdAux

namespace FibreIdAux

section Core

variable {A₀ A M S : Type*} [CommRing A₀] [CommRing A] [CommRing M] [CommRing S]
  [IsLocalRing A] [IsLocalRing M] [Algebra A₀ A] [Algebra A₀ M]

theorem surj_core (𝔪 : Ideal A)
    (hsurj : ∀ a : A, ∃ a₀ : A₀, a - algebraMap A₀ A a₀ ∈ 𝔪)
    (𝔮 : Ideal (M ⊗[A₀] A)) [𝔮.IsPrime]
    (hcomap : 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A₀) (S := A₀) (A := M) (B := A)).toRingHom =
      maximalIdeal M)
    (e : S ≃+* Localization.AtPrime 𝔮)
    (g : M →+* S) (hg : ∀ s : M, e (g s) = algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1))
    (c : A →+* S) (hc : ∀ a : A, e (c a) = algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A₀] a))
    (hJ𝔮 : ∀ m ∈ 𝔪, (1 : M) ⊗ₜ[A₀] m ∈ 𝔮) :
    (∀ u : M ⊗[A₀] A, u ∉ 𝔮 → ∃ s : M, IsUnit s ∧
      u - s ⊗ₜ[A₀] 1 ∈ Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (𝔪 : Set A))) ∧
    (∀ t : S, ∃ s : M, t - g s ∈ 𝔪.map c) := by
  have hJle : Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (𝔪 : Set A)) ≤ 𝔮 := by
    rw [Ideal.span_le]; rintro _ ⟨m, hm, rfl⟩; exact hJ𝔮 m hm
  have hunit : ∀ u : M ⊗[A₀] A, u ∉ 𝔮 → ∃ s : M, IsUnit s ∧
      u - s ⊗ₜ[A₀] 1 ∈ Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (𝔪 : Set A)) := by
    intro u hu
    obtain ⟨s, hs⟩ := exists_sub_tmul_one_mem (M := M) 𝔪 hsurj u
    refine ⟨s, ?_, hs⟩
    have hs1 : s ⊗ₜ[A₀] (1 : A) ∉ 𝔮 := by
      intro hmem; apply hu
      have := 𝔮.add_mem hmem (hJle hs)
      simpa using this
    by_contra hsu
    apply hs1
    have : s ∈ maximalIdeal M := (IsLocalRing.mem_maximalIdeal _).mpr hsu
    rw [← hcomap] at this
    exact this
  refine ⟨hunit, ?_⟩
  let ρ : M ⊗[A₀] A →+* S := e.symm.toRingHom.comp (algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮))
  have hρg : ∀ s : M, ρ (s ⊗ₜ[A₀] 1) = g s := fun s => by
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hg, RingEquiv.symm_apply_apply]
  have hρc : ∀ a : A, ρ (1 ⊗ₜ[A₀] a) = c a := fun a => by
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hc, RingEquiv.symm_apply_apply]
  have hJI : Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (𝔪 : Set A)) ≤ (𝔪.map c).comap ρ := by
    rw [Ideal.span_le]; rintro _ ⟨m, hm, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, hρc]
    exact Ideal.mem_map_of_mem _ hm
  intro t
  obtain ⟨⟨τ, u⟩, hτ⟩ := IsLocalization.surj 𝔮.primeCompl (e t)
  obtain ⟨s, hs⟩ := exists_sub_tmul_one_mem (M := M) 𝔪 hsurj τ
  obtain ⟨s', hs'u, hs'⟩ := hunit u.1 u.2
  have hρτ : ρ τ = t * ρ (u : M ⊗[A₀] A) := by
    simp only [ρ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hτ, map_mul, RingEquiv.symm_apply_apply]
  have i₁ := hJI hs'
  have i₂ := hJI hs
  rw [Ideal.mem_comap, map_sub, hρg] at i₁ i₂
  obtain ⟨s'inv, hs'inv⟩ := hs'u.exists_right_inv
  refine ⟨s * s'inv, ?_⟩
  have hone : g s' * g s'inv = 1 := by rw [← map_mul, hs'inv, map_one]
  have key : t - g (s * s'inv) = ((ρ τ - g s) - t * (ρ (u : M ⊗[A₀] A) - g s')) * g s'inv := by
    rw [hρτ, map_mul]
    linear_combination (-t) * hone
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.sub_mem _ i₂ (Ideal.mul_mem_left _ _ i₁))

end Core

end FibreIdAux

namespace FibreIdAux

section Inj

variable {A₀ A M S : Type*} [CommRing A₀] [CommRing A] [CommRing M] [CommRing S]
  [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing M] [Algebra A₀ A] [Algebra A₀ M]
  [IsLocalHom (algebraMap A₀ A)]

theorem inj_core
    (hsurj : ∀ a : A, ∃ a₀ : A₀, a - algebraMap A₀ A a₀ ∈ maximalIdeal A)
    (𝔮 : Ideal (M ⊗[A₀] A)) [𝔮.IsPrime]
    (hcomap : 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A₀) (S := A₀) (A := M) (B := A)).toRingHom =
      maximalIdeal M)
    (e : S ≃+* Localization.AtPrime 𝔮)
    (g : M →+* S) (hg : ∀ s : M, e (g s) = algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1))
    (c : A →+* S) (hc : ∀ a : A, e (c a) = algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A₀] a))
    (hJ𝔮 : ∀ m ∈ maximalIdeal A, (1 : M) ⊗ₜ[A₀] m ∈ 𝔮)
    (s : M) (hs : g s ∈ (maximalIdeal A).map c) :
    s ∈ (maximalIdeal A₀).map (algebraMap A₀ M) := by
  classical

  let rmap : ResidueField A₀ →+* ResidueField A := IsLocalRing.ResidueField.map (algebraMap A₀ A)
  have hrinj : Function.Injective rmap := RingHom.injective _
  have hrsurj : Function.Surjective rmap := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a₀, ha₀⟩ := hsurj a
    refine ⟨IsLocalRing.residue A₀ a₀, ?_⟩
    show IsLocalRing.residue A (algebraMap A₀ A a₀) = IsLocalRing.residue A a
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha₀
  let riso : ResidueField A₀ ≃+* ResidueField A := RingEquiv.ofBijective rmap ⟨hrinj, hrsurj⟩

  let I₀ : Ideal M := (maximalIdeal A₀).map (algebraMap A₀ M)
  let lam₀ : ResidueField A₀ →+* M ⧸ I₀ :=
    Ideal.Quotient.lift (maximalIdeal A₀) ((Ideal.Quotient.mk I₀).comp (algebraMap A₀ M))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hlam₀ : ∀ a₀ : A₀, lam₀ (IsLocalRing.residue A₀ a₀) = Ideal.Quotient.mk I₀ (algebraMap A₀ M a₀) := fun _ => rfl

  let ψ : A →+* M ⧸ I₀ := (lam₀.comp riso.symm.toRingHom).comp (IsLocalRing.residue A)
  have hψι : ∀ a₀ : A₀, ψ (algebraMap A₀ A a₀) = Ideal.Quotient.mk I₀ (algebraMap A₀ M a₀) := by
    intro a₀
    have h1 : riso.symm (IsLocalRing.residue A (algebraMap A₀ A a₀)) = IsLocalRing.residue A₀ a₀ := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h1, hlam₀]
  have hψ𝔪 : ∀ m ∈ maximalIdeal A, ψ m = 0 := by
    intro m hm
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, (IsLocalRing.residue_eq_zero_iff m).mpr hm, map_zero]

  let ψₐ : A →ₐ[A₀] M ⧸ I₀ :=
    { toRingHom := ψ
      commutes' := fun a₀ => by
        change ψ (algebraMap A₀ A a₀) = algebraMap A₀ (M ⧸ I₀) a₀
        rw [hψι]
        rfl }
  let Φ : M ⊗[A₀] A →ₐ[A₀] M ⧸ I₀ :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ A₀ I₀) ψₐ (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (m : M) (a : A), Φ (m ⊗ₜ[A₀] a) = Ideal.Quotient.mk I₀ m * ψ a := fun m a => by
    simp only [Φ, Algebra.TensorProduct.lift_tmul]
    rfl

  have hΦJ : ∀ m ∈ maximalIdeal A, Φ ((1 : M) ⊗ₜ[A₀] m) = 0 := fun m hm => by
    rw [hΦ, hψ𝔪 m hm, mul_zero]
  have hΦJ' : ∀ j ∈ Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (maximalIdeal A : Set A)), Φ j = 0 := by
    intro j hj
    have : Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (maximalIdeal A : Set A)) ≤
        RingHom.ker Φ.toRingHom := by
      rw [Ideal.span_le]; rintro _ ⟨m, hm, rfl⟩; exact hΦJ m hm
    exact this hj
  obtain ⟨hunit, -⟩ := surj_core (maximalIdeal A) hsurj 𝔮 hcomap e g hg c hc hJ𝔮
  have hΦu : ∀ u : M ⊗[A₀] A, u ∉ 𝔮 → IsUnit (Φ u) := by
    intro u hu
    obtain ⟨s', hs'u, hs'⟩ := hunit u hu
    have : Φ u = Ideal.Quotient.mk I₀ s' := by
      have h1 := hΦJ' _ hs'
      rw [map_sub, sub_eq_zero] at h1
      rw [h1, hΦ, map_one, mul_one]
    rw [this]
    exact hs'u.map _

  have hI : ((maximalIdeal A).map c).map e.toRingHom =
      (Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (maximalIdeal A : Set A))).map
        (algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮)) := by
    rw [Ideal.map_map, Ideal.map_span, Ideal.map, ← Set.image_comp]
    congr 1
    ext y
    simp only [Set.mem_image, Function.comp_apply, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, SetLike.mem_coe]
    constructor
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, (hc m).symm⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, hc m⟩
  have hmem : algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1) ∈
      (Ideal.span ((fun m : A => (1 : M) ⊗ₜ[A₀] m) '' (maximalIdeal A : Set A))).map
        (algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮)) := by
    rw [← hI, ← hg]
    exact Ideal.mem_map_of_mem _ hs
  rw [IsLocalization.mem_map_algebraMap_iff 𝔮.primeCompl] at hmem
  obtain ⟨⟨⟨j, hj⟩, u⟩, hju⟩ := hmem

  have hzero : algebraMap (M ⊗[A₀] A) (Localization.AtPrime 𝔮) (s ⊗ₜ[A₀] 1 * (u : M ⊗[A₀] A) - j) = 0 := by
    rw [map_sub, map_mul, sub_eq_zero]
    exact hju
  rw [IsLocalization.map_eq_zero_iff 𝔮.primeCompl] at hzero
  obtain ⟨v, hv⟩ := hzero

  have := congrArg Φ hv
  rw [map_zero, map_mul, map_sub, map_mul, hΦJ' j hj, sub_zero, hΦ, map_one, mul_one] at this

  have hs0 : Ideal.Quotient.mk I₀ s = 0 := by
    have hu' := hΦu u.1 u.2
    have hv' := hΦu v.1 v.2
    have h1 : Ideal.Quotient.mk I₀ s * Φ (u : M ⊗[A₀] A) = 0 :=
      (hv'.mul_right_eq_zero).mp this
    exact (hu'.mul_left_eq_zero).mp h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp hs0

end Inj

end FibreIdAux

namespace FibreIdAux

section Iso

variable {M S : Type*} [CommRing M] [CommRing S]

theorem iso_and_lift (g : M →+* S) (I₀ : Ideal M) (I : Ideal S) (hle : I₀ ≤ I.comap g)
    (hsurj : ∀ t : S, ∃ s : M, t - g s ∈ I) (hinj : ∀ s : M, g s ∈ I → s ∈ I₀) :
    (∃ e : (M ⧸ I₀) ≃+* (S ⧸ I), ∀ s : M, e (Ideal.Quotient.mk I₀ s) = Ideal.Quotient.mk I (g s)) ∧
    (∀ P : Ideal M, P.IsPrime → I₀ ≤ P → ∃ Q : Ideal S, Q.IsPrime ∧ I ≤ Q ∧ Q.comap g = P) := by
  classical
  let f : M ⧸ I₀ →+* S ⧸ I := Ideal.quotientMap I g hle
  have hf : ∀ s, f (Ideal.Quotient.mk I₀ s) = Ideal.Quotient.mk I (g s) := fun s => Ideal.quotientMap_mk
  have hfinj : Function.Injective f := by
    refine Ideal.quotientMap_injective' ?_
    intro s hs
    exact hinj s hs
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs⟩ := hsurj t
    refine ⟨Ideal.Quotient.mk I₀ s, ?_⟩
    rw [hf, eq_comm, Ideal.Quotient.eq]
    exact hs
  let e : (M ⧸ I₀) ≃+* (S ⧸ I) := RingEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have he : ∀ s, e (Ideal.Quotient.mk I₀ s) = Ideal.Quotient.mk I (g s) := hf
  refine ⟨⟨e, he⟩, ?_⟩
  intro P hP hI₀P
  haveI := hP

  have hker : RingHom.ker (Ideal.Quotient.mk I₀) ≤ P := by rw [Ideal.mk_ker]; exact hI₀P
  haveI hP₁ : (P.map (Ideal.Quotient.mk I₀)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  let Q₁ : Ideal (S ⧸ I) := (P.map (Ideal.Quotient.mk I₀)).comap e.symm.toRingHom
  haveI hQ₁ : Q₁.IsPrime := Ideal.comap_isPrime _ _
  let Q : Ideal S := Q₁.comap (Ideal.Quotient.mk I)
  refine ⟨Q, Ideal.comap_isPrime _ _, ?_, ?_⟩
  · intro t ht
    show Ideal.Quotient.mk I t ∈ Q₁
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ht]
    exact Q₁.zero_mem
  · ext s
    simp only [Q, Q₁, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← he, RingEquiv.symm_apply_apply, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr hI₀P]

end Iso

end FibreIdAux

theorem solution
    {A₀ A : Type} [CommRing A₀] [CommRing A] [IsLocalRing A₀] [IsLocalRing A]
    (ι : A₀ →+* A) [IsLocalHom ι] (hres : Function.Surjective ((IsLocalRing.residue A).comp ι))
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    (iso : X ≅ pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (x : X) (hx : toBase.base x = closedPoint A) :
    let pr := iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    let c : A →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    let c₀ : A₀ →+* X₀.presheaf.stalk (pr.base x) :=
      (X₀.presheaf.germ ⊤ (pr.base x) trivial).hom.comp
        (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)

    (∀ a : A₀, (pr.stalkMap x).hom (c₀ a) = c (ι a)) ∧

    (∃ e : (X₀.presheaf.stalk (pr.base x) ⧸ (maximalIdeal A₀).map c₀) ≃+*
        (X.presheaf.stalk x ⧸ (maximalIdeal A).map c),
      ∀ s : X₀.presheaf.stalk (pr.base x),
        e (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ ((pr.stalkMap x).hom s)) ∧

    (∀ Q Q' : Ideal (X.presheaf.stalk x), Q'.IsPrime →
      (maximalIdeal A).map c ≤ Q → (maximalIdeal A).map c ≤ Q' →
      Q.comap (pr.stalkMap x).hom ≤ Q'.comap (pr.stalkMap x).hom → Q ≤ Q') ∧

    (∀ P : Ideal (X₀.presheaf.stalk (pr.base x)), P.IsPrime → (maximalIdeal A₀).map c₀ ≤ P →
      ∃ Q : Ideal (X.presheaf.stalk x), Q.IsPrime ∧ (maximalIdeal A).map c ≤ Q ∧
        Q.comap (pr.stalkMap x).hom = P) := by
  intro pr c c₀
  classical
  letI algA : Algebra A₀ A := ι.toAlgebra
  haveI : IsLocalHom (algebraMap A₀ A) := inferInstanceAs (IsLocalHom ι)
  letI algO : Algebra A₀ (X₀.presheaf.stalk (pr.base x)) := c₀.toAlgebra
  have hsq : IsPullback pr toBase toBase₀ (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso rfl hiso
    rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
  obtain ⟨𝔮, h𝔮, e, hcomap, hfst, hsnd⟩ :=
    FibreIdAux.stalk_level_localization_tensor ι toBase₀ toBase pr hsq x
  let g : X₀.presheaf.stalk (pr.base x) →+* X.presheaf.stalk x := (pr.stalkMap x).hom
  haveI : IsLocalHom g := inferInstanceAs (IsLocalHom (pr.stalkMap x).hom)
  have hg : ∀ s, e (g s) = algebraMap (X₀.presheaf.stalk (pr.base x) ⊗[A₀] A) (Localization.AtPrime 𝔮)
      (s ⊗ₜ[A₀] 1) := hfst
  have hc : ∀ a : A, e (c a) = algebraMap (X₀.presheaf.stalk (pr.base x) ⊗[A₀] A) (Localization.AtPrime 𝔮)
      ((1 : X₀.presheaf.stalk (pr.base x)) ⊗ₜ[A₀] a) := hsnd
  have hsurj : ∀ a : A, ∃ a₀ : A₀, a - algebraMap A₀ A a₀ ∈ maximalIdeal A := by
    intro a
    obtain ⟨a₀, ha₀⟩ := hres (IsLocalRing.residue A a)
    exact ⟨a₀, by rw [← Ideal.Quotient.eq]; exact ha₀.symm⟩

  have hcompat : ∀ a : A₀, g (c₀ a) = c (ι a) := by
    intro a
    apply e.injective
    have key : (c₀ a) ⊗ₜ[A₀] (1 : A) = (1 : X₀.presheaf.stalk (pr.base x)) ⊗ₜ[A₀] (ι a) := by
      change (algebraMap A₀ (X₀.presheaf.stalk (pr.base x)) a) ⊗ₜ[A₀] (1 : A) =
        (1 : X₀.presheaf.stalk (pr.base x)) ⊗ₜ[A₀] (algebraMap A₀ A a)
      simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hg, hc, key]

  have hcnu : ∀ m ∈ maximalIdeal A, ¬ IsUnit (c m) := by
    intro m hm hu
    have h1 : c = (toBase.stalkMap x).hom.comp (StructureSheaf.toStalk A (toBase.base x)).hom := by
      have h2 : c = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ toBase.appTop ≫ X.presheaf.germ ⊤ x trivial).hom := by
        simp only [c, CommRingCat.hom_comp, RingHom.comp_assoc]
      have h3 : (Spec (CommRingCat.of A)).presheaf.germ ⊤ (toBase.base x) trivial ≫ toBase.stalkMap x =
          toBase.appTop ≫ X.presheaf.germ ⊤ x trivial :=
        Scheme.Hom.germ_stalkMap toBase ⊤ x trivial
      rw [h2, ← h3]
      rfl
    rw [h1, RingHom.comp_apply, isUnit_map_iff] at hu
    have h3 : IsUnit (algebraMap A ((Spec.structureSheaf A).presheaf.stalk (toBase.base x)) m) := hu
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (toBase.base x).asIdeal] at h3
    apply h3
    rw [hx]
    exact hm
  have hJ𝔮 : ∀ m ∈ maximalIdeal A, (1 : X₀.presheaf.stalk (pr.base x)) ⊗ₜ[A₀] m ∈ 𝔮 := by
    intro m hm
    by_contra hnot
    apply hcnu m hm
    have hu : IsUnit (algebraMap (X₀.presheaf.stalk (pr.base x) ⊗[A₀] A) (Localization.AtPrime 𝔮)
        ((1 : X₀.presheaf.stalk (pr.base x)) ⊗ₜ[A₀] m)) :=
      IsLocalization.map_units (Localization.AtPrime 𝔮) (⟨_, hnot⟩ : 𝔮.primeCompl)
    rw [← hc] at hu
    convert hu.map e.symm using 1
    exact (e.symm_apply_apply _).symm

  have hSURJ := (FibreIdAux.surj_core (maximalIdeal A) hsurj 𝔮 hcomap e g hg c hc hJ𝔮).2
  have hINJ : ∀ s, g s ∈ (maximalIdeal A).map c → s ∈ (maximalIdeal A₀).map c₀ :=
    fun s hs => FibreIdAux.inj_core hsurj 𝔮 hcomap e g hg c hc hJ𝔮 s hs
  have hle : (maximalIdeal A₀).map c₀ ≤ ((maximalIdeal A).map c).comap g := by
    rw [Ideal.map_le_iff_le_comap]
    intro m₀ hm₀
    rw [Ideal.mem_comap, Ideal.mem_comap, hcompat]
    apply Ideal.mem_map_of_mem
    have : ¬ IsUnit (ι m₀) := fun h => (IsLocalRing.mem_maximalIdeal _).mp hm₀ ((isUnit_map_iff ι m₀).mp h)
    exact (IsLocalRing.mem_maximalIdeal _).mpr this
  obtain ⟨hISO, hLIFT⟩ := FibreIdAux.iso_and_lift g _ _ hle hSURJ hINJ
  refine ⟨hcompat, hISO, ?_, hLIFT⟩
  intro Q Q' _ hQ hQ' hQQ'
  exact FibreIdAux.le_of_comap_le (M := X₀.presheaf.stalk (pr.base x)) (maximalIdeal A) hsurj 𝔮 e g hg c hc Q Q'
    (fun m hm => hQ (Ideal.mem_map_of_mem _ hm)) (fun m hm => hQ' (Ideal.mem_map_of_mem _ hm)) hQQ'

end S_AlgebraicGeometry_exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_quotient_map_maximalIdeal_of_iso_pullback_of_residue_surjective (solution)
