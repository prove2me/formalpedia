-- Prove2me | solution 1 for AlgebraicCurve.ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d6ddedd1-7f0f-50a0-9115-337681a44783

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import Theorems.Thm_AlgebraicCurve_SemistableModel_localRing_le_and_exists_mem_localRing_mul_eq_of_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel TensorProduct

namespace BranchDescAux

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

end BranchDescAux

namespace BranchDescAux

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

theorem algebraMap_eq (X : Scheme.{0}) [IsIntegral X] {x η : X} (h : η ⤳ x) (s : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk x) X.functionField s =
      algebraMap (X.presheaf.stalk η) X.functionField ((X.presheaf.stalkSpecializes h).hom s) := by
  simp only [RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem fromSpecStalk_comap (X : Scheme.{0}) {x η : X} (h : η ⤳ x) :
    (X.fromSpecStalk x).base ⟨(maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes h).hom,
      inferInstance⟩ = η := by
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  have h2 := congrArg (fun k => k.base (closedPoint (X.presheaf.stalk η))) h1
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.fromSpecStalk_closedPoint] at h2
  exact h2

end BranchDescAux

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (hres₀ : Function.Surjective ((IsLocalRing.residue ↥A).comp ι₀))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w) (hwu : IsUnit ((w : ℕ) : A₀))
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))

    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀]
    (hmem₀ : ∀ f : F, f ∈ 𝒩₀ ↔ ∃ g : X₀.presheaf.stalk ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x),
      φ f = algebraMap (X.presheaf.stalk x) X.functionField
        (((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).stalkMap x).hom g))
    (hle : 𝒩₀ ≤ SemistableModel.localRing X φ x)
    (hle₁ : 𝒩₀ ≤ R₁.integers.toSubring) (hle₂ : 𝒩₀ ≤ R₂.integers.toSubring) :
    RingHom.ker (R₁.residue.comp (Subring.inclusion hle₁)) ≠ RingHom.ker (R₂.residue.comp (Subring.inclusion hle₂)) ∧
    RingHom.ker (R₁.residue.comp (Subring.inclusion hle₁)) ≠ maximalIdeal ↥𝒩₀ ∧
    RingHom.ker (R₂.residue.comp (Subring.inclusion hle₂)) ≠ maximalIdeal ↥𝒩₀ := by
  classical

  set pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) with hpr

  let ψ : X.presheaf.stalk x →+* F :=
    (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk x) X.functionField)
  have hψ_apply : ∀ s, ψ s = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s) := fun _ => rfl
  have hψinj : Function.Injective ψ :=
    φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  have hrange : SemistableModel.localRing X φ x = ψ.range := rfl

  have hloc₁ : SemistableModel.localRing X φ x ≤ R₁.integers.toSubring :=
    hR₁ ▸ (AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes X φ h₁).1
  have hloc₂ : SemistableModel.localRing X φ x ≤ R₂.integers.toSubring :=
    hR₂ ▸ (AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes X φ h₂).1
  have hψ₁ : ∀ s, ψ s ∈ R₁.integers := fun s => hloc₁ (hrange ▸ ⟨s, rfl⟩)
  have hψ₂ : ∀ s, ψ s ∈ R₂.integers := fun s => hloc₂ (hrange ▸ ⟨s, rfl⟩)
  let ψ₁ : X.presheaf.stalk x →+* R₁.integers := ψ.codRestrict R₁.integers hψ₁
  let ψ₂ : X.presheaf.stalk x →+* R₂.integers := ψ.codRestrict R₂.integers hψ₂

  let Q₁ : Ideal (X.presheaf.stalk x) := (maximalIdeal R₁.integers).comap ψ₁
  let Q₂ : Ideal (X.presheaf.stalk x) := (maximalIdeal R₂.integers).comap ψ₂

  let c : ↥A →+* X.presheaf.stalk x :=
    (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
  have hψc : ∀ a : ↥A, ψ (c a) = algebraMap L F (a : L) := by
    intro a
    rw [hψ_apply, RingEquiv.symm_apply_eq, hφ]
    change (X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    rfl

  have hQmem : ∀ {Fb : Type} [Field Fb] [Algebra (ResidueField ↥A) Fb] (R : RegularProlongation A F Fb)
      (hψR : ∀ s, ψ s ∈ R.integers) (s : X.presheaf.stalk x),
      s ∈ (maximalIdeal R.integers).comap (ψ.codRestrict R.integers hψR) ↔
        R.residue ⟨ψ s, hψR s⟩ = 0 := by
    intro Fb _ _ R hψR s
    rw [Ideal.mem_comap, ← R.ker_residue, RingHom.mem_ker]
    rfl

  have hcQ : ∀ {Fb : Type} [Field Fb] [Algebra (ResidueField ↥A) Fb] (R : RegularProlongation A F Fb)
      (hψR : ∀ s, ψ s ∈ R.integers), ∀ a ∈ maximalIdeal ↥A,
      c a ∈ (maximalIdeal R.integers).comap (ψ.codRestrict R.integers hψR) := by
    intro Fb _ _ R hψR a ha
    rw [hQmem R hψR]
    have : (⟨ψ (c a), hψR (c a)⟩ : R.integers) = ⟨algebraMap L F (a : L), (R.algebraMap_mem_iff a).mpr a.2⟩ :=
      Subtype.ext (hψc a)
    rw [this, R.residue_algebraMap, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

  have hQeq : ∀ {Fb : Type} [Field Fb] [Algebra (ResidueField ↥A) Fb] (R : RegularProlongation A F Fb)
      (hψR : ∀ s, ψ s ∈ R.integers) (η : X) (hη : η ⤳ x)
      (hR : R.integers.toSubring = SemistableModel.localRing X φ η),
      (maximalIdeal R.integers).comap (ψ.codRestrict R.integers hψR) =
        (maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hη).hom := by
    intro Fb _ _ R hψR η hη hR

    have hρmem : ∀ r : X.presheaf.stalk η, φ.symm (algebraMap (X.presheaf.stalk η) X.functionField r) ∈ R.integers := by
      intro r
      show _ ∈ R.integers.toSubring
      rw [hR]
      exact ⟨r, rfl⟩
    let ρ : X.presheaf.stalk η →+* R.integers :=
      ((φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk η) X.functionField)).codRestrict
        R.integers hρmem
    have hρ_apply : ∀ r, (ρ r : F) = φ.symm (algebraMap (X.presheaf.stalk η) X.functionField r) := fun _ => rfl
    have hρinj : Function.Injective ρ := by
      intro r₁ r₂ hr
      have := congrArg (fun t : R.integers => (t : F)) hr
      simp only [hρ_apply] at this
      exact IsFractionRing.injective (X.presheaf.stalk η) X.functionField (φ.symm.injective this)
    have hρsurj : Function.Surjective ρ := by
      intro t
      have ht : (t : F) ∈ R.integers.toSubring := t.2
      rw [hR] at ht
      obtain ⟨r, hr⟩ := ht
      exact ⟨r, Subtype.ext hr⟩
    let ρe : X.presheaf.stalk η ≃+* R.integers := RingEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
    have hψρ : ∀ s, ψ.codRestrict R.integers hψR s = ρe ((X.presheaf.stalkSpecializes hη).hom s) := by
      intro s
      apply Subtype.ext
      show ψ s = φ.symm (algebraMap (X.presheaf.stalk η) X.functionField ((X.presheaf.stalkSpecializes hη).hom s))
      rw [hψ_apply, BranchDescAux.algebraMap_eq X hη]
    ext s
    rw [Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff, hψρ]
    refine not_congr ⟨fun hu => ?_, fun hu => hu.map ρe⟩
    simpa using hu.map ρe.symm
  have hQ₁eq := hQeq R₁ hψ₁ η₁ h₁ hR₁
  have hQ₂eq := hQeq R₂ hψ₂ η₂ h₂ hR₂

  have hQne : Q₁ ≠ Q₂ := by
    intro heq
    apply h₁₂
    rw [← BranchDescAux.fromSpecStalk_comap X h₁, ← BranchDescAux.fromSpecStalk_comap X h₂]
    congr 2
    rw [← hQ₁eq, ← hQ₂eq]
    exact heq
  have hQneM : ∀ {η : X} (hη : η ⤳ x) (hηx : η ≠ x),
      (maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hη).hom ≠
        maximalIdeal (X.presheaf.stalk x) := by
    intro η hη hηx heq
    apply hηx
    rw [← BranchDescAux.fromSpecStalk_comap X hη]
    have : (⟨(maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hη).hom, inferInstance⟩ :
        PrimeSpectrum (X.presheaf.stalk x)) = closedPoint (X.presheaf.stalk x) := PrimeSpectrum.ext heq
    rw [this]
    exact Scheme.fromSpecStalk_closedPoint
  have hQ₁ne : Q₁ ≠ maximalIdeal (X.presheaf.stalk x) := fun heq => hQneM h₁ h₁x (hQ₁eq.symm.trans heq)
  have hQ₂ne : Q₂ ≠ maximalIdeal (X.presheaf.stalk x) := fun heq => hQneM h₂ h₂x (hQ₂eq.symm.trans heq)

  letI algA : Algebra A₀ ↥A := ι₀.toAlgebra
  letI algO : Algebra A₀ (X₀.presheaf.stalk (pr.base x)) :=
    ((X₀.presheaf.germ ⊤ (pr.base x) trivial).hom.comp
      (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)).toAlgebra
  have hsq : IsPullback pr toBase toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso (by rw [hpr]) hiso
    rw [hpr, Category.assoc, Limits.pullback.condition, ← Category.assoc, hiso]
  obtain ⟨𝔮, h𝔮, e, -, hfst, hsnd⟩ :=
    BranchDescAux.stalk_level_localization_tensor ι₀ toBase₀ toBase pr hsq x
  have hsurj : ∀ a : ↥A, ∃ a₀ : A₀, a - algebraMap A₀ ↥A a₀ ∈ maximalIdeal ↥A := by
    intro a
    obtain ⟨a₀, ha₀⟩ := hres₀ (IsLocalRing.residue ↥A a)
    refine ⟨a₀, ?_⟩
    rw [← Ideal.Quotient.eq]
    exact ha₀.symm
  let g : X₀.presheaf.stalk (pr.base x) →+* X.presheaf.stalk x := (pr.stalkMap x).hom
  haveI : IsLocalHom g := inferInstanceAs (IsLocalHom (pr.stalkMap x).hom)
  let P₁ : Ideal (X₀.presheaf.stalk (pr.base x)) := Q₁.comap g
  let P₂ : Ideal (X₀.presheaf.stalk (pr.base x)) := Q₂.comap g
  have hc' : ∀ a : ↥A, e (c a) = algebraMap ((X₀.presheaf.stalk (pr.base x)) ⊗[A₀] ↥A) (Localization.AtPrime 𝔮)
      ((1 : X₀.presheaf.stalk (pr.base x)) ⊗ₜ[A₀] a) := hsnd
  have L := fun (Q Q' : Ideal (X.presheaf.stalk x)) [Q'.IsPrime] =>
    BranchDescAux.le_of_comap_le (M := X₀.presheaf.stalk (pr.base x)) (maximalIdeal ↥A) hsurj 𝔮 e g hfst c hc' Q Q'
  have hPne : P₁ ≠ P₂ := by
    intro heq
    exact hQne (le_antisymm (L Q₁ Q₂ (hcQ R₁ hψ₁) (hcQ R₂ hψ₂) heq.le) (L Q₂ Q₁ (hcQ R₂ hψ₂) (hcQ R₁ hψ₁) heq.ge))
  have hcomap_max : (maximalIdeal (X.presheaf.stalk x)).comap g = maximalIdeal (X₀.presheaf.stalk (pr.base x)) :=
    ((IsLocalRing.local_hom_TFAE g).out 0 4).mp ‹IsLocalHom g›
  have hPneM : ∀ (Q : Ideal (X.presheaf.stalk x)) [Q.IsPrime], (∀ a ∈ maximalIdeal ↥A, c a ∈ Q) →
      Q ≠ maximalIdeal (X.presheaf.stalk x) → Q.comap g ≠ maximalIdeal (X₀.presheaf.stalk (pr.base x)) := by
    intro Q _ hcQ' hQne' heq
    apply hQne'
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    refine L (maximalIdeal _) Q (fun a ha => IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) (hcQ' a ha)) hcQ' ?_
    rw [hcomap_max, heq]
  have hP₁ne : P₁ ≠ maximalIdeal _ := hPneM Q₁ (hcQ R₁ hψ₁) hQ₁ne
  have hP₂ne : P₂ ≠ maximalIdeal _ := hPneM Q₂ (hcQ R₂ hψ₂) hQ₂ne

  have hθmem : ∀ o : X₀.presheaf.stalk (pr.base x), ψ (g o) ∈ 𝒩₀ := fun o =>
    (hmem₀ _).mpr ⟨o, by rw [hψ_apply, RingEquiv.apply_symm_apply]⟩
  let θ : X₀.presheaf.stalk (pr.base x) →+* ↥𝒩₀ := (ψ.comp g).codRestrict 𝒩₀ hθmem
  have hθsurj : Function.Surjective θ := by
    intro n
    obtain ⟨o, ho⟩ := (hmem₀ (n : F)).mp n.2
    refine ⟨o, Subtype.ext ?_⟩
    show ψ (g o) = n
    rw [hψ_apply, ← ho, RingEquiv.symm_apply_apply]
  have hθker : ∀ {Fb : Type} [Field Fb] [Algebra (ResidueField ↥A) Fb] (R : RegularProlongation A F Fb)
      (hψR : ∀ s, ψ s ∈ R.integers) (hleR : 𝒩₀ ≤ R.integers.toSubring) (o : X₀.presheaf.stalk (pr.base x)),
      θ o ∈ RingHom.ker (R.residue.comp (Subring.inclusion hleR)) ↔
        o ∈ ((maximalIdeal R.integers).comap (ψ.codRestrict R.integers hψR)).comap g := by
    intro Fb _ _ R hψR hleR o
    rw [Ideal.mem_comap, hQmem R hψR, RingHom.mem_ker]
    rfl
  have hθunit : ∀ o, IsUnit (θ o) ↔ IsUnit o := by
    intro o
    refine ⟨fun hu => ?_, fun hu => hu.map θ⟩
    have hu' : IsUnit (Subring.inclusion hle (θ o)) := hu.map _

    let re : X.presheaf.stalk x ≃+* ψ.range := RingEquiv.ofBijective ψ.rangeRestrict
      ⟨fun a b hab => hψinj (congrArg Subtype.val hab), ψ.rangeRestrict_surjective⟩
    have : Subring.inclusion hle (θ o) = re (g o) := Subtype.ext rfl
    rw [this] at hu'
    have hg : IsUnit (g o) := by
      convert hu'.map re.symm using 1
      exact (re.symm_apply_apply (g o)).symm
    exact (isUnit_map_iff g o).mp hg
  refine ⟨fun heq => hPne ?_, fun heq => hP₁ne ?_, fun heq => hP₂ne ?_⟩
  · ext o
    rw [← hθker R₁ hψ₁ hle₁, ← hθker R₂ hψ₂ hle₂, heq]
  · ext o
    rw [← hθker R₁ hψ₁ hle₁, heq, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, hθunit]
  · ext o
    rw [← hθker R₂ hψ₂ hle₂, heq, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, hθunit]

end S_AlgebraicCurve_ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne
end P2MW
export P2MW.S_AlgebraicCurve_ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne (solution)
