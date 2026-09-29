-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_comp_eq_of_finite_free_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/952db26d-eb1d-555e-b184-05d410628557

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_isPullback_of_isPullback_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_comp_eq_of_finite_free_transitive

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace FQESol

theorem epi_of_faithfullyFlat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {Y : Scheme.{0}} (ψ₁ ψ₂ : Spec (CommRingCat.of A) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ ψ₁ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ ψ₂) :
    ψ₁ = ψ₂ := by
  set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp
  set q₁ := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B)) with hq₁
  set q₂ := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) with hq₂
  have sqp : IsPullback p (𝟙 _) (𝟙 (Spec (CommRingCat.of A))) p := IsPullback.of_vert_isIso ⟨by simp⟩
  have sq₁ : IsPullback q₁ (𝟙 _) (𝟙 (Spec (CommRingCat.of B))) q₁ := IsPullback.of_vert_isIso ⟨by simp⟩
  have sq₂ : IsPullback q₂ (𝟙 _) (𝟙 (Spec (CommRingCat.of B))) q₂ := IsPullback.of_vert_isIso ⟨by simp⟩
  have hq : q₁ ≫ p = q₂ ≫ p := by
    simp only [hp, hq₁, hq₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change (algebraMap A B a) ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] (algebraMap A B a)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨φ, -, huniq⟩ := AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
    (𝟙 (Spec (CommRingCat.of A))) (𝟙 (Spec (CommRingCat.of B))) p sqp (𝟙 _) q₁ q₂ sq₁ sq₂ hq (p ≫ ψ₁)
    (by rw [← Category.assoc, hq, Category.assoc])
  exact (huniq ψ₁ rfl).trans (huniq ψ₂ h.symm).symm

theorem isPullback_val {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X X') :
    PolarisedAbelianScheme.IsPullback φ X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme := by
  obtain ⟨gA, hg, hmul, hP, hpol, -⟩ := h
  exact ⟨gA, hg, hmul, hP, hpol⟩

end FQESol

theorem solution
    (g N n : ℕ) (hn : 3 ≤ n) (𝒪 : Type) [CommRing 𝒪] (hn' : IsUnit ((n : ℕ) : 𝒪))
    (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g (N + 1) n S → Prop)

    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (hQdesc : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S'] [Algebra.Etale S S']
      (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S'),
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u u' → Q S' u' → Q S u)
    (hSHEAF : ∀ {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
      {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
      (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)],
      (∀ (u : ∀ i, PolarisedAbelianScheme g d n (B i)),
      (∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
      (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
      PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
      PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂) →
      ∃ u₀ : PolarisedAbelianScheme g d n S, ∀ (i : Fin k) (v : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)) ∧
      (∀ (u₀ u₀' : PolarisedAbelianScheme g d n S),
      (∀ (i : Fin k) (v v' : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v →
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀' v' →
      PolarisedAbelianScheme.Iso v v') →
      PolarisedAbelianScheme.Iso u₀ u₀'))
    (hEFF : ∀ {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
      (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
      (u' : PolarisedAbelianScheme g d n S')
      (hdesc : ∀ (v₁ v₂ : PolarisedAbelianScheme g d n (S' ⊗[S] S')),
      PolarisedAbelianScheme.IsPullback
      (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₁ →
      PolarisedAbelianScheme.IsPullback
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂),
      (∃ u : PolarisedAbelianScheme g d n S, ∀ v : PolarisedAbelianScheme g d n S',
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u v → PolarisedAbelianScheme.Iso v u') ∧
      (∀ (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u₁ v₁ →
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u₂ v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂ → PolarisedAbelianScheme.Iso u₁ u₂))
    (hBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (u : PolarisedAbelianScheme g (N + 1) n S),
      ∃ u' : PolarisedAbelianScheme g (N + 1) n S', PolarisedAbelianScheme.IsPullback φ u u')
    (Θ : ∀ (S : Type) [CommRing S], FramedPolarisedAbelianScheme g N n S → Prop)
    (hΘQ : ∀ (S : Type) [CommRing S] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Q S X.toPolarisedAbelianScheme)
    (hΘiso : ∀ (S : Type) [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S),
      FramedPolarisedAbelianScheme.Iso X X' → Θ S X → Θ S X')
    (hΘbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (φ : S →+* S')
      (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' → Θ S X → Θ S' X')
    (hΘBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (X : FramedPolarisedAbelianScheme g N n S),
      ∃ X' : FramedPolarisedAbelianScheme g N n S', FramedPolarisedAbelianScheme.IsPullback φ X X')
    (HΘ : Scheme.{0}) (πΘ : HΘ ⟶ Spec (CommRingCat.of 𝒪))
    (ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s πΘ)
    (hpt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'),
      FramedPolarisedAbelianScheme.Iso X X' → ptΘ S s X hX = ptΘ S s X' hX')
    (hpt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') (hX : Θ S X) (hX' : Θ S' X'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' →
      (ptΘ S' s' X' hX').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptΘ S s X hX).1)
    (hpt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (x : SchemeHomOver s πΘ),
      ∃ (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), ptΘ S s X hX = x)
    (hpt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'), ptΘ S s X hX = ptΘ S s X' hX' →
      FramedPolarisedAbelianScheme.Iso X X')
    (hsep : IsSeparated πΘ) (hqc : QuasiCompact πΘ) (hfp : LocallyOfFinitePresentation πΘ)
    (hAF : ∀ F : Finset HΘ, ∃ U : HΘ.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut HΘ) (hρ : ∀ γ : Γ, (ρ γ).hom ≫ πΘ = πΘ)
    (act : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) →
      Γ → FramedPolarisedAbelianScheme g N n S → FramedPolarisedAbelianScheme g N n S)
    (hactΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S (act S s γ X))
    (hact_val : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S),
      (act S s γ X).toPolarisedAbelianScheme = X.toPolarisedAbelianScheme)
    (hact_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X),
      (ptΘ S s (act S s γ X) (hactΘ S s γ X hX)).1 = (ptΘ S s X hX).1 ≫ (ρ γ).hom)

    (hfree : ∀ (S : Type) [CommRing S] [Nontrivial S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (γ : Γ)
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → FramedPolarisedAbelianScheme.Iso (act S s γ X) X → γ = 1)

    (htrans : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S X' →
      PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme →
      ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ (j : Fin m)
        (Y Y' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j))),
        FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X Y →
        FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X' Y' →
        ∃ γ : Γ, FramedPolarisedAbelianScheme.Iso
          (act (Localization.Away (r j)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r j)))) ≫ s) γ Y) Y')

    (hsurj : ∀ (S : Type) [CommRing S] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : PolarisedAbelianScheme g (N + 1) n S), Q S u →
      ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'), Module.FaithfullyFlat S S' ∧
        ∃ X' : FramedPolarisedAbelianScheme g N n S', Θ S' X' ∧
          PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme)

    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : HΘ ⟶ M)
    (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q) (hqπ : q ≫ πM = πΘ)
    (horbit : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X₁ X₂ : FramedPolarisedAbelianScheme g N n S) (h₁ : Θ S X₁) (h₂ : Θ S X₂),
      PolarisedAbelianScheme.Iso X₁.toPolarisedAbelianScheme X₂.toPolarisedAbelianScheme →
      (ptΘ S s X₁ h₁).1 ≫ q = (ptΘ S s X₂ h₂).1 ≫ q) :
    ∃ (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n Q S → SchemeHomOver s πM),
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S) (X' : FramedPolarisedAbelianScheme g N n S') (hX' : Θ S' X'),
        PolarisedAbelianScheme.IsPullback φ U.val X'.toPolarisedAbelianScheme →
        (ptΘ S' s' X' hX').1 ≫ q = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s U).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (U U' : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S),
        PolarisedAbelianScheme.Satisfying.Iso U U' → pt S s U = pt S s U') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S) (U' : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S'),
        PolarisedAbelianScheme.Satisfying.IsPullback φ U U' →
        (pt S' s' U').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s U).1) := by
  classical

  have key : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S),
      ∃ φ : SchemeHomOver s πM,
        ∀ (S'' : Type) [CommRing S''] (ψ : S →+* S'') (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of 𝒪)),
          Spec.map (CommRingCat.ofHom ψ) ≫ s = s'' →
          ∀ (X'' : FramedPolarisedAbelianScheme g N n S'') (hX'' : Θ S'' X''),
            PolarisedAbelianScheme.IsPullback ψ U.val X''.toPolarisedAbelianScheme →
            (ptΘ S'' s'' X'' hX'').1 ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ φ.1 := by
    intro S _ s U
    obtain ⟨S', _, _, hff, X', hX', hpb'⟩ := hsurj S s U.val U.prop

    let p : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S'))
    let iL : S' →+* S' ⊗[S] S' := Algebra.TensorProduct.includeLeftRingHom
    let iR : S' →+* S' ⊗[S] S' := (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom
    let q₁ : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') := Spec.map (CommRingCat.ofHom iL)
    let q₂ : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') := Spec.map (CommRingCat.ofHom iR)
    have hc : iL.comp (algebraMap S S') = iR.comp (algebraMap S S') := by
      ext a
      change (algebraMap S S' a) ⊗ₜ[S] (1 : S') = (1 : S') ⊗ₜ[S] (algebraMap S S' a)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have hq : q₁ ≫ p = q₂ ≫ p := by
      change Spec.map (CommRingCat.ofHom iL) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) =
        Spec.map (CommRingCat.ofHom iR) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
    have sqp : IsPullback p (𝟙 _) (𝟙 (Spec (CommRingCat.of S))) p := IsPullback.of_vert_isIso ⟨by simp⟩
    have sq₁ : IsPullback q₁ (𝟙 _) (𝟙 (Spec (CommRingCat.of S'))) q₁ := IsPullback.of_vert_isIso ⟨by simp⟩
    have sq₂ : IsPullback q₂ (𝟙 _) (𝟙 (Spec (CommRingCat.of S'))) q₂ := IsPullback.of_vert_isIso ⟨by simp⟩

    obtain ⟨X₁, hX₁⟩ := hΘBC iL X'
    obtain ⟨X₂, hX₂⟩ := hΘBC iR X'
    have hΘ₁ : Θ (S' ⊗[S] S') X₁ := hΘbc S' (S' ⊗[S] S') (p ≫ s) iL X' X₁ hX₁ hX'
    have hΘ₂ : Θ (S' ⊗[S] S') X₂ := hΘbc S' (S' ⊗[S] S') (p ≫ s) iR X' X₂ hX₂ hX'
    have hu₁ : PolarisedAbelianScheme.IsPullback (iL.comp (algebraMap S S')) U.val X₁.toPolarisedAbelianScheme :=
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans (algebraMap S S') iL U.val _ _ hpb'
        (FQESol.isPullback_val iL X' X₁ hX₁)
    have hu₂ : PolarisedAbelianScheme.IsPullback (iL.comp (algebraMap S S')) U.val X₂.toPolarisedAbelianScheme :=
      (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id (S := S) (S' := S' ⊗[S] S')).1 _ _ _ _ hc.symm
        (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans (algebraMap S S') iR U.val _ _ hpb'
          (FQESol.isPullback_val iR X' X₂ hX₂))
    have hiso : PolarisedAbelianScheme.Iso X₁.toPolarisedAbelianScheme X₂.toPolarisedAbelianScheme :=
      AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback _ U.val _ _ hu₁ hu₂
    have e₁ := hpt_pullback S' (S' ⊗[S] S') iL (p ≫ s) (q₁ ≫ p ≫ s) rfl X' X₁ hX' hΘ₁ hX₁
    have e₂ := hpt_pullback S' (S' ⊗[S] S') iR (p ≫ s) (q₁ ≫ p ≫ s)
      (by rw [← Category.assoc, ← hq, Category.assoc]) X' X₂ hX' hΘ₂ hX₂
    have horb := horbit (S' ⊗[S] S') (q₁ ≫ p ≫ s) X₁ X₂ hΘ₁ hΘ₂ hiso
    have hφ' : q₁ ≫ ((ptΘ S' (p ≫ s) X' hX').1 ≫ q) = q₂ ≫ ((ptΘ S' (p ≫ s) X' hX').1 ≫ q) := by
      change (Spec.map (CommRingCat.ofHom iL) ≫ (ptΘ S' (p ≫ s) X' hX').1) ≫ q =
        (Spec.map (CommRingCat.ofHom iR) ≫ (ptΘ S' (p ≫ s) X' hX').1) ≫ q
      rw [← e₁, ← e₂]
      exact horb

    obtain ⟨φ, hφ, -⟩ := AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
      (𝟙 (Spec (CommRingCat.of S))) (𝟙 (Spec (CommRingCat.of S'))) p sqp (𝟙 _) q₁ q₂ sq₁ sq₂ hq
      ((ptΘ S' (p ≫ s) X' hX').1 ≫ q) hφ'
    have hφπ : φ ≫ πM = s := by
      apply FQESol.epi_of_faithfullyFlat (A := S) (B := S')
      change p ≫ φ ≫ πM = p ≫ s
      rw [← Category.assoc, hφ, Category.assoc, hqπ, (ptΘ S' (p ≫ s) X' hX').2]
    refine ⟨⟨φ, hφπ⟩, ?_⟩

    intro S'' _ ψ s'' hss X'' hX'' hpb''
    letI : Algebra S S'' := ψ.toAlgebra
    let jL : S'' →+* S'' ⊗[S] S' := algebraMap S'' (S'' ⊗[S] S')
    let jR : S' →+* S'' ⊗[S] S' := (Algebra.TensorProduct.includeRight : S' →ₐ[S] S'' ⊗[S] S').toRingHom
    have hcomm : jL.comp ψ = jR.comp (algebraMap S S') := by
      ext a
      change (ψ a) ⊗ₜ[S] (1 : S') = (1 : S'') ⊗ₜ[S] (algebraMap S S' a)
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    obtain ⟨Y₁, hY₁⟩ := hΘBC jL X''
    obtain ⟨Y₂, hY₂⟩ := hΘBC jR X'
    have hΘY₁ : Θ (S'' ⊗[S] S') Y₁ := hΘbc S'' (S'' ⊗[S] S') s'' jL X'' Y₁ hY₁ hX''
    have hΘY₂ : Θ (S'' ⊗[S] S') Y₂ := hΘbc S' (S'' ⊗[S] S') (p ≫ s) jR X' Y₂ hY₂ hX'
    have hv₁ : PolarisedAbelianScheme.IsPullback (jL.comp ψ) U.val Y₁.toPolarisedAbelianScheme :=
      AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans ψ jL U.val _ _ hpb'' (FQESol.isPullback_val jL X'' Y₁ hY₁)
    have hv₂ : PolarisedAbelianScheme.IsPullback (jL.comp ψ) U.val Y₂.toPolarisedAbelianScheme :=
      (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id (S := S) (S' := S'' ⊗[S] S')).1 _ _ _ _ hcomm.symm
        (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans (algebraMap S S') jR U.val _ _ hpb'
          (FQESol.isPullback_val jR X' Y₂ hY₂))
    have hisoY : PolarisedAbelianScheme.Iso Y₁.toPolarisedAbelianScheme Y₂.toPolarisedAbelianScheme :=
      AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback _ U.val _ _ hv₁ hv₂
    have hsC : Spec.map (CommRingCat.ofHom jR) ≫ (p ≫ s) = Spec.map (CommRingCat.ofHom jL) ≫ s'' := by
      rw [← hss, ← Category.assoc, ← Category.assoc]
      change (Spec.map (CommRingCat.ofHom jR) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) ≫ s =
        (Spec.map (CommRingCat.ofHom jL) ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
    have f₁ := hpt_pullback S'' (S'' ⊗[S] S') jL s'' (Spec.map (CommRingCat.ofHom jL) ≫ s'') rfl X'' Y₁ hX'' hΘY₁ hY₁
    have f₂ := hpt_pullback S' (S'' ⊗[S] S') jR (p ≫ s) (Spec.map (CommRingCat.ofHom jL) ≫ s'') hsC X' Y₂ hX' hΘY₂ hY₂
    have horbY := horbit (S'' ⊗[S] S') (Spec.map (CommRingCat.ofHom jL) ≫ s'') Y₁ Y₂ hΘY₁ hΘY₂ hisoY
    apply FQESol.epi_of_faithfullyFlat (A := S'') (B := S'' ⊗[S] S')
    change Spec.map (CommRingCat.ofHom jL) ≫ (ptΘ S'' s'' X'' hX'').1 ≫ q = Spec.map (CommRingCat.ofHom jL) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ φ
    rw [← Category.assoc, ← f₁, horbY, f₂, Category.assoc]
    change Spec.map (CommRingCat.ofHom jR) ≫ (ptΘ S' (p ≫ s) X' hX').1 ≫ q = _
    rw [← hφ, ← Category.assoc, ← Category.assoc]
    change (Spec.map (CommRingCat.ofHom jR) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) ≫ φ =
      (Spec.map (CommRingCat.ofHom jL) ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ φ
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
  choose pt hpt using key
  refine ⟨pt, ?_, ?_, ?_⟩
  ·
    intro S S' _ _ φ s s' hss U X' hX' hpb
    exact hpt S s U S' φ s' hss X' hX' hpb
  ·
    intro S _ s U U' hUU'
    obtain ⟨S₁, _, _, hff₁, X₁, hX₁, hpb₁⟩ := hsurj S s U.val U.prop
    obtain ⟨S₂, _, _, hff₂, X₂, hX₂, hpb₂⟩ := hsurj S s U'.val U'.prop
    let jL : S₁ →+* S₁ ⊗[S] S₂ := Algebra.TensorProduct.includeLeftRingHom
    let jR : S₂ →+* S₁ ⊗[S] S₂ := (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] S₁ ⊗[S] S₂).toRingHom
    have hL : jL.comp (algebraMap S S₁) = algebraMap S (S₁ ⊗[S] S₂) := RingHom.ext fun a => rfl
    have hR : jR.comp (algebraMap S S₂) = algebraMap S (S₁ ⊗[S] S₂) := by
      ext a
      change (1 : S₁) ⊗ₜ[S] (algebraMap S S₂ a) = (algebraMap S S₁ a) ⊗ₜ[S] (1 : S₂)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    obtain ⟨Y₁, hY₁⟩ := hΘBC jL X₁
    obtain ⟨Y₂, hY₂⟩ := hΘBC jR X₂
    have hΘY₁ : Θ (S₁ ⊗[S] S₂) Y₁ := hΘbc S₁ (S₁ ⊗[S] S₂) (Spec.map (CommRingCat.ofHom (algebraMap S S₁)) ≫ s) jL X₁ Y₁ hY₁ hX₁
    have hΘY₂ : Θ (S₁ ⊗[S] S₂) Y₂ := hΘbc S₂ (S₁ ⊗[S] S₂) (Spec.map (CommRingCat.ofHom (algebraMap S S₂)) ≫ s) jR X₂ Y₂ hY₂ hX₂
    have hv₁ : PolarisedAbelianScheme.IsPullback (algebraMap S (S₁ ⊗[S] S₂)) U.val Y₁.toPolarisedAbelianScheme :=
      (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id (S := S) (S' := S₁ ⊗[S] S₂)).1 _ _ _ _ hL
        (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans (algebraMap S S₁) jL U.val _ _ hpb₁ (FQESol.isPullback_val jL X₁ Y₁ hY₁))
    have hv₂ : PolarisedAbelianScheme.IsPullback (algebraMap S (S₁ ⊗[S] S₂)) U'.val Y₂.toPolarisedAbelianScheme :=
      (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id (S := S) (S' := S₁ ⊗[S] S₂)).1 _ _ _ _ hR
        (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans (algebraMap S S₂) jR U'.val _ _ hpb₂ (FQESol.isPullback_val jR X₂ Y₂ hY₂))
    have hisoY : PolarisedAbelianScheme.Iso Y₁.toPolarisedAbelianScheme Y₂.toPolarisedAbelianScheme :=
      AlgebraicGeometry.PolarisedAbelianScheme.iso_of_isPullback_of_isPullback_of_iso (algebraMap S (S₁ ⊗[S] S₂)) hv₁ hv₂ hUU'
    have g₁ := hpt S s U (S₁ ⊗[S] S₂) (algebraMap S (S₁ ⊗[S] S₂))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S₁ ⊗[S] S₂))) ≫ s) rfl Y₁ hΘY₁ hv₁
    have g₂ := hpt S s U' (S₁ ⊗[S] S₂) (algebraMap S (S₁ ⊗[S] S₂))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S₁ ⊗[S] S₂))) ≫ s) rfl Y₂ hΘY₂ hv₂
    have horbY := horbit (S₁ ⊗[S] S₂) (Spec.map (CommRingCat.ofHom (algebraMap S (S₁ ⊗[S] S₂))) ≫ s) Y₁ Y₂ hΘY₁ hΘY₂ hisoY
    haveI : Module.FaithfullyFlat S (S₁ ⊗[S] S₂) := by
      first
        | infer_instance
        | exact Module.FaithfullyFlat.trans S S₁ (S₁ ⊗[S] S₂)
    apply Subtype.ext
    apply FQESol.epi_of_faithfullyFlat (A := S) (B := S₁ ⊗[S] S₂)
    rw [← g₁, ← g₂]
    exact horbY
  ·
    intro S S' _ _ φ s s' hss U U' hpb
    obtain ⟨S₂, _, _, hff₂, X₂, hX₂, hpb₂⟩ := hsurj S' s' U'.val U'.prop
    have g₁ := hpt S' s' U' S₂ (algebraMap S' S₂) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)) ≫ s') rfl X₂ hX₂ hpb₂
    have hss₂ : Spec.map (CommRingCat.ofHom ((algebraMap S' S₂).comp φ)) ≫ s =
        Spec.map (CommRingCat.ofHom (algebraMap S' S₂)) ≫ s' := by
      rw [← hss, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have g₂ := hpt S s U S₂ ((algebraMap S' S₂).comp φ) (Spec.map (CommRingCat.ofHom (algebraMap S' S₂)) ≫ s') hss₂ X₂ hX₂
      (AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans φ (algebraMap S' S₂) U.val U'.val _ hpb hpb₂)
    apply FQESol.epi_of_faithfullyFlat (A := S') (B := S₂)
    rw [← g₁, g₂, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_comp_eq_of_finite_free_transitive
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_comp_eq_of_finite_free_transitive (solution)
