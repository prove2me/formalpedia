-- Prove2me | solution 1 for AlgebraicGeometry.exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ae6f4ccf-9856-52fb-8e7a-7f77a75b7665

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace G2

theorem affine {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FiniteType) :
    LocallyOfFinitePresentation (pullback.diagonal (Spec.map φ)) := by
  algebraize [φ.hom]
  rw [show φ = CommRingCat.ofHom (algebraMap R S) from rfl, diagonal_SpecMap R S]
  haveI : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom]
    refine RingHom.FinitePresentation.of_surjective _ (fun x => ⟨x ⊗ₜ[R] 1, by simp⟩) ?_
    haveI : Algebra.FiniteType R S := hφ
    haveI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_finiteType R S
    exact KaehlerDifferential.ideal_fg R S
  infer_instance

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Pullback in
theorem restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (𝒰 : Y.OpenCover) (𝒱 : ∀ i, (pullback f (𝒰.f i)).OpenCover)
    [∀ i, IsAffine (𝒰.X i)] [∀ i j, IsAffine ((𝒱 i).X j)] :
    LocallyOfFinitePresentation (pullback.diagonal f ∣_ diagonalCoverDiagonalRange f 𝒰 𝒱) := by
  let U : (Σ i, (𝒱 i).I₀) → (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i ↦
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right, Opens.opensRange_ι]
    exact le_iSup (fun i : Σ i, (𝒱 i).I₀ ↦ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange) i
  have hf : iSup U = ⊤ := (TopologicalSpace.Opens.map_iSup _ _).symm.trans
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι_preimage_self
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _ hf]
  intro i
  rw [MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFinitePresentation) (morphismRestrictRestrict _ _ _),
    MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFinitePresentation) (morphismRestrictEq _ (hU i)),
    MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFinitePresentation) (diagonalRestrictIsoDiagonal ..)]

  let g := (𝒱 i.1).f i.2 ≫ pullback.snd f (𝒰.f i.1)
  haveI : LocallyOfFiniteType g := inferInstance
  show LocallyOfFinitePresentation (pullback.diagonal g)
  have e := MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.diagonal @LocallyOfFinitePresentation)
    (arrowIsoSpecΓOfIsAffine g)
  change (MorphismProperty.diagonal @LocallyOfFinitePresentation) g
  rw [e]
  show LocallyOfFinitePresentation (pullback.diagonal (Spec.map g.appTop))
  refine affine g.appTop ?_
  rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have e2 := MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFiniteType) (arrowIsoSpecΓOfIsAffine g)
  exact e2.mp inferInstance

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Pullback in
theorem main {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i : 𝒰.I₀) := (pullback f (𝒰.f i)).affineCover
  let W := diagonalCoverDiagonalRange f 𝒰 𝒱
  have hW : Set.range (pullback.diagonal f) ⊆ (W : Set _) :=
    range_diagonal_subset_diagonalCoverDiagonalRange f 𝒰 𝒱
  have hres : LocallyOfFinitePresentation (pullback.diagonal f ∣_ W) := restrict f 𝒰 𝒱
  have htop : pullback.diagonal f ⁻¹ᵁ W = ⊤ := by
    rw [eq_top_iff]; intro x _; exact hW ⟨x, rfl⟩
  haveI : IsIso (pullback.diagonal f ⁻¹ᵁ W).ι := by
    rw [htop]; exact (Scheme.topIso X).isIso_hom
  have hfac : pullback.diagonal f = inv (pullback.diagonal f ⁻¹ᵁ W).ι ≫ (pullback.diagonal f ∣_ W) ≫ W.ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [hfac]
  infer_instance

end G2

noncomputable section

namespace G1

theorem eq_toSpecΓ_comp {T : Scheme.{u}} {R : CommRingCat.{u}} (h : T ⟶ Spec R) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ h.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

def kerIdeal {R : Type u} [CommRing R] {W : Scheme.{u}} (c : W ⟶ Spec (CommRingCat.of R)) : Ideal R :=
  RingHom.ker ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appTop).hom

theorem exists_comp_eq_iff_kerIdeal_le {R : Type u} [CommRing R] {W : Scheme.{u}} (c : W ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion c] (R'' : Type u) [CommRing R''] (ψ : R →+* R'') :
    (∃ w : Spec (CommRingCat.of R'') ⟶ W, w ≫ c = Spec.map (CommRingCat.ofHom ψ)) ↔ kerIdeal c ≤ RingHom.ker ψ := by
  let θ : CommRingCat.of R ⟶ Γ(W, ⊤) := (Scheme.ΓSpecIso (.of R)).inv ≫ c.appTop
  constructor
  · rintro ⟨w, hw⟩ x hx
    have e : CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of R'')).inv = θ ≫ w.appTop := by
      rw [Scheme.ΓSpecIso_inv_naturality, ← hw, Scheme.Hom.comp_appTop, Category.assoc]
    have e2 := congrArg (fun φ => φ.hom x) e
    change (Scheme.ΓSpecIso (.of R'')).inv (ψ x) = w.appTop.hom (θ.hom x) at e2
    rw [show θ.hom x = 0 from hx, map_zero] at e2
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R'')).inv :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R'')).inv).1
    exact hinj (e2.trans (map_zero _).symm)
  · intro hle
    obtain ⟨hW, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine c
    haveI := hW
    have hθsurj : Function.Surjective θ.hom := by
      show Function.Surjective (c.appTop.hom ∘ (Scheme.ΓSpecIso (.of R)).inv.hom)
      exact hsurj.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    let ψ' : Γ(W, ⊤) →+* R'' := (θ.hom.liftOfSurjective hθsurj) ⟨ψ, hle⟩
    have hψ' : ψ'.comp θ.hom = ψ := θ.hom.liftOfSurjective_comp hθsurj ⟨ψ, hle⟩
    refine ⟨Spec.map (CommRingCat.ofHom ψ') ≫ W.isoSpec.inv, ?_⟩
    conv_rhs => rw [← hψ']
    rw [Category.assoc, CommRingCat.ofHom_comp, Spec.map_comp]
    congr 1
    rw [Iso.inv_comp_eq, Scheme.isoSpec_hom]
    exact eq_toSpecΓ_comp c

theorem exists_comp_snd_eq_iff {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    {T : C} (t : T ⟶ Y) : (∃ w : T ⟶ pullback f g, w ≫ pullback.snd f g = t) ↔ ∃ v : T ⟶ X, v ≫ f = t ≫ g := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w ≫ pullback.fst f g, by rw [Category.assoc, pullback.condition, Category.assoc]⟩
  · rintro ⟨v, hv⟩
    exact ⟨pullback.lift v t hv, pullback.lift_snd _ _ _⟩

variable {Y S : Scheme.{u}} (p : Y ⟶ S) [IsSeparated p]

abbrev pair {R : Type u} [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p) :
    Spec (CommRingCat.of R) ⟶ pullback p p :=
  pullback.lift σ τ h

abbrev eqImm {R : Type u} [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p) :
    pullback (pullback.diagonal p) (pair p σ τ h) ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (pullback.diagonal p) (pair p σ τ h)

def eqIdeal (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p) : Ideal R :=
  kerIdeal (eqImm p σ τ h)

theorem factors_diagonal_iff {T : Scheme.{u}} (q : T ⟶ pullback p p) :
    (∃ v : T ⟶ Y, v ≫ pullback.diagonal p = q) ↔ q ≫ pullback.fst p p = q ≫ pullback.snd p p := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  · intro hq
    refine ⟨q ≫ pullback.fst p p, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hq]

theorem eqIdeal_le_ker_iff {R : Type u} [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p)
    (R'' : Type u) [CommRing R''] (ψ : R →+* R'') :
    eqIdeal p R σ τ h ≤ RingHom.ker ψ ↔
      Spec.map (CommRingCat.ofHom ψ) ≫ σ = Spec.map (CommRingCat.ofHom ψ) ≫ τ := by
  rw [eqIdeal, ← exists_comp_eq_iff_kerIdeal_le, exists_comp_snd_eq_iff, factors_diagonal_iff]
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

theorem eqIdeal_eq_bot_iff {R : Type u} [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p) :
    eqIdeal p R σ τ h = ⊥ ↔ σ = τ := by
  have hk : RingHom.ker (RingHom.id R) = ⊥ := by
    ext x; simp [RingHom.mem_ker]
  have := eqIdeal_le_ker_iff p σ τ h R (RingHom.id R)
  rw [hk, le_bot_iff, CommRingCat.ofHom_id] at this
  erw [Spec.map_id, Category.id_comp, Category.id_comp] at this
  exact this

theorem eqIdeal_baseChange {R R' : Type u} [CommRing R] [CommRing R'] (ψ : R →+* R')
    (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p) :
    eqIdeal p R' (Spec.map (CommRingCat.ofHom ψ) ≫ σ) (Spec.map (CommRingCat.ofHom ψ) ≫ τ)
        (by rw [Category.assoc, Category.assoc, h]) = (eqIdeal p R σ τ h).map ψ := by

  have key : ∀ (R'' : Type u) [CommRing R''] (χ : R' →+* R''),
      eqIdeal p R' (Spec.map (CommRingCat.ofHom ψ) ≫ σ) (Spec.map (CommRingCat.ofHom ψ) ≫ τ)
          (by rw [Category.assoc, Category.assoc, h]) ≤ RingHom.ker χ ↔
        (eqIdeal p R σ τ h).map ψ ≤ RingHom.ker χ := by
    intro R'' _ χ
    have hck : Ideal.comap ψ (RingHom.ker χ) = RingHom.ker (χ.comp ψ) := by
      ext x; simp [RingHom.mem_ker]
    rw [eqIdeal_le_ker_iff, Ideal.map_le_iff_le_comap, hck, eqIdeal_le_ker_iff,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc]
  apply le_antisymm
  · have h1 := (key _ (Ideal.Quotient.mk ((eqIdeal p R σ τ h).map ψ))).2 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at h1
  · have h1 := (key _ (Ideal.Quotient.mk (eqIdeal p R' (Spec.map (CommRingCat.ofHom ψ) ≫ σ)
      (Spec.map (CommRingCat.ofHom ψ) ≫ τ) (by rw [Category.assoc, Category.assoc, h])))).1 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at h1

theorem eqIdeal_fg [LocallyOfFiniteType p] {R : Type u} [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y)
    (h : σ ≫ p = τ ≫ p) : (eqIdeal p R σ τ h).FG := by
  haveI : LocallyOfFinitePresentation (pullback.diagonal p) := G2.main p
  let c := eqImm p σ τ h
  haveI hc : LocallyOfFinitePresentation c := inferInstance
  obtain ⟨hW, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine c
  haveI := hW
  have hfp : c.appTop.hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp hc

  have hker : (RingHom.ker c.appTop.hom).FG := by
    algebraize [c.appTop.hom]
    have := Algebra.FinitePresentation.ker_fG_of_surjective
      (Algebra.ofId (Γ(Spec (CommRingCat.of R), ⊤)) (Γ(pullback (pullback.diagonal p) (pair p σ τ h), ⊤))) hsurj
    exact this

  have e : eqIdeal p R σ τ h = (RingHom.ker c.appTop.hom).map (Scheme.ΓSpecIso (.of R)).hom.hom := by
    show RingHom.ker ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appTop).hom = _
    rw [CommRingCat.hom_comp, ← RingHom.comap_ker]
    apply le_antisymm
    · intro x hx
      have : x = (Scheme.ΓSpecIso (.of R)).hom.hom ((Scheme.ΓSpecIso (.of R)).inv.hom x) := by
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      show (Scheme.ΓSpecIso (.of R)).inv.hom ((Scheme.ΓSpecIso (.of R)).hom.hom y) ∈ RingHom.ker c.appTop.hom
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      exact hy
  rw [e]
  exact hker.map _

end G1

end

theorem solution
    {Y S : Scheme.{u}} (p : Y ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] :
    ∃ I : ∀ (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y), σ ≫ p = τ ≫ p → Ideal R,
      (∀ (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p),
          I R σ τ h = ⊥ ↔ σ = τ) ∧
      (∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (σ τ : Spec (CommRingCat.of R) ⟶ Y)
          (h : σ ≫ p = τ ≫ p),
        I R' (Spec.map (CommRingCat.ofHom ψ) ≫ σ) (Spec.map (CommRingCat.ofHom ψ) ≫ τ)
            (by rw [Category.assoc, Category.assoc, h]) = (I R σ τ h).map ψ) ∧
      (∀ (R : Type u) [CommRing R] (σ τ : Spec (CommRingCat.of R) ⟶ Y) (h : σ ≫ p = τ ≫ p), (I R σ τ h).FG) :=
  ⟨fun R _ σ τ h => G1.eqIdeal p R σ τ h, fun R _ σ τ h => G1.eqIdeal_eq_bot_iff p σ τ h,
    fun R R' _ _ ψ σ τ h => G1.eqIdeal_baseChange p ψ σ τ h, fun R _ σ τ h => G1.eqIdeal_fg p σ τ h⟩

end S_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType (solution)
