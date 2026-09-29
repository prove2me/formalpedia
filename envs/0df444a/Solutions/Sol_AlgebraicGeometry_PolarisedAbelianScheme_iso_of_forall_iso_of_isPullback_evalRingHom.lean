-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.iso_of_forall_iso_of_isPullback_evalRingHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2f351e81-6873-5717-965d-812297c93f6e

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_iso_of_isPullback_evalRingHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

namespace G2IsoProd

variable {k : ℕ} (R : Fin k → Type) [∀ i, CommRing (R i)]

noncomputable abbrev ιS (i : Fin k) : Spec (CommRingCat.of (R i)) ⟶ Spec (CommRingCat.of (∀ i, R i)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i))

scoped instance isOpenImmersion_ιS (i : Fin k) : IsOpenImmersion (ιS R i) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i))))

theorem exists_ιS_eq (s : ↥(Spec (CommRingCat.of (∀ i, R i)))) :
    ∃ (i : Fin k) (q : ↥(Spec (CommRingCat.of (R i)))), (ιS R i).base q = s :=
  PrimeSpectrum.exists_comap_evalRingHom_eq s

theorem ιS_ne {i j : Fin k} (hij : i ≠ j) (q : ↥(Spec (CommRingCat.of (R i)))) (q' : ↥(Spec (CommRingCat.of (R j)))) :
    (ιS R i).base q ≠ (ιS R j).base q' := by
  classical
  intro heq
  have h1 : (Pi.single j (1 : R j) : ∀ i, R i) ∈ ((ιS R i).base q).asIdeal := by
    show Pi.evalRingHom R i (Pi.single j 1) ∈ q.asIdeal
    rw [Pi.evalRingHom_apply, Pi.single_eq_of_ne hij]
    exact q.asIdeal.zero_mem
  have h2 : (Pi.single j (1 : R j) : ∀ i, R i) ∉ ((ιS R j).base q').asIdeal := by
    show Pi.evalRingHom R j (Pi.single j 1) ∉ q'.asIdeal
    rw [Pi.evalRingHom_apply, Pi.single_eq_same, ← Ideal.eq_top_iff_one]
    exact q'.isPrime.ne_top
  exact h2 (heq ▸ h1)

section Cover

variable {W : Scheme.{0}} (fW : W ⟶ Spec (CommRingCat.of (∀ i, R i)))
  {V : Fin k → Scheme.{0}} (fV : ∀ i, V i ⟶ Spec (CommRingCat.of (R i))) (c : ∀ i, V i ⟶ W)
  (hc : ∀ i, IsPullback (c i) (fV i) fW (ιS R i))

include hc in
theorem isOpenImmersion_c (i : Fin k) : IsOpenImmersion (c i) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hc i).flip inferInstance

include hc in
theorem c_apply_eq (i : Fin k) (x : ↥(V i)) : fW.base ((c i).base x) = (ιS R i).base ((fV i).base x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (hc i).w]

include hc in

theorem exists_c_eq (i : Fin k) (w : ↥W) (q : ↥(Spec (CommRingCat.of (R i)))) (hw : fW.base w = (ιS R i).base q) :
    ∃ x : ↥(V i), (c i).base x = w ∧ (fV i).base x = q := by
  have hy : w ∈ Set.range (pullback.fst fW (ιS R i)).base := by
    rw [Scheme.Pullback.range_fst]; exact ⟨q, hw.symm⟩
  obtain ⟨z, hz⟩ := hy
  refine ⟨(hc i).isoPullback.inv.base z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, (hc i).isoPullback_inv_fst]; exact hz
  · apply (ιS R i).isOpenEmbedding.injective
    rw [← c_apply_eq R fW fV c hc]
    have : (c i).base ((hc i).isoPullback.inv.base z) = w := by
      rw [← Scheme.Hom.comp_apply, (hc i).isoPullback_inv_fst]; exact hz
    rw [this, hw]

include hc in
theorem covers (w : ↥W) : ∃ (i : Fin k) (x : ↥(V i)), (c i).base x = w := by
  obtain ⟨i, q, hq⟩ := exists_ιS_eq R (fW.base w)
  obtain ⟨x, hx, -⟩ := exists_c_eq R fW fV c hc i w q hq.symm
  exact ⟨i, x, hx⟩

include hc in

noncomputable def cov : W.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin k) V c (covers R fW fV c hc) (fun i => isOpenImmersion_c R fW fV c hc i)

include hc in
theorem isEmpty_pullback {i j : Fin k} (hij : i ≠ j) : IsEmpty ↥(pullback (c i) (c j)) := by
  refine ⟨fun z => ιS_ne R hij ((fV i).base ((pullback.fst (c i) (c j)).base z)) ((fV j).base ((pullback.snd (c i) (c j)).base z)) ?_⟩
  rw [← c_apply_eq R fW fV c hc, ← c_apply_eq R fW fV c hc]
  have h := congrArg (fun m : pullback (c i) (c j) ⟶ W => fW.base (m.base z)) (pullback.condition (f := c i) (g := c j))
  exact h

include hc in

theorem exists_glued {Z : Scheme.{0}} (φ : ∀ i, V i ⟶ Z) : ∃ m : W ⟶ Z, ∀ i, c i ≫ m = φ i := by
  have hcompat : ∀ i j : Fin k, pullback.fst ((cov R fW fV c hc).f i) ((cov R fW fV c hc).f j) ≫ φ i =
      pullback.snd ((cov R fW fV c hc).f i) ((cov R fW fV c hc).f j) ≫ φ j := by
    intro i j
    change pullback.fst (c i) (c j) ≫ φ i = pullback.snd (c i) (c j) ≫ φ j
    by_cases hij : i = j
    · subst hij
      haveI := isOpenImmersion_c R fW fV c hc i
      rw [fst_eq_snd_of_mono_eq]
    · haveI := isEmpty_pullback R fW fV c hc hij
      exact Limits.IsInitial.hom_ext isInitialOfIsEmpty _ _
  exact ⟨(cov R fW fV c hc).glueMorphisms φ hcompat, fun i => (cov R fW fV c hc).ι_glueMorphisms φ hcompat i⟩

include hc in
private theorem _root_.G2IsoProd.hom_ext {Z : Scheme.{0}} (a b : W ⟶ Z) (h : ∀ i, c i ≫ a = c i ≫ b) : a = b :=
  (cov R fW fV c hc).hom_ext a b h

p2m_export "G2IsoProd" "hom_ext"
end Cover

theorem mul_val_congr' {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst h; cases Subtype.ext hx; cases Subtype.ext hy; rfl

noncomputable def pullbackInvHomIso {A A' : Scheme.{0}} (e : A ≅ A') (M : A'.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫ (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
    (Scheme.Modules.pullbackId A').app M

noncomputable def isoOfPullbackIso {A A' : Scheme.{0}} (e : A' ≅ A) {M N : A.Modules}
    (φ : (Scheme.Modules.pullback e.hom).obj M ≅ (Scheme.Modules.pullback e.hom).obj N) : M ≅ N :=
  (pullbackInvHomIso e M).symm ≪≫ (Scheme.Modules.pullback e.inv).mapIso φ ≪≫ pullbackInvHomIso e N

noncomputable def pullbackSquareIso {V V' A A' : Scheme.{0}} (j : V' ⟶ V) (ι : V ⟶ A) (ι' : V' ⟶ A') (c : A' ⟶ A)
    (h : j ≫ ι = ι' ≫ c) (M : A.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj M) ≅
      (Scheme.Modules.pullback ι').obj ((Scheme.Modules.pullback c).obj M) :=
  (Scheme.Modules.pullbackComp j ι).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp ι' c).app M).symm

end G2IsoProd
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_iso_of_isPullback_evalRingHom.G2IsoProd"

open G2IsoProd in
theorem solution
    {g d n : ℕ} {k : ℕ} (R : Fin k → Type) [∀ i, CommRing (R i)]
    (w₁ w₂ : PolarisedAbelianScheme g d n (∀ i, R i))
    (v₁ v₂ : ∀ i, PolarisedAbelianScheme g d n (R i))
    (h₁ : ∀ i, PolarisedAbelianScheme.IsPullback (Pi.evalRingHom R i) w₁ (v₁ i))
    (h₂ : ∀ i, PolarisedAbelianScheme.IsPullback (Pi.evalRingHom R i) w₂ (v₂ i))
    (h : ∀ i, PolarisedAbelianScheme.Iso (v₁ i) (v₂ i)) :
    PolarisedAbelianScheme.Iso w₁ w₂ := by
  classical
  choose c₁ pb₁ mul₁ lev₁ pol₁ using h₁
  choose c₂ pb₂ mul₂ lev₂ pol₂ using h₂
  choose e he hemul helev hepol using h

  obtain ⟨m₁₂, hm₁₂⟩ := exists_glued R w₁.f (fun i => (v₁ i).f) c₁ pb₁ (fun i => (e i).hom ≫ c₂ i)
  obtain ⟨m₂₁, hm₂₁⟩ := exists_glued R w₂.f (fun i => (v₂ i).f) c₂ pb₂ (fun i => (e i).inv ≫ c₁ i)
  let E : w₁.A ≅ w₂.A :=
    { hom := m₁₂, inv := m₂₁,
      hom_inv_id := hom_ext R w₁.f (fun i => (v₁ i).f) c₁ pb₁ _ _ fun i => by
        rw [← Category.assoc, hm₁₂, Category.assoc, hm₂₁, Iso.hom_inv_id_assoc, Category.comp_id]
      inv_hom_id := hom_ext R w₂.f (fun i => (v₂ i).f) c₂ pb₂ _ _ fun i => by
        rw [← Category.assoc, hm₂₁, Category.assoc, hm₁₂, Iso.inv_hom_id_assoc, Category.comp_id] }
  have hE : E.hom ≫ w₂.f = w₁.f := hom_ext R w₁.f (fun i => (v₁ i).f) c₁ pb₁ _ _ fun i => by
    show c₁ i ≫ m₁₂ ≫ w₂.f = c₁ i ≫ w₁.f
    rw [← Category.assoc, hm₁₂, Category.assoc, (pb₂ i).w, ← Category.assoc, he i, (pb₁ i).w]
  refine ⟨E, hE, ?_, ?_, ?_⟩
  ·
    intro T t x y
    refine hom_ext R t (fun i => pullback.snd t (ιS R i)) (fun i => pullback.fst t (ιS R i))
      (fun i => IsPullback.of_hasPullback t (ιS R i)) _ _ fun i => ?_
    have hcond : pullback.fst t (ιS R i) ≫ t = pullback.snd t (ιS R i) ≫ ιS R i := pullback.condition

    let xᵢ : SchemeHomOver (pullback.snd t (ιS R i)) (v₁ i).f :=
      ⟨(pb₁ i).lift (pullback.fst t (ιS R i) ≫ x.1) (pullback.snd t (ιS R i)) (by rw [Category.assoc, x.2, hcond]),
        (pb₁ i).lift_snd _ _ _⟩
    let yᵢ : SchemeHomOver (pullback.snd t (ιS R i)) (v₁ i).f :=
      ⟨(pb₁ i).lift (pullback.fst t (ιS R i) ≫ y.1) (pullback.snd t (ιS R i)) (by rw [Category.assoc, y.2, hcond]),
        (pb₁ i).lift_snd _ _ _⟩
    have hx : xᵢ.1 ≫ c₁ i = pullback.fst t (ιS R i) ≫ x.1 := (pb₁ i).lift_fst _ _ _
    have hy : yᵢ.1 ≫ c₁ i = pullback.fst t (ιS R i) ≫ y.1 := (pb₁ i).lift_fst _ _ _

    have eL := congrArg Subtype.val (w₁.L.mul_natural t _ (pullback.fst t (ιS R i)) rfl x y)
    have eR := congrArg Subtype.val (w₂.L.mul_natural t _ (pullback.fst t (ιS R i)) rfl
      ⟨x.1 ≫ E.hom, by rw [Category.assoc, hE]; exact x.2⟩ ⟨y.1 ≫ E.hom, by rw [Category.assoc, hE]; exact y.2⟩)
    simp only [schemeHomOverComp_coe] at eL eR
    have step1 : (w₁.L.mul (pullback.fst t (ιS R i) ≫ t) (schemeHomOverComp (pullback.fst t (ιS R i)) rfl x)
        (schemeHomOverComp (pullback.fst t (ιS R i)) rfl y)).1 =
        (w₁.L.mul (pullback.snd t (ιS R i) ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))
          ⟨xᵢ.1 ≫ c₁ i, by rw [Category.assoc, (pb₁ i).w, ← Category.assoc, xᵢ.2]⟩
          ⟨yᵢ.1 ≫ c₁ i, by rw [Category.assoc, (pb₁ i).w, ← Category.assoc, yᵢ.2]⟩).1 :=
      mul_val_congr' w₁.L hcond _ _ _ _ (by show pullback.fst t (ιS R i) ≫ x.1 = xᵢ.1 ≫ c₁ i; exact hx.symm)
        (by show pullback.fst t (ιS R i) ≫ y.1 = yᵢ.1 ≫ c₁ i; exact hy.symm)
    have step2 := mul₁ i _ xᵢ yᵢ
    show pullback.fst t (ιS R i) ≫ (w₁.L.mul t x y).1 ≫ m₁₂ = pullback.fst t (ιS R i) ≫ (w₂.L.mul t _ _).1
    rw [← Category.assoc, eL, step1, ← step2, Category.assoc, hm₁₂ i, ← Category.assoc, hemul i, mul₂ i, eR]
    exact mul_val_congr' w₂.L hcond.symm _ _ _ _
      (by
        show (xᵢ.1 ≫ (e i).hom) ≫ c₂ i = pullback.fst t (ιS R i) ≫ x.1 ≫ m₁₂
        rw [Category.assoc, ← hm₁₂ i, ← Category.assoc, hx, Category.assoc])
      (by
        show (yᵢ.1 ≫ (e i).hom) ≫ c₂ i = pullback.fst t (ιS R i) ≫ y.1 ≫ m₁₂
        rw [Category.assoc, ← hm₁₂ i, ← Category.assoc, hy, Category.assoc])
  ·
    intro j
    let cP : (Spec (CommRingCat.of (∀ i, R i))).OpenCover :=
      Scheme.Cover.mkOfCovers (Fin k) (fun i => Spec (CommRingCat.of (R i))) (ιS R) (exists_ιS_eq R)
    refine cP.hom_ext _ _ fun i => ?_
    show ιS R i ≫ (w₁.P j).1 ≫ m₁₂ = ιS R i ≫ (w₂.P j).1
    rw [← Category.assoc, ← lev₁ i j, Category.assoc, hm₁₂, ← Category.assoc, helev i j, lev₂ i j]
  ·
    intro s
    obtain ⟨i, q, rfl⟩ := exists_ιS_eq R s
    obtain ⟨U', hq, ⟨φ⟩⟩ := hepol i q
    refine ⟨(ιS R i) ''ᵁ U', ⟨q, hq, rfl⟩, ⟨?_⟩⟩

    let V : w₁.A.Opens := w₁.f ⁻¹ᵁ ((ιS R i) ''ᵁ U')
    let V' : (v₁ i).A.Opens := (v₁ i).f ⁻¹ᵁ U'
    haveI := isOpenImmersion_c R w₁.f (fun i => (v₁ i).f) c₁ pb₁ i
    have hrange : Set.range (V'.ι ≫ c₁ i).base ⊆ Set.range V.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      show w₁.f.base ((c₁ i).base (V'.ι.base x)) ∈ (ιS R i) ''ᵁ U'
      rw [c_apply_eq R w₁.f (fun i => (v₁ i).f) c₁ pb₁]
      exact ⟨(v₁ i).f.base (V'.ι.base x), x.2, rfl⟩
    let j := IsOpenImmersion.lift V.ι (V'.ι ≫ c₁ i) hrange
    have hj : j ≫ V.ι = V'.ι ≫ c₁ i := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
    haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
    have hjsurj : Function.Surjective j.base := by
      intro v
      have hv2 : w₁.f.base (V.ι.base v) ∈ (ιS R i).base '' (U' : Set _) := v.2
      obtain ⟨q', hq', hv⟩ := hv2
      obtain ⟨x, hx, hxq⟩ := exists_c_eq R w₁.f (fun i => (v₁ i).f) c₁ pb₁ i (V.ι.base v) q' hv.symm
      refine ⟨⟨x, show (v₁ i).f.base x ∈ U' by rw [hxq]; exact hq'⟩, ?_⟩
      apply V.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]
      exact hx
    haveI : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j
      (TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr hjsurj))

    let α : (Scheme.Modules.pullback (c₁ i)).obj ((Scheme.Modules.pullback E.hom).obj w₂.pol) ≅
        (Scheme.Modules.pullback (e i).hom).obj (v₂ i).pol :=
      (Scheme.Modules.pullbackComp (c₁ i) E.hom).app w₂.pol ≪≫ (Scheme.Modules.pullbackCongr (hm₁₂ i)).app w₂.pol ≪≫
        ((Scheme.Modules.pullbackComp (e i).hom (c₂ i)).app w₂.pol).symm ≪≫
        (Scheme.Modules.pullback (e i).hom).mapIso (pol₂ i).some
    let K : (Scheme.Modules.pullback V'.ι).obj ((Scheme.Modules.pullback (c₁ i)).obj ((Scheme.Modules.pullback E.hom).obj w₂.pol)) ≅
        (Scheme.Modules.pullback V'.ι).obj ((Scheme.Modules.pullback (c₁ i)).obj w₁.pol) :=
      (Scheme.Modules.pullback V'.ι).mapIso α ≪≫ φ ≪≫ (Scheme.Modules.pullback V'.ι).mapIso (pol₁ i).some.symm
    exact isoOfPullbackIso (asIso j)
      (pullbackSquareIso j V.ι V'.ι (c₁ i) hj _ ≪≫ K ≪≫ (pullbackSquareIso j V.ι V'.ι (c₁ i) hj _).symm)

end S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_iso_of_isPullback_evalRingHom
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_iso_of_forall_iso_of_isPullback_evalRingHom (solution)
