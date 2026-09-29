-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_chart_iff_of_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e5da8701-4ea1-5fd0-8987-4c0ff4a489f1

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_of_descent

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens)
    (R₀ : Type) [CommRing R₀] [IsNoetherianRing R₀] (φ : R₀ →+* R)
    (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (L₀ : RelativeGroupLaw R₀ f₀) (hA₀ : AbelianSchemePropertyBundle R₀ f₀)
    (X₀ : Scheme.{0}) (g₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) [LocallyOfFiniteType g₀]
    (M₀ : RigidifiedLineBundle f₀ (L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) g₀)
    (a : A ⟶ A₀) (ha : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom φ)))
    (u : ((U : X.Opens) : Scheme.{0}) ⟶ X₀) (hu : IsPullback u ((U : X.Opens).ι ≫ g) g₀ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (hM : Nonempty ((M.pullbackAlong (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g) g)).L ≅
      (Scheme.Modules.pullback
        (pullback.map f ((U : X.Opens).ι ≫ g) f₀ g₀ a u (Spec.map (CommRingCat.ofHom φ)) ha.w.symm hu.w.symm)).obj M₀.L))
    (Z₀ : Scheme.{0}) (ι₀ : Z₀ ⟶ X₀) (hι₀ : IsClosedImmersion ι₀)
    (hZ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (ψ : SchemeHomOver t g₀),
        Nonempty ((M₀.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f₀) (ε := L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z₀, ψ₀ ≫ ι₀ = ψ.1) :
    ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})),
        IsClosedImmersion ιU ∧ LocallyOfFinitePresentation ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU) := by
  classical
  haveI := hι₀
  haveI : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian g₀
  haveI : LocallyOfFinitePresentation ι₀ := inferInstance

  refine ⟨pullback ι₀ u, pullback.snd ι₀ u, inferInstance, inferInstance, ?_⟩
  intro T t ψU hψ

  have hψ' : ψU ≫ ((U : X.Opens).ι ≫ g) = t := by rw [← Category.assoc]; exact hψ
  let ψ : SchemeHomOver t g := ⟨ψU ≫ (U : X.Opens).ι, hψ⟩
  let ψUo : SchemeHomOver t ((U : X.Opens).ι ≫ g) := ⟨ψU, hψ'⟩
  let t' : T ⟶ Spec (CommRingCat.of R₀) := t ≫ Spec.map (CommRingCat.ofHom φ)
  let ψ' : SchemeHomOver t' g₀ := ⟨ψU ≫ u, by
    show ψU ≫ u ≫ g₀ = t ≫ Spec.map (CommRingCat.ofHom φ)
    rw [hu.w, ← Category.assoc, hψ']⟩

  let θ : pullback f t ⟶ pullback f₀ t' :=
    pullback.lift (pullback.fst f t ≫ a) (pullback.snd f t) (by rw [Category.assoc, ha.w, pullback.condition_assoc])
  have hθ₁ : θ ≫ pullback.fst f₀ t' = pullback.fst f t ≫ a := pullback.lift_fst _ _ _
  have hθ₂ : θ ≫ pullback.snd f₀ t' = pullback.snd f t := pullback.lift_snd _ _ _
  let θi : pullback f₀ t' ⟶ pullback f t :=
    pullback.lift (ha.lift (pullback.fst f₀ t') (pullback.snd f₀ t' ≫ t) (by rw [pullback.condition, Category.assoc]))
      (pullback.snd f₀ t') (by rw [ha.lift_snd])
  have hθi₁ : θi ≫ pullback.fst f t = ha.lift (pullback.fst f₀ t') (pullback.snd f₀ t' ≫ t)
      (by rw [pullback.condition, Category.assoc]) := pullback.lift_fst _ _ _
  have hθi₂ : θi ≫ pullback.snd f t = pullback.snd f₀ t' := pullback.lift_snd _ _ _
  have hθθi : θ ≫ θi = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθi₁, Category.id_comp]
      apply ha.hom_ext
      · rw [Category.assoc, ha.lift_fst, hθ₁]
      · rw [Category.assoc, ha.lift_snd, ← Category.assoc, hθ₂, pullback.condition]
    · rw [Category.assoc, hθi₂, hθ₂, Category.id_comp]
  have hθiθ : θi ≫ θ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθ₁, ← Category.assoc, hθi₁, ha.lift_fst, Category.id_comp]
    · rw [Category.assoc, hθ₂, hθi₂, Category.id_comp]

  have key : baseChangeSnd f ψUo ≫
      pullback.map f ((U : X.Opens).ι ≫ g) f₀ g₀ a u (Spec.map (CommRingCat.ofHom φ)) ha.w.symm hu.w.symm =
        θ ≫ baseChangeSnd f₀ ψ' := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, baseChangeSnd, pullback.lift_fst_assoc, Category.comp_id]
      rw [hθ₁]
    · simp only [Category.assoc, pullback.lift_snd, baseChangeSnd, pullback.lift_snd_assoc]
      show (pullback.snd f t ≫ ψU) ≫ u = θ ≫ pullback.snd f₀ t' ≫ (ψU ≫ u)
      rw [reassoc_of% hθ₂, Category.assoc]
  have hψsplit : baseChangeSnd f ψ = baseChangeSnd f ψUo ≫
      baseChangeSnd f (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g) g) := by
    rw [baseChangeSnd_comp]
    rfl

  have cmp : (M.pullbackAlong ψ).L ≅ (Scheme.Modules.pullback θ).obj ((M₀.pullbackAlong ψ').L) := by
    change (Scheme.Modules.pullback (baseChangeSnd f ψ)).obj M.L ≅
      (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback (baseChangeSnd f₀ ψ')).obj M₀.L)
    exact (Scheme.Modules.pullbackCongr hψsplit).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd f ψUo)).mapIso hM.some ≪≫
      (Scheme.Modules.pullbackComp _ _).app M₀.L ≪≫
      (Scheme.Modules.pullbackCongr key).app M₀.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M₀.L).symm

  have htriv : Nonempty ((M.pullbackAlong ψ).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
      Nonempty ((M₀.pullbackAlong ψ').L ≅
        (RigidifiedLineBundle.unit (c := f₀) (ε := L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) t').L) := by
    constructor
    · rintro ⟨e⟩

      refine ⟨?_⟩
      change (Scheme.Modules.pullback (baseChangeSnd f₀ ψ')).obj M₀.L ≅ SheafOfModules.unit _
      have e1 : (Scheme.Modules.pullback (baseChangeSnd f₀ ψ')).obj M₀.L ≅
          (Scheme.Modules.pullback θi).obj ((Scheme.Modules.pullback θ).obj
            ((Scheme.Modules.pullback (baseChangeSnd f₀ ψ')).obj M₀.L)) :=
        ((Scheme.Modules.pullbackId _).app _).symm ≪≫
        (Scheme.Modules.pullbackCongr hθiθ.symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm
      exact e1 ≪≫ (Scheme.Modules.pullback θi).mapIso (cmp.symm ≪≫ e) ≪≫ Scheme.Modules.pullbackUnitIso θi
    · rintro ⟨e⟩
      exact ⟨cmp ≪≫ (Scheme.Modules.pullback θ).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso θ⟩
  rw [htriv, hZ₀ t' ψ']

  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨pullback.lift χ ψU hχ, pullback.lift_snd _ _ _⟩
  · rintro ⟨ψ₀, hψ₀⟩
    exact ⟨ψ₀ ≫ pullback.fst ι₀ u, by rw [Category.assoc, pullback.condition, ← Category.assoc, hψ₀]⟩

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_of_descent
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_of_descent (solution)
