-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/37261583-b127-5ffa-a68d-2c52a186d750

import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open scoped TensorProduct

universe u

namespace KTDescent

theorem locIsoOnBase_unit_pullback_base {S S'' : Type u} [CommRing S] [CommRing S''] {X X' : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of S)) (q' : X' ⟶ Spec (CommRingCat.of S''))
    (π : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S)) (θ : X' ⟶ X) (hθ : θ ≫ q = q' ≫ π)
    (M : X.Modules) (h : LocIsoOnBase q M (𝟙_ X.Modules)) :
    LocIsoOnBase q' ((Scheme.Modules.pullback θ).obj M) (𝟙_ X'.Modules) := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h (π.base s)
  refine ⟨π ⁻¹ᵁ U, hs, ⟨?_⟩⟩
  have hle : q' ⁻¹ᵁ (π ⁻¹ᵁ U) ≤ θ ⁻¹ᵁ (q ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hθ]
  have hρ := Scheme.Hom.resLE_comp_ι θ hle
  exact (Scheme.Modules.pullbackComp (q' ⁻¹ᵁ (π ⁻¹ᵁ U)).ι θ).app M ≪≫
    (Scheme.Modules.pullbackCongr hρ.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (θ.resLE (q ⁻¹ᵁ U) (q' ⁻¹ᵁ (π ⁻¹ᵁ U)) hle) (q ⁻¹ᵁ U).ι).app M).symm ≪≫
    (Scheme.Modules.pullback (θ.resLE (q ⁻¹ᵁ U) (q' ⁻¹ᵁ (π ⁻¹ᵁ U)) hle)).mapIso e ≪≫
    (Scheme.Modules.pullback (θ.resLE (q ⁻¹ᵁ U) (q' ⁻¹ᵁ (π ⁻¹ᵁ U)) hle)).mapIso
      (Scheme.Modules.pullbackTensorUnitObjIso (q ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (θ.resLE (q ⁻¹ᵁ U) (q' ⁻¹ᵁ (π ⁻¹ᵁ U)) hle) ≪≫
    (Scheme.Modules.pullbackTensorUnitObjIso (q' ⁻¹ᵁ (π ⁻¹ᵁ U)).ι).symm

theorem locIsoOnBase_unit_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of S')) {M N : X.Modules} (e : M ≅ N)
    (h : LocIsoOnBase g M (𝟙_ X.Modules)) : LocIsoOnBase g N (𝟙_ X.Modules) := by
  intro s
  obtain ⟨U, hs, ⟨e'⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e.symm ≪≫ e'⟩⟩

theorem mul_coe_congr {S : Type u} [CommRing S] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

noncomputable def pullbackTensor₃ {X Y : Scheme.{u}} (φ : X ⟶ Y) (A B C : Y.Modules) :
    (Scheme.Modules.pullback φ).obj (A ⊗ (B ⊗ C)) ≅
      (Scheme.Modules.pullback φ).obj A ⊗ ((Scheme.Modules.pullback φ).obj B ⊗ (Scheme.Modules.pullback φ).obj C) :=
  Scheme.Modules.pullbackTensorObjIso φ A (B ⊗ C) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso φ B C)

noncomputable def pbComp {X Y Z : Scheme.{u}} (ψ : X ⟶ Y) (φ : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback φ).obj M) ≅ (Scheme.Modules.pullback (ψ ≫ φ)).obj M :=
  (Scheme.Modules.pullbackComp ψ φ).app M

theorem epi_SpecMap_baseChange (k k' R : Type u) [Field k] [Field k'] [Algebra k k'] [CommRing R] [Algebra k R] :
    Epi (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] k')))) := by
  have hff : (CommRingCat.ofHom (algebraMap R (R ⊗[k] k'))).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff _).mpr hff
  exact Flat.epi_of_flat_of_surjective _

end KTDescent

open KTDescent

theorem solution
    (k k' : Type) [Field k] [Field k'] [Algebra k k']
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (f' : A' ⟶ Spec (CommRingCat.of k')) (L' : RelativeGroupLaw k' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : KernelTrivial f' L' ((Scheme.Modules.pullback g).obj 𝓛)) :
    KernelTrivial f L 𝓛 := by
  intro R _ t x hloc

  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective t
  letI : Algebra k R := φ₀.hom.toAlgebra

  obtain ⟨π, hπ⟩ : ∃ π : Spec (CommRingCat.of (R ⊗[k] k')) ⟶ Spec (CommRingCat.of R),
      π = Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] k'))) := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of (R ⊗[k] k')) ⟶ Spec (CommRingCat.of k'),
      t' = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := k')).toRingHom) := ⟨_, rfl⟩
  haveI : Epi π := hπ ▸ epi_SpecMap_baseChange k k' R
  have hsq : π ≫ t = t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
    rw [hπ, ht', ← hφ₀, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    change algebraMap R (R ⊗[k] k') (φ₀.hom r) =
      (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := k')) (algebraMap k k' r)
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply,
      show φ₀.hom r = algebraMap k R r from rfl, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

  obtain ⟨x', hx'g⟩ : ∃ x' : SchemeHomOver t' f', x'.1 ≫ g = π ≫ x.1 :=
    ⟨⟨hg.lift (π ≫ x.1) t' (by rw [Category.assoc, x.2, hsq]), hg.lift_snd _ _ _⟩, hg.lift_fst _ _ _⟩

  let Θ : pullback f' t' ⟶ pullback f t :=
    pullback.lift (pullback.fst f' t' ≫ g) (pullback.snd f' t' ≫ π)
      (by simp only [Category.assoc, hg.w, hsq]; rw [← Category.assoc, pullback.condition, Category.assoc])
  have hΘ : Θ ≫ pullback.snd f t = pullback.snd f' t' ≫ π := pullback.lift_snd _ _ _

  obtain ⟨edual⟩ := h𝓛.pullback_dual_monoidalV2 g
  have E2 : (sliceAt f' x' ≫ pullback.fst f' f') ≫ g = (Θ ≫ sliceAt f x) ≫ pullback.fst f f := by
    simp only [sliceAt, Θ, Category.assoc, pullback.lift_fst]
  have E3 : (sliceAt f' x' ≫ pullback.snd f' f') ≫ g = (Θ ≫ sliceAt f x) ≫ pullback.snd f f := by
    simp only [sliceAt, Θ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hx'g]
  have E1 : (sliceAt f' x' ≫ addMor f' L') ≫ g = (Θ ≫ sliceAt f x) ≫ addMor f L := by
    have lhs : (sliceAt f' x' ≫ addMor f' L') ≫ g =
        (L.mul (sliceAt f' x' ≫ ((pullback.fst f' f' ≫ f') ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))))
          (GoodReductionJacobian.schemeHomOverComp (sliceAt f' x') rfl
            ⟨pullback.fst f' f' ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc]⟩)
          (GoodReductionJacobian.schemeHomOverComp (sliceAt f' x') rfl
            ⟨pullback.snd f' f' ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, pullback.condition]⟩)).1 := by
      rw [← L.mul_natural]
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, addMor, Category.assoc, hg_mul]
    have rhs : (Θ ≫ sliceAt f x) ≫ addMor f L =
        (L.mul ((Θ ≫ sliceAt f x) ≫ (pullback.fst f f ≫ f))
          (GoodReductionJacobian.schemeHomOverComp (Θ ≫ sliceAt f x) rfl ⟨pullback.fst f f, rfl⟩)
          (GoodReductionJacobian.schemeHomOverComp (Θ ≫ sliceAt f x) rfl
            ⟨pullback.snd f f, pullback.condition.symm⟩)).1 := by
      rw [← L.mul_natural]
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, addMor]
    rw [lhs, rhs]
    apply mul_coe_congr L
    · simp only [sliceAt, Θ, Category.assoc, pullback.lift_fst_assoc]
      rw [hg.w]
    · simpa only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] using E2
    · simpa only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] using E3
  have Φ : (Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback g).obj 𝓛)) ≅
      (Scheme.Modules.pullback Θ).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) := by
    refine pullbackTensor₃ _ _ _ _ ≪≫ ?_ ≪≫
      ((Scheme.Modules.pullback Θ).mapIso (pullbackTensor₃ _ _ _ _) ≪≫ pullbackTensor₃ _ _ _ _).symm
    refine tensorIso ?_ (tensorIso ?_ ?_)
    · exact pbComp _ _ _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullbackCongr E1).app 𝓛 ≪≫
        (pbComp _ _ _).symm ≪≫ (pbComp _ _ _).symm
    · exact (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso edual.symm) ≪≫
        pbComp _ _ _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullbackCongr E2).app _ ≪≫
        (pbComp _ _ _).symm ≪≫ (pbComp _ _ _).symm
    · exact (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso edual.symm) ≪≫
        pbComp _ _ _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullbackCongr E3).app _ ≪≫
        (pbComp _ _ _).symm ≪≫ (pbComp _ _ _).symm

  have h1 := locIsoOnBase_unit_pullback_base (pullback.snd f t) (pullback.snd f' t') π Θ hΘ _ hloc
  have h2 : LocIsoOnBase (pullback.snd f' t')
      ((Scheme.Modules.pullback (sliceAt f' x')).obj (mumfordBundle f' L' ((Scheme.Modules.pullback g).obj 𝓛)))
      (𝟙_ _) :=
    locIsoOnBase_unit_of_iso _ Φ.symm h1

  have hxe' : x' = L'.one t' := h (R ⊗[k] k') t' x' h2
  have hone : (L'.one t').1 ≫ g = (L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))).1 := by
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
    let F : SchemeHomOver t' f' →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) f :=
      MonoidHom.mk' (fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩)
        (fun a b => Subtype.ext (hg_mul t' a b))
    exact congrArg Subtype.val (map_one F)

  have key : π ≫ x.1 = π ≫ (L.one t).1 := by
    calc π ≫ x.1 = x'.1 ≫ g := hx'g.symm
      _ = (L'.one t').1 ≫ g := by rw [hxe']
      _ = (L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))).1 := hone
      _ = (L.one (π ≫ t)).1 := by rw [hsq]
      _ = π ≫ (L.one t).1 := by
          rw [← L.one_natural t (π ≫ t) π rfl, GoodReductionJacobian.schemeHomOverComp_coe]
  exact Subtype.ext ((cancel_epi π).mp key)

end S_AlgebraicGeometry_Polarisation_kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_kernelTrivial_pullback_of_isPullback_of_field (solution)
