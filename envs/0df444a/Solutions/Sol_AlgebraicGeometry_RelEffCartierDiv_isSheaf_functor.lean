-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.isSheaf_functor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a62b32ad-296e-5305-a661-9f88b4affdb3

import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Cover.Open
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.zariskiTopology Scheme.IdealSheafData.comap_comp Scheme.Hom IsFinite Scheme.exists_preimage_of_isPullback IsZariskiLocalAtTarget Scheme IsOpenImmersion Scheme.OpenCover Scheme.Cover.pullbackHom Flat Scheme.Hom.finrank_of_isPullback IsZariskiLocalAtTarget.iff_of_openCover Scheme.exists_cover_of_mem_pretopology Scheme.Cover.mkOfCovers Scheme.Cover.hom_ext LocallyOfFinitePresentation Scheme.IdealSheafData.comapIso_hom_fst Scheme.IdealSheafData Scheme.Cover RelEffCartierDiv.functor RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd isPullback_mapOnProdOver RelEffCartierDiv.I Scheme.IdealSheafData.exists_comap_eq_of_openCover Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "pullbackAlong_heq functor functor_map_apply ext pullbackAlong I mk flat isFinite finrank_eq locallyOfFinitePresentation"
namespace SheafProof
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

noncomputable def prodCover {T : Scheme.{u}} (g : T ⟶ S) (𝒰 : T.OpenCover) (gi : ∀ i, 𝒰.X i ⟶ S)
    (hgi : ∀ i, 𝒰.f i ≫ g = gi i) : (pullback f g).OpenCover :=
  Scheme.Cover.mkOfCovers 𝒰.I₀ (fun i => pullback f (gi i))
    (fun i => mapOnProdOver f (𝒰.f i) (hgi i))
    (fun z => by
      obtain ⟨y, hy⟩ := 𝒰.covers (pullback.snd f g z)
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
        (isPullback_mapOnProdOver f (𝒰.f _) (hgi _)) z y hy.symm
      exact ⟨_, w, hw⟩)
    (fun i => MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_mapOnProdOver f (𝒰.f i) (hgi i)).flip inferInstance)

@[scoped simp] lemma prodCover_f {T : Scheme.{u}} (g : T ⟶ S) (𝒰 : T.OpenCover) (gi : ∀ i, 𝒰.X i ⟶ S)
    (hgi : ∀ i, 𝒰.f i ≫ g = gi i) (i : 𝒰.I₀) :
    (prodCover f g 𝒰 gi hgi).f i = mapOnProdOver f (𝒰.f i) (hgi i) := rfl

set_option backward.isDefEq.respectTransparency false in
open _root_.CategoryTheory.Presieve in
theorem isSheaf : Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro T R hR x hx
  obtain ⟨(𝒰 : Scheme.OpenCover T), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hR

  let gi : ∀ i, 𝒰.X i ⟶ S := fun i => (x (𝒰.f i) (.mk i)).1
  let Di : ∀ i, RelEffCartierDiv f r (gi i) := fun i => (x (𝒰.f i) (.mk i)).2

  have hcompat : ∀ {i j : 𝒰.I₀} {V : Scheme.{u}} (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j)
      (hab : a ≫ 𝒰.f i = b ≫ 𝒰.f j),
      (RelEffCartierDiv.functor f r).map a.op (x (𝒰.f i) (.mk i)) =
        (RelEffCartierDiv.functor f r).map b.op (x (𝒰.f j) (.mk j)) :=
    fun a b hab => hx a b (.mk _) (.mk _) hab

  have hgcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ gi i = pullback.snd _ _ ≫ gi j := by
    intro i j
    have := congrArg Sigma.fst (hcompat (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd _ _)
      pullback.condition)
    simpa [functor_map_apply] using this
  let g : T ⟶ S := 𝒰.glueMorphisms gi hgcompat
  have hgi : ∀ i, 𝒰.f i ≫ g = gi i := fun i => 𝒰.ι_glueMorphisms gi hgcompat i

  let 𝒱 := prodCover f g 𝒰 gi hgi
  have hIcompat : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒱.X i) (b : V ⟶ 𝒱.X j),
      a ≫ 𝒱.f i = b ≫ 𝒱.f j → (Di i).I.comap a = (Di j).I.comap b := by
    intro i j V a b hab
    let gi' : V ⟶ 𝒰.X i := a ≫ pullback.snd f (gi i)
    let gj' : V ⟶ 𝒰.X j := b ≫ pullback.snd f (gi j)
    have hab' : gi' ≫ 𝒰.f i = gj' ≫ 𝒰.f j := by
      have := congrArg (· ≫ pullback.snd f g) hab
      simpa [𝒱, gi', gj', mapOnProdOver_snd] using this
    have hc := hcompat gi' gj' hab'
    rw [functor_map_apply, functor_map_apply] at hc
    have hk : gi' ≫ gi i = gj' ≫ gi j := congrArg Sigma.fst hc
    have hIk : ((Di i).pullbackAlong gi' hk).I = ((Di j).pullbackAlong gj' rfl).I := by
      have h2 := (Sigma.ext_iff.mp hc).2
      exact congrArg RelEffCartierDiv.I
        (eq_of_heq (((Di i).pullbackAlong_heq gi' hk rfl).trans h2))

    have hfst : a ≫ pullback.fst f (gi i) = b ≫ pullback.fst f (gi j) := by
      have := congrArg (· ≫ pullback.fst f g) hab
      simpa [𝒱, mapOnProdOver_fst] using this
    let γ : V ⟶ pullback f (gj' ≫ gi j) := pullback.lift (a ≫ pullback.fst f (gi i)) (𝟙 V)
      (by rw [Category.assoc, pullback.condition, Category.id_comp, ← Category.assoc]; exact hk)
    have ha : a = γ ≫ mapOnProdOver f gi' hk := by
      apply pullback.hom_ext
      · simp [γ, mapOnProdOver_fst]; try erw [Category.id_comp]
      · simp [γ, gi', mapOnProdOver_snd]; try erw [Category.id_comp]
    have hb : b = γ ≫ mapOnProdOver f gj' rfl := by
      apply pullback.hom_ext
      · simp [γ, mapOnProdOver_fst, hfst]; try erw [Category.id_comp]
      · simp [γ, gj', mapOnProdOver_snd]; try erw [Category.id_comp]
    rw [ha, hb, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    change ((Di i).pullbackAlong gi' hk).I.comap γ = ((Di j).pullbackAlong gj' rfl).I.comap γ
    rw [hIk]
  obtain ⟨I₀, hI₀⟩ := Scheme.IdealSheafData.exists_comap_eq_of_openCover 𝒱 (fun i => (Di i).I) hIcompat

  let q := I₀.subschemeι ≫ pullback.snd f g
  have Hsq : ∀ i, ∃ (t : (Di i).I.subscheme ⟶ I₀.subscheme),
      IsPullback t ((Di i).I.subschemeι ≫ pullback.snd f (gi i)) q (𝒰.f i) := by
    intro i
    rw [← hI₀ i]
    refine ⟨(I₀.comapIso (𝒱.f i)).hom ≫ pullback.snd _ _, ?_⟩
    have A : IsPullback ((I₀.comap (𝒱.f i)).subschemeι)
        ((I₀.comapIso (𝒱.f i)).hom ≫ pullback.snd _ _) (𝒱.f i) I₀.subschemeι := by
      refine IsPullback.of_iso (IsPullback.of_hasPullback (𝒱.f i) I₀.subschemeι)
        (I₀.comapIso (𝒱.f i)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp [← Scheme.IdealSheafData.comapIso_hom_fst]
      · rw [Iso.symm_hom, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
      · simp
      · simp
    exact A.flip.paste_vert (isPullback_mapOnProdOver f (𝒰.f i) (hgi i))

  have hfin : IsFinite q := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) 𝒰]
    intro i
    obtain ⟨t, Hi⟩ := Hsq i
    have := (Di i).isFinite
    dsimp [Scheme.Cover.pullbackHom]
    rw [← Hi.isoPullback_inv_snd]
    infer_instance
  have hflat : Flat q := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) 𝒰]
    intro i
    obtain ⟨t, Hi⟩ := Hsq i
    have := (Di i).flat
    dsimp [Scheme.Cover.pullbackHom]
    rw [← Hi.isoPullback_inv_snd]
    infer_instance
  have hlfp : LocallyOfFinitePresentation q := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFinitePresentation) 𝒰]
    intro i
    obtain ⟨t, Hi⟩ := Hsq i
    have := (Di i).locallyOfFinitePresentation
    dsimp [Scheme.Cover.pullbackHom]
    rw [← Hi.isoPullback_inv_snd]
    infer_instance
  have hrank : ∀ t : T, q.finrank t = r := by
    intro t
    obtain ⟨y, hy⟩ := 𝒰.covers t
    obtain ⟨tm, Hi⟩ := Hsq (𝒰.idx t)
    have := (Di (𝒰.idx t)).isFinite
    have := (Di (𝒰.idx t)).flat
    rw [← hy, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ Hi y]
    exact (Di _).finrank_eq y
  let D : RelEffCartierDiv f r g := ⟨I₀, hfin, hflat, hlfp, hrank⟩
  have hDi : ∀ i, D.pullbackAlong (𝒰.f i) (hgi i) = Di i := fun i =>
    RelEffCartierDiv.ext (hI₀ i)

  refine ⟨⟨g, D⟩, ?_, ?_⟩
  · rintro Y _ ⟨i⟩
    rw [functor_map_apply]
    change (⟨𝒰.f i ≫ g, D.pullbackAlong (𝒰.f i) rfl⟩ : Σ g, RelEffCartierDiv f r g) = ⟨gi i, Di i⟩
    exact Sigma.ext (hgi i)
      ((D.pullbackAlong_heq (𝒰.f i) rfl (hgi i)).trans (heq_of_eq (hDi i)))
  · rintro ⟨g', D'⟩ hA
    have hA' : ∀ i, (⟨𝒰.f i ≫ g', D'.pullbackAlong (𝒰.f i) rfl⟩ : Σ g, RelEffCartierDiv f r g) =
        ⟨gi i, Di i⟩ := fun i => by
      have := hA (𝒰.f i) (.mk i)
      rwa [functor_map_apply] at this
    have hg' : g' = g := Scheme.Cover.hom_ext 𝒰 _ _ fun i =>
      (congrArg Sigma.fst (hA' i)).trans (hgi i).symm
    subst hg'
    congr 1
    apply RelEffCartierDiv.ext
    apply Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq 𝒱
    intro i
    have h2 := (Sigma.ext_iff.mp (hA' i)).2
    have hD'i : D'.pullbackAlong (𝒰.f i) (hgi i) = Di i :=
      eq_of_heq ((D'.pullbackAlong_heq (𝒰.f i) (hgi i) rfl).trans h2)
    exact (congrArg RelEffCartierDiv.I hD'i).trans (congrArg RelEffCartierDiv.I (hDi i)).symm

end AlgebraicGeometry.RelEffCartierDiv.SheafProof
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry.RelEffCartierDiv P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry.RelEffCartierDiv.SheafProof"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry.RelEffCartierDiv"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.AlgebraicGeometry"

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) :=
  AlgebraicGeometry.RelEffCartierDiv.SheafProof.isSheaf f r

end S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor (solution)
