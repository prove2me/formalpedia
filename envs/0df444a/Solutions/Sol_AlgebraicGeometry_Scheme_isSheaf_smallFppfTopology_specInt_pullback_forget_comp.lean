-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_specInt_pullback_forget_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/585f14be-0899-5ba3-a775-5adc9800514d

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp

set_option autoImplicit false

p2m_open "CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme"

namespace BCSheaf

universe w u

variable {S T : Scheme.{u}} (ι : T ⟶ S)

theorem map_map {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (t : P.obj (op Z)) :
    P.map a.op (P.map b.op t) = P.map (a ≫ b).op t := by
  simp only [op_comp, Functor.map_comp, types_comp_apply]

noncomputable def objOf {Y : Scheme.{u}} (a : Y ⟶ S) (ha : fppfProperty a) : S.Fppf :=
  MorphismProperty.Over.mk ⊤ a ha

noncomputable def homOf {Y : Scheme.{u}} {a : Y ⟶ S} {ha : fppfProperty a} (Z : S.Fppf)
    (k : Y ⟶ Z.left) (w : k ≫ Z.hom = a) : objOf a ha ⟶ Z :=
  MorphismProperty.Over.homMk k w trivial

noncomputable abbrev bc : S.Fppf ⥤ Scheme.{u} :=
  Scheme.Fppf.forget S ⋙ Over.pullback ι ⋙ Over.forget T

@[reassoc]
theorem bc_map_fst {V U : S.Fppf} (k : V ⟶ U) :
    (bc ι).map k ≫ pullback.fst U.hom ι = pullback.fst V.hom ι ≫ k.left := by
  dsimp [Over.pullback, Scheme.Fppf.forget]
  try erw [pullback.lift_fst]
  try rfl

@[reassoc]
theorem bc_map_snd {V U : S.Fppf} (k : V ⟶ U) :
    (bc ι).map k ≫ pullback.snd U.hom ι = pullback.snd V.hom ι := by
  dsimp [Over.pullback, Scheme.Fppf.forget]
  try erw [pullback.lift_snd]
  try rfl

theorem isPullback_bc_map {V U : S.Fppf} (k : V ⟶ U) :
    IsPullback ((bc ι).map k) (pullback.fst V.hom ι) (pullback.fst U.hom ι) k.left := by
  have big : IsPullback (pullback.snd V.hom ι) (pullback.fst V.hom ι) ι V.hom :=
    (IsPullback.of_hasPullback V.hom ι).flip
  have right : IsPullback (pullback.snd U.hom ι) (pullback.fst U.hom ι) ι U.hom :=
    (IsPullback.of_hasPullback U.hom ι).flip
  have hw : k.left ≫ U.hom = V.hom := MorphismProperty.Over.w k
  have big' : IsPullback ((bc ι).map k ≫ pullback.snd U.hom ι) (pullback.fst V.hom ι) ι
      (k.left ≫ U.hom) := by
    rw [bc_map_snd, hw]
    exact big
  exact IsPullback.of_right big' (bc_map_fst ι k) right

theorem fppfProperty_bc_map {V U : S.Fppf} (k : V ⟶ U) (hk : fppfProperty k.left) :
    fppfProperty ((bc ι).map k) :=
  fppfProperty.of_isPullback (isPullback_bc_map ι k).flip hk

section Cover

variable (U : S.Fppf) (𝒰 : Cover.{u} (precoverage fppfProperty) U.left)

noncomputable def coverObj (i : 𝒰.I₀) : S.Fppf :=
  objOf (𝒰.f i ≫ U.hom) (fppfProperty.comp_mem _ _ (𝒰.map_prop i) U.prop)

noncomputable def coverHom (i : 𝒰.I₀) : coverObj U 𝒰 i ⟶ U := homOf U (𝒰.f i) rfl

theorem coverHom_left (i : 𝒰.I₀) : (coverHom U 𝒰 i).left = 𝒰.f i := rfl

noncomputable def bcCover : Cover.{u} (precoverage fppfProperty) ((bc ι).obj U) :=
  Cover.mkOfCovers 𝒰.I₀ (fun i => (bc ι).obj (coverObj U 𝒰 i))
    (fun i => (bc ι).map (coverHom U 𝒰 i))
    (by
      intro z
      obtain ⟨i, v, hv⟩ := 𝒰.exists_eq ((pullback.fst U.hom ι) z)
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback
        (isPullback_bc_map ι (coverHom U 𝒰 i)) z v (by rw [coverHom_left]; exact hv.symm)
      exact ⟨i, y, hy⟩)
    (fun i => fppfProperty_bc_map ι (coverHom U 𝒰 i) (𝒰.map_prop i))

noncomputable def overlapObj (i j : 𝒰.I₀) : S.Fppf :=
  objOf (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ U.hom)
    (fppfProperty.comp_mem _ _ (fppfProperty.pullback_fst _ _ (𝒰.map_prop j))
      (fppfProperty.comp_mem _ _ (𝒰.map_prop i) U.prop))

noncomputable def overlapFst (i j : 𝒰.I₀) : overlapObj U 𝒰 i j ⟶ coverObj U 𝒰 i :=
  homOf _ (pullback.fst (𝒰.f i) (𝒰.f j)) rfl

noncomputable def overlapSnd (i j : 𝒰.I₀) : overlapObj U 𝒰 i j ⟶ coverObj U 𝒰 j :=
  homOf _ (pullback.snd (𝒰.f i) (𝒰.f j))
    (by
      change pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j ≫ U.hom = pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ U.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc])

theorem overlapFst_left (i j : 𝒰.I₀) : (overlapFst U 𝒰 i j).left = pullback.fst (𝒰.f i) (𝒰.f j) := rfl
theorem overlapSnd_left (i j : 𝒰.I₀) : (overlapSnd U 𝒰 i j).left = pullback.snd (𝒰.f i) (𝒰.f j) := rfl

theorem overlap_condition (i j : 𝒰.I₀) :
    overlapFst U 𝒰 i j ≫ coverHom U 𝒰 i = overlapSnd U 𝒰 i j ≫ coverHom U 𝒰 j := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

theorem isPullback_bc_overlap (i j : 𝒰.I₀) :
    IsPullback ((bc ι).map (overlapFst U 𝒰 i j)) ((bc ι).map (overlapSnd U 𝒰 i j))
      ((bc ι).map (coverHom U 𝒰 i)) ((bc ι).map (coverHom U 𝒰 j)) := by

  have t : IsPullback (pullback.fst (coverObj U 𝒰 i).hom ι) ((bc ι).map (coverHom U 𝒰 i))
      (𝒰.f i) (pullback.fst U.hom ι) := (isPullback_bc_map ι (coverHom U 𝒰 i)).flip

  have s₁ : IsPullback (pullback.fst (overlapObj U 𝒰 i j).hom ι) ((bc ι).map (overlapSnd U 𝒰 i j))
      (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.fst (coverObj U 𝒰 j).hom ι) :=
    (isPullback_bc_map ι (overlapSnd U 𝒰 i j)).flip
  have s₂ : IsPullback (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (𝒰.f i) (𝒰.f j) := IsPullback.of_hasPullback _ _
  have s := s₁.paste_horiz s₂
  have e1 : pullback.fst (overlapObj U 𝒰 i j).hom ι ≫ pullback.fst (𝒰.f i) (𝒰.f j) =
      (bc ι).map (overlapFst U 𝒰 i j) ≫ pullback.fst (coverObj U 𝒰 i).hom ι :=
    (bc_map_fst ι (overlapFst U 𝒰 i j)).symm
  have e2 : pullback.fst (coverObj U 𝒰 j).hom ι ≫ 𝒰.f j =
      (bc ι).map (coverHom U 𝒰 j) ≫ pullback.fst U.hom ι :=
    (bc_map_fst ι (coverHom U 𝒰 j)).symm
  rw [e1] at s
  have p : (bc ι).map (overlapFst U 𝒰 i j) ≫ (bc ι).map (coverHom U 𝒰 i) =
      (bc ι).map (overlapSnd U 𝒰 i j) ≫ (bc ι).map (coverHom U 𝒰 j) := by
    rw [← Functor.map_comp, ← Functor.map_comp, overlap_condition]
  refine IsPullback.of_right ?_ p t
  exact e2 ▸ s

end Cover

theorem isSheaf_bc_comp (P : Scheme.{u}ᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf Scheme.fppfTopology P) :
    Presieve.IsSheaf (smallFppfTopology S) ((bc ι).op ⋙ P) := by
  intro U R hR x hx

  have hR₁ : Sieve.overEquiv ((Scheme.Fppf.forget S).obj U)
      (R.functorPushforward (Scheme.Fppf.forget S)) ∈
        Scheme.grothendieckTopology fppfProperty U.left := by
    rw [smallFppfTopology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff,
      GrothendieckTopology.mem_over_iff] at hR
    exact hR
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (X := U.left)).mp hR₁

  have hmem : ∀ i, (R.functorPushforward (Scheme.Fppf.forget S)).arrows (Over.homMk (𝒰.f i) :
      Over.mk (𝒰.f i ≫ ((Scheme.Fppf.forget S).obj U).hom) ⟶ (Scheme.Fppf.forget S).obj U) :=
    fun i => (Sieve.overEquiv_iff _ _).mp (h𝒰 _ _ (Presieve.ofArrows.mk i))
  let σ := fun i => Presieve.getFunctorPushforwardStructure (hmem i)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ∀ i, 𝒰.X i ⟶ (σ i).preobj.left, ∀ i, ℓ i = (σ i).lift.left :=
    ⟨fun i => (σ i).lift.left, fun _ => rfl⟩
  have hfac : ∀ i, 𝒰.f i = ℓ i ≫ (σ i).premap.left := fun i => by
    rw [hℓ]; exact congrArg CommaMorphism.left (σ i).fac
  have hw : ∀ i, ℓ i ≫ (σ i).preobj.hom = 𝒰.f i ≫ U.hom := fun i => by
    rw [hℓ]; exact Over.w (σ i).lift

  let ℓ' : ∀ i, coverObj U 𝒰 i ⟶ (σ i).preobj := fun i => homOf _ (ℓ i) (hw i)
  have hfac' : ∀ i, ℓ' i ≫ (σ i).premap = coverHom U 𝒰 i := fun i => by
    apply MorphismProperty.Over.Hom.ext
    exact (hfac i).symm

  let y : ∀ i, P.obj (op ((bc ι).obj (coverObj U 𝒰 i))) :=
    fun i => P.map ((bc ι).map (ℓ' i)).op (x (σ i).premap (σ i).cover)
  have hsheaf : Presieve.IsSheafFor P (Presieve.ofArrows (bcCover ι U 𝒰).X (bcCover ι U 𝒰).f) :=
    hP.isSheafFor _ (Scheme.Cover.mem_grothendieckTopology (bcCover ι U 𝒰))
  have hcompat : Presieve.Arrows.PullbackCompatible (P := P) (π := (bcCover ι U 𝒰).f) y := by
    intro i j
    have hθ := isPullback_bc_overlap ι U 𝒰 i j
    have comm : (overlapFst U 𝒰 i j ≫ ℓ' i) ≫ (σ i).premap =
        (overlapSnd U 𝒰 i j ≫ ℓ' j) ≫ (σ j).premap := by
      rw [Category.assoc, Category.assoc, hfac', hfac', overlap_condition]
    have hxo := hx (overlapFst U 𝒰 i j ≫ ℓ' i) (overlapSnd U 𝒰 i j ≫ ℓ' j)
      (σ i).cover (σ j).cover comm

    have hxo' : P.map ((bc ι).map (overlapFst U 𝒰 i j)).op (y i) =
        P.map ((bc ι).map (overlapSnd U 𝒰 i j)).op (y j) := by
      simp only [y, map_map, ← Functor.map_comp]
      exact hxo
    change P.map (pullback.fst ((bcCover ι U 𝒰).f i) ((bcCover ι U 𝒰).f j)).op (y i) =
      P.map (pullback.snd ((bcCover ι U 𝒰).f i) ((bcCover ι U 𝒰).f j)).op (y j)
    have e₁ : pullback.fst ((bcCover ι U 𝒰).f i) ((bcCover ι U 𝒰).f j) =
        hθ.isoPullback.inv ≫ (bc ι).map (overlapFst U 𝒰 i j) := (hθ.isoPullback_inv_fst).symm
    have e₂ : pullback.snd ((bcCover ι U 𝒰).f i) ((bcCover ι U 𝒰).f j) =
        hθ.isoPullback.inv ≫ (bc ι).map (overlapSnd U 𝒰 i j) := (hθ.isoPullback_inv_snd).symm
    rw [e₁, e₂]
    calc P.map (hθ.isoPullback.inv ≫ (bc ι).map (overlapFst U 𝒰 i j)).op (y i)
        = P.map hθ.isoPullback.inv.op (P.map ((bc ι).map (overlapFst U 𝒰 i j)).op (y i)) :=
          (map_map P _ _ _).symm
      _ = P.map hθ.isoPullback.inv.op (P.map ((bc ι).map (overlapSnd U 𝒰 i j)).op (y j)) := by
          rw [hxo']
      _ = P.map (hθ.isoPullback.inv ≫ (bc ι).map (overlapSnd U 𝒰 i j)).op (y j) :=
          map_map P _ _ _
  obtain ⟨t, ht, huniq⟩ :=
    (Presieve.isSheafFor_arrows_iff_pullbacks (P := P) (π := (bcCover ι U 𝒰).f)).mp hsheaf _ hcompat
  have ht' : ∀ i, P.map ((bc ι).map (coverHom U 𝒰 i)).op t = y i := fun i => ht i
  refine ⟨t, ?_, ?_⟩
  ·
    intro V f hf
    change P.map ((bc ι).map f).op t = x f hf
    let 𝒱 := 𝒰.pullback₁ f.left
    have hsep : Presieve.IsSeparatedFor P
        (Presieve.ofArrows (bcCover ι V 𝒱).X (bcCover ι V 𝒱).f) :=
      (hP.isSheafFor _ (Scheme.Cover.mem_grothendieckTopology (bcCover ι V 𝒱))).isSeparatedFor
    refine hsep.ext ?_
    rintro _ _ ⟨i⟩
    change P.map ((bc ι).map (coverHom V 𝒱 i)).op (P.map ((bc ι).map f).op t) =
      P.map ((bc ι).map (coverHom V 𝒱 i)).op (x f hf)

    let k₂ : coverObj V 𝒱 i ⟶ coverObj U 𝒰 i := homOf _ (pullback.snd f.left (𝒰.f i))
      (by
        change pullback.snd f.left (𝒰.f i) ≫ 𝒰.f i ≫ U.hom = pullback.fst f.left (𝒰.f i) ≫ V.hom
        rw [← Category.assoc, ← pullback.condition, Category.assoc, MorphismProperty.Over.w f])
    have comm₁ : coverHom V 𝒱 i ≫ f = k₂ ≫ coverHom U 𝒰 i := by
      apply MorphismProperty.Over.Hom.ext
      exact pullback.condition
    have comm₂ : coverHom V 𝒱 i ≫ f = (k₂ ≫ ℓ' i) ≫ (σ i).premap := by
      rw [Category.assoc, hfac', comm₁]
    calc P.map ((bc ι).map (coverHom V 𝒱 i)).op (P.map ((bc ι).map f).op t)
        = P.map ((bc ι).map (coverHom V 𝒱 i ≫ f)).op t := by rw [map_map, ← Functor.map_comp]
      _ = P.map ((bc ι).map (k₂ ≫ coverHom U 𝒰 i)).op t := by rw [comm₁]
      _ = P.map ((bc ι).map k₂).op (P.map ((bc ι).map (coverHom U 𝒰 i)).op t) := by
          rw [Functor.map_comp, ← map_map]
      _ = P.map ((bc ι).map k₂).op (y i) := by rw [ht' i]
      _ = P.map ((bc ι).map (k₂ ≫ ℓ' i)).op (x (σ i).premap (σ i).cover) := by
          simp only [y, map_map, ← Functor.map_comp]
      _ = P.map ((bc ι).map (coverHom V 𝒱 i)).op (x f hf) :=
          (hx (coverHom V 𝒱 i) (k₂ ≫ ℓ' i) hf (σ i).cover comm₂).symm
  ·
    intro t' ht'
    apply huniq
    intro i
    have h : P.map ((bc ι).map (σ i).premap).op t' = x (σ i).premap (σ i).cover :=
      ht' (σ i).premap (σ i).cover
    change P.map ((bc ι).map (coverHom U 𝒰 i)).op t' = y i
    rw [← hfac' i, Functor.map_comp, ← map_map, h]

end BCSheaf

theorem solution
    {T : Scheme.{0}} (ι : T ⟶ specInt)
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    Presheaf.IsSheaf (smallFppfTopology specInt)
      ((Scheme.Fppf.forget specInt ⋙ Over.pullback ι ⋙ Over.forget T).op ⋙ X.obj) := by
  intro E
  exact BCSheaf.isSheaf_bc_comp ι (X.obj ⋙ coyoneda.obj (op E)) (X.property E)

end S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp (solution)
