-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitSheaf
-- name    : AlgebraicGeometry_EtaleAffineLimitSheaf
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T04:55:57.911614+00:00
-- url     : https://prove2.me/theorems/9f9c2bb6-c66c-488d-8ae1-99e7fc6f3abb
-- title:
--   The limit sheaf of a compatible system on affine schemes
-- statement:
--   On an affine étale chart of the inverse limit, sections are computed as a filtered colimit over models of the chart. These sections satisfy gluing and extend to an abelian sheaf on the entire small étale site.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineStageSystems
import Definitions.Def_AlgebraicGeometry_EtaleModeledCech
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleModeledSections

universe u

private def overChartMap {S X' V' W' : Scheme.{u}} (r : X' ⟶ S)
    (v' : V' ⟶ S) (w' : W' ⟶ S) (a : V' ⟶ W') (ha : a ≫ w' = v') :
    pullback r v' ⟶ pullback r w' :=
  pullback.lift (pullback.fst r v') (pullback.snd r v' ≫ a)
    (by rw [Category.assoc, ha, pullback.condition])

private theorem overChartMap_comm {S X₀ X₁ V' W' : Scheme.{u}}
    {r₀ : X₀ ⟶ S} {r₁ : X₁ ⟶ S} (v' : V' ⟶ S) (w' : W' ⟶ S)
    (a : V' ⟶ W') (ha : a ≫ w' = v') (d : X₀ ⟶ X₁)
    (mV : pullback r₀ v' ⟶ pullback r₁ v') (mW : pullback r₀ w' ⟶ pullback r₁ w')
    (hv₁ : mV ≫ pullback.fst r₁ v' = pullback.fst r₀ v' ≫ d)
    (hv₂ : mV ≫ pullback.snd r₁ v' = pullback.snd r₀ v')
    (hw₁ : mW ≫ pullback.fst r₁ w' = pullback.fst r₀ w' ≫ d)
    (hw₂ : mW ≫ pullback.snd r₁ w' = pullback.snd r₀ w') :
    mV ≫ overChartMap r₁ v' w' a ha = overChartMap r₀ v' w' a ha ≫ mW := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hw₁, overChartMap, overChartMap,
      pullback.lift_fst, pullback.lift_fst_assoc, hv₁]
  · rw [Category.assoc, Category.assoc, hw₂, overChartMap, overChartMap,
      pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hv₂]

private theorem overChartMap_id {S X' V' : Scheme.{u}} (r : X' ⟶ S) (v' : V' ⟶ S) :
    overChartMap r v' v' (𝟙 _) (Category.id_comp _) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [overChartMap]

private theorem overChartMap_comp {S X' U' V' W' : Scheme.{u}} (r : X' ⟶ S)
    (u' : U' ⟶ S) (v' : V' ⟶ S) (w' : W' ⟶ S)
    (a : U' ⟶ V') (b : V' ⟶ W') (ha : a ≫ v' = u') (hb : b ≫ w' = v') :
    overChartMap r u' w' (a ≫ b) (by rw [Category.assoc, hb, ha]) =
      overChartMap r u' v' a ha ≫ overChartMap r v' w' b hb := by
  apply pullback.hom_ext <;> simp [overChartMap, Category.assoc]

private theorem overChartMap_paste {Q S A B T W : Scheme.{u}}
    {m : Q ⟶ S} {b : B ⟶ Q} {t : B ⟶ T} {v : T ⟶ S}
    {a : A ⟶ B} {g : A ⟶ W} {w : W ⟶ T}
    (h : IsPullback a g t w) (k : IsPullback b t m v) :
    (h.paste_horiz k).isoPullback.hom ≫ overChartMap m (w ≫ v) v w rfl =
      a ≫ k.isoPullback.hom := by
  let e := (h.paste_horiz k).isoPullback
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, k.isoPullback_hom_fst]
    change e.hom ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst]
    exact (h.paste_horiz k).isoPullback_hom_fst
  · rw [Category.assoc, Category.assoc, k.isoPullback_hom_snd]
    change e.hom ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, ← Category.assoc, (h.paste_horiz k).isoPullback_hom_snd]
    exact h.w.symm

/-- Étale base change using the base as the first factor of the pullback. -/
def reversedBaseChange {X X' : Scheme.{u}} (r : X' ⟶ X) : X.Etale ⥤ X'.Etale where
  obj U := Scheme.Etale.mk (pullback.fst r U.hom)
  map b := MorphismProperty.Over.homMk (overChartMap r _ _ b.left (MorphismProperty.Over.w b))
    (pullback.lift_fst ..) trivial
  map_id U := MorphismProperty.Over.Hom.ext (overChartMap_id r U.hom)
  map_comp {U V W} a b := MorphismProperty.Over.Hom.ext (overChartMap_comp r
    U.hom V.hom W.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b))

/-- Swapping the factors identifies the two choices of étale base change. -/
def reversedBaseChangeIso {X X' : Scheme.{u}} (r : X' ⟶ X) :
    reversedBaseChange r ≅ baseChange r := by
  refine NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk
    (pullbackSymmetry r U.hom) (pullbackSymmetry_hom_comp_snd ..)) ?_
  intro U V b
  apply MorphismProperty.Over.Hom.ext
  let a := overChartMap r U.hom V.hom b.left (MorphismProperty.Over.w b)
  let d := ((baseChange r).map b).left
  change a ≫ (pullbackSymmetry r V.hom).hom = (pullbackSymmetry r U.hom).hom ≫ d
  have h₁ : d ≫ pullback.fst V.hom r = pullback.fst U.hom r ≫ b.left := pullback.lift_fst ..
  have h₂ : d ≫ pullback.snd V.hom r = pullback.snd U.hom r := pullback.lift_snd ..
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst, h₁,
      pullbackSymmetry_hom_comp_fst_assoc]
    exact pullback.lift_snd ..
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd, h₂,
      pullbackSymmetry_hom_comp_snd]
    exact pullback.lift_fst ..

/-- The comparison from a pasted pullback square commutes with the map
on reversed base changes. -/
theorem reversedBaseChange_paste {Q S A B T W : Scheme.{u}}
    {m : Q ⟶ S} {b : B ⟶ Q} {t : B ⟶ T} {v : T ⟶ S} [Etale v]
    {a : A ⟶ B} {g : A ⟶ W} {w : W ⟶ T} [Etale w]
    (h : IsPullback a g t w) (k : IsPullback b t m v) :
    (h.paste_horiz k).isoPullback.hom ≫
        ((reversedBaseChange m).map (MorphismProperty.Over.homMk
          (A := Scheme.Etale.mk (w ≫ v)) (B := Scheme.Etale.mk v) w rfl trivial)).left =
      a ≫ k.isoPullback.hom :=
  overChartMap_paste h k

end PhilipponEtaleModeledSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleTotalStageSite (StageChart)
open PhilipponEtaleChartLimitDiagram (chartDiagram chartCone chartCone_isLimit chartProjection_fst
  chartProjection_snd stageCharts)
open PhilipponEtaleModeledSections (reversedBaseChange reversedBaseChange_paste)


namespace PhilipponEtaleAffineCoverModel

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D) (A : StageChart D)

private theorem isPullback_chartCone (j : Over A.index) :
    IsPullback (pullback.fst (c.π.app A.index) A.etale.hom) ((chartCone A c).π.app j)
      (c.π.app j.left) (pullback.fst (D.map j.hom) A.etale.hom) := by
  apply IsPullback.of_bot _ (chartProjection_fst A c j).symm (IsPullback.of_hasPullback _ _)
  rw [chartProjection_snd, c.w]
  exact IsPullback.of_hasPullback _ _

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)] [IsAffine A.etale.left] (hc : IsLimit c)

include hc in
/-- Every covering sieve of a pulled-back affine étale chart contains the
pullback of an affine covering family at a common stage. -/
theorem exists_cover_model
    (S : Sieve ((reversedBaseChange (c.π.app A.index)).obj A.etale))
    (hS : S ∈ c.pt.smallEtaleTopology _) :
    ∃ (j : I) (T : (D.obj j).Etale)
      (e : (reversedBaseChange (c.π.app A.index)).obj A.etale ≅
        (reversedBaseChange (c.π.app j)).obj T)
      (β : Type u) (_ : Fintype β) (W : β → (D.obj j).Etale) (a : ∀ l, W l ⟶ T),
      IsAffine T.left ∧ (∀ l, IsAffine (W l).left) ∧
      Sieve.ofArrows W a ∈ (D.obj j).smallEtaleTopology T ∧
      (∀ l, S ((reversedBaseChange (c.π.app j)).map (a l) ≫ e.inv)) ∧
      Sieve.ofArrows _ (fun l => (reversedBaseChange (c.π.app j)).map (a l) ≫ e.inv) ∈
        c.pt.smallEtaleTopology _ := by
  classical
  let V := (reversedBaseChange (c.π.app A.index)).obj A.etale
  let G := chartDiagram A
  let C := chartCone A c
  let (j : Over A.index) : IsAffine (G.obj j) :=
    @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine (D.obj j.left) A.etale.left
      (D.obj A.index) (D.map j.hom) A.etale.hom inferInstance ‹_› inferInstance
  let (j : Over A.index) : CompactSpace (G.obj j) := inferInstance
  let {j k : Over A.index} (f : j ⟶ k) : IsAffineHom (G.map f) := isAffineHom_of_isAffine _
  let f (a : S.arrows.category) : a.obj.left.left ⟶ C.pt := a.obj.hom.left
  let (a : S.arrows.category) : Etale (f a) := inferInstanceAs (Etale a.obj.hom.left)
  have hcov (x : C.pt) : ∃ a, x ∈ Set.range (f a) := by
    rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion] at hS
    exact hS x
  obtain ⟨j, β, hβ, b, R, M, r, m, g, hr, hh, hm⟩ :=
    PhilipponEtaleCoverLimitDescent.exists_refined_cover_model G C (chartCone_isLimit A c hc) f hcov
  let T : (D.obj j.left).Etale := ((stageCharts A).obj j).etale
  let K := reversedBaseChange (c.π.app j.left)
  let k : IsPullback V.hom (C.π.app j) (c.π.app j.left) T.hom := isPullback_chartCone c A j
  let e : V ≅ K.obj T := MorphismProperty.Over.isoMk k.isoPullback k.isoPullback_hom_fst
  let (l : β) : Etale (m l) := (hr l).2.2.2.1
  let W (l : β) : (D.obj j.left).Etale := Scheme.Etale.mk (m l ≫ T.hom)
  let a (l : β) : W l ⟶ T := MorphismProperty.Over.homMk (m l) rfl trivial
  let q (l : β) : R l ⟶ V.left := r l ≫ f (b l)
  let h (l : β) : IsPullback (q l) (g l) (C.π.app j) (m l) := (hr l).2.2.2.2
  let (l : β) : IsOpenImmersion (r l) := (hr l).2.1
  let B (l : β) : c.pt.Etale := Scheme.Etale.mk (q l ≫ V.hom)
  let z (l : β) : B l ⟶ V := MorphismProperty.Over.homMk (q l) rfl trivial
  let ρ (l : β) : B l ≅ K.obj (W l) := MorphismProperty.Over.isoMk
    ((h l).paste_horiz k).isoPullback ((h l).paste_horiz k).isoPullback_hom_fst
  have he (l : β) : (ρ l).hom ≫ K.map (a l) = z l ≫ e.hom :=
    MorphismProperty.Over.Hom.ext (reversedBaseChange_paste (h l) k)
  have hz (l : β) : (ρ l).hom ≫ (K.map (a l) ≫ e.inv) = z l := by
    rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨j.left, T, e, β, hβ, W, a, inferInstanceAs (IsAffine (G.obj j)),
    fun l => (hr l).2.2.1, ?_, ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion]
    exact hm
  · intro l
    let s : B l ⟶ (b l).obj.left := MorphismProperty.Over.homMk (r l) (by
      change r l ≫ (b l).obj.left.hom = (r l ≫ (b l).obj.hom.left) ≫ V.hom
      rw [Category.assoc, MorphismProperty.Over.w]) trivial
    have hl : z l = s ≫ (b l).obj.hom := MorphismProperty.Over.Hom.ext rfl
    rw [← Category.id_comp (K.map (a l) ≫ e.inv), ← (ρ l).inv_hom_id, Category.assoc, hz, hl]
    exact S.downward_closed (S.downward_closed (b l).property s) (ρ l).inv
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun l => K.map (a l) ≫ e.inv)).mpr
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨l, y, hy⟩ := hh x
    exact Set.mem_iUnion.mpr ⟨l, (ρ l).hom.left y,
      (congrArg (fun d : B l ⟶ V => d.left y) (hz l)).trans hy⟩

end PhilipponEtaleAffineCoverModel

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleSystemPresheaf (colimitAt presheaf)
open PhilipponEtaleTotalStageSite (StageChart toLimit)


namespace PhilipponEtaleLimitAffinePresheaf

universe u

/-- The affine objects of the small étale site. -/
def affineCharts (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun U => IsAffine U.left

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D)

/-- A model of a limit chart by an affine étale chart of a stage. -/
structure AffineModel (U : c.pt.Etale) where
  chart : StageChart D
  affine : IsAffine chart.etale.left
  comparison : U ≅ (toLimit c).obj chart

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)] (hc : IsLimit c)

include hc in
theorem exists_affineModel (U : c.pt.Etale) [IsAffine U.left] :
    Nonempty (AffineModel c U) := by
  let : Etale U.hom := inferInstance
  obtain ⟨i, Y, f, g, hY, hf, h⟩ :=
    PhilipponEtaleCoverLimitDescent.exists_affine_model D c hc (Y := U.left) U.hom
  let : Etale f := hf
  let A : StageChart D := ⟨i, Scheme.Etale.mk f⟩
  refine ⟨⟨A, hY, MorphismProperty.Over.isoMk h.flip.isoPullback ?_⟩⟩
  exact h.flip.isoPullback_hom_snd

variable (F : System (directImages D))

/-- Every affine chart of the limit has a pointwise colimit for the family
of coefficient sheaves. -/
def affineColimit (U : (affineCharts c.pt).FullSubcategory) :
    ColimitCocone (CostructuredArrow.proj (toLimit c).op (op U.obj) ⋙ presheaf F) := by
  let : IsAffine U.obj.left := U.property
  let M := (exists_affineModel c hc U.obj).some
  let : IsAffine M.chart.etale.left := M.affine
  let e : CostructuredArrow (toLimit c).op (op U.obj) ≌
      CostructuredArrow (toLimit c).op (op ((toLimit c).obj M.chart)) :=
    CostructuredArrow.mapIso M.comparison.symm.op
  let t := colimitAt F c hc M.chart
  exact ⟨t.cocone.whisker e.functor, t.isColimit.whiskerEquivalence e⟩

/-- The pointwise colimits form a presheaf on the affine étale charts
of the limit. -/
def affinePresheaf : (affineCharts c.pt).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u} :=
  PhilipponRestrictedKan.restrictedColimit (toLimit c).op (presheaf F)
    (affineCharts c.pt).ι.op (fun U => affineColimit c hc F U.unop)

@[reassoc]
theorem affinePresheaf_ι_map {U V : (affineCharts c.pt).FullSubcategory} (s : U ⟶ V)
    (j : CostructuredArrow (toLimit c).op (op V.obj)) :
    (affineColimit c hc F V).cocone.ι.app j ≫ (affinePresheaf c hc F).map s.op =
      (affineColimit c hc F U).cocone.ι.app ((CostructuredArrow.map s.hom.op).obj j) :=
  PhilipponRestrictedKan.ι_map (toLimit c).op (presheaf F)
    (affineCharts c.pt).ι.op (fun T => affineColimit c hc F T.unop) s.op j

end PhilipponEtaleLimitAffinePresheaf

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleTotalStageSite (StageChart StageHom atStage toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts chartMap_fst chartMap_snd chartMap_snd_assoc
  toOriginal toLimitIso toLimitIso_hom)


namespace PhilipponEtaleStageChartNaturality

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {i : I}
  {U V : (D.obj i).Etale}

private abbrev original (U : (D.obj i).Etale) : StageChart D := ⟨i, U⟩

/-- A map of charts at a fixed stage gives a map of their base changes
at every earlier stage. -/
def atEarlierStage (s : U ⟶ V) (j : Over i) :
    (stageCharts (original U)).obj j ⟶ (stageCharts (original V)).obj j :=
  ⟨𝟙 j.left, pullback.lift (pullback.fst (D.map j.hom) U.hom)
    (pullback.snd (D.map j.hom) U.hom ≫ s.left) (by
      change pullback.fst (D.map j.hom) U.hom ≫ D.map j.hom =
        (pullback.snd (D.map j.hom) U.hom ≫ s.left) ≫ V.hom
      rw [Category.assoc, MorphismProperty.Over.w s, pullback.condition]), by
    change pullback.lift _ _ _ ≫ pullback.fst (D.map j.hom) V.hom =
      pullback.fst (D.map j.hom) U.hom ≫ D.map (𝟙 j.left)
    rw [D.map_id, Category.comp_id]
    exact pullback.lift_fst ..⟩

@[reassoc]
theorem earlier_fst (s : U ⟶ V) (j : Over i) :
    (atEarlierStage s j).left ≫ pullback.fst (D.map j.hom) V.hom =
      pullback.fst (D.map j.hom) U.hom :=
  pullback.lift_fst ..

@[reassoc]
theorem earlier_snd (s : U ⟶ V) (j : Over i) :
    (atEarlierStage s j).left ≫ pullback.snd (D.map j.hom) V.hom =
      pullback.snd (D.map j.hom) U.hom ≫ s.left :=
  pullback.lift_snd ..

@[simp]
theorem earlier_id (U : (D.obj i).Etale) (j : Over i) : atEarlierStage (𝟙 U) j = 𝟙 _ := by
  refine StageHom.ext ?_ ?_
  · rfl
  apply pullback.hom_ext
  · change (atEarlierStage (𝟙 U) j).left ≫ pullback.fst (D.map j.hom) U.hom = 𝟙 _ ≫ _
    rw [earlier_fst, Category.id_comp]
  · change (atEarlierStage (𝟙 U) j).left ≫ pullback.snd (D.map j.hom) U.hom = 𝟙 _ ≫ _
    rw [earlier_snd, Category.id_comp]
    exact Category.comp_id _

theorem earlier_comp {W : (D.obj i).Etale} (s : U ⟶ V) (t : V ⟶ W) (j : Over i) :
    atEarlierStage (s ≫ t) j = atEarlierStage s j ≫ atEarlierStage t j := by
  apply StageHom.ext (Category.id_comp _).symm
  apply pullback.hom_ext
  · change (atEarlierStage (s ≫ t) j).left ≫ pullback.fst (D.map j.hom) W.hom =
      (atEarlierStage s j).left ≫ (atEarlierStage t j).left ≫ _
    rw [earlier_fst, earlier_fst, earlier_fst]
  · change (atEarlierStage (s ≫ t) j).left ≫ pullback.snd (D.map j.hom) W.hom =
      (atEarlierStage s j).left ≫ (atEarlierStage t j).left ≫ _
    rw [earlier_snd, earlier_snd, earlier_snd_assoc]
    rfl

/-- All earlier base changes vary naturally with the original chart. -/
def earlierStagesMap (s : U ⟶ V) : stageCharts (original U) ⟶ stageCharts (original V) where
  app j := atEarlierStage s j
  naturality {j k} f := by
    apply StageHom.ext
    · exact (Category.comp_id f.left).trans (Category.id_comp f.left).symm
    · apply pullback.hom_ext
      · change ((stageCharts (original U)).map f).left ≫
          (atEarlierStage s k).left ≫ pullback.fst (D.map k.hom) V.hom =
          (atEarlierStage s j).left ≫ ((stageCharts (original V)).map f).left ≫
            pullback.fst (D.map k.hom) V.hom
        rw [earlier_fst,
          show ((stageCharts (original U)).map f).left ≫ pullback.fst (D.map k.hom) U.hom = _ from
            chartMap_fst (original U) f,
          show ((stageCharts (original V)).map f).left ≫ pullback.fst (D.map k.hom) V.hom = _ from
            chartMap_fst (original V) f,
          earlier_fst_assoc]
      · change ((stageCharts (original U)).map f).left ≫
          (atEarlierStage s k).left ≫ pullback.snd (D.map k.hom) V.hom =
          (atEarlierStage s j).left ≫ ((stageCharts (original V)).map f).left ≫
            pullback.snd (D.map k.hom) V.hom
        rw [earlier_snd,
          show ((stageCharts (original U)).map f).left ≫ pullback.snd (D.map k.hom) U.hom ≫ s.left = _ from
            chartMap_snd_assoc (original U) f _,
          show ((stageCharts (original V)).map f).left ≫ pullback.snd (D.map k.hom) V.hom = _ from
            chartMap_snd (original V) f,
          earlier_snd]

@[reassoc]
theorem earlier_toOriginal (s : U ⟶ V) (j : Over i) :
    atEarlierStage s j ≫ toOriginal (original V) j =
      toOriginal (original U) j ≫ (atStage i).map s := by
  apply StageHom.ext
  · exact (Category.id_comp j.hom).trans (Category.comp_id j.hom).symm
  · exact earlier_snd s j

@[reassoc]
theorem earlier_toLimitIso (c : Cone D) (s : U ⟶ V) (j : Over i) :
    (toLimit c).map (atEarlierStage s j) ≫ (toLimitIso (original V) c j).hom =
      (toLimitIso (original U) c j).hom ≫ (toLimit c).map ((atStage i).map s) := by
  rw [toLimitIso_hom, toLimitIso_hom, ← (toLimit c).map_comp, ← (toLimit c).map_comp,
    earlier_toOriginal]

end PhilipponEtaleStageChartNaturality

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart atStage toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts toLimitIso)
open PhilipponEtaleLimitChartIndex (fromStages fromStages_final)
open PhilipponEtaleStageChartNaturality (atEarlierStage earlierStagesMap earlier_id earlier_comp
  earlier_toLimitIso)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affineColimit affinePresheaf affinePresheaf_ι_map)
open PhilipponEtaleSystemPresheaf (presheaf)


namespace PhilipponEtaleAffineSectionColimit

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}
  (F : System (directImages D)) (i : I)

private abbrev stage (U : (D.obj i).Etale) : StageChart D := ⟨i, U⟩

private def mapStageSections {U V : (D.obj i).Etale} (s : U ⟶ V) :
    (stageCharts (stage i V)).op ⋙ presheaf F ⟶ (stageCharts (stage i U)).op ⋙ presheaf F where
  app j := (presheaf F).map (atEarlierStage s j.unop).op
  naturality {j k} f := by
    change (presheaf F).map ((stageCharts (stage i V)).map f.unop).op ≫
      (presheaf F).map (atEarlierStage s k.unop).op =
      (presheaf F).map (atEarlierStage s j.unop).op ≫
        (presheaf F).map ((stageCharts (stage i U)).map f.unop).op
    rw [← (presheaf F).map_comp, ← (presheaf F).map_comp, ← op_comp, ← op_comp]
    have hw := (earlierStagesMap s).naturality f.unop
    change ((stageCharts (stage i U)).map f.unop) ≫ atEarlierStage s j.unop =
      atEarlierStage s k.unop ≫ ((stageCharts (stage i V)).map f.unop) at hw
    rw [hw]

/-- The section diagrams on all refinements of an étale chart of a
fixed stage. -/
def stageSections : (D.obj i).Etaleᵒᵖ ⥤ (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := (stageCharts (stage i U.unop)).op ⋙ presheaf F
  map s := mapStageSections F i s.unop
  map_id U := by
    apply NatTrans.ext
    funext j
    change (presheaf F).map (atEarlierStage (𝟙 U.unop) j.unop).op = 𝟙 _
    rw [earlier_id, op_id, (presheaf F).map_id]
  map_comp s t := by
    apply NatTrans.ext
    funext j
    change (presheaf F).map (atEarlierStage (t.unop ≫ s.unop) j.unop).op =
      (presheaf F).map (atEarlierStage s.unop j.unop).op ≫
        (presheaf F).map (atEarlierStage t.unop j.unop).op
    rw [earlier_comp, op_comp, (presheaf F).map_comp]

variable [IsCofiltered I] [∀ j, IsAffine (D.obj j)] (c : Cone D) (hc : IsLimit c)

/-- Regard the pullback of an affine chart to the limit as an affine chart. -/
def pullbackAffine : (affineCharts (D.obj i)).FullSubcategory ⥤
    (affineCharts c.pt).FullSubcategory where
  obj U := ⟨(toLimit c).obj (stage i U.obj), by
    let : IsAffine U.obj.left := U.property
    let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
    change IsAffine (pullback U.obj.hom (c.π.app i))
    exact @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine U.obj.left c.pt (D.obj i)
      U.obj.hom (c.π.app i) ‹_› ‹_› inferInstance⟩
  map s := ObjectProperty.homMk ((toLimit c).map ((atStage i).map s.hom))
  map_id U := ObjectProperty.hom_ext _ (by
    change (toLimit c).map (𝟙 (stage i U.obj)) = 𝟙 _
    exact (toLimit c).map_id _)
  map_comp s t := ObjectProperty.hom_ext _ (by simp)

private def stageCocone (U : (affineCharts (D.obj i)).FullSubcategory) :
    Cocone ((stageSections F i).obj (op U.obj)) :=
  (affineColimit c hc F ((pullbackAffine i c hc).obj U)).cocone.whisker
    (fromStages c (stage i U.obj))

private def stageCocone_isColimit (U : (affineCharts (D.obj i)).FullSubcategory) :
    IsColimit (stageCocone F i c hc U) := by
  let : IsAffine (stage i U.obj).etale.left := U.property
  let : (fromStages c (stage i U.obj)).Final := fromStages_final c (stage i U.obj) hc
  exact (Functor.Final.isColimitWhiskerEquiv (fromStages c (stage i U.obj)) _).symm
    (affineColimit c hc F ((pullbackAffine i c hc).obj U)).isColimit

omit [IsCofiltered I] [∀ j, IsAffine (D.obj j)] in
private theorem earlier_inv (U V : (D.obj i).Etale) (s : U ⟶ V) (j : Over i) :
    (toLimitIso (stage i U) c j).inv ≫ (toLimit c).map (atEarlierStage s j) =
      (toLimit c).map ((atStage i).map s) ≫ (toLimitIso (stage i V) c j).inv := by
  apply (cancel_mono (toLimitIso (stage i V) c j).hom).mp
  rw [Category.assoc, earlier_toLimitIso, Iso.inv_hom_id_assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Section colimits over a fixed stage agree naturally with the
restriction of the presheaf on the affine limit charts. -/
def sectionIso : (affineCharts (D.obj i)).ι.op ⋙ stageSections F i ⋙ colim ≅
    (pullbackAffine i c hc).op ⋙ affinePresheaf c hc F := by
  refine NatIso.ofComponents (fun U => (colimit.isColimit _).coconePointUniqueUpToIso
    (stageCocone_isColimit F i c hc U.unop)) ?_
  intro V U f
  let s := f.unop
  let DV := (stageSections F i).obj (op V.unop.obj)
  let DU := (stageSections F i).obj (op U.unop.obj)
  let η := (stageSections F i).map s.hom.op
  let C_V := stageCocone F i c hc V.unop
  let C_U := stageCocone F i c hc U.unop
  let E_V := (colimit.isColimit DV).coconePointUniqueUpToIso
    (stageCocone_isColimit F i c hc V.unop)
  let E_U := (colimit.isColimit DU).coconePointUniqueUpToIso
    (stageCocone_isColimit F i c hc U.unop)
  let P := affinePresheaf c hc F
  let p := (pullbackAffine i c hc).map s
  change colim.map η ≫ E_U.hom = E_V.hom ≫ P.map p.op
  apply colimit.hom_ext
  intro j
  have hV : colimit.ι DV j ≫ E_V.hom = C_V.ι.app j := (colimit.isColimit DV).fac C_V j
  have hU : colimit.ι DU j ≫ E_U.hom = C_U.ι.app j := (colimit.isColimit DU).fac C_U j
  change colimit.ι DV j ≫ colimMap η ≫ E_U.hom = colimit.ι DV j ≫ E_V.hom ≫ P.map p.op
  rw [ι_colimMap_assoc, hU, ← Category.assoc, hV]
  let a := (fromStages c (stage i V.unop.obj)).obj j
  let b := (fromStages c (stage i U.unop.obj)).obj j
  change (presheaf F).map (atEarlierStage s.hom j.unop).op ≫
      (affineColimit c hc F ((pullbackAffine i c hc).obj U.unop)).cocone.ι.app b =
    (affineColimit c hc F ((pullbackAffine i c hc).obj V.unop)).cocone.ι.app a ≫
      P.map p.op
  rw [affinePresheaf_ι_map]
  let m : (CostructuredArrow.map p.hom.op).obj a ⟶ b :=
    CostructuredArrow.homMk (atEarlierStage s.hom j.unop).op
      (Quiver.Hom.unop_inj (earlier_inv i c _ _ s.hom j.unop))
  exact (affineColimit c hc F ((pullbackAffine i c hc).obj U.unop)).cocone.w m

end PhilipponEtaleAffineSectionColimit

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (chart directImages)
open PhilipponEtaleTotalStageSite (atStage)
open PhilipponEtaleStageChartNaturality (atEarlierStage)
open PhilipponEtaleSystemPresheaf (presheaf map_atStage)
open PhilipponEtaleAffineSectionColimit (stageSections pullbackAffine sectionIso)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affinePresheaf)
open PhilipponEtaleModeledSections (reversedBaseChange reversedBaseChangeIso)


namespace PhilipponEtaleStageSectionSheaf

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}
  (F : System (directImages D)) {i : I} (j : Over i)

private def evalIsoReverse :
    stageSections F i ⋙ (evaluation _ _).obj (op j) ≅
      (reversedBaseChange (D.map j.hom)).op ⋙ (F.obj j.left).obj := by
  refine NatIso.ofComponents (fun U => Iso.refl ((F.obj j.left).obj.obj
    (op ((reversedBaseChange (D.map j.hom)).obj U.unop)))) ?_
  intro V U s
  simp only [Iso.refl_hom]
  change (presheaf F).map (atEarlierStage s.unop j).op =
    (F.obj j.left).obj.map (((reversedBaseChange (D.map j.hom)).map s.unop).op)
  exact map_atStage F ((reversedBaseChange (D.map j.hom)).map s.unop)

/-- Evaluating the section diagram at an earlier stage gives the direct image
of that stage's coefficient sheaf. -/
def evalIso :
    stageSections F i ⋙ (evaluation _ _).obj (op j) ≅
      (chart D j.hom).op ⋙ (F.obj j.left).obj :=
  evalIsoReverse F j ≪≫
    Functor.isoWhiskerRight (NatIso.op (reversedBaseChangeIso (D.map j.hom)).symm)
      (F.obj j.left).obj

/-- At each earlier stage the section diagram evaluates to a sheaf on the
fixed stage. -/
theorem isSheaf :
    Presheaf.IsSheaf (D.obj i).smallEtaleTopology
      (stageSections F i ⋙ (evaluation _ _).obj (op j)) := by
  apply (Presheaf.isSheaf_of_iso_iff (evalIso F j)).mpr
  let : (chart D j.hom).IsContinuous (D.obj i).smallEtaleTopology
      (D.obj j.left).smallEtaleTopology :=
    PhilipponEtaleBaseChangeComparison.baseChange_isContinuous (D.map j.hom)
  exact (chart D j.hom).op_comp_isSheaf_of_isSheaf _ _ _ (F.obj j.left).property

/-- The colimits of the section diagrams satisfy gluing for finite
étale hypercovers of a fixed stage. -/
def isLimitMultifork [IsCofiltered I] {U : (D.obj i).Etale}
    (H : (D.obj i).smallEtaleTopology.OneHypercover.{u} U)
    [Fintype H.I₀] [Fintype H.I₁'] :
    IsLimit (H.multifork (stageSections F i ⋙ colim)) :=
  PhilipponFilteredSheafGluing.isLimitMultiforkColim H.toPreOneHypercover _ fun a =>
    H.isLimitMultifork ⟨_, isSheaf F a.unop⟩

/-- The affine limit presheaf satisfies gluing on the pullback of every
finite étale hypercover by affine stage charts. -/
def isLimitPullbackMultifork [IsCofiltered I] [∀ j, IsAffine (D.obj j)]
    (c : Cone D) (hc : IsLimit c) {U : (affineCharts (D.obj i)).FullSubcategory}
    (H : PreOneHypercover.{u} U) [Fintype H.I₀] [Fintype H.I₁']
    (H₀ : (D.obj i).smallEtaleTopology.OneHypercover.{u} U.obj)
    (hH : H.map (affineCharts (D.obj i)).ι = H₀.toPreOneHypercover) :
    IsLimit ((H.map (pullbackAffine i c hc)).multifork (affinePresheaf c hc F)) := by
  let : Fintype H₀.I₀ := by rw [← hH]; exact ‹Fintype H.I₀›
  let : Fintype H₀.I₁' := by rw [← hH]; exact ‹Fintype H.I₁'›
  let G := (affineCharts (D.obj i)).ι
  let R := stageSections F i ⋙ colim
  have h : IsLimit ((H.map G).multifork R) := by
    rw [hH]
    exact isLimitMultifork F H₀
  let t := PhilipponFilteredSheafGluing.isLimitMultiforkOfIso H (sectionIso F i c hc)
    ((H.isLimitMapMultiforkEquiv G R) h)
  exact (H.isLimitMapMultiforkEquiv (pullbackAffine i c hc) (affinePresheaf c hc F)).symm t

end PhilipponEtaleStageSectionSheaf

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleModeledSections PhilipponEtaleModeledGluing
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleRefinementGluing

universe u

/-- Gluing for a hypercover's multifork gives gluing on its generating presieve. -/
theorem isSheafFor_of_multifork {C A : Type*} [Category* C] [Category* A]
    {V U : C} (H : PreOneHypercover.{u} V) (e : U ≅ V) (P : Cᵒᵖ ⥤ A)
    (h : IsLimit (H.multifork P)) (B : Aᵒᵖ) :
    (Presieve.ofArrows H.X (fun i => H.f i ≫ e.inv)).IsSheafFor (P ⋙ coyoneda.obj B) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let N : Multifork (H.multicospanIndex P) := Multifork.ofι _ B.unop x (by
    rintro ⟨⟨i, j⟩, k⟩
    exact hx i j (H.Y k) (H.p₁ k) (H.p₂ k) (by
      simpa only [Category.assoc] using congrArg (· ≫ e.inv) (H.w k)))
  have hι (i : H.I₀) : h.lift N ≫ P.map (H.f i).op = x i :=
    h.fac N (.left i)
  refine ⟨h.lift N ≫ P.map e.hom.op, ?_, ?_⟩
  · intro i
    change (h.lift N ≫ P.map e.hom.op) ≫ P.map (H.f i ≫ e.inv).op = x i
    rw [op_comp, P.map_comp, Category.assoc, ← P.map_comp_assoc, ← op_comp,
      e.inv_hom_id, op_id, P.map_id, Category.id_comp, hι]
  · intro t ht
    apply (cancel_mono (P.map e.inv.op)).mp
    have he : (h.lift N ≫ P.map e.hom.op) ≫ P.map e.inv.op = h.lift N := by
      rw [Category.assoc, ← P.map_comp, ← op_comp, e.inv_hom_id, op_id, P.map_id]
      exact Category.comp_id (h.lift N)
    rw [he]
    apply Multifork.IsLimit.hom_ext h
    intro i
    change (t ≫ P.map e.inv.op) ≫ P.map (H.f i).op = h.lift N ≫ P.map (H.f i).op
    rw [Category.assoc, ← P.map_comp, ← op_comp, hι]
    exact ht i

end PhilipponEtaleRefinementGluing

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (toLimit atStage atStage_toLimit)
open PhilipponEtaleLimitAffinePresheaf (affineCharts affinePresheaf exists_affineModel)
open PhilipponEtaleAffineSectionColimit (pullbackAffine stageSections sectionIso)
open PhilipponEtaleModeledSections (reversedBaseChange reversedBaseChangeIso)
open PhilipponEtaleModeledGluing (fullSubcategoryHypercover)
open PhilipponEtaleRefinementGluing (isSheafFor_of_multifork)
open PhilipponEtaleStageSectionSheaf (isLimitPullbackMultifork)


namespace PhilipponEtaleLimitSheaf

universe u

private theorem affineCharts_hasCover {X : Scheme.{u}} (U : X.Etale) :
    ∃ (β : Type u) (V : β → (affineCharts X).FullSubcategory)
      (f : ∀ b, ((affineCharts X).ι.obj (V b)) ⟶ U),
      Sieve.ofArrows _ f ∈ X.smallEtaleTopology U := by
  let 𝒰 := U.left.affineCover
  let V (b : 𝒰.I₀) : X.Etale := Scheme.Etale.mk (𝒰.f b ≫ U.hom)
  let f (b : 𝒰.I₀) : V b ⟶ U := MorphismProperty.Over.homMk (𝒰.f b) rfl trivial
  refine ⟨𝒰.I₀, fun b => ⟨V b, Scheme.isAffine_affineCover U.left b⟩, f, ?_⟩
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
  exact 𝒰.iUnion_range

instance affineCharts_coverDense (X : Scheme.{u}) :
    (affineCharts X).ι.IsCoverDense X.smallEtaleTopology where
  is_cover U := by
    obtain ⟨β, V, f, hf⟩ := affineCharts_hasCover U
    apply X.smallEtaleTopology.superset_covering _ hf
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨b⟩
    exact Presieve.in_coverByImage (affineCharts X).ι (f b)

private def specToAffineCharts (X : Scheme.{u}) :
    X.AffineEtale ⥤ (affineCharts X).FullSubcategory where
  obj V := ⟨(Scheme.AffineEtale.Spec X).obj V, by
    change IsAffine (Spec _)
    infer_instance⟩
  map f := ObjectProperty.homMk ((Scheme.AffineEtale.Spec X).map f)
  map_id V := ObjectProperty.hom_ext _ ((Scheme.AffineEtale.Spec X).map_id V)
  map_comp f g := ObjectProperty.hom_ext _ ((Scheme.AffineEtale.Spec X).map_comp f g)

private def specToAffineChartsFullyFaithful (X : Scheme.{u}) :
    (specToAffineCharts X).FullyFaithful := by
  apply Functor.FullyFaithful.ofCompFaithful (G := (affineCharts X).ι)
  change (Scheme.AffineEtale.Spec X).FullyFaithful
  exact Functor.FullyFaithful.ofFullyFaithful (Scheme.AffineEtale.Spec X)

instance affineCharts_essentiallySmall (X : Scheme.{u}) :
    EssentiallySmall.{u} (affineCharts X).FullSubcategory := by
  let K := specToAffineCharts X
  let : K.Full := (specToAffineChartsFullyFaithful X).full
  let : K.Faithful := (specToAffineChartsFullyFaithful X).faithful
  let : K.EssSurj := ⟨fun U => by
    let : IsAffine U.obj.left := U.property
    let e := U.obj.left.isoSpec
    let f := e.inv ≫ U.obj.hom
    let V := Scheme.AffineEtale.mk f
    let a : (K.obj V).obj ≅ U.obj :=
      MorphismProperty.Over.isoMk e.symm rfl
    exact ⟨V, ⟨ObjectProperty.isoMk (affineCharts X) a⟩⟩⟩
  let : K.IsEquivalence := {}
  exact (essentiallySmall_congr K.asEquivalence).mp inferInstance

/-- Fiber products of affine étale charts over an affine chart are affine. -/
theorem affineOverlap {X : Scheme.{u}} {T V W : X.Etale}
    [IsAffine T.left] [IsAffine V.left] [IsAffine W.left] (f : V ⟶ T) (g : W ⟶ T) :
    IsAffine (pullback f g).left := by
  let K := Scheme.Etale.forget X ⋙ Over.forget X
  let : PreservesLimitsOfShape WalkingCospan K := by dsimp [K]; infer_instance
  have h : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map K
  let : IsAffine (pullback f.left g.left) :=
    @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine V.left W.left T.left
      f.left g.left ‹_› ‹_› ‹_›
  exact IsAffine.of_isIso h.isoPullback.hom

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (F : System (directImages D))

private abbrev G := (affineCharts c.pt).ι

/-- The topology induced on the affine objects of the limit's étale site. -/
abbrev topology := (G c).inducedTopology c.pt.smallEtaleTopology

instance : HasSheafify (topology c) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Compare the two pullback conventions for charts at the limit. -/
def chartComparison (i : I) :
    reversedBaseChange (c.π.app i) ≅ atStage (D := D) i ⋙ toLimit c :=
  reversedBaseChangeIso (c.π.app i) ≪≫ (atStage_toLimit c i).symm

include hc in
private theorem exists_gluing_refinement {U : (affineCharts c.pt).FullSubcategory}
    (S : Sieve U) (hS : S ∈ topology c U) :
    ∃ R : Sieve U, R ≤ S ∧ R ∈ topology c U ∧
      ∀ B : AddCommGrpCat.{u}ᵒᵖ, R.arrows.IsSheafFor (affinePresheaf c hc F ⋙ coyoneda.obj B) := by
  classical
  let P := affinePresheaf c hc F
  have hS' := ((G c).mem_inducedTopology_iff_of_isCoverDense _ S).mp hS
  let : IsAffine U.obj.left := U.property
  let M := (exists_affineModel c hc U.obj).some
  let : IsAffine M.chart.etale.left := M.affine
  let z : U.obj ≅ (reversedBaseChange (c.π.app M.chart.index)).obj M.chart.etale :=
    M.comparison ≪≫ ((chartComparison c M.chart.index).app M.chart.etale).symm
  obtain ⟨i, T, e, β, hβ, W, a, hT, hW, hstage, hmem, hcover⟩ :=
    PhilipponEtaleAffineCoverModel.exists_cover_model c M.chart hc
      ((S.functorPushforward (G c)).pullback z.inv)
      (c.pt.smallEtaleTopology.pullback_stable z.inv hS')
  let : Fintype β := hβ
  let h₀ : PreZeroHypercover.{u} T := ⟨β, W, a⟩
  let H : (D.obj i).smallEtaleTopology.OneHypercover.{u} T :=
    GrothendieckTopology.OneHypercover.mk' h₀.toPreOneHypercover hstage (by simp)
  let : Fintype H.I₀ := hβ
  let : Finite H.I₁' := by change Finite (Sigma fun _ : β × β => PUnit); infer_instance
  let : Fintype H.I₁' := Fintype.ofFinite _
  let V : (affineCharts (D.obj i)).FullSubcategory := ⟨T, hT⟩
  have hY ⦃l l' : H.I₀⦄ (b : H.I₁ l l') : IsAffine (H.Y b).left := by
    let : IsAffine T.left := hT
    let : IsAffine (W l).left := hW l
    let : IsAffine (W l').left := hW l'
    exact affineOverlap (a l) (a l')
  let HH : PreOneHypercover V := fullSubcategoryHypercover _ V.property H.toPreOneHypercover hW hY
  let : Fintype HH.I₀ := ‹Fintype H.I₀›
  let : Fintype HH.I₁' := ‹Fintype H.I₁'›
  let K := pullbackAffine i c hc
  let L := HH.map K
  let θ := chartComparison c i
  let e' : U ≅ K.obj V := ObjectProperty.isoMk (affineCharts c.pt) (z ≪≫ e ≪≫ θ.app T)
  let a' (l : β) := L.f l ≫ e'.inv
  have he (l : β) : (θ.hom.app (W l)) ≫ (a' l).hom =
      (reversedBaseChange (c.π.app i)).map (a l) ≫ e.inv ≫ z.inv := by
    change θ.hom.app (W l) ≫ (atStage i ⋙ toLimit c).map (a l) ≫
      (θ.inv.app T ≫ e.inv) ≫ z.inv = _
    rw [← θ.hom.naturality_assoc, Category.assoc, Iso.hom_inv_id_app_assoc]
  refine ⟨Sieve.ofArrows L.X a', ?_, ?_, fun B => ?_⟩
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨l⟩
    rw [← Sieve.functorPullback_functorPushforward_eq (G c) (S := S)]
    have hm : (S.functorPushforward (G c)) (θ.hom.app (W l) ≫ (a' l).hom) := by
      rw [he]
      simpa only [Sieve.pullback_apply, Category.assoc] using hmem l
    have hm' := (S.functorPushforward (G c)).downward_closed hm (θ.inv.app (W l))
    change (S.functorPushforward (G c)) (a' l).hom
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hm'
  · apply ((G c).mem_inducedTopology_iff_of_isCoverDense _ _).mpr
    rw [Sieve.functorPushforward_ofArrows]
    apply c.pt.smallEtaleTopology.superset_covering _
      (c.pt.smallEtaleTopology.pullback_stable z.hom hcover)
    rintro B f ⟨Q, g, _, ⟨l⟩, hf⟩
    refine ⟨_, g ≫ θ.hom.app (W l), _, ⟨l⟩, ?_⟩
    have hh := congrArg (· ≫ z.inv) hf
    change (g ≫ θ.hom.app (W l)) ≫ (a' l).hom = f
    simpa only [Category.assoc, he, Iso.hom_inv_id, Category.comp_id] using hh
  · apply (Presieve.isSheafFor_iff_generate _).mp
    exact isSheafFor_of_multifork L e' P
      (isLimitPullbackMultifork F c hc HH H rfl) B

/-- The section colimits form a sheaf on the affine charts of the limit. -/
theorem isSheaf : Presheaf.IsSheaf (topology c) (affinePresheaf c hc F) := by
  intro B U S hS
  obtain ⟨R, hRS, hRcov, hR⟩ := exists_gluing_refinement c hc F S hS
  apply Presieve.isSheafFor_subsieve_aux _ hRS (hR (op B))
  intro W f _
  obtain ⟨T, hT, _, hTglue⟩ := exists_gluing_refinement c hc F
    (R.pullback f) ((topology c).pullback_stable f hRcov)
  intro x y₁ y₂ hy₁ hy₂
  exact (hTglue (op B)).isSeparatedFor _ _ _
    (Presieve.isAmalgamation_restrict hT x _ hy₁)
    (Presieve.isAmalgamation_restrict hT x _ hy₂)

/-- Restriction of abelian sheaves to the dense affine subsite. -/
def restriction :
    Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u} ⥤ Sheaf (topology c) AddCommGrpCat.{u} :=
  (G c).sheafPushforwardContinuous _ _ _

instance : (restriction c).IsEquivalence := by
  let : (G c).IsOneHypercoverDense.{u} (topology c) c.pt.smallEtaleTopology :=
    Functor.IsOneHypercoverDense.of_hasPullbacks affineCharts_hasCover
  exact Functor.isEquivalence_of_isOneHypercoverDense (G c) (topology c) c.pt.smallEtaleTopology _

/-- The limit of a compatible system of small étale sheaves, characterized
by the filtered colimits of its sections on affine charts. -/
def limitSheaf : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  (restriction c).asEquivalence.inverse.obj ⟨affinePresheaf c hc F, isSheaf c hc F⟩

/-- The constructed limit sheaf restricts to the given affine presheaf. -/
def restrictionIso :
    (restriction c).obj (limitSheaf c hc F) ≅ ⟨affinePresheaf c hc F, isSheaf c hc F⟩ :=
  (restriction c).asEquivalence.counitIso.app _

/-- On the pullback of an affine stage chart, sections of the full limit sheaf
are canonically the colimit of the sections at earlier stages. -/
def sectionsIso (i : I) :
    (affineCharts (D.obj i)).ι.op ⋙ stageSections F i ⋙ colim ≅
      ((affineCharts (D.obj i)).ι ⋙ (atStage i ⋙ toLimit c)).op ⋙
      (limitSheaf c hc F).obj := by
  let e := (sheafToPresheaf (topology c) AddCommGrpCat.{u}).mapIso (restrictionIso c hc F).symm
  exact sectionIso F i c hc ≪≫ Functor.isoWhiskerLeft (pullbackAffine i c hc).op e

end PhilipponEtaleLimitSheaf

end

end


