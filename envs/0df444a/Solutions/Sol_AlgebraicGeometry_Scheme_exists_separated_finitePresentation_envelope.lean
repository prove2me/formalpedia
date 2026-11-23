-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_separated_finitePresentation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-22T09:38:48.593534+00:00
-- url     : https://prove2.me/submissions/e698aee0-7907-455b-96e4-c5b82b8da683

import Definitions.Def_AlgebraicGeometry_ProperAffineBaseChangeModels
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finitePresentation_diagram_over_integer

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace PhilipponDiagonalOfMono

universe v u

/-- The relative diagonal of a subobject is the pullback of the ambient
relative diagonal along the induced map of fiber products. -/
theorem isPullback {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y S : C} (a : X ⟶ Y) [Mono a] (f : Y ⟶ S) :
    IsPullback a (pullback.diagonal (a ≫ f)) (pullback.diagonal f)
      (pullback.map (a ≫ f) (a ≫ f) f f a a (𝟙 S) (Category.comp_id _) (Category.comp_id _)) := by
  refine (pullback_map_diagonal_isPullback a a f).of_iso
    (asIso (pullback.diagonal a)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · apply (cancel_epi (pullback.diagonal a)).mp
    simp
  · apply (cancel_epi (pullback.diagonal a)).mp
    apply pullback.hom_ext <;> simp

end PhilipponDiagonalOfMono

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PhilipponImmersionLimitBoundary

universe u

private theorem exists_compact_boundary_neighborhood {Y : Scheme.{u}} [CompactSpace Y]
    (U : Y.Opens) {Z : Set Y} (hZ : IsClosed Z) (hZU : Z ⊆ U) :
    ∃ V : Y.Opens, IsCompact (V : Set Y) ∧ U ⊔ V = ⊤ ∧ (V : Set Y) ⊆ Zᶜ := by
  classical
  let B := (U : Set Y)ᶜ
  have hB : IsCompact B := U.isOpen.isClosed_compl.isCompact
  have hW (x : B) : ∃ W : Y.Opens, IsAffineOpen W ∧ (x : Y) ∈ W ∧ (W : Set Y) ⊆ Zᶜ := by
    have hx : (x : Y) ∈ Zᶜ := fun hx => x.2 (hZU hx)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWZ⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx hZ.isOpen_compl
    exact ⟨W, hW, hxW, hWZ⟩
  choose W hWA hWx hWZ using hW
  obtain ⟨s, hs⟩ := hB.elim_finite_subcover (fun x : B => (W x : Set Y))
    (fun x => (W x).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hWx ⟨x, hx⟩⟩)
  let V : Y.Opens := ⨆ x : s, W x.1
  refine ⟨V, ?_, top_unique ?_, ?_⟩
  · change IsCompact (↑(⨆ x : s, W x.1) : Set Y)
    rw [Opens.coe_iSup]
    exact isCompact_iUnion fun x : s => (hWA x.1).isCompact
  · intro x _
    by_cases hx : x ∈ U
    · exact Opens.mem_sup.mpr (Or.inl hx)
    · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Opens.mem_sup.mpr (Or.inr (Opens.mem_iSup.mpr ⟨⟨j, hj⟩, hxj⟩))
  · intro x hx
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hx
    exact hWZ j.1 hxj

private theorem closed_of_boundary_disjoint {X Y : Scheme.{u}} (U V : Y.Opens)
    (a : X ⟶ U.toScheme) [IsClosedImmersion a] (hCover : U ⊔ V = ⊤)
    (hMiss : (a ≫ U.ι) ⁻¹ᵁ V = ⊥) : IsClosedImmersion (a ≫ U.ι) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [← isOpen_compl_iff]
  have hCompl : (Set.range (a ≫ U.ι))ᶜ = U.ι '' (Set.range a)ᶜ ∪ (V : Set Y) := by
    ext y
    constructor
    · intro hy
      have hUV : y ∈ U ⊔ V := hCover.ge (Set.mem_univ y)
      rcases Opens.mem_sup.mp hUV with hyU | hyV
      · refine Or.inl ⟨⟨y, hyU⟩, ?_, rfl⟩
        rintro ⟨x, hx⟩
        exact hy ⟨x, (Scheme.Hom.comp_apply _ _ _).trans (congrArg U.ι hx)⟩
      · exact Or.inr hyV
    · rintro (⟨z, hz, rfl⟩ | hy) ⟨x, hx⟩
      · apply hz
        exact ⟨x, U.ι.isOpenEmbedding.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hx)⟩
      · have hh : x ∈ (a ≫ U.ι) ⁻¹ᵁ V := by
          change (a ≫ U.ι) x ∈ V
          rwa [hx]
        rw [hMiss] at hh
        exact hh
  rw [hCompl]
  exact (U.ι.isOpenEmbedding.isOpenMap _ a.isClosedEmbedding.isClosed_range.isOpen_compl).union V.isOpen

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D P : I ⥤ Scheme.{u}} {cD : Cone D} {cP : Cone P}
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (P.map v)]
    [∀ j, CompactSpace (P.obj j)]

/-- A closed limit immersion whose stage maps are closed inside the preimages
of a fixed open becomes a closed immersion at some stage. -/
theorem exists_closed_stage_of_closed_in_open (hD : IsLimit cD) (hP : IsLimit cP)
    (p : D ⟶ P) [∀ j, QuasiCompact (p.app j)] (g : cD.pt ⟶ cP.pt) [IsClosedImmersion g]
    (h : ∀ i, cD.π.app i ≫ p.app i = g ≫ cP.π.app i)
    (i : I) (U : (P.obj i).Opens)
    (hgU : Set.range g ⊆ ((cP.π.app i : cP.pt ⟶ P.obj i) ⁻¹ᵁ U : cP.pt.Opens).1)
    (hf : ∀ {j : I} (v : j ⟶ i), ∃ a : D.obj j ⟶ (P.map v ⁻¹ᵁ U).toScheme,
      IsClosedImmersion a ∧ a ≫ (P.map v ⁻¹ᵁ U).ι = p.app j) :
    ∃ (j : I) (_ : j ⟶ i), IsClosedImmersion (p.app j) := by
  let : CompactSpace cP.pt := Scheme.compactSpace_of_isLimit P cP hP
  obtain ⟨V, hV, hCover, hVg⟩ := exists_compact_boundary_neighborhood (Y := cP.pt)
    (cP.π.app i ⁻¹ᵁ U) g.isClosedEmbedding.isClosed_range hgU
  obtain ⟨j, W, hW, hWV⟩ := exists_preimage_eq P cP hP V hV
  obtain ⟨k, u, v, _⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Uₖ := P.map u ⁻¹ᵁ U
  let Wₖ := P.map v ⁻¹ᵁ W
  have h₀ : cP.π.app k ⁻¹ᵁ (Uₖ ⊔ Wₖ) = ⊤ := by
    simp only [Uₖ, Wₖ, Scheme.Hom.preimage_sup, ← Scheme.Hom.comp_preimage, cP.w, hWV, hCover]
  obtain ⟨l, w, hw⟩ := exists_map_eq_top P cP hP (Uₖ ⊔ Wₖ) h₀
  let E := p.app l ⁻¹ᵁ P.map w ⁻¹ᵁ Wₖ
  have hE : IsCompact (E : Set (D.obj l)) :=
    QuasiCompact.isCompact_preimage _ (P.map w ⁻¹ᵁ Wₖ).isOpen
      (QuasiCompact.isCompact_preimage _ Wₖ.isOpen (QuasiCompact.isCompact_preimage _ W.isOpen hW))
  have hPull : cP.π.app l ⁻¹ᵁ P.map w ⁻¹ᵁ Wₖ = V := by
    rw [← Scheme.Hom.comp_preimage, cP.w w]
    change cP.π.app k ⁻¹ᵁ P.map v ⁻¹ᵁ W = V
    rw [← Scheme.Hom.comp_preimage, cP.w v, hWV]
  have hMiss : cD.π.app l ⁻¹ᵁ E ≤ cD.π.app l ⁻¹ᵁ ⊥ := by
    change cD.π.app l ⁻¹ᵁ p.app l ⁻¹ᵁ P.map w ⁻¹ᵁ Wₖ ≤ _
    rw [← Scheme.Hom.comp_preimage, h l, Scheme.Hom.comp_preimage, hPull]
    intro x hx
    exact (hVg hx ⟨x, rfl⟩).elim
  obtain ⟨m, z, hz⟩ := exists_map_preimage_le_map_preimage D cD hD hE hMiss
  let q := (z ≫ w) ≫ u
  let B := P.map (z ≫ w) ⁻¹ᵁ Wₖ
  obtain ⟨a, ha, haeq⟩ := hf q
  let _ := ha
  have hB : (P.map q ⁻¹ᵁ U) ⊔ B = ⊤ := by
    simpa only [q, B, Uₖ, Functor.map_comp, Scheme.Hom.comp_preimage,
      Scheme.Hom.preimage_sup, Scheme.Hom.preimage_top] using
      congrArg (fun S => P.map z ⁻¹ᵁ S) hw
  have he : (a ≫ (P.map q ⁻¹ᵁ U).ι) ⁻¹ᵁ B = ⊥ := by
    rw [haeq, show B = P.map z ⁻¹ᵁ P.map w ⁻¹ᵁ Wₖ by
      simp only [B, Functor.map_comp, Scheme.Hom.comp_preimage], ← Scheme.Hom.comp_preimage,
      ← p.naturality z, Scheme.Hom.comp_preimage]
    exact le_bot_iff.mp (by simpa only [E, Scheme.Hom.preimage_bot] using hz)
  exact ⟨m, q, haeq ▸ closed_of_boundary_disjoint _ B a hB he⟩

end PhilipponImmersionLimitBoundary

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponDiagonalNeighborhood

universe u v

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The open where both projections to the source lie in the same chart. -/
def chart (V : X.Opens) : (pullback.diagonalObj f).Opens :=
  pullback.fst f f ⁻¹ᵁ V ⊓ pullback.snd f f ⁻¹ᵁ V

theorem preimage_diagonal_chart (V : X.Opens) : pullback.diagonal f ⁻¹ᵁ chart f V = V := by
  simp only [chart, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    pullback.diagonal_fst, pullback.diagonal_snd, Scheme.Hom.id_preimage, inf_idem]

theorem preimage_map_chart {Y : Scheme.{u}} (g : Y ⟶ S) (a : X ⟶ Y) (h : f = a ≫ g)
    (V : Y.Opens) :
    pullback.map f f g g a a (𝟙 S) ((Category.comp_id _).trans h)
      ((Category.comp_id _).trans h) ⁻¹ᵁ chart g V = chart f (a ⁻¹ᵁ V) := by
  simp only [chart, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, pullback.map,
    pullback.lift_fst, pullback.lift_snd]

private theorem closed_restrict_chart (V : X.Opens) [IsSeparated (V.ι ≫ f)] :
    IsClosedImmersion (pullback.diagonal f ∣_ chart f V) := by
  let w := V.ι ≫ f
  let p : pullback w w ⟶ pullback f f :=
    pullback.map w w f f V.ι V.ι (𝟙 S) (Category.comp_id _) (Category.comp_id _)
  let : IsOpenImmersion p := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion V.ι) inferInstance rfl rfl
  have hp : p.opensRange = chart f V := by
    apply Opens.ext
    change Set.range p = _
    dsimp only [p]
    rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι]
    rfl
  let e := (PhilipponDiagonalOfMono.isPullback V.ι f).isoPullback
  have he : e.hom ≫ pullback.snd (pullback.diagonal f) p = pullback.diagonal w :=
    (PhilipponDiagonalOfMono.isPullback V.ι f).isoPullback_hom_snd
  have hClosed : IsClosedImmersion (pullback.snd (pullback.diagonal f) p) := by
    have hh : IsClosedImmersion (e.hom ≫ pullback.snd (pullback.diagonal f) p) :=
      he.symm ▸ inferInstanceAs (IsClosedImmersion (pullback.diagonal w))
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e.hom _).mp hh
  rw [← hp, MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictOpensRange (pullback.diagonal f) p)]
  exact hClosed

variable {ι : Type v} (V : ι → X.Opens)

/-- The open neighborhood of the diagonal from a cover by source charts. -/
def neighborhood : (pullback.diagonalObj f).Opens :=
  ⨆ i, chart f (V i)

theorem preimage_diagonal (hV : iSup V = ⊤) :
    pullback.diagonal f ⁻¹ᵁ neighborhood f V = ⊤ := by
  simpa only [neighborhood, Scheme.Hom.preimage_iSup, preimage_diagonal_chart] using hV

theorem range_subset (hV : iSup V = ⊤) :
    Set.range (pullback.diagonal f) ⊆ (neighborhood f V).1 := by
  rintro _ ⟨x, rfl⟩
  change x ∈ pullback.diagonal f ⁻¹ᵁ neighborhood f V
  rw [preimage_diagonal f V hV]
  exact Set.mem_univ x

/-- The diagonal is closed in the neighborhood given by charts that are
separated over the base. -/
theorem exists_factor (hV : iSup V = ⊤) [∀ i, IsSeparated ((V i).ι ≫ f)] :
    ∃ e : X ⟶ (neighborhood f V).toScheme,
      IsClosedImmersion e ∧ e ≫ (neighborhood f V).ι = pullback.diagonal f := by
  let d := pullback.diagonal f
  let U := neighborhood f V
  let W (i : ι) : U.toScheme.Opens := U.ι ⁻¹ᵁ chart f (V i)
  have hW : iSup W = ⊤ := by
    change (⨆ i, U.ι ⁻¹ᵁ chart f (V i)) = ⊤
    rw [← Scheme.Hom.preimage_iSup]
    exact U.ι_preimage_self
  have hImage (i : ι) : U.ι ''ᵁ W i = chart f (V i) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
    exact le_iSup (fun i => chart f (V i)) i
  let : IsClosedImmersion (d ∣_ U) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hW]
    intro i
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictRestrict d U (W i)),
      MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictEq d (hImage i))]
    exact closed_restrict_chart f (V i)
  let e : (d ⁻¹ᵁ U).toScheme ≅ X := X.isoOfEq (preimage_diagonal f V hV) ≪≫ X.topIso
  refine ⟨e.inv ≫ d ∣_ U, inferInstance, ?_⟩
  rw [Category.assoc, morphismRestrict_ι]
  simp [e, d]

end PhilipponDiagonalNeighborhood

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponSeparatedLimit

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {S : Scheme.{u}}
    (g : D ⟶ (Functor.const I).obj S)

private abbrev selfProduct := PhilipponPullbackLimit.diagram g g

private def diagonal : D ⟶ selfProduct g where
  app i := pullback.diagonal (g.app i)
  naturality i j v := by
    apply pullback.hom_ext <;> simp [selfProduct, PhilipponPullbackLimit.diagram, pullback.map]

private theorem transition_over {i j : I} (v : i ⟶ j) : D.map v ≫ g.app j = g.app i := by
  exact (g.naturality v).trans (Category.comp_id _)

private theorem product_map {i j : I} (v : i ⟶ j) :
    (selfProduct g).map v =
      pullback.map (g.app i) (g.app i) (g.app j) (g.app j) (D.map v) (D.map v)
        (𝟙 S) ((Category.comp_id _).trans (transition_over g v).symm)
        ((Category.comp_id _).trans (transition_over g v).symm) := rfl

private theorem diagonal_square {X Y : Scheme.{u}} (a : X ⟶ Y) [Mono a] (r : Y ⟶ S)
    (s : X ⟶ S) (h : s = a ≫ r) :
    IsPullback a (pullback.diagonal s) (pullback.diagonal r)
      (pullback.map s s r r a a (𝟙 S) ((Category.comp_id _).trans h)
        ((Category.comp_id _).trans h)) := by
  subst s
  exact PhilipponDiagonalOfMono.isPullback a r

private theorem closed_in_preimage {Z W P T : Scheme.{u}} (d : Z ⟶ P) (b : W ⟶ T)
    [IsImmersion b] (a : Z ⟶ W) (p : P ⟶ T)
    (h : IsPullback a d b p) :
    ∃ e : Z ⟶ (p ⁻¹ᵁ b.coborderRange).toScheme,
      IsClosedImmersion e ∧ e ≫ (p ⁻¹ᵁ b.coborderRange).ι = d := by
  let U := b.coborderRange
  have hRange : Set.range d ⊆ ((p ⁻¹ᵁ U : P.Opens) : Set P) := by
    rintro _ ⟨x, rfl⟩
    change p (d x) ∈ U
    have hx : p (d x) = b (a x) := by
      simpa only [Scheme.Hom.comp_apply] using (congrArg (fun q : Z ⟶ T => q x) h.w).symm
    rw [hx]
    exact subset_coborder ⟨a x, rfl⟩
  let e := IsOpenImmersion.lift (p ⁻¹ᵁ U).ι d (by simpa using hRange)
  have he : e ≫ (p ⁻¹ᵁ U).ι = d := IsOpenImmersion.lift_fac ..
  have hBig : IsPullback a (e ≫ (p ⁻¹ᵁ U).ι) (b.liftCoborder ≫ U.ι) p := by
    rwa [he, Scheme.Hom.liftCoborder_ι]
  have hSmall : IsPullback a e b.liftCoborder (p ∣_ U) :=
    hBig.of_bot (by
      rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.liftCoborder_ι, Category.assoc,
        morphismRestrict_ι, ← Category.assoc, he, h.w])
      (isPullback_morphismRestrict p U)
  exact ⟨e, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hSmall inferInstance, he⟩

variable [IsCofiltered I] {c : Cone D} (hc : IsLimit c)
    (f : c.pt ⟶ S) (hf : ∀ i, c.π.app i ≫ g.app i = f)

private abbrev productCone :
    Cone (selfProduct g) :=
  PhilipponPullbackLimit.cone g g (cX := c) (cY := c) (cS := constCone I S) f f
    (fun i => (hf i).trans (Category.comp_id f).symm)
    (fun i => (hf i).trans (Category.comp_id f).symm)

include hc hf in
private theorem exists_isSeparated_of_neighborhood
    [CompactSpace S] [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] [IsSeparated f]
    (i : I) (U : ((selfProduct g).obj i).Opens)
    (hRangeStage : Set.range ((diagonal g).app i) ⊆ ↑U)
    (hStage : ∀ {j : I} (v : j ⟶ i),
      ∃ a : D.obj j ⟶ ((selfProduct g).map v ⁻¹ᵁ U).toScheme,
        IsClosedImmersion a ∧ a ≫ ((selfProduct g).map v ⁻¹ᵁ U).ι = (diagonal g).app j) :
    ∃ i, IsSeparated (g.app i) := by
  let : IsConnected I := IsCofiltered.isConnected I
  let : ∀ {i j : I} (v : i ⟶ j), IsAffineHom ((selfProduct g).map v) := fun v => by
    rw [product_map]
    exact MorphismProperty.pullbackMap (P := @IsAffineHom) (inferInstance : IsAffineHom (D.map v))
      inferInstance (transition_over g v).symm (transition_over g v).symm
  let : ∀ i, CompactSpace ((selfProduct g).obj i) := fun i => by
    let : CompactSpace (D.obj i) :=
      @QuasiCompact.compactSpace_of_compactSpace _ S (g.app i) inferInstance inferInstance
    change CompactSpace ↥(pullback (g.app i) (g.app i))
    infer_instance
  let : ∀ i, QuasiCompact ((diagonal g).app i) := fun i =>
    QuasiSeparated.quasiCompact_diagonal (f := g.app i)
  let cP := productCone g f hf
  let hP : IsLimit cP := PhilipponPullbackLimit.isLimit g g f f _ _ hc hc (isLimitConstCone I S)
  have hCompat (i : I) : c.π.app i ≫ (diagonal g).app i =
      pullback.diagonal f ≫ cP.π.app i := by
    apply pullback.hom_ext
    · simp [cP, diagonal, pullback.map]
    · simp [cP, diagonal, pullback.map]
  have hRange : Set.range (pullback.diagonal f) ⊆ ((cP.π.app i ⁻¹ᵁ U : cP.pt.Opens) : Set cP.pt) := by
    rintro _ ⟨x, rfl⟩
    change cP.π.app i (pullback.diagonal f x) ∈ U
    have hx : cP.π.app i (pullback.diagonal f x) = (diagonal g).app i (c.π.app i x) :=
      (Scheme.Hom.comp_apply (pullback.diagonal f) (cP.π.app i) x).symm.trans
        ((congrArg (fun q : c.pt ⟶ (selfProduct g).obj i => q x) (hCompat i)).symm.trans
          (Scheme.Hom.comp_apply (c.π.app i) ((diagonal g).app i) x))
    rw [hx]
    exact hRangeStage ⟨c.π.app i x, rfl⟩
  obtain ⟨j, _, hj⟩ := PhilipponImmersionLimitBoundary.exists_closed_stage_of_closed_in_open
    hc hP (diagonal g) (pullback.diagonal f) hCompat i U hRange hStage
  exact ⟨j, ⟨hj⟩⟩

include hc hf in
/-- Separatedness over a fixed quasi-compact base descends to some stage of
a cofiltered diagram with closed immersion transition maps. -/
theorem exists_isSeparated
    [CompactSpace S] [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ {i j : I} (v : i ⟶ j), IsClosedImmersion (D.map v)] [IsSeparated f] :
    ∃ i, IsSeparated (g.app i) := by
  let : ∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v) := fun v => inferInstance
  let i : I := (IsCofiltered.nonempty (C := I)).some
  let b := pullback.diagonal (g.app i)
  let U := b.coborderRange
  refine exists_isSeparated_of_neighborhood g hc f hf i U subset_coborder ?_
  intro j v
  have hb : IsPullback (D.map v) ((diagonal g).app j) b ((selfProduct g).map v) := by
    rw [product_map]
    exact diagonal_square (D.map v) (g.app i) (g.app j) (transition_over g v).symm
  exact closed_in_preimage ((diagonal g).app j) b (D.map v) ((selfProduct g).map v) hb

include hc hf in
/-- Separatedness over a fixed affine base descends along affine transition maps. -/
theorem exists_isSeparated_of_affine
    [IsAffine S] [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] [IsSeparated f] :
    ∃ i, IsSeparated (g.app i) := by
  let i : I := (IsCofiltered.nonempty (C := I)).some
  let V : (D.obj i).affineOpens → (D.obj i).Opens := Subtype.val
  let U := PhilipponDiagonalNeighborhood.neighborhood (g.app i) V
  refine exists_isSeparated_of_neighborhood g hc f hf i U
    (PhilipponDiagonalNeighborhood.range_subset (g.app i) V (iSup_affineOpens_eq_top _)) ?_
  intro j v
  let W : (D.obj i).affineOpens → (D.obj j).Opens := fun t => D.map v ⁻¹ᵁ V t
  have hW : iSup W = ⊤ := (D.map v).iSup_preimage_eq_top (U := V) (iSup_affineOpens_eq_top _)
  have hU : (selfProduct g).map v ⁻¹ᵁ U = PhilipponDiagonalNeighborhood.neighborhood (g.app j) W := by
    simp only [U, PhilipponDiagonalNeighborhood.neighborhood, Scheme.Hom.preimage_iSup]
    congr 1
    funext t
    rw [product_map g v]
    exact PhilipponDiagonalNeighborhood.preimage_map_chart (g.app j) (g.app i) (D.map v)
      (transition_over g v).symm (V t)
  let : ∀ t, IsSeparated ((W t).ι ≫ g.app j) := fun t => by
    let : IsAffine (W t).toScheme := t.2.preimage (D.map v)
    let : IsAffineHom ((W t).ι ≫ g.app j) :=
      isAffineHom_of_isAffine (Y := S) ((W t).ι ≫ g.app j)
    infer_instance
  rw [hU]
  exact PhilipponDiagonalNeighborhood.exists_factor (g.app j) W hW

end PhilipponSeparatedLimit

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponFiniteStageSections

universe u v

/-- Finite sets of functions on finitely many affine limit schemes all lift
at one common stage of the indexing category. -/
theorem exists_common_stage {I : Type u} [Category.{u} I] [IsCofiltered I]
    {J : Type v} [Finite J] (D : J → I ⥤ Scheme.{u}) (c : ∀ j, Cone (D j))
    (hc : ∀ j, IsLimit (c j)) [∀ j i, IsAffine ((D j).obj i)]
    (s : ∀ j, Finset Γ((c j).pt, ⊤)) :
    ∃ i : I, ∀ j (x : Γ((c j).pt, ⊤)), x ∈ s j →
      ∃ y : Γ((D j).obj i, ⊤), ((c j).π.app i).appTop y = x := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have h (a : Σ j, ↥(s j)) : ∃ (i : I) (y : Γ((D a.1).obj i, ⊤)),
      ((c a.1).π.app i).appTop y = a.2.1 :=
    exists_appTop_π_eq_of_isAffine_of_isLimit (D a.1) (c a.1) (hc a.1) a.2.1
  choose stage representative hRepresentative using h
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image stage)
  refine ⟨i, ?_⟩
  intro j x hx
  let a : Σ j, ↥(s j) := ⟨j, ⟨x, hx⟩⟩
  let v : i ⟶ stage a := (hi (Finset.mem_image_of_mem stage (Finset.mem_univ a))).some
  refine ⟨((D j).map v).appTop (representative a), ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, (c j).w v]
  exact hRepresentative a

end PhilipponFiniteStageSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponAffineGraphClosed

universe u

/-- If the sections from the first projection generate the coordinate ring
over the base of the second projection, the induced graph is closed. -/
theorem isClosedImmersion {X Y B S : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine B] [IsAffine S]
    (a : X ⟶ Y) (f : X ⟶ B) (g : Y ⟶ S) (b : B ⟶ S) (h : a ≫ g = f ≫ b)
    (s : Set Γ(X, ⊤))
    (hs : letI := f.appTop.hom.toAlgebra; Algebra.adjoin Γ(B, ⊤) s = ⊤)
    (ha : s ⊆ Set.range a.appTop) :
    IsClosedImmersion (pullback.lift a f h) := by
  let p := pullback.lift a f h
  let q := pullback.snd g b
  let r := pullback.fst g b
  have hq : p ≫ q = f := pullback.lift_snd ..
  have hr : p ≫ r = a := pullback.lift_fst ..
  let : Algebra Γ(B, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(B, ⊤) Γ(pullback g b, ⊤) := q.appTop.hom.toAlgebra
  let liftSections : Γ(pullback g b, ⊤) →ₐ[Γ(B, ⊤)] Γ(X, ⊤) :=
    { toRingHom := p.appTop.hom
      commutes' x := by
        change p.appTop (q.appTop x) = f.appTop x
        rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hq] }
  apply IsClosedImmersion.of_surjective_of_isAffine p
  change Function.Surjective liftSections
  apply (AlgHom.range_eq_top liftSections).mp
  refine top_unique ?_
  rw [← hs]
  apply Algebra.adjoin_le
  intro x hx
  obtain ⟨y, rfl⟩ := ha hx
  refine ⟨r.appTop y, ?_⟩
  change p.appTop (r.appTop y) = a.appTop y
  rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hr]

end PhilipponAffineGraphClosed

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponStageBaseChange

universe u

variable {V W B T : Scheme.{u}} {v : V ⟶ B} {w : W ⟶ B} (p : V ⟶ W) (h : p ≫ w = v)

def map (b : T ⟶ B) : pullback v b ⟶ pullback w b :=
  pullback.lift (pullback.fst v b ≫ p) (pullback.snd v b)
    (by rw [Category.assoc, h, pullback.condition])

@[reassoc (attr := simp)]
theorem fst (b : T ⟶ B) : map p h b ≫ pullback.fst w b = pullback.fst v b ≫ p :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem snd (b : T ⟶ B) : map p h b ≫ pullback.snd w b = pullback.snd v b :=
  pullback.lift_snd ..

theorem isPullback (b : T ⟶ B) :
    IsPullback (pullback.fst v b) (map p h b) p (pullback.fst w b) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd w b) (v₂₂ := w) (h₃₁ := b) ?_
    (fst p h b).symm (IsPullback.of_hasPullback w b)
  rw [snd, h]
  exact IsPullback.of_hasPullback v b

theorem property {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] (hp : P p)
    (b : T ⟶ B) : P (map p h b) :=
  MorphismProperty.of_isPullback (P := P) (isPullback p h b) hp

instance (b : T ⟶ B) [IsOpenImmersion p] : IsOpenImmersion (map p h b) :=
  property p h (P := @IsOpenImmersion) inferInstance b

theorem opensRange (b : T ⟶ B) [IsOpenImmersion p] :
    (map p h b).opensRange = pullback.fst w b ⁻¹ᵁ p.opensRange := by
  let e := (isPullback p h b).isoPullback
  have he : e.hom ≫ pullback.snd p (pullback.fst w b) = map p h b :=
    (isPullback p h b).isoPullback_hom_snd
  apply TopologicalSpace.Opens.ext
  change Set.range (map p h b) = _
  rw [← he]
  have hOpen : (e.hom ≫ pullback.snd p (pullback.fst w b)).opensRange =
      pullback.fst w b ⁻¹ᵁ p.opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]
  exact congrArg (fun o : (pullback w b).Opens => o.1) hOpen

end PhilipponStageBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponStageGraphEnvelope

universe u

private theorem closed_of_cover {X Y B S : Scheme.{u}} (a : X ⟶ Y) (f : X ⟶ B)
    (g : Y ⟶ S) (b : B ⟶ S) (h : a ≫ g = f ≫ b) {J : Type u}
    (V : J → Y.Opens) (hV : iSup V = ⊤)
    (hLocal : ∀ j, ∃ (e : (a ⁻¹ᵁ V j).ι ≫ f ≫ b = (a ∣_ V j) ≫ (V j).ι ≫ g),
      IsClosedImmersion (pullback.lift (a ∣_ V j) ((a ⁻¹ᵁ V j).ι ≫ f)
        (e.symm.trans (Category.assoc _ _ _).symm))) :
    IsClosedImmersion (pullback.lift a f h) := by
  let A := pullback.lift a f h
  let q := pullback.fst g b
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (q.iSup_preimage_eq_top hV)]
  intro j
  let U := V j
  obtain ⟨he, hClosed⟩ := hLocal j
  let d : (a ⁻¹ᵁ U).toScheme ⟶ pullback (U.ι ≫ g) b := pullback.lift (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ f)
    (he.symm.trans (Category.assoc _ _ _).symm)
  let p := PhilipponStageBaseChange.map U.ι (rfl : U.ι ≫ g = U.ι ≫ g) b
  have hp : IsPullback (pullback.fst (U.ι ≫ g) b) p U.ι q :=
    PhilipponStageBaseChange.isPullback U.ι rfl b
  have hdf : d ≫ pullback.fst (U.ι ≫ g) b = a ∣_ U := pullback.lift_fst ..
  have hds : d ≫ pullback.snd (U.ι ≫ g) b = (a ⁻¹ᵁ U).ι ≫ f := pullback.lift_snd ..
  have hd : IsPullback d (a ⁻¹ᵁ U).ι p A := by
    refine IsPullback.of_right (h₁₂ := pullback.fst (U.ι ≫ g) b) (v₁₃ := U.ι) (h₂₂ := q)
      ?_ ?_ hp
    · change IsPullback (d ≫ pullback.fst _ _) (a ⁻¹ᵁ U).ι U.ι (A ≫ pullback.fst _ _)
      dsimp only [d, A]
      rw [pullback.lift_fst, pullback.lift_fst]
      exact isPullback_morphismRestrict a U
    · apply pullback.hom_ext
      · simp only [Category.assoc, p, PhilipponStageBaseChange.fst, A, pullback.lift_fst]
        rw [← Category.assoc, hdf, morphismRestrict_ι]
      · simp only [Category.assoc, p, PhilipponStageBaseChange.snd, hds, A, pullback.lift_snd]
  have hOpen : p.opensRange = q ⁻¹ᵁ U := by
    change (PhilipponStageBaseChange.map U.ι (rfl : U.ι ≫ g = U.ι ≫ g) b).opensRange = _
    rw [PhilipponStageBaseChange.opensRange, Scheme.Opens.opensRange_ι]
  rw [← hOpen, MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictOpensRange A p)]
  have hIso : hd.flip.isoPullback.hom ≫ pullback.snd A p = d :=
    hd.flip.isoPullback_hom_snd
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hd.flip.isoPullback.hom _).mp (hIso.symm ▸ hClosed)

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] [∀ i, CompactSpace (D.obj i)]
    {S B : Scheme.{u}} [IsAffine S] [IsAffine B] (b : B ⟶ S)
    (g : D ⟶ (Functor.const I).obj S) (f : c.pt ⟶ B) [LocallyOfFiniteType f]
    (hf : ∀ i, c.π.app i ≫ g.app i = f ≫ b)

include hc in
/-- Some affine-transition stage receives a map whose base change graph is a
closed immersion, when the limit is locally of finite type over the new base. -/
theorem exists_closed_graph (i : I) :
    ∃ (j : I) (_ : j ⟶ i), IsClosedImmersion (pullback.lift (c.π.app j) f (hf j)) := by
  let 𝒰 := (D.obj i).affineCover.finiteSubcover
  let V : 𝒰.I₀ → (D.obj i).Opens := fun z => (𝒰.f z).opensRange
  have hV : iSup V = ⊤ := 𝒰.isOpenCover_opensRange.iSup_eq_top
  have hVA (z : 𝒰.I₀) : IsAffineOpen (V z) := isAffineOpen_opensRange (𝒰.f z)
  let : ∀ j, IsAffineHom (c.π.app j) := isAffineHom_π_app D c hc
  let E (z : 𝒰.I₀) := opensDiagram D i (V z)
  let C (z : 𝒰.I₀) := opensCone D c i (V z)
  let : ∀ z j, IsAffine ((E z).obj j) := fun z j => (hVA z).preimage (D.map j.hom)
  let : ∀ z, IsAffine (C z).pt := fun z => (hVA z).preimage (c.π.app i)
  let r (z : 𝒰.I₀) : (c.π.app i ⁻¹ᵁ V z).toScheme ⟶ B := (c.π.app i ⁻¹ᵁ V z).ι ≫ f
  have hGen (z : 𝒰.I₀) : ∃ t : Finset Γ((c.π.app i ⁻¹ᵁ V z).toScheme, ⊤),
      letI := (r z).appTop.hom.toAlgebra
      Algebra.adjoin Γ(B, ⊤) (t : Set Γ((c.π.app i ⁻¹ᵁ V z).toScheme, ⊤)) = ⊤ := by
    let : IsAffine (c.π.app i ⁻¹ᵁ V z).toScheme := (hVA z).preimage (c.π.app i)
    let : LocallyOfFiniteType (r z) := inferInstanceAs
      (LocallyOfFiniteType ((c.π.app i ⁻¹ᵁ V z).ι ≫ f))
    have hs : (r z).appTop.hom.FiniteType :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    let : Algebra Γ(B, ⊤) Γ((c.π.app i ⁻¹ᵁ V z).toScheme, ⊤) := (r z).appTop.hom.toAlgebra
    let : Algebra.FiniteType Γ(B, ⊤) Γ((c.π.app i ⁻¹ᵁ V z).toScheme, ⊤) := hs
    exact Algebra.FiniteType.out
  choose t ht using hGen
  obtain ⟨j, hj⟩ := PhilipponFiniteStageSections.exists_common_stage E C
    (fun z => isLimitOpensCone D c hc i (V z)) t
  let W (z : 𝒰.I₀) := D.map j.hom ⁻¹ᵁ V z
  have hW : iSup W = ⊤ := (D.map j.hom).iSup_preimage_eq_top hV
  refine ⟨j.left, j.hom, closed_of_cover (c.π.app j.left) f (g.app j.left) b (hf j.left) W hW ?_⟩
  intro z
  have hDom : c.π.app j.left ⁻¹ᵁ W z = c.π.app i ⁻¹ᵁ V z := by
    dsimp only [W]
    rw [← Scheme.Hom.comp_preimage, c.w]
  let e := c.pt.isoOfEq hDom
  have hι : e.hom ≫ (c.π.app i ⁻¹ᵁ V z).ι = (c.π.app j.left ⁻¹ᵁ W z).ι :=
    c.pt.isoOfEq_hom_ι hDom
  let p : (c.π.app i ⁻¹ᵁ V z).toScheme ⟶ (W z).toScheme := (C z).π.app j
  have hp : e.hom ≫ p = c.π.app j.left ∣_ W z := by
    have hpi : p ≫ (W z).ι = (c.π.app i ⁻¹ᵁ V z).ι ≫ c.π.app j.left :=
      Scheme.Hom.resLE_comp_ι ..
    rw [← cancel_mono (W z).ι, Category.assoc, hpi, ← Category.assoc, hι,
      morphismRestrict_ι]
  have hr : e.hom ≫ r z = (c.π.app j.left ⁻¹ᵁ W z).ι ≫ f := by
    change e.hom ≫ (c.π.app i ⁻¹ᵁ V z).ι ≫ f = _
    rw [← Category.assoc, hι]
  have he : (c.π.app j.left ⁻¹ᵁ W z).ι ≫ f ≫ b =
      (c.π.app j.left ∣_ W z) ≫ (W z).ι ≫ g.app j.left := by
    rw [← hf, ← Category.assoc (c.π.app j.left ∣_ W z), morphismRestrict_ι, Category.assoc]
  have hP : p ≫ ((W z).ι ≫ g.app j.left) = r z ≫ b := by
    apply (cancel_epi e.hom).mp
    calc
      _ = (e.hom ≫ p) ≫ (W z).ι ≫ g.app j.left := (Category.assoc _ _ _).symm
      _ = (c.π.app j.left ∣_ W z) ≫ (W z).ι ≫ g.app j.left := by rw [hp]
      _ = (c.π.app j.left ⁻¹ᵁ W z).ι ≫ f ≫ b := he.symm
      _ = (e.hom ≫ r z) ≫ b := by rw [hr, Category.assoc]
      _ = _ := Category.assoc _ _ _
  let : IsAffine (c.π.app i ⁻¹ᵁ V z).toScheme := (hVA z).preimage (c.π.app i)
  let : IsAffine (W z).toScheme := (hVA z).preimage (D.map j.hom)
  have hLoc := PhilipponAffineGraphClosed.isClosedImmersion (S := S) p (r z) ((W z).ι ≫ g.app j.left) b
    hP (t z : Set Γ((c.π.app i ⁻¹ᵁ V z).toScheme, ⊤)) (ht z) (fun x hx => hj z x hx)
  refine ⟨he, ?_⟩
  have hLift : e.hom ≫ pullback.lift p (r z) hP =
      pullback.lift (c.π.app j.left ∣_ W z) ((c.π.app j.left ⁻¹ᵁ W z).ι ≫ f)
        (he.symm.trans (Category.assoc _ _ _).symm) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, hp]
    · simp only [Category.assoc, pullback.lift_snd, hr]
  let _ := hLoc
  exact hLift ▸ (inferInstance : IsClosedImmersion (e.hom ≫ pullback.lift p (r z) hP))

end PhilipponStageGraphEnvelope

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponSeparatedEnvelopeFromLimit

universe u

/-- An affine-transition presentation over an affine base supplies a separated
finite-presentation envelope for a separated finite-type morphism from its limit
to another affine scheme. -/
theorem exists_envelope {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    {S B : Scheme.{u}} [IsAffine S] [IsAffine B] (b : B ⟶ S)
    (g : D ⟶ (Functor.const I).obj S)
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, LocallyOfFinitePresentation (g.app i)]
    (f : c.pt ⟶ B) [LocallyOfFiniteType f] [IsSeparated f]
    (hf : ∀ i, c.π.app i ≫ g.app i = f ≫ b) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ B) (a : c.pt ⟶ Y),
      IsSeparated q ∧ LocallyOfFinitePresentation q ∧ QuasiCompact q ∧
        IsClosedImmersion a ∧ a ≫ q = f := by
  let : IsAffineHom b := isAffineHom_of_isAffine b
  let : IsSeparated (f ≫ b) := inferInstance
  obtain ⟨i, hi⟩ := PhilipponSeparatedLimit.exists_isSeparated_of_affine g hc (f ≫ b) hf
  let : ∀ j, CompactSpace (D.obj j) := fun j =>
    @QuasiCompact.compactSpace_of_compactSpace _ S (g.app j) inferInstance inferInstance
  obtain ⟨j, v, hj⟩ := PhilipponStageGraphEnvelope.exists_closed_graph D c hc b g f hf i
  let _ := hi
  let : IsSeparated (g.app j) := by
    have he : D.map v ≫ g.app i = g.app j := (g.naturality v).trans (Category.comp_id _)
    exact he ▸ (inferInstance : IsSeparated (D.map v ≫ g.app i))
  refine ⟨pullback (g.app j) b, pullback.snd (g.app j) b,
    pullback.lift (c.π.app j) f (hf j), inferInstance, ?_, ?_, hj, pullback.lift_snd ..⟩
  · exact MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  · exact MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance

end PhilipponSeparatedEnvelopeFromLimit

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of R)) (a : X ⟶ Y),
      IsSeparated g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧
        IsClosedImmersion a ∧ a ≫ g = f := by
  let : Algebra (ULift.{u} ℤ) R := ULift.algebra' ℤ R
  let b : Spec (.of R) ⟶ Spec (.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨I, instCategory, instCofiltered, D, c, g, e, ⟨hc⟩, hOver, hAff, hFP⟩ := AlgebraicGeometry.Scheme.exists_finitePresentation_diagram_over_integer X (f ≫ b)
  let _ := instCategory
  let _ := instCofiltered
  let _ := @hAff
  let : ∀ i, LocallyOfFinitePresentation (g.app i) := fun i => (hFP i).1
  let : ∀ i, QuasiCompact (g.app i) := fun i => (hFP i).2.1
  let : ∀ i, QuasiSeparated (g.app i) := fun i => (hFP i).2.2
  let f' := e.inv ≫ f
  let : LocallyOfFiniteType f' := inferInstance
  let : IsSeparated f' := inferInstance
  have hf (i : I) : c.π.app i ≫ g.app i = f' ≫ b := by
    apply (cancel_epi e.hom).mp
    simp only [Category.assoc, hOver, f', Iso.hom_inv_id_assoc]
  obtain ⟨Y, q, a, hSep, hPres, hQC, hClosed, hq⟩ :=
    PhilipponSeparatedEnvelopeFromLimit.exists_envelope hc b g f' hf
  let _ := hClosed
  exact ⟨Y, q, e.hom ≫ a, hSep, hPres, hQC, inferInstance, by simp [Category.assoc, hq, f']⟩

end

end
