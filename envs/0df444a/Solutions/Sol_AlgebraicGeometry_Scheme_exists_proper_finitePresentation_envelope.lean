-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-22T08:57:57.544287+00:00
-- url     : https://prove2.me/submissions/0e8b6912-b0a2-4e6f-a890-2ed733fce115

import Definitions.Def_AlgebraicGeometry_ClosedSubdiagramLimit
import Definitions.Def_AlgebraicGeometry_ProperAffineBaseChangeModels
import Definitions.Def_AlgebraicGeometry_SchematicImageLimitIdeal
import Definitions.Def_AlgebraicGeometry_SubalgebraStages
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_separated_finitePresentation_envelope
import Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData


namespace PhilipponSchematicImageDiagram

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}
    (c : Cone D) {X : Scheme.{u}} (a : X ⟶ c.pt)

private abbrev ideals (i : I) := (a ≫ c.π.app i).ker

private theorem compatible {i j : I} (v : i ⟶ j) :
    ideals c a j ≤ (ideals c a i).map (D.map v) := by
  simp only [ideals, ← Scheme.Hom.ker_comp, Category.assoc, c.w, le_refl]

/-- The schematic images of the maps from a scheme to the stages. -/
abbrev diagram := PhilipponClosedSubdiagramLimit.diagram D (ideals c a) (compatible c a)

/-- The inclusions of the schematic images into the original stages. -/
abbrev inclusion : diagram c a ⟶ D :=
  PhilipponClosedSubdiagramLimit.inclusion D (ideals c a) (compatible c a)

instance (i : I) : IsClosedImmersion ((inclusion c a).app i) :=
  inferInstanceAs (IsClosedImmersion (ideals c a i).subschemeι)

/-- The original map to the limit induces a cone on its stage images. -/
def cone : Cone (diagram c a) where
  pt := X
  π :=
    { app i := (a ≫ c.π.app i).toImage
      naturality i j v := by
        rw [← cancel_mono ((inclusion c a).app j)]
        change (𝟙 X ≫ (a ≫ c.π.app j).toImage) ≫ (ideals c a j).subschemeι =
          ((a ≫ c.π.app i).toImage ≫ (diagram c a).map v) ≫ (ideals c a j).subschemeι
        rw [Category.id_comp, Category.assoc]
        change (a ≫ c.π.app j).toImage ≫ (a ≫ c.π.app j).imageι =
          (a ≫ c.π.app i).toImage ≫
            (subschemeMap _ _ (D.map v) (compatible c a v) ≫ (ideals c a j).subschemeι)
        rw [subschemeMap_subschemeι, Scheme.Hom.toImage_imageι, ← Category.assoc]
        change a ≫ c.π.app j = ((a ≫ c.π.app i).toImage ≫ (a ≫ c.π.app i).imageι) ≫ D.map v
        rw [Scheme.Hom.toImage_imageι, Category.assoc, c.w] }

@[reassoc (attr := simp)]
theorem cone_compat (i : I) :
    (cone c a).π.app i ≫ (inclusion c a).app i = a ≫ c.π.app i :=
  Scheme.Hom.toImage_imageι _

instance [∀ {j k : I} (v : j ⟶ k), IsAffineHom (D.map v)] {j k : I} (v : j ⟶ k) :
    IsAffineHom ((diagram c a).map v) :=
  PhilipponClosedSubdiagramLimit.affine_transition D (ideals c a) (compatible c a) v

/-- A closed subscheme of an affine-transition limit is the limit of its
schematic images. -/
def isLimit [IsCofiltered I] [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [IsClosedImmersion a] (hc : IsLimit c) :
    IsLimit (cone c a) := by
  let d := PhilipponClosedSubdiagramLimit.cone D (ideals c a) (compatible c a) c
  let L := PhilipponClosedSubdiagramLimit.limitIdeal D (ideals c a) c
  have hL : L = a.ker := PhilipponImageLimitIdeal.iSup_kernels_eq hc a
  let r : X ⟶ d.pt := IsClosedImmersion.lift L.subschemeι a (by rw [ker_subschemeι, hL])
  have hr : r ≫ L.subschemeι = a := IsClosedImmersion.lift_fac ..
  let : IsIso r := IsClosedImmersion.isIso_of_ker_eq a L.subschemeι r hr (by rw [ker_subschemeι, hL])
  have e : cone c a ≅ d := Cone.ext (asIso r) (fun i => by
    rw [← cancel_mono ((inclusion c a).app i), cone_compat, Category.assoc]
    have hd : d.π.app i ≫ (inclusion c a).app i = L.subschemeι ≫ c.π.app i := by
      simp [d, inclusion, L, PhilipponClosedSubdiagramLimit.cone, PhilipponClosedSubdiagramLimit.inclusion]
    rw [hd]
    change a ≫ c.π.app i = r ≫ L.subschemeι ≫ c.π.app i
    rw [← Category.assoc, hr])
  exact (PhilipponClosedSubdiagramLimit.isLimit D (ideals c a) (compatible c a) hc).ofIsoLimit e.symm

end PhilipponSchematicImageDiagram

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

open AlgebraicGeometry AlgebraicGeometry.SubalgebraStages
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

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)
    {v₀ : V ⟶ Spec (.of A₀)} {w₀ : W ⟶ Spec (.of A₀)}
    (p₀ : V ⟶ W) (h₀ : p₀ ≫ w₀ = v₀)

def stages : diagram S v₀ ⟶ diagram S w₀ where
  app i := map p₀ h₀ (specHom S i.unop)
  naturality i j a := by
    apply pullback.hom_ext
    · simp only [Category.assoc, fst, trans_fst_assoc, trans_fst]
    · simp only [Category.assoc, snd, trans_snd, snd_assoc]

@[reassoc]
theorem leg_compat (i : ιᵒᵖ) :
    (cone S v₀).π.app i ≫ (stages S p₀ h₀).app i =
      map p₀ h₀ specHomTop ≫ (cone S w₀).π.app i := by
  change (cone S v₀).π.app i ≫ map p₀ h₀ (specHom S i.unop) = _
  apply pullback.hom_ext
  · simp only [Category.assoc, fst, cone_π_app_fst_assoc, leg_fst]
  · simp only [Category.assoc, snd, leg_snd, snd_assoc]

end PhilipponStageBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open AlgebraicGeometry AlgebraicGeometry.SubalgebraStages
open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponProperSchematicImage

universe u

private theorem affine_transition {I : Type u} [Category.{u} I]
    {D E : I ⥤ Scheme.{u}} (p : D ⟶ E)
    [∀ i, IsAffineHom (p.app i)] [∀ {i j : I} (v : i ⟶ j), IsAffineHom (E.map v)]
    {i j : I} (v : i ⟶ j) : IsAffineHom (D.map v) := by
  let : IsAffineHom (D.map v ≫ p.app j) := p.naturality v ▸
    (inferInstance : IsAffineHom (p.app i ≫ E.map v))
  exact IsAffineHom.of_comp (D.map v) (p.app j)

variable {A₀ R : Type u} [CommRing A₀] [IsNoetherianRing A₀] [CommRing R] [Algebra A₀ R]
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι →o Subalgebra A₀ R) (hS : ∀ r : R, ∃ i, r ∈ S i)
    [∀ i, IsNoetherianRing ↥(S i)]
    {Y X : Scheme.{u}} (g : Y ⟶ Spec (.of A₀)) [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (a : X ⟶ (cone S g).pt) [IsClosedImmersion a]
    [IsProper (a ≫ pullback.snd g (specHomTop (A₀ := A₀) (A := R)))]

include hS in
/-- A proper closed subscheme of the limit has a proper schematic image over
some Noetherian stage of the base. -/
theorem exists_proper_stage :
    ∃ i : ιᵒᵖ, IsProper ((PhilipponSchematicImageDiagram.inclusion (cone S g) a).app i ≫
      pullback.snd g (specHom S i.unop)) := by
  obtain ⟨W, P, π, j, q, hπ, hsurj, hj, hq, heq⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated g
  let _ := hπ
  let _ := hsurj
  let _ := hj
  let _ := hq
  let fW := π ≫ g
  let b := PhilipponStageBaseChange.map π (rfl : π ≫ g = fW)
    (specHomTop (A₀ := A₀) (A := R))
  let jR := PhilipponStageBaseChange.map j heq
    (specHomTop (A₀ := A₀) (A := R))
  let m := PhilipponSchematicImageDiagram.inclusion (cone S g) a
  let πs := PhilipponStageBaseChange.stages S π (rfl : π ≫ g = fW)
  let js := PhilipponStageBaseChange.stages S j heq
  let tX := PhilipponPullbackLimit.first m πs
  let tW := PhilipponPullbackLimit.second m πs
  let p := tW ≫ js
  let t := pullback.snd a b ≫ jR
  obtain ⟨hY⟩ := SubalgebraStages.nonempty_isLimit_cone S hS g
  obtain ⟨hW⟩ := SubalgebraStages.nonempty_isLimit_cone S hS fW
  obtain ⟨hP⟩ := SubalgebraStages.nonempty_isLimit_cone S hS q
  let hX := PhilipponSchematicImageDiagram.isLimit (cone S g) a hY
  have hab := PhilipponSchematicImageDiagram.cone_compat (cone S g) a
  have hbb := PhilipponStageBaseChange.leg_compat S π (rfl : π ≫ g = fW)
  let cT := PhilipponPullbackLimit.cone m πs (cX := PhilipponSchematicImageDiagram.cone (cone S g) a)
    (cY := cone S fW) (cS := cone S g) a b hab hbb
  let hT : IsLimit cT := PhilipponPullbackLimit.isLimit m πs a b hab hbb hX hW hY
  let : IsProper b := PhilipponStageBaseChange.property π _ (P := @IsProper) inferInstance _
  let : IsOpenImmersion jR := PhilipponStageBaseChange.instIsOpenImmersionMap j heq _
  let : IsClosedImmersion t := by
    have hComp : t ≫ pullback.snd q specHomTop =
        pullback.fst a b ≫ a ≫ pullback.snd g specHomTop := by
      dsimp only [t, jR]
      rw [Category.assoc, PhilipponStageBaseChange.snd, ←
        PhilipponStageBaseChange.snd (p := π) (h := (rfl : π ≫ g = fW)) (b := specHomTop),
        ← Category.assoc, ← pullback.condition, Category.assoc]
    let : IsProper (t ≫ pullback.snd q specHomTop) := hComp ▸
      (inferInstance : IsProper (pullback.fst a b ≫ a ≫ pullback.snd g specHomTop))
    let : IsProper t := IsProper.of_comp t (pullback.snd q specHomTop)
    exact IsClosedImmersion.of_isPreimmersion t (t.isClosedMap.isClosed_range)
  let : ∀ i, IsClosedImmersion (tW.app i) := fun i =>
    inferInstanceAs (IsClosedImmersion (pullback.snd (m.app i) (πs.app i)))
  let : ∀ i, IsAffineHom (tW.app i) := fun _ => inferInstance
  let : ∀ {i k : ιᵒᵖ} (v : i ⟶ k), IsAffineHom ((PhilipponPullbackLimit.diagram m πs).map v) :=
    fun v => affine_transition tW v
  let : ∀ i : ιᵒᵖ, IsOpenImmersion (js.app i) := fun i =>
    PhilipponStageBaseChange.instIsOpenImmersionMap j heq (specHom S i.unop)
  let : ∀ i : ιᵒᵖ, QuasiCompact (p.app i) := fun i => by
    let : IsLocallyNoetherian ((diagram S q).obj i) :=
      inferInstanceAs (IsLocallyNoetherian (pullback q (specHom S i.unop)))
    change QuasiCompact (tW.app i ≫ js.app i)
    infer_instance
  have hp : ∀ i, cT.π.app i ≫ p.app i = t ≫ (cone S q).π.app i := by
    intro i
    have hProj : cT.π.app i ≫ tW.app i = pullback.snd a b ≫ (cone S fW).π.app i :=
      PhilipponPullbackLimit.cone_second m πs
        (cX := PhilipponSchematicImageDiagram.cone (cone S g) a)
        (cY := cone S fW) (cS := cone S g) a b hab hbb i
    change cT.π.app i ≫ tW.app i ≫ js.app i =
      (pullback.snd a b ≫ jR) ≫ (cone S q).π.app i
    have hjCompat : (cone S fW).π.app i ≫ js.app i = jR ≫ (cone S q).π.app i :=
      PhilipponStageBaseChange.leg_compat S j heq i
    calc
      _ = (cT.π.app i ≫ tW.app i) ≫ js.app i := (Category.assoc _ _ _).symm
      _ = (pullback.snd a b ≫ (cone S fW).π.app i) ≫ js.app i :=
        congrArg (fun d => d ≫ js.app i) hProj
      _ = pullback.snd a b ≫ (cone S fW).π.app i ≫ js.app i := Category.assoc _ _ _
      _ = pullback.snd a b ≫ (jR ≫ (cone S q).π.app i) :=
        congrArg (fun d => pullback.snd a b ≫ d) hjCompat
      _ = _ := (Category.assoc _ _ _).symm
  let U (i : ιᵒᵖ) : ((diagram S q).obj i).Opens :=
    pullback.fst q (specHom S i.unop) ⁻¹ᵁ j.opensRange
  have hU (i : ιᵒᵖ) : (js.app i).opensRange = U i :=
    PhilipponStageBaseChange.opensRange j heq (specHom S i.unop)
  let i : ιᵒᵖ := Classical.choice inferInstance
  have hRange : Set.range t ⊆ ((cone S q).π.app i ⁻¹ᵁ U i : (cone S q).pt.Opens).1 := by
    change Set.range (pullback.snd a b ≫ jR) ⊆
      ((cone S q).π.app i ⁻¹ᵁ (pullback.fst q (specHom S i.unop) ⁻¹ᵁ j.opensRange) :
        (cone S q).pt.Opens).1
    rw [← Scheme.Hom.comp_preimage, cone_π_app_fst, ← PhilipponStageBaseChange.opensRange j heq]
    rintro _ ⟨x, rfl⟩
    exact ⟨pullback.snd a b x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hClosed {k : ιᵒᵖ} (v : k ⟶ i) :
      ∃ c : (PhilipponPullbackLimit.diagram m πs).obj k ⟶ ((diagram S q).map v ⁻¹ᵁ U i).toScheme,
        IsClosedImmersion c ∧ c ≫ ((diagram S q).map v ⁻¹ᵁ U i).ι = p.app k := by
    have hPre : (diagram S q).map v ⁻¹ᵁ U i = U k := by
      dsimp only [U]
      rw [← Scheme.Hom.comp_preimage, diagram_map_fst S q v]
    rw [hPre, ← hU k]
    refine ⟨tW.app k ≫ (js.app k).isoOpensRange.hom, inferInstance, ?_⟩
    change (tW.app k ≫ (js.app k).isoOpensRange.hom) ≫ (js.app k).opensRange.ι =
      tW.app k ≫ js.app k
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  obtain ⟨k, _, hk⟩ :=
    PhilipponImmersionLimitBoundary.exists_closed_stage_of_closed_in_open hT hP p t hp i (U i)
      hRange hClosed
  let _ := hk
  let s := pullback.snd g (specHom S k.unop)
  have hkOver : p.app k ≫ pullback.snd q (specHom S k.unop) = tX.app k ≫ m.app k ≫ s := by
    change (tW.app k ≫ js.app k) ≫ pullback.snd q _ = _
    rw [Category.assoc]
    change tW.app k ≫ PhilipponStageBaseChange.map j heq _ ≫ pullback.snd q _ = _
    rw [PhilipponStageBaseChange.snd, ← PhilipponStageBaseChange.snd
      (p := π) (h := (rfl : π ≫ g = fW)) (b := specHom S k.unop), ← Category.assoc]
    change (tW.app k ≫ πs.app k) ≫ s = _
    rw [← PhilipponPullbackLimit.projection_condition m πs k, Category.assoc]
  let : Surjective (πs.app k) :=
    PhilipponStageBaseChange.property π (rfl : π ≫ g = fW) (P := @Surjective) inferInstance
      (specHom S k.unop)
  let : Surjective (tX.app k) :=
    inferInstanceAs (Surjective (pullback.fst (m.app k) (πs.app k)))
  let : UniversallyClosed (tX.app k ≫ m.app k ≫ s) := hkOver ▸
    (inferInstance : UniversallyClosed (p.app k ≫ pullback.snd q (specHom S k.unop)))
  have hUC : UniversallyClosed (m.app k ≫ s) := UniversallyClosed.of_comp_surjective (tX.app k) _
  let : IsSeparated s := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  let : LocallyOfFiniteType s := MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  let : IsClosedImmersion (m.app k) :=
    inferInstanceAs (IsClosedImmersion ((PhilipponSchematicImageDiagram.inclusion (cone S g) a).app k))
  have hSep : IsSeparated (m.app k ≫ s) := inferInstance
  have hFT : LocallyOfFiniteType (m.app k ≫ s) := inferInstance
  refine ⟨k, ?_⟩
  change IsProper (m.app k ≫ s)
  rw [isProper_iff]
  exact ⟨hSep, hUC, hFT⟩

end PhilipponProperSchematicImage

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry AlgebraicGeometry.SubalgebraStages
open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponProperEnvelope

universe u

private abbrev base (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :
    Spec (.of R) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A R))

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

private theorem of_noetherian_model [IsProper f] {A₀ : Type u}
    [CommRing A₀] [IsNoetherianRing A₀] [Algebra A₀ R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A₀)) [IsSeparated g] [QuasiCompact g]
    [LocallyOfFinitePresentation g]
    (a : X ⟶ pullback g (base A₀ R)) [IsClosedImmersion a]
    (ha : a ≫ pullback.snd g (base A₀ R) = f) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ Spec (.of R)) (b : X ⟶ Z),
      IsProper q ∧ LocallyOfFinitePresentation q ∧ IsClosedImmersion b ∧ b ≫ q = f := by
  let I : Type u := {T : Subalgebra A₀ R // T.FG}
  let : Nonempty I := ⟨⟨Algebra.adjoin A₀ (∅ : Finset R), Subalgebra.fg_adjoin_finset ∅⟩⟩
  let : IsDirected I (· ≤ ·) := ⟨fun T U =>
    ⟨⟨T.1 ⊔ U.1, T.2.sup U.2⟩, le_sup_left (a := T.1) (b := U.1),
      le_sup_right (a := T.1) (b := U.1)⟩⟩
  let S : I →o Subalgebra A₀ R := ⟨Subtype.val, fun _ _ h => h⟩
  have hS (r : R) : ∃ i, r ∈ S i :=
    ⟨⟨Algebra.adjoin A₀ ({r} : Finset R), Subalgebra.fg_adjoin_finset _⟩,
      Algebra.subset_adjoin (by simp)⟩
  let : ∀ i : I, IsNoetherianRing ↥(S i) := fun i =>
    let : Algebra.FiniteType A₀ ↥(S i) := (Subalgebra.fg_iff_finiteType _).mp i.2
    Algebra.FiniteType.isNoetherianRing A₀ _
  let : IsProper (a ≫ pullback.snd g (base A₀ R)) := ha.symm ▸ inferInstance
  obtain ⟨i, hi⟩ := PhilipponProperSchematicImage.exists_proper_stage S hS g a
  let m := (PhilipponSchematicImageDiagram.inclusion (cone S g) a).app i
  let s := pullback.snd g (specHom S i.unop)
  let t := m ≫ s
  let c : X ⟶ (PhilipponSchematicImageDiagram.diagram (cone S g) a).obj i :=
    (PhilipponSchematicImageDiagram.cone (cone S g) a).π.app i
  let : IsProper t := hi
  let : LocallyOfFinitePresentation t := inferInstance
  have hcm : c ≫ m = a ≫ (cone S g).π.app i :=
    PhilipponSchematicImageDiagram.cone_compat (cone S g) a i
  have hc : c ≫ t = f ≫ specLeg S i.unop := by
    change c ≫ m ≫ pullback.snd g (specHom S i.unop) = _
    rw [← Category.assoc, hcm, Category.assoc, cone_π_app_snd S g i, ← Category.assoc, ha]
  let b : X ⟶ pullback t (specLeg S i.unop) := pullback.lift c f hc
  have hBase : (m ≫ pullback.fst g (specHom S i.unop)) ≫ g =
      t ≫ specHom S i.unop := by
    simp only [t, s, Category.assoc, pullback.condition]
  let e : pullback t (specLeg S i.unop) ⟶ pullback g (base A₀ R) :=
    pullback.lift (pullback.fst t (specLeg S i.unop) ≫ m ≫ pullback.fst g (specHom S i.unop))
      (pullback.snd t (specLeg S i.unop)) (by
        rw [Category.assoc, hBase, ← Category.assoc, pullback.condition,
          Category.assoc, specLeg_specHom])
  have he : b ≫ e = a := by
    apply pullback.hom_ext
    · simp only [e, b, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, hcm, Category.assoc, cone_π_app_fst S g i]
    · simp only [e, b, Category.assoc, pullback.lift_snd, ha]
  let : IsClosedImmersion (b ≫ e) := he.symm ▸ inferInstance
  let : IsSeparated e := by
    let : IsSeparated (e ≫ pullback.snd g (base A₀ R)) := by
      change IsSeparated (pullback.lift _ _ _ ≫ _)
      rw [pullback.lift_snd]
      infer_instance
    exact IsSeparated.of_comp e (pullback.snd g (base A₀ R))
  exact ⟨_, pullback.snd t (specLeg S i.unop), b, inferInstance, inferInstance,
    IsClosedImmersion.of_comp b e, pullback.lift_snd ..⟩

/-- A separated finite presentation envelope of a proper scheme can be
replaced by a proper finite presentation envelope. -/
theorem of_separated_envelope [IsProper f] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R))
    [IsSeparated g] [QuasiCompact g] [LocallyOfFinitePresentation g]
    (a : X ⟶ Y) [IsClosedImmersion a] (ha : a ≫ g = f) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ Spec (.of R)) (b : X ⟶ Z),
      IsProper q ∧ LocallyOfFinitePresentation q ∧ IsClosedImmersion b ∧ b ≫ q = f := by
  let : Algebra (ULift.{u} ℤ) R := ULift.algebra' ℤ R
  obtain ⟨B, hB, _, Y₀, g₀, a₀, hfp, hqc, hqs, hCart⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := ULift.{u} ℤ) g ∅
  let _ := hfp
  let _ := hqc
  let _ := hqs
  let : IsSeparated (pullback.snd g₀ (base B R)) := by
    have h : IsSeparated (hCart.isoPullback.hom ≫ pullback.snd g₀ (base B R)) :=
      hCart.isoPullback_hom_snd.symm ▸ (inferInstance : IsSeparated g)
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated)
      hCart.isoPullback.hom _).mp h
  obtain ⟨C, hC, _, hSep⟩ :=
    AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := R) g₀ ∅
  let _ := hSep
  let : Algebra.FiniteType (ULift.{u} ℤ) B := (Subalgebra.fg_iff_finiteType B).mp hB
  let : Algebra.FiniteType B C := (Subalgebra.fg_iff_finiteType C).mp hC
  let : Algebra.FiniteType (ULift.{u} ℤ) C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  let : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing (ULift.{u} ℤ) C
  have hBase : base C R ≫ base B C = base B R := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let g₁ := pullback.snd g₀ (base B C)
  have hOver : a₀ ≫ g₀ = (g ≫ base C R) ≫ base B C := by
    rw [Category.assoc, hBase, hCart.w]
  let d := pullback.lift a₀ (g ≫ base C R) hOver
  have hd : IsPullback d g g₁ (base C R) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst g₀ (base B C)) (v₁₃ := g₀)
      (h₂₂ := base B C) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    change IsPullback (pullback.lift _ _ _ ≫ pullback.fst _ _) g g₀ (base C R ≫ base B C)
    rwa [pullback.lift_fst, hBase]
  let : QuasiCompact g₁ := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ hqc
  let : LocallyOfFinitePresentation g₁ :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ hfp
  exact of_noetherian_model f g₁ (a ≫ hd.isoPullback.hom)
    (by rw [Category.assoc, hd.isoPullback_hom_snd, ha])

end PhilipponProperEnvelope

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of R)) (a : X ⟶ Y),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion a ∧ a ≫ g = f := by
  obtain ⟨Y, g, a, hg, hfp, hqc, ha, hOver⟩ := AlgebraicGeometry.Scheme.exists_separated_finitePresentation_envelope f
  let _ := hg
  let _ := hfp
  let _ := hqc
  let _ := ha
  exact PhilipponProperEnvelope.of_separated_envelope f g a hOver

end

end
