-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleZariskiSectionGluing
-- name    : AlgebraicGeometry_EtaleZariskiSectionGluing
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T22:25:51.238901+00:00
-- url     : https://prove2.me/theorems/eacc083d-a508-4311-b539-7f805253e5cf
-- title:
--   Gluing étale sections over Zariski open covers
-- statement:
--   Local lifting on Zariski opens and gluing over a closed subset that intersects point closures in connected sets.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponZariskiTorsorCoordinates
universe u
variable {X : Scheme.{u}}

/-- Open subsets form a diagram in the small étale site by open immersions. -/
def opensToEtale (X : Scheme.{u}) : X.Opens ⥤ X.Etale where
  obj U := Scheme.Etale.mk U.ι
  map f := MorphismProperty.Over.homMk (X.homOfLE (leOfHom f))
    (X.homOfLE_ι (leOfHom f))
  map_id U := MorphismProperty.Over.Hom.ext (X.homOfLE_rfl U)
  map_comp f g := MorphismProperty.Over.Hom.ext
    (X.homOfLE_homOfLE (leOfHom f) (leOfHom g)).symm

end PhilipponZariskiTorsorCoordinates

end

section

set_option autoImplicit false

open CategoryTheory Filter Opposite TopologicalSpace
open scoped Topology


namespace PhilipponSpectralClosedSections

universe u

section Topology

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

private abbrev inPatch (V : Set X) : Set (WithConstructibleTopology X) :=
  WithTopology.ofTopology ⁻¹' V

omit [SpectralSpace X] in
private theorem isClopen_inPatch {V : Set X} (hV : IsOpen V) (hVc : IsCompact V) :
    IsClopen (inPatch V) := by
  have hOpen : IsOpen[constructibleTopology X] V :=
    hVc.isOpen_constructibleTopology_of_isOpen hV
  have hCompl : IsOpen[constructibleTopology X] Vᶜ :=
    IsCompact.isOpen_constructibleTopology_of_isClosed (by simpa using hVc) hV.isClosed_compl
  exact ⟨isOpen_compl_iff.mp (WithConstructibleTopology.isOpen_iff.mpr hCompl),
    WithConstructibleTopology.isOpen_iff.mpr hOpen⟩

private theorem isOpen_inPatch {V : Set X} (hV : IsOpen V) : IsOpen (inPatch V) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨U, ⟨hU, hUc⟩, hxU, hUV⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
      (show x.ofTopology ∈ V from hx) hV
  exact ⟨inPatch U, Set.preimage_mono hUV, (isClopen_inPatch hU hUc).2, hxU⟩

private theorem exists_compactOpen_of_not_specializes {x z : X} (h : ¬ x ⤳ z) :
    ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ z ∈ V ∧ x ∉ V := by
  obtain ⟨W, hW, hz, hx⟩ := not_specializes_iff_exists_open.mp h
  obtain ⟨V, ⟨hV, hVc⟩, hzV, hVW⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hz hW
  exact ⟨V, hV, hVc, hzV, fun hxV => hx (hVW hxV)⟩

/-- A constructibly open set stable under generalization is open in the
original spectral topology. -/
theorem isOpen_of_isOpen_constructible {V : Set X}
    (hV : IsOpen (inPatch V))
    (hGen : ∀ {x y : X}, x ⤳ y → y ∈ V → x ∈ V) : IsOpen V := by
  classical
  have hK : IsCompact (inPatch Vᶜ) := hV.isClosed_compl.isCompact
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  have h (y : ↥(Vᶜ)) : ¬ (y : X) ⤳ x := fun h => y.property (hGen h hx)
  choose U hU hUc hxU hyU using fun y : ↥(Vᶜ) => exists_compactOpen_of_not_specializes (h y)
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun y => (inPatch (U y))ᶜ)
    (fun y => (isClopen_inPatch (hU y) (hUc y)).1.isOpen_compl)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y.ofTopology, hy⟩, hyU ⟨y.ofTopology, hy⟩⟩)
  refine ⟨⋂ y ∈ I, U y, ?_, isOpen_biInter_finset (fun y _ => hU y), ?_⟩
  · intro y hy
    by_contra hyV
    have hy' : WithTopology.toTopology (constructibleTopology X) y ∈ inPatch Vᶜ := hyV
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hI hy')
    exact hyz (Set.mem_iInter₂.mp hy z hz)
  · exact Set.mem_iInter₂.mpr fun y _ => hxU y

/-- The set of points having a specialization in a constructibly closed
set is constructibly closed. -/
theorem isClosed_constructible_of_specializes_to {C : Set X}
    (hC : IsClosed (inPatch C)) :
    IsClosed (inPatch {x | ∃ z ∈ C, x ⤳ z}) := by
  classical
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  have hn (z : C) : ¬ x.ofTopology ⤳ (z : X) := fun h => hx ⟨z, z.property, h⟩
  choose U hU hUc hzU hxU using fun z : C => exists_compactOpen_of_not_specializes (hn z)
  obtain ⟨I, hI⟩ := hC.isCompact.elim_finite_subcover (fun z => inPatch (U z))
    (fun z => (isClopen_inPatch (hU z) (hUc z)).2)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z.ofTopology, hz⟩, hzU ⟨z.ofTopology, hz⟩⟩)
  let W := ⋃ z ∈ I, inPatch (U z)
  have hWc : IsClosed W := isClosed_biUnion_finset fun z _ => (isClopen_inPatch (hU z) (hUc z)).1
  refine ⟨Wᶜ, ?_, hWc.isOpen_compl, ?_⟩
  · rintro y hy ⟨z, hz, h⟩
    have hz' : WithTopology.toTopology (constructibleTopology X) z ∈ inPatch C := hz
    obtain ⟨j, hj, hzU⟩ := Set.mem_iUnion₂.mp (hI hz')
    exact hy (Set.mem_iUnion₂.mpr ⟨j, hj, h.mem_open (hU j) hzU⟩)
  · intro hxW
    obtain ⟨z, _, hxz⟩ := Set.mem_iUnion₂.mp hxW
    exact hxU z hxz

end Topology

section Sections

variable {X : TopCat.{u}} [SpectralSpace X]

private abbrev centers (Z : Set X) (x : X) : Set X :=
  {z | z ∈ Z ∧ x ⤳ z}

/-- A locally represented family of germs on a closed subset of a
spectral space extends to a section if its intersection with every
point closure is connected and nonempty. -/
theorem exists_section_of_closed_germs (F : TopCat.Sheaf (Type u) X)
    (Z : Set X) (hZ : IsClosed Z) (hConn : ∀ x : X, IsConnected (centers Z x))
    (s : ∀ z : Z, F.presheaf.stalk z.val)
    (hLocal : ∀ z : Z, ∃ (U : Opens X) (_ : z.val ∈ U) (b : F.presheaf.obj (op U)),
      ∀ (w : Z) (hw : w.val ∈ U), F.presheaf.germ U w.val hw b = s w) :
    ∃ b : F.presheaf.obj (op (⊤ : Opens X)),
      ∀ z : Z, F.presheaf.germ ⊤ z.val (Opens.mem_top _) b = s z := by
  classical
  let P := F.presheaf
  choose z hz using fun x : X => (hConn x).nonempty
  let fromCenter (x : X) (w : centers Z x) : P.stalk x :=
    P.stalkSpecializes w.property.2 (s ⟨w.val, w.property.1⟩)
  let a (x : X) : P.stalk x := fromCenter x ⟨z x, hz x⟩
  have ha (x : X) (w : centers Z x) : fromCenter x w = a x := by
    have : PreconnectedSpace (centers Z x) := isPreconnected_iff_preconnectedSpace.mp (hConn x).2
    suffices h : IsLocallyConstant (fromCenter x) from
      h.apply_eq_of_preconnectedSpace w ⟨z x, hz x⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w'
    obtain ⟨U, hwU, b, hb⟩ := hLocal ⟨w'.val, w'.property.1⟩
    have hxU : x ∈ U := w'.property.2.mem_open U.isOpen hwU
    have hval (v : centers Z x) (hv : v.val ∈ U) :
        fromCenter x v = P.germ U x hxU b := by
      dsimp only [fromCenter]
      rw [← hb ⟨v.val, v.property.1⟩ hv]
      exact ConcreteCategory.congr_hom (P.germ_stalkSpecializes hv v.property.2) b
    filter_upwards [(U.isOpen.preimage continuous_subtype_val).mem_nhds hwU] with v hv
    exact (hval v hv).trans (hval w' hwU).symm
  have haGen {x y : X} (h : x ⤳ y) : P.stalkSpecializes h (a y) = a x := by
    calc
      _ = fromCenter x ⟨z y, (hz y).1, h.trans (hz y).2⟩ :=
        ConcreteCategory.congr_hom (P.stalkSpecializes_comp h (hz y).2) _
      _ = _ := ha x _
  have hOnZ (w : Z) : a w.val = s w := by
    have he : fromCenter w.val ⟨w.val, w.property, specializes_rfl⟩ = a w.val := ha w.val _
    dsimp only [fromCenter] at he
    rw [P.stalkSpecializes_refl] at he
    exact he.symm
  let agrees (V : Opens X) (b : P.obj (op V)) : Set X :=
    {x | ∃ hx : x ∈ V, P.germ V x hx b = a x}
  have hAgrees (V : Opens X) (b : P.obj (op V)) : IsOpen (agrees V b) := by
    apply isOpen_of_isOpen_constructible
    · apply isOpen_iff_forall_mem_open.mpr
      rintro x ⟨hxV, hxb⟩
      let y : X := x.ofTopology
      let C := centers Z y
      have hC : IsCompact C := by
        have he : C = Z ∩ closure ({y} : Set X) := by
          ext v
          simp only [C, centers, Set.mem_ofPred_eq, Set.mem_inter_iff, specializes_iff_mem_closure]
        exact he ▸ (hZ.inter isClosed_closure).isCompact
      choose U hvU c hc using fun v : C => hLocal ⟨v.val, v.property.1⟩
      obtain ⟨I, hI⟩ := hC.elim_finite_subcover (fun v => (U v : Set X)) (fun v => (U v).isOpen)
        (fun v hv => Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hvU ⟨v, hv⟩⟩)
      let hyU (v : C) : y ∈ U v := v.property.2.mem_open (U v).isOpen (hvU v)
      have hcGerm (v : C) : P.germ (U v) y (hyU v) (c v) = P.germ V y hxV b := by
        calc
          _ = fromCenter y v := by
            dsimp only [fromCenter]
            rw [← hc v ⟨v.val, v.property.1⟩ (hvU v)]
            exact (ConcreteCategory.congr_hom
              (P.germ_stalkSpecializes (hvU v) v.property.2) (c v)).symm
          _ = a y := ha y v
          _ = _ := hxb.symm
      choose W hyW iU iV hw using fun v : C => P.germ_eq y (hyU v) hxV (c v) b (hcGerm v)
      let D := ⋃ v ∈ I, (U v : Set X)
      let missing := {p : X | ∃ v ∈ Z \ D, p ⤳ v}
      have hD : IsOpen D := isOpen_iUnion fun v => isOpen_iUnion fun _ => (U v).isOpen
      have hZp : IsClosed (inPatch Z) := by
        simpa only [inPatch, Set.preimage_compl, compl_compl] using
          (isOpen_inPatch hZ.isOpen_compl).isClosed_compl
      have hMissing : IsClosed (inPatch missing) :=
        isClosed_constructible_of_specializes_to (hZp.sdiff (isOpen_inPatch hD))
      let N := (inPatch ((V : Set X) ∩ ⋂ v ∈ I, (W v : Set X))) \ inPatch missing
      refine ⟨N, ?_, (isOpen_inPatch (V.isOpen.inter
        (isOpen_biInter_finset fun v _ => (W v).isOpen))).sdiff hMissing, ?_⟩
      · intro p hp
        have hpV : p.ofTopology ∈ V := hp.1.1
        refine ⟨hpV, ?_⟩
        let q := p.ofTopology
        have hzD : z q ∈ D := by
          by_contra h
          exact hp.2 ⟨z q, ⟨(hz q).1, h⟩, (hz q).2⟩
        obtain ⟨v, hv, hzU⟩ := Set.mem_iUnion₂.mp hzD
        have hpW : q ∈ W v := Set.mem_iInter₂.mp hp.1.2 v hv
        have hpU : q ∈ U v := (iU v).le hpW
        have he := congrArg (fun d => P.germ (W v) q hpW d) (hw v)
        rw [P.germ_res_apply, P.germ_res_apply] at he
        calc
          _ = P.germ (U v) q hpU (c v) := he.symm
          _ = fromCenter q ⟨z q, hz q⟩ := by
            dsimp only [fromCenter]
            rw [← hc v ⟨z q, (hz q).1⟩ hzU]
            exact (ConcreteCategory.congr_hom
              (P.germ_stalkSpecializes hzU (hz q).2) (c v)).symm
          _ = a q := rfl
      · refine ⟨⟨hxV, Set.mem_iInter₂.mpr fun v _ => hyW v⟩, ?_⟩
        rintro ⟨v, ⟨hvZ, hvD⟩, hv⟩
        exact hvD (hI ⟨hvZ, hv⟩)
    · rintro x y h ⟨hyV, hy⟩
      refine ⟨h.mem_open V.isOpen hyV, ?_⟩
      calc
        _ = P.stalkSpecializes h (P.germ V y hyV b) :=
          (ConcreteCategory.congr_hom (P.germ_stalkSpecializes hyV h) b).symm
        _ = a x := hy ▸ haGen h
  choose V hxV b hb using fun x : X => P.exists_germ_eq (a x)
  let W (x : X) : Opens X := ⟨agrees (V x) (b x), hAgrees (V x) (b x)⟩
  let e (x : X) : W x ⟶ V x := homOfLE fun _ h => h.1
  let d (x : X) := P.map (e x).op (b x)
  have hd (x y : X) (hy : y ∈ W x) : P.germ (W x) y hy (d x) = a y := by
    dsimp only [d]
    rw [P.germ_res_apply]
    exact hy.choose_spec
  have hCover : (⊤ : Opens X) ≤ iSup W := fun x _ =>
    Opens.mem_iSup.mpr ⟨x, hxV x, hb x⟩
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top) hCover d (by
    intro x y
    apply TopCat.Presheaf.section_ext F
    intro p hp
    let i₁ : W x ⊓ W y ⟶ W x := homOfLE inf_le_left
    let i₂ : W x ⊓ W y ⟶ W y := homOfLE inf_le_right
    change P.germ (W x ⊓ W y) p hp (P.map i₁.op (d x)) =
      P.germ (W x ⊓ W y) p hp (P.map i₂.op (d y))
    rw [P.germ_res_apply i₁, P.germ_res_apply i₂]
    exact (hd x p hp.1).trans (hd y p hp.2).symm)
  refine ⟨t, fun x => ?_⟩
  have hx : x.val ∈ W x.val := ⟨hxV x.val, hb x.val⟩
  have h := (P.germ_res_apply (homOfLE le_top : W x.val ⟶ ⊤) _ hx t).symm
  rw [ht x.val, hd] at h
  exact h.trans (hOnZ x)

end Sections

section Restriction

variable {X : TopCat.{u}} [SpectralSpace X]

/-- Global sections restrict surjectively to a closed subspace meeting
each point closure in a connected, nonempty subset. -/
theorem surjective_restrict_sections (F : TopCat.Sheaf (Type u) X)
    (Z : Set X) (hZ : IsClosed Z) (hConn : ∀ x : X, IsConnected (centers Z x)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F).hom.app
        (op (⊤ : Opens X))) := by
  classical
  dsimp only
  let Y := TopCat.of Z
  let i : Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P := F.presheaf
  let Q := (TopCat.Presheaf.pullback (Type u) i).obj P
  let J := Opens.grothendieckTopology Y
  let G : TopCat.Sheaf (Type u) Y := (presheafToSheaf J (Type u)).obj Q
  have : (Opens.map i).IsContinuous (Opens.grothendieckTopology X) J :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map i)
      (coverPreserving_opens_map i)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map i)
    (Type u) (Opens.grothendieckTopology X) J
  let η := (adj.unit.app F).hom
  have hUnit := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i) adj F
  have hη : Function.Surjective (η.app (op (⊤ : Opens X))) := by
    have heIso (z : Y) : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) z).map
        (CategoryTheory.toSheafify J Q)) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z (Type u) Q
    let e (z : Y) : P.stalk (i z) ≅ G.presheaf.stalk z :=
      TopCat.Presheaf.stalkPullbackIso (Type u) i P z ≪≫
        @asIso (Type u) _ _ _ ((TopCat.Presheaf.stalkFunctor (Type u) z).map
          (CategoryTheory.toSheafify J Q)) (heIso z)
    have eGerm (V : Opens X) (z : Y) (hz : i z ∈ V) (b : P.obj (op V)) :
        (e z).hom (P.germ V (i z) hz b) =
          G.presheaf.germ ((Opens.map i).obj V) z hz (η.app (op V) b) := by
      let α := CategoryTheory.toSheafify J Q
      let β := (TopCat.Presheaf.stalkFunctor (Type u) z).map α
      let c := ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) i).unit.app P).app (op V) b
      let d := (TopCat.Presheaf.stalkPullbackIso (Type u) i P z).hom
      have h : d (P.germ V (i z) hz b) = Q.germ ((Opens.map i).obj V) z hz c :=
        ConcreteCategory.congr_hom
          (TopCat.Presheaf.germ_stalkPullbackHom (Type u) i P z V hz) b
      change β (d (P.germ V (i z) hz b)) = _
      exact (congrArg (fun v => β v) h).trans
        (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map i).obj V) z hz α c)
    intro a
    change G.presheaf.obj (op ((Opens.map i).obj ⊤)) at a
    let bGerm (z : Z) := (e z).inv (G.presheaf.germ ((Opens.map i).obj ⊤) z trivial a)
    have hLocal (z : Z) :
        ∃ (U : Opens X) (_ : z.val ∈ U) (b : P.obj (op U)),
          ∀ (w : Z) (hw : w.val ∈ U), P.germ U w.val hw b = bGerm w := by
      obtain ⟨V, hzV, b, hb⟩ := P.exists_germ_eq (bGerm z)
      have he : G.presheaf.germ ((Opens.map i).obj V) z hzV (η.app (op V) b) =
          G.presheaf.germ ((Opens.map i).obj ⊤) z trivial a := by
        rw [← eGerm, hb]
        exact ConcreteCategory.congr_hom (e z).inv_hom_id _
      obtain ⟨W, hzW, l, r, hEq⟩ :=
        G.presheaf.germ_eq (U := (Opens.map i).obj V) (V := (Opens.map i).obj ⊤)
          z hzV trivial (η.app (op V) b) a he
      obtain ⟨D, hD, hDW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp W.isOpen
      let U : Opens X := (⟨D, hD⟩ : Opens X) ⊓ V
      let k : U ⟶ V := homOfLE inf_le_right
      have hzD : z.val ∈ D := by
        change z ∈ Subtype.val ⁻¹' D
        rw [hDW]
        exact hzW
      refine ⟨U, ⟨hzD, hzV⟩, P.map k.op b, ?_⟩
      intro w hw
      have hwW : w ∈ W := by
        change w ∈ (W : Set Z)
        rw [← hDW]
        exact hw.1
      have h := congrArg (fun c => G.presheaf.germ W w hwW c) hEq
      apply (ConcreteCategory.bijective_of_isIso (e w).hom).1
      calc
        _ = (e w).hom (P.germ V w.val (k.le hw) b) :=
          congrArg (fun c => (e w).hom c) (P.germ_res_apply k w.val hw b)
        _ = _ := eGerm V w (k.le hw) b
        _ = G.presheaf.germ ((Opens.map i).obj ⊤) w trivial a :=
          (G.presheaf.germ_res_apply l w hwW _).symm.trans
            (h.trans (G.presheaf.germ_res_apply r w hwW a))
        _ = _ := (ConcreteCategory.congr_hom (e w).inv_hom_id _).symm
    obtain ⟨b, hb⟩ := exists_section_of_closed_germs F Z hZ hConn bGerm hLocal
    refine ⟨b, ?_⟩
    apply TopCat.Presheaf.section_ext G
    intro z hz
    calc
      _ = (e z).hom (P.germ ⊤ (i z) hz b) := (eGerm ⊤ z hz b).symm
      _ = (e z).hom (bGerm z) := congrArg (fun c => (e z).hom c) (hb z)
      _ = _ := ConcreteCategory.congr_hom (e z).inv_hom_id _
  intro a
  let E := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).leftAdjointUniq adj
  let ev := (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op (⊤ : Opens X))
  let e := ev.mapIso ((TopCat.Sheaf.pushforward (Type u) i).mapIso (E.app F))
  obtain ⟨b, hb⟩ := hη (e.hom a)
  refine ⟨b, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  exact (congrArg (fun m => m.hom.app (op (⊤ : Opens X)) b) hUnit).trans hb

end Restriction

section LocallyLifted

variable {X : TopCat.{u}} [SpectralSpace X]

/-- A section with local lifts along a closed set has a global lift when
the lift is unique on stalks along the closed set and the target stalks
outside it are trivial. -/
theorem exists_preimage_of_locally_lifted_on_closed {F G : TopCat.Sheaf (Type u) X}
    (η : F ⟶ G) (Z : Set X) (hZ : IsClosed Z)
    (hConn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (hinj : ∀ z : Z, Function.Injective
      ((TopCat.Presheaf.stalkFunctor (Type u) z.val).map η.hom))
    (hzero : ∀ x ∉ Z, Subsingleton (G.presheaf.stalk x))
    (a : G.presheaf.obj (op (⊤ : Opens X)))
    (hloc : ∀ z : Z, ∃ (U : Opens X) (_ : z.val ∈ U) (b : F.presheaf.obj (op U)),
      η.hom.app (op U) b =
        G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a) :
    ∃ b : F.presheaf.obj (op (⊤ : Opens X)), η.hom.app (op (⊤ : Opens X)) b = a := by
  classical
  choose U hzU b hb using hloc
  let s (z : Z) := F.presheaf.germ (U z) z.val (hzU z) (b z)
  let m (x : X) := (TopCat.Presheaf.stalkFunctor (Type u) x).map η.hom
  have hGerm (z w : Z) (hw : w.val ∈ U z) :
      m w.val (F.presheaf.germ (U z) w.val hw (b z)) =
        G.presheaf.germ ⊤ w.val (Opens.mem_top _) a := by
    calc
      _ = G.presheaf.germ (U z) w.val hw (η.hom.app (op (U z)) (b z)) :=
        TopCat.Presheaf.stalkFunctor_map_germ_apply (U z) w.val hw η.hom (b z)
      _ = _ := (congrArg (fun d => G.presheaf.germ (U z) w.val hw d) (hb z)).trans
        (G.presheaf.germ_res_apply (homOfLE le_top) w.val hw a)
  have hc (x : X) : IsConnected (centers Z x) := by
    have he : centers Z x = Z ∩ closure ({x} : Set X) := by
      ext z
      simp only [centers, Set.mem_ofPred_eq, Set.mem_inter_iff, specializes_iff_mem_closure]
    exact he.symm ▸ hConn x
  obtain ⟨d, hd⟩ := exists_section_of_closed_germs F Z hZ hc s (fun z =>
    ⟨U z, hzU z, b z, fun w hw => hinj w ((hGerm z w hw).trans
      (hGerm w w (hzU w)).symm)⟩)
  refine ⟨d, ?_⟩
  apply TopCat.Presheaf.section_ext G
  intro x hx
  by_cases h : x ∈ Z
  · let z : Z := ⟨x, h⟩
    change G.presheaf.germ ⊤ x hx (η.hom.app (op (⊤ : Opens X)) d) =
      G.presheaf.germ ⊤ x hx a
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x hx η.hom d).symm.trans
      ((congrArg (fun c => m x c) (hd z)).trans (hGerm z z (hzU z)))
  · exact (hzero x h).elim _ _

end LocallyLifted

end PhilipponSpectralClosedSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponZariskiTorsorCoordinates (opensToEtale)


namespace PhilipponEtaleZariskiSections

universe u
variable {X : Scheme.{u}}

private abbrev chart (U : X.Opens) := (opensToEtale X).obj U

private def chartImage (V : X.Etale) : X.Opens :=
  ⟨Set.range V.hom, V.hom.isOpenMap.isOpen_range⟩

private theorem chartImage_mono {V W : X.Etale} (g : V ⟶ W) :
    chartImage V ≤ chartImage W := by
  rintro x ⟨y, rfl⟩
  refine ⟨g.left y, ?_⟩
  exact congrArg (fun m : V.left ⟶ X => m y) (MorphismProperty.Over.w g)

private theorem hom_to_chart_ext {V : X.Etale} {U : X.Opens} (g h : V ⟶ chart U) :
    g = h := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono U.ι).mp
  exact (MorphismProperty.Over.w g).trans (MorphismProperty.Over.w h).symm

private def toChart {V : X.Etale} {U : X.Opens} (h : chartImage V ≤ U) : V ⟶ chart U :=
  let hr : Set.range V.hom ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  MorphismProperty.Over.homMk (IsOpenImmersion.lift U.ι V.hom hr)
    (IsOpenImmersion.lift_fac _ _ _)

private def imageFunctor (X : Scheme.{u}) : X.Etale ⥤ X.Opens where
  obj := chartImage
  map g := homOfLE (chartImage_mono g)

/-- The inclusion of Zariski opens into the étale site is right adjoint
to the open image of an étale chart. -/
private def imageAdjunction (X : Scheme.{u}) : imageFunctor X ⊣ opensToEtale X :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun V U => {
      toFun := fun g => toChart g.le
      invFun := fun g => homOfLE (by
        have hg := chartImage_mono g
        change Set.range V.hom ⊆ Set.range U.ι at hg
        rwa [Scheme.Opens.range_ι] at hg)
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => hom_to_chart_ext _ _ }
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => hom_to_chart_ext _ _ }

private theorem opens_coverPreserving (X : Scheme.{u}) :
    CoverPreserving (Opens.grothendieckTopology X)
      X.smallEtaleTopology (opensToEtale X) where
  cover_preserve {U S} hS := by
    rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
      Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨V, g, hg, hx⟩ := hS x.val x.property
    refine Set.mem_iUnion.mpr ⟨⟨Over.mk g, hg⟩, ⟨⟨x.val, hx⟩, ?_⟩⟩
    change (X.homOfLE g.le) ⟨x.val, hx⟩ = x
    exact Subtype.ext (Scheme.homOfLE_apply g.le ⟨x.val, hx⟩)

private instance (X : Scheme.{u}) : (opensToEtale X).IsContinuous
    (Opens.grothendieckTopology X) X.smallEtaleTopology := by
  have : (opensToEtale X).IsRightAdjoint := (imageAdjunction X).isRightAdjoint
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) (opens_coverPreserving X)

/-- Regard an étale abelian sheaf as a sheaf of sets on the Zariski space. -/
def zariskiSections (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ TopCat.Sheaf (Type u) X.carrier :=
  sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u}) ⋙
    (opensToEtale X).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology X) X.smallEtaleTopology

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem sections_map_injective {U V : X.Etale} (g : V ⟶ U)
    (hg : Function.Surjective g.left) (F : Ab X) :
    Function.Injective (F.obj.map g.op) := by
  have hCover := PhilipponEtaleModeledCoverArrow.singleton_cover_of_surjective g hg
  have hF := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat.{u}) F.property
  intro a b hab
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp hF _ hCover).isSeparatedFor.ext
  rintro W _ ⟨T, r, _, ⟨⟩, rfl⟩
  change F.obj.map (r ≫ g).op a = F.obj.map (r ≫ g).op b
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hab]

private def pointOnChart (x : X) (U : X.Opens) (hx : x ∈ U) :
    (geometricPoint x).fiber.obj (chart U) := by
  let s := geometricMap x
  have hrange : Set.range s ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    have hv : v = default := Subsingleton.elim _ _
    change geometricMap x v ∈ U
    rwa [hv, PhilipponEtaleGeometricStalks.geometricMap_apply]
  exact Over.homMk (IsOpenImmersion.lift U.ι s hrange) (IsOpenImmersion.lift_fac _ _ _)

/-- A geometric stalk detects equality of Zariski germs of sections of
an étale sheaf. -/
theorem zariski_germ_eq_of_etale_germ_eq (F : Ab X) (x : X) (U : X.Opens) (hx : x ∈ U)
    (a b : ↥(F.obj.obj (op (chart U))))
    (h : (geometricPoint x).toPresheafFiber (chart U) (pointOnChart x U hx) F.obj a =
      (geometricPoint x).toPresheafFiber (chart U) (pointOnChart x U hx) F.obj b) :
    ((zariskiSections X).obj F).presheaf.germ U x hx a =
      ((zariskiSections X).obj F).presheaf.germ U x hx b := by
  let P := ((zariskiSections X).obj F).presheaf
  let Φ := geometricPoint x
  obtain ⟨V, g, v, _, hV⟩ := (Φ.toPresheafFiber_eq_iff' (chart U) (pointOnChart x U hx) a b).mp h
  let W := chartImage V
  have hWU : W ≤ U := by
    have h := chartImage_mono g
    change Set.range V.hom ⊆ Set.range U.ι at h
    rwa [Scheme.Opens.range_ι] at h
  let l : W ⟶ U := homOfLE hWU
  let r : V ⟶ chart W := toChart le_rfl
  have hr : r ≫ (opensToEtale X).map l = g := hom_to_chart_ext _ _
  have hSurj : Function.Surjective r.left := by
    intro y
    obtain ⟨z, hz⟩ : y.val ∈ Set.range V.hom := y.property
    refine ⟨z, Subtype.ext ?_⟩
    change W.ι (r.left z) = y.val
    exact (congrArg (fun m : V.left ⟶ X => m z) (MorphismProperty.Over.w r)).trans hz
  have hRW : P.map l.op a = P.map l.op b := by
    apply sections_map_injective r hSurj F
    change F.obj.map r.op (F.obj.map ((opensToEtale X).map l).op a) =
      F.obj.map r.op (F.obj.map ((opensToEtale X).map l).op b)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hr]
    exact hV
  let c : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) := default
  have hxW : x ∈ W := by
    refine ⟨v.left c, ?_⟩
    have hv := congrArg (fun m : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ X =>
      m c) (Over.w v)
    exact hv.trans (PhilipponEtaleGeometricStalks.geometricMap_apply x)
  exact (P.germ_res_apply l x hxW a).symm.trans
    ((congrArg (fun d => P.germ W x hxW d) hRW).trans (P.germ_res_apply l x hxW b))

variable {Z : Scheme.{u}} (i : Z ⟶ X)

private abbrev unit (F : Ab X) := (pullbackAdjunction i).unit.app F

private abbrev unitTarget (F : Ab X) := (pushforward i).obj ((pullbackSheaves i).obj F)

set_option maxHeartbeats 1000000 in
/-- Restriction to a closed subscheme is injective on Zariski germs at
points of the closed subscheme. -/
theorem zariski_stalk_unit_injective [IsClosedImmersion i] (F : Ab X)
    (x : X) (hx : x ∈ Set.range i) :
    Function.Injective
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((zariskiSections X).map (unit i F)).hom) := by
  let P := ((zariskiSections X).obj F).presheaf
  let Q := ((zariskiSections X).obj (unitTarget i F)).presheaf
  let η := ((zariskiSections X).map (unit i F)).hom
  intro p q hpq
  obtain ⟨U, hxU, a, rfl⟩ := P.exists_germ_eq p
  obtain ⟨V, hxV, b, rfl⟩ := P.exists_germ_eq q
  have hq : Q.germ U x hxU (η.app (op U) a) = Q.germ V x hxV (η.app (op V) b) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU η a).symm.trans
      (hpq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV η b))
  obtain ⟨W, hxW, f, g, hw⟩ := Q.germ_eq x hxU hxV _ _ hq
  let c := P.map f.op a
  let d := P.map g.op b
  have he : η.app (op W) c = η.app (op W) d :=
    (NatTrans.naturality_apply η f.op a).trans
      (hw.trans (NatTrans.naturality_apply η g.op b).symm)
  have hGeom : geometricMap x default ∈ Set.range i := by
    rwa [PhilipponEtaleGeometricStalks.geometricMap_apply]
  obtain ⟨z, hz⟩ := PhilipponEtaleStalkPullback.exists_point_lift_of_mem_range i (geometricMap x) hGeom
  let Φ := geometricPoint x
  let H (t : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ X) :=
    Function.Injective ((Scheme.pointSmallEtale t).sheafFiber.map (unit i F))
  have hinj : H (geometricMap x) :=
    (congrArg H hz).mp (PhilipponEtaleStalkPullback.stalk_unit_injective i z F)
  let w := pointOnChart x W hxW
  have hEt : Φ.toPresheafFiber (chart W) w F.obj c =
      Φ.toPresheafFiber (chart W) w F.obj d := by
    apply hinj
    change (Φ.presheafFiber.map (unit i F).hom) (Φ.toPresheafFiber (chart W) w F.obj c) =
      (Φ.presheafFiber.map (unit i F).hom) (Φ.toPresheafFiber (chart W) w F.obj d)
    exact (Φ.toPresheafFiber_naturality_apply (unit i F).hom (chart W) w c).trans
      ((congrArg (fun b => Φ.toPresheafFiber (chart W) w (unitTarget i F).obj b) he).trans
        (Φ.toPresheafFiber_naturality_apply (unit i F).hom (chart W) w d).symm)
  exact (P.germ_res_apply f x hxW a).symm.trans
    ((zariski_germ_eq_of_etale_germ_eq F x W hxW c d hEt).trans
      (P.germ_res_apply g x hxW b))

private theorem zariski_pushforward_stalk_subsingleton [IsClosedImmersion i]
    (G : Ab Z) (x : X) (hx : x ∉ Set.range i) :
    Subsingleton (((zariskiSections X).obj ((pushforward i).obj G)).presheaf.stalk x) := by
  let P := ((zariskiSections X).obj ((pushforward i).obj G)).presheaf
  let D : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let zero : P.obj (op (⊤ : X.Opens)) :=
    (0 : ↥(((pushforward i).obj G).obj.obj (op (chart (⊤ : X.Opens)))))
  let e := P.germ ⊤ x (TopologicalSpace.Opens.mem_top x) zero
  suffices h : ∀ p : P.stalk x, p = e from ⟨fun a b => (h a).trans (h b).symm⟩
  intro p
  obtain ⟨U, hxU, a, rfl⟩ := P.exists_germ_eq p
  let W : X.Opens := U ⊓ D
  let l : W ⟶ U := homOfLE inf_le_left
  let r : W ⟶ (⊤ : X.Opens) := homOfLE le_top
  have hxW : x ∈ W := ⟨hxU, hx⟩
  have hEmpty : IsEmpty ((baseChange i).obj (chart W)).left := by
    refine ⟨fun y => ?_⟩
    let z := pullback.fst W.ι i y
    have hc := congrArg (fun m : pullback W.ι i ⟶ X => m y)
      (pullback.condition (f := W.ι) (g := i))
    change W.ι z = i (pullback.snd W.ι i y) at hc
    exact z.property.2 ⟨pullback.snd W.ι i y, hc.symm⟩
  have hSub : Subsingleton (P.obj (op W)) :=
    Scheme.subsingleton_sections_of_isEmpty hEmpty G
  exact (P.germ_res_apply l x hxW a).symm.trans
    ((congrArg (fun c => P.germ W x hxW c) (hSub.elim _ _)).trans
      (P.germ_res_apply r x hxW zero))

private abbrev terminalChart (X : Scheme.{u}) := Scheme.Etale.mk (𝟙 X)

/-- The map from an open chart to the terminal étale chart. -/
def openToTerminal (U : X.Opens) : chart U ⟶ terminalChart X :=
  MorphismProperty.Over.homMk U.ι (Category.comp_id _)

private def topChartIso (X : Scheme.{u}) : chart (⊤ : X.Opens) ≅ terminalChart X :=
  MorphismProperty.Over.isoMk X.topIso (Category.comp_id _)

/-- A closed-subscheme section with Zariski-local lifts has a global
étale lift when the closed subset meets every point closure in a
connected, nonempty set. -/
theorem exists_global_lift_of_open_lifts [IsClosedImmersion i] [SpectralSpace X]
    (F : Ab X)
    (hConn : ∀ x : X, IsConnected (Set.range i ∩ closure ({x} : Set X)))
    (a : ↥((unitTarget i F).obj.obj (op (terminalChart X))))
    (hLocal : ∀ x ∈ Set.range i, ∃ (U : X.Opens) (_ : x ∈ U)
      (b : ↥(F.obj.obj (op (chart U)))),
      (unit i F).hom.app (op (chart U)) b = (unitTarget i F).obj.map (openToTerminal U).op a) :
    ∃ b : ↥(F.obj.obj (op (terminalChart X))), (unit i F).hom.app (op (terminalChart X)) b = a := by
  let P := zariskiSections X
  let η := (P.map (unit i F))
  let G := unitTarget i F
  let e := topChartIso X
  let a' : (P.obj G).presheaf.obj (op (⊤ : X.Opens)) := G.obj.map e.hom.op a
  have hLift (x : Set.range i) :
      ∃ (U : X.Opens) (_ : x.val ∈ U) (b : (P.obj F).presheaf.obj (op U)),
        η.hom.app (op U) b = (P.obj G).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a' := by
    obtain ⟨U, hxU, b, hb⟩ := hLocal x.val x.property
    refine ⟨U, hxU, b, ?_⟩
    let r := (opensToEtale X).map (homOfLE (le_top : U ≤ ⊤))
    have hr : r ≫ e.hom = openToTerminal U := by
      apply MorphismProperty.Over.Hom.ext
      exact X.homOfLE_ι le_top
    change (unit i F).hom.app (op (chart U)) b = G.obj.map r.op (G.obj.map e.hom.op a)
    rw [← Functor.map_comp_apply, ← op_comp, hr]
    exact hb
  have : SpectralSpace X.carrier := inferInstanceAs (SpectralSpace X)
  obtain ⟨d, hd⟩ := PhilipponSpectralClosedSections.exists_preimage_of_locally_lifted_on_closed
    η (Set.range i) i.isClosedEmbedding.isClosed_range hConn
    (fun x => zariski_stalk_unit_injective i F x.val x.property)
    (zariski_pushforward_stalk_subsingleton i ((pullbackSheaves i).obj F)) a' hLift
  have hF : IsIso (F.obj.map e.hom.op) := Functor.map_isIso _ _
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (F.obj.map e.hom.op)).2 d
  refine ⟨b, (ConcreteCategory.bijective_of_isIso (G.obj.map e.hom.op)).1 ?_⟩
  calc
    _ = (unit i F).hom.app (op (chart (⊤ : X.Opens))) (F.obj.map e.hom.op b) :=
      (NatTrans.naturality_apply (unit i F).hom e.hom.op b).symm
    _ = _ := hb.symm ▸ hd

end PhilipponEtaleZariskiSections

end

end


