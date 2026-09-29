-- Prove2me | solution 1 for AlgebraicGeometry.irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a573f726-fc2b-537f-808d-7d6e52f278ed

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one.AlgebraicGeometry TopologicalSpace Topology"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian LocallyOfFiniteType.isLocallyNoetherian QuasiCompact IsLocallyNoetherian.quasiSeparatedSpace LocallyOfFiniteType Spec Spec.map Scheme Spec.map_surjective QuasiCompact.compactSpace_of_compactSpace Scheme.stalkClosedPointTo Spec.map_injective Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField locallyOfFiniteType_of_comp Spec.map_id quasiCompact_of_noetherianSpace_source IsNoetherian Scheme.residueFieldCongr_fromSpecResidueField LocallyOfFinitePresentation.iff_locallyOfFiniteType LocallyOfFinitePresentation IsNoetherian.noetherianSpace Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton jacobsonSpace_of_locallyOfFiniteType isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType"
namespace TopIrredAux
p2m_open "AlgebraicGeometry"

section Sections

variable {k : Type u} [Field k]

theorem hom_eq_of_retraction {Y : Scheme.{u}} (y : Y) (ι : CommRingCat.of k ⟶ Y.residueField y)
    (φ ψ : Y.residueField y ⟶ CommRingCat.of k)
    (hφ : ι ≫ φ = 𝟙 _) (hψ : ι ≫ ψ = 𝟙 _) : φ = ψ := by
  have hφ' : ∀ b, φ.hom (ι.hom b) = b := fun b => by
    have := congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f.hom b) hφ
    simpa using this
  have hψ' : ∀ b, ψ.hom (ι.hom b) = b := fun b => by
    have := congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f.hom b) hψ
    simpa using this
  have hinj : Function.Injective φ.hom := φ.hom.injective
  have hsurj : ∀ a, ι.hom (φ.hom a) = a := fun a => hinj (by rw [hφ'])
  ext a
  rw [← hsurj a, hφ', hψ']

theorem section_eq_of_base_eq {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of k))
    (s₁ s₂ : Spec (CommRingCat.of k) ⟶ Y) (h₁ : s₁ ≫ fY = 𝟙 _) (h₂ : s₂ ≫ fY = 𝟙 _)
    (hpt : s₁.base (IsLocalRing.closedPoint k) = s₂.base (IsLocalRing.closedPoint k)) : s₁ = s₂ := by
  set y := s₁.base (IsLocalRing.closedPoint k) with hy
  set φ₁ : Y.residueField y ⟶ CommRingCat.of k := Y.descResidueField (Scheme.stalkClosedPointTo s₁) with hφ₁
  set φ₂ : Y.residueField y ⟶ CommRingCat.of k :=
    (Y.residueFieldCongr hpt).hom ≫ Y.descResidueField (Scheme.stalkClosedPointTo s₂) with hφ₂
  have hs₁ : Spec.map φ₁ ≫ Y.fromSpecResidueField y = s₁ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y s₁
  have hs₂ : Spec.map φ₂ ≫ Y.fromSpecResidueField y = s₂ := by
    rw [hφ₂, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y s₂
  obtain ⟨ι, hι⟩ := Spec.map_surjective (Y.fromSpecResidueField y ≫ fY)
  have key : ∀ φ : Y.residueField y ⟶ CommRingCat.of k, Spec.map φ ≫ Y.fromSpecResidueField y ≫ fY = 𝟙 _ →
      ι ≫ φ = 𝟙 _ := by
    intro φ hφ
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hι]
    exact hφ
  have e : φ₁ = φ₂ :=
    hom_eq_of_retraction y ι φ₁ φ₂ (key φ₁ (by rw [← Category.assoc, hs₁, h₁])) (key φ₂ (by rw [← Category.assoc, hs₂, h₂]))
  rw [← hs₁, ← hs₂, e]

theorem isClosed_singleton_base_of_section {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (s : Spec (CommRingCat.of k) ⟶ Y) (h : s ≫ fY = 𝟙 _) :
    IsClosed ({s.base (IsLocalRing.closedPoint k)} : Set Y) := by
  have : LocallyOfFiniteType (s ≫ fY) := by rw [h]; infer_instance
  have : LocallyOfFiniteType s := locallyOfFiniteType_of_comp s fY
  have hclosed : ∀ p : Spec (CommRingCat.of k), IsClosed ({p} : Set (Spec (CommRingCat.of k))) := fun p => by
    have : ({p} : Set (Spec (CommRingCat.of k))) = Set.univ := Set.eq_univ_of_forall fun q => Subsingleton.elim q p
    rw [this]; exact isClosed_univ
  exact AlgebraicGeometry.isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType s fY
    (hclosed _) (hclosed _)

theorem exists_section_of_isClosed [IsAlgClosed k] {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) :
    ∃ s : Spec (CommRingCat.of k) ⟶ Y, s ≫ fY = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint k) = y := by
  obtain ⟨z, hz, hzy⟩ := AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton fY k y hy
  refine ⟨z, ?_, hzy⟩
  rw [hz, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

end Sections

section Topology

variable {T Y : Type u} [TopologicalSpace T] [TopologicalSpace Y]

private theorem _root_.Set.Finite.isClosed_of_subset_closedPoints' {s : Set T} (hs : s.Finite) (h : s ⊆ closedPoints T) :
    IsClosed s := by
  have : s = ⋃ x ∈ s, {x} := (Set.biUnion_of_singleton s).symm
  rw [this]
  exact hs.isClosed_biUnion fun x hx => h hx

p2m_alias "P2MW.S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one.Set.Finite.isClosed_of_subset_closedPoints'" "Set.Finite.isClosed_of_subset_closedPoints'"

theorem isClopen_singleton_of_isOpen_finite {o : Set T} (ho : IsOpen o) (hfin : o.Finite)
    (hcl : o ⊆ closedPoints T) {c : T} (hc : c ∈ o) : IsClopen ({c} : Set T) := by
  refine ⟨hcl hc, ?_⟩
  have heq : ({c} : Set T) = o \ (o \ {c}) :=
    (Set.diff_diff_cancel_left (Set.singleton_subset_iff.mpr hc)).symm
  rw [heq]
  exact ho.sdiff (Set.Finite.isClosed_of_subset_closedPoints' hfin.diff (fun x hx => hcl hx.1))

theorem infinite_inter_closedPoints_of_isOpen [JacobsonSpace T] (hT : ∀ c : T, IsClopen ({c} : Set T) → False)
    {o : Set T} (ho : IsOpen o) (hne : o.Nonempty) : (o ∩ closedPoints T).Infinite := by
  intro hfin
  have hcl : closure o = o ∩ closedPoints T := by
    rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure ho.isLocallyClosed]
    exact (Set.Finite.isClosed_of_subset_closedPoints' hfin Set.inter_subset_right).closure_eq
  have hsub : o ⊆ o ∩ closedPoints T := hcl ▸ subset_closure
  have hofin : o.Finite := hfin.subset hsub
  obtain ⟨c, hc⟩ := hne
  exact hT c (isClopen_singleton_of_isOpen_finite ho hofin (fun x hx => (hsub hx).2) hc)

variable (T) in

def compOpen (C : Set T) : Set T := (⋃₀ (irreducibleComponents T \ {C}))ᶜ

theorem not_mem_of_mem_compOpen {C C' : Set T} (hC' : C' ∈ irreducibleComponents T) (hne : C' ≠ C)
    {x : T} (hx : x ∈ compOpen T C) : x ∉ C' := by
  intro hxC'
  apply hx
  exact ⟨C', ⟨hC', hne⟩, hxC'⟩

theorem isOpen_compOpen (hfin : (irreducibleComponents T).Finite) (C : Set T) : IsOpen (compOpen T C) := by
  unfold compOpen
  rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
  exact hfin.diff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1

theorem compOpen_subset (hfin : (irreducibleComponents T).Finite) {C : Set T} (hC : C ∈ irreducibleComponents T) :
    compOpen T C ⊆ C :=
  subset_closure.trans (closure_sUnion_irreducibleComponents_sdiff_singleton hfin C hC).le

theorem compOpen_nonempty (hfin : (irreducibleComponents T).Finite) {C : Set T} (hC : C ∈ irreducibleComponents T) :
    (compOpen T C).Nonempty := by
  have hZ := closure_sUnion_irreducibleComponents_sdiff_singleton hfin C hC
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  change compOpen T C = ∅ at h
  rw [show closure (⋃₀ (irreducibleComponents T \ {C}))ᶜ = closure (compOpen T C) from rfl, h, closure_empty] at hZ
  exact hC.1.nonempty.ne_empty hZ.symm

theorem irreducibleSpace_of_bijOn_closedPoints [NoetherianSpace T] [JacobsonSpace T] [JacobsonSpace Y]
    (u : T → Y) (hu : Continuous u)
    (hmaps : Set.MapsTo u (closedPoints T) (closedPoints Y))
    (hinj : Set.InjOn u (closedPoints T))
    (hcof : ∀ C : Set T, IsClosed C → (u '' C).Finite ∨ (u '' C)ᶜ.Finite)
    (hT : ∀ c : T, IsClopen ({c} : Set T) → False) [Nonempty T] :
    IrreducibleSpace T := by
  classical
  have hfinC : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents

  have hinf : ∀ C ∈ irreducibleComponents T, (compOpen T C ∩ closedPoints T).Infinite := fun C hC =>
    infinite_inter_closedPoints_of_isOpen hT (isOpen_compOpen hfinC C) (compOpen_nonempty hfinC hC)

  have hcofC : ∀ C ∈ irreducibleComponents T, (u '' C)ᶜ.Finite := by
    intro C hC
    rcases hcof C (isClosed_of_mem_irreducibleComponents C hC) with h | h
    · exfalso
      apply hinf C hC
      refine Set.Finite.of_finite_image (h.subset ?_) (hinj.mono Set.inter_subset_right)
      exact Set.image_mono (Set.inter_subset_left.trans (compOpen_subset hfinC hC))
    · exact h

  have hsubs : ∀ C₁ ∈ irreducibleComponents T, ∀ C₂ ∈ irreducibleComponents T, C₁ = C₂ := by
    intro C₁ hC₁ C₂ hC₂
    by_contra hne

    have hS := hinf C₁ hC₁
    have himg : (u '' (compOpen T C₁ ∩ closedPoints T)).Infinite :=
      hS.image (hinj.mono Set.inter_subset_right)
    obtain ⟨y, ⟨t₁, ht₁S, rfl⟩, hyC₂⟩ := ((himg.diff (hcofC C₂ hC₂)).nonempty)
    simp only [Set.mem_compl_iff, not_not] at hyC₂
    obtain ⟨t, htC₂, hut⟩ := hyC₂
    have hcl_sub : closure ({t} : Set T) ⊆ C₂ :=
      (isClosed_of_mem_irreducibleComponents C₂ hC₂).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr htC₂)
    obtain ⟨t₂, ht₂cl, ht₂c⟩ :=
      nonempty_inter_closedPoints (⟨t, subset_closure rfl⟩ : (closure ({t} : Set T)).Nonempty)
        isClosed_closure.isLocallyClosed
    have hut₂ : u t₂ ∈ closure ({u t} : Set Y) := by
      have := image_closure_subset_closure_image hu ⟨t₂, ht₂cl, rfl⟩
      simpa [Set.image_singleton] using this
    rw [hut, (hmaps ht₁S.2).closure_eq, Set.mem_singleton_iff] at hut₂
    have heq : t₂ = t₁ := hinj ht₂c ht₁S.2 hut₂
    exact not_mem_of_mem_compOpen hC₂ (Ne.symm hne) ht₁S.1 (heq ▸ hcl_sub ht₂cl)

  obtain ⟨x⟩ := (inferInstance : Nonempty T)
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have huniv : irreducibleComponent x = Set.univ := by
    rw [← sUnion_irreducibleComponents (X := T)]
    apply le_antisymm
    · exact Set.subset_sUnion_of_mem hC
    · intro y hy
      obtain ⟨C', hC', hyC'⟩ := hy
      rwa [hsubs C' hC' _ hC] at hyC'
  rw [irreducibleSpace_def]
  have := hC.1
  rw [huniv] at this
  exact this

end Topology

section TopologyFinite

variable {T Y : Type u} [TopologicalSpace T] [TopologicalSpace Y]

theorem irreducibleSpace_of_finite_of_bijOn_closedPoints [Finite T] [JacobsonSpace T] [JacobsonSpace Y]
    [IrreducibleSpace Y] (u : T → Y)
    (hinj : Set.InjOn u (closedPoints T))
    (hsurj : Set.SurjOn u (closedPoints T) (closedPoints Y)) [Nonempty T] :
    IrreducibleSpace T := by
  haveI : DiscreteTopology T := inferInstance
  have hTc : closedPoints T = Set.univ := closedPoints_eq_univ
  have hYfin : (closedPoints Y).Finite := by
    refine (Set.finite_univ.image u).subset ?_
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hsurj hy
    exact ⟨t, Set.mem_univ t, rfl⟩
  haveI : DiscreteTopology Y := JacobsonSpace.discreteTopology hYfin
  have hYsub : ∀ y₁ y₂ : Y, y₁ = y₂ := by
    intro y₁ y₂
    by_contra hne
    obtain ⟨z, hz₁, hz₂⟩ := nonempty_preirreducible_inter (isOpen_discrete {y₁}) (isOpen_discrete {y₂})
      (Set.singleton_nonempty y₁) (Set.singleton_nonempty y₂)
    exact hne ((Set.mem_singleton_iff.mp hz₁).symm.trans (Set.mem_singleton_iff.mp hz₂))
  have hTsub : ∀ t₁ t₂ : T, t₁ = t₂ := fun t₁ t₂ =>
    hinj (hTc.symm ▸ Set.mem_univ t₁) (hTc.symm ▸ Set.mem_univ t₂) (hYsub _ _)
  obtain ⟨x⟩ := (inferInstance : Nonempty T)
  have : (Set.univ : Set T) = {x} := Set.eq_singleton_iff_unique_mem.mpr ⟨Set.mem_univ x, fun t _ => hTsub t x⟩
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set T)
  rw [this]
  exact isIrreducible_singleton

end TopologyFinite

section Curve

variable {Y : Type u} [TopologicalSpace Y]

theorem finite_of_isClosed_ne_univ [IrreducibleSpace Y] [NoetherianSpace Y] [T0Space Y]
    (hdim : topologicalKrullDim Y ≤ 1) {Z : Set Y} (hZ : IsClosed Z) (hne : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine Set.Finite.sUnion hSfin fun t ht => Set.Subsingleton.finite ?_
  have htne : t ≠ Set.univ := by
    intro h; apply hne; exact Set.eq_univ_of_univ_subset (h ▸ Set.subset_sUnion_of_mem ht)

  have hgen : ∀ a ∈ t, closure ({a} : Set Y) = t := by
    intro a ha
    by_contra hca
    have hlt₁ : closure ({a} : Set Y) < t :=
      lt_of_le_of_ne ((hSclosed t ht).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ha)) hca
    have hlt₂ : t < Set.univ := lt_of_le_of_ne (Set.subset_univ _) htne
    let A : IrreducibleCloseds Y := ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds Y := ⟨t, hSirr t ht, hSclosed t ht⟩
    let C : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
    have hAB : A < B := hlt₁
    have hBC : B < C := hlt₂
    let p : LTSeries (IrreducibleCloseds Y) :=
      ((RelSeries.singleton _ A).snoc B (by simpa using hAB)).snoc C (by simpa using hBC)
    have hp : p.length = 2 := rfl
    have := Order.LTSeries.length_le_krullDim p
    rw [hp] at this
    have h2 : (2 : WithBot ℕ∞) ≤ 1 := this.trans hdim
    exact absurd h2 (by decide)
  intro a ha b hb
  have : closure ({a} : Set Y) = closure {b} := (hgen a ha).trans (hgen b hb).symm
  exact (inseparable_iff_closure_eq.mpr this).eq

theorem finite_or_cofinite_of_isConstructible [IrreducibleSpace Y] [NoetherianSpace Y] [T0Space Y]
    (hdim : topologicalKrullDim Y ≤ 1) {s : Set Y} (hs : IsConstructible s) : s.Finite ∨ sᶜ.Finite := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : U = ∅
    · left; rw [h]; exact Set.finite_empty
    · right
      refine finite_of_isClosed_ne_univ hdim hU.isClosed_compl ?_
      intro hc
      apply h
      rw [← compl_compl U, hc, Set.compl_univ]
  | union s _ t _ hs ht =>
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · left; exact hs.union ht
      · right; rw [Set.compl_union]; exact ht.subset Set.inter_subset_right
    · right; rw [Set.compl_union]; exact hs.subset Set.inter_subset_left
  | compl s _ hs =>
    rcases hs with hs | hs
    · right; rwa [compl_compl]
    · left; exact hs

end Curve

end AlgebraicGeometry.TopIrredAux

open AlgebraicGeometry.TopIrredAux

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {T Y : Scheme.{u}}
    (fT : T ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fT] [QuasiCompact fT] [LocallyOfFiniteType fY] [QuasiCompact fY]
    (u : T ⟶ Y) (hu : u ≫ fY = fT)
    [IrreducibleSpace ↑Y] (hdim : topologicalKrullDim ↑Y ≤ 1)
    (hinj : ∀ x₁ x₂ : Spec (CommRingCat.of k) ⟶ T, x₁ ≫ fT = 𝟙 _ → x₂ ≫ fT = 𝟙 _ → x₁ ≫ u = x₂ ≫ u → x₁ = x₂)
    (hsurj : ∀ y : Spec (CommRingCat.of k) ⟶ Y, y ≫ fY = 𝟙 _ → ∃ x : Spec (CommRingCat.of k) ⟶ T, x ≫ fT = 𝟙 _ ∧ x ≫ u = y)
    (hT : ∀ c : ↑T, IsClopen ({c} : Set ↑T) → Finite ↑T) :
    IrreducibleSpace ↑T := by
  classical
  haveI : JacobsonSpace ↑T := AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType fT
  haveI : JacobsonSpace ↑Y := AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType fY
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian fT
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  haveI : CompactSpace ↑T := QuasiCompact.compactSpace_of_compactSpace fT
  haveI : CompactSpace ↑Y := QuasiCompact.compactSpace_of_compactSpace fY
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsNoetherian Y := ⟨⟩
  haveI : NoetherianSpace ↑T := IsNoetherian.noetherianSpace
  haveI : NoetherianSpace ↑Y := IsNoetherian.noetherianSpace
  haveI : QuasiSeparatedSpace ↑T := IsLocallyNoetherian.quasiSeparatedSpace
  haveI : QuasiSeparatedSpace ↑Y := IsLocallyNoetherian.quasiSeparatedSpace
  haveI : QuasiCompact u := quasiCompact_of_noetherianSpace_source u
  haveI : LocallyOfFiniteType u := by
    have : LocallyOfFiniteType (u ≫ fY) := by rw [hu]; infer_instance
    exact locallyOfFiniteType_of_comp u fY
  haveI : LocallyOfFinitePresentation u := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

  have hmaps : Set.MapsTo u.base (closedPoints ↑T) (closedPoints ↑Y) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := exists_section_of_isClosed fT t ht
    have h : (s ≫ u) ≫ fY = 𝟙 _ := by rw [Category.assoc, hu, hs]
    have := isClosed_singleton_base_of_section fY (s ≫ u) h
    simpa using this
  have hinj' : Set.InjOn u.base (closedPoints ↑T) := by
    intro t₁ h₁ t₂ h₂ heq
    obtain ⟨s₁, hs₁, rfl⟩ := exists_section_of_isClosed fT t₁ h₁
    obtain ⟨s₂, hs₂, rfl⟩ := exists_section_of_isClosed fT t₂ h₂
    have e : s₁ ≫ u = s₂ ≫ u :=
      section_eq_of_base_eq fY _ _ (by rw [Category.assoc, hu, hs₁]) (by rw [Category.assoc, hu, hs₂])
        (by simpa using heq)
    rw [hinj s₁ s₂ hs₁ hs₂ e]
  have hsurj' : Set.SurjOn u.base (closedPoints ↑T) (closedPoints ↑Y) := by
    intro y hy
    obtain ⟨sy, hsy, rfl⟩ := exists_section_of_isClosed fY y hy
    obtain ⟨x, hx, hxu⟩ := hsurj sy hsy
    refine ⟨x.base (IsLocalRing.closedPoint k), isClosed_singleton_base_of_section fT x hx, ?_⟩
    rw [← hxu]
    simp
  by_cases hfin : ∃ c : ↑T, IsClopen ({c} : Set ↑T)
  · obtain ⟨c, hc⟩ := hfin
    haveI : Finite ↑T := hT c hc
    haveI : Nonempty ↑T := ⟨c⟩
    exact irreducibleSpace_of_finite_of_bijOn_closedPoints u.base hinj' hsurj'
  · push Not at hfin

    obtain ⟨y, -, hy⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set ↑Y).Nonempty)
      isOpen_univ.isLocallyClosed
    obtain ⟨t, -, -⟩ := hsurj' hy
    haveI : Nonempty ↑T := ⟨t⟩
    have hcof : ∀ C : Set ↑T, IsClosed C → (u.base '' C).Finite ∨ (u.base '' C)ᶜ.Finite := by
      intro C hC
      have hCc : IsConstructible C := by
        rw [← compl_compl C]
        exact (IsCompact.isConstructible (NoetherianSpace.isCompact _) hC.isOpen_compl).compl
      exact finite_or_cofinite_of_isConstructible hdim (u.isConstructible_image hCc)
    exact irreducibleSpace_of_bijOn_closedPoints u.base u.continuous hmaps hinj' hcof hfin

end S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one
end P2MW
export P2MW.S_AlgebraicGeometry_irreducibleSpace_of_bijective_sections_of_topologicalKrullDim_le_one (solution)
