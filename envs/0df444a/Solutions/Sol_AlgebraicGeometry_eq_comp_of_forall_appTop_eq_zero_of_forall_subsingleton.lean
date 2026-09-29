-- Prove2me | solution 1 for AlgebraicGeometry.eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/732a613d-8df0-56f5-8bd5-3b5a3fb6d689

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton.AlgebraicGeometry Opposite"
open Topology TopologicalSpace

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.le_ofIdeals_iff Scheme.Hom pointOfClosedPoint_apply pointOfClosedPoint LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace Scheme.Hom.ideal_ker_le Scheme.IdealSheafData.ker_subschemeι Scheme.Hom.comp_appTop pointOfClosedPoint_comp IsClosedImmersion IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.ker IsAffineOpen Scheme.IdealSheafData.ofIdealTop Scheme.Hom.comp_apply Scheme.IdealSheafData.ofIdealTop_ideal Scheme.IdealSheafData"
namespace ArtinianPointsDetect
p2m_open "AlgebraicGeometry"

section Sections

variable {X Y : Scheme.{u}}

theorem app_res_top (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, ⊤)) :
    (f.app U).hom ((Y.presheaf.map (homOfLE (le_top (a := U))).op).hom s) =
      (X.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ U))).op).hom (f.appTop.hom s) := by
  have h := f.naturality (homOfLE (le_top (a := U))).op
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  rw [h']
  rfl

theorem appTop_eq_zero_of_forall_app (f : X ⟶ Y) (s : Γ(Y, ⊤))
    (h : ∀ U : Y.affineOpens,
      (f.app U.1).hom ((Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s) = 0) :
    f.appTop.hom s = 0 := by

  let V : Y.affineOpens → X.Opens := fun U => f ⁻¹ᵁ U.1
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    obtain ⟨U, hU, hxU⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ f x ∈ U := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
      exact ⟨U, hU, hxU⟩
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf V ⊤ (fun U => homOfLE le_top) hcover
  intro U
  have hU := h U
  rw [app_res_top] at hU
  have h0 : (X.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ U.1))).op).hom 0 = 0 := map_zero _
  exact hU.trans h0.symm

theorem ofIdealTop_le_ker (f : X ⟶ Y) (S : Set Γ(Y, ⊤)) (hS : ∀ s ∈ S, f.appTop.hom s = 0) :
    Scheme.IdealSheafData.ofIdealTop (Ideal.span S) ≤ f.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro s hs
  rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, app_res_top, hS s hs, map_zero]

theorem subschemeι_appTop_eq_zero (S : Set Γ(Y, ⊤)) (s : Γ(Y, ⊤)) (hs : s ∈ S) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span S)).subschemeι.appTop.hom s = 0 := by
  set I := Scheme.IdealSheafData.ofIdealTop (X := Y) (Ideal.span S) with hI
  apply appTop_eq_zero_of_forall_app
  intro U
  have h1 : (Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s ∈ I.ideal U := by
    rw [hI, Scheme.IdealSheafData.ofIdealTop_ideal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hs)
  have h2 : I.ideal U ≤ RingHom.ker (I.subschemeι.app U.1).hom := by
    have h := Scheme.Hom.ideal_ker_le I.subschemeι U
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h2 h1

end Sections

section Main

theorem main
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e := by

  set I := Scheme.IdealSheafData.ofIdealTop (X := Z) (Ideal.span S) with hI
  let Z' : Scheme.{u} := I.subscheme
  let ι' : Z' ⟶ Z := I.subschemeι
  let q' : Z' ⟶ Spec (CommRingCat.of k) := ι' ≫ q
  have hι'S : ∀ s ∈ S, ι'.appTop.hom s = 0 := fun s hs => subschemeι_appTop_eq_zero S s hs
  haveI : JacobsonSpace Z' := LocallyOfFiniteType.jacobsonSpace q'

  have hclosed : ∀ z : Z', IsClosed ({z} : Set Z') → ι' z = e (IsLocalRing.closedPoint k) := by
    intro z hz
    let kz := pointOfClosedPoint q' z hz
    have h1 : (kz ≫ ι') ≫ q = 𝟙 _ := by
      rw [Category.assoc]; exact pointOfClosedPoint_comp q' z hz
    have h2 : ∀ s ∈ S, (kz ≫ ι').appTop.hom s = 0 := by
      intro s hs
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hι'S s hs, map_zero]
    have h3 : kz ≫ ι' = 𝟙 _ ≫ e := hart (𝟙 _) (kz ≫ ι') h1 h2
    rw [Category.id_comp] at h3
    have h4 := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ Z => φ (IsLocalRing.closedPoint k)) h3
    simp only [Scheme.Hom.comp_apply] at h4
    rwa [pointOfClosedPoint_apply] at h4

  haveI : Subsingleton ↥Z' := by
    constructor
    intro z₁ z₂
    have hinj : Function.Injective ι' := ι'.isClosedEmbedding.injective
    have hcp : ∀ c ∈ closedPoints Z', closedPoints Z' = {c} := by
      intro c hc
      ext z
      constructor
      · intro hz
        exact hinj ((hclosed z hz).trans (hclosed c hc).symm)
      · rintro rfl; exact hc
    have hz₁ : z₁ ∈ closure (closedPoints Z') := by rw [closure_closedPoints]; trivial
    have hz₂ : z₂ ∈ closure (closedPoints Z') := by rw [closure_closedPoints]; trivial
    have hne : (closedPoints Z').Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, closure_empty] at hz₁
      exact hz₁
    obtain ⟨c, hc⟩ := hne
    rw [hcp c hc, (mem_closedPoints_iff.mp hc).closure_eq] at hz₁ hz₂
    rw [Set.mem_singleton_iff] at hz₁ hz₂
    rw [hz₁, hz₂]

  have hι' : ι' = q' ≫ e := hart q' ι' rfl hι'S

  have hker : ι'.ker ≤ x.ker := by
    show I.subschemeι.ker ≤ x.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ofIdealTop_le_ker x S hs
  let x' : T ⟶ Z' := IsClosedImmersion.lift ι' x hker
  have hx' : x' ≫ ι' = x := IsClosedImmersion.lift_fac _ _ _
  calc x = x' ≫ ι' := hx'.symm
    _ = x' ≫ q' ≫ e := by rw [← hι']
    _ = (x' ≫ ι') ≫ q ≫ e := by simp only [q', Category.assoc]
    _ = t ≫ e := by rw [hx', ← Category.assoc, hx]

end Main

end AlgebraicGeometry.ArtinianPointsDetect

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e :=
  AlgebraicGeometry.ArtinianPointsDetect.main k q S e hart t x hx hs

end S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
end P2MW
export P2MW.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton (solution)
