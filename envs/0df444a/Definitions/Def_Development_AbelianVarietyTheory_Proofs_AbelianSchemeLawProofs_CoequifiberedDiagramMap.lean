-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:24.958876+00:00
-- url     : https://prove2.me/theorems/96187f17-97f9-455e-bf54-915fdf4c649f
-- title:
--   Coequifibered Diagram Map
-- statement:
--   Definitions and structural lemmas for Coequifibered Diagram Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoequifiberedDiagramMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
def pullOver (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (U : Y.Opens) :
    Γ(X, f ⁻¹ᵁ U) ⟶ Γ(W, g ⁻¹ᵁ U) :=
  a.appLE _ _ (by rw [← ha]; exact le_rfl)
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
lemma app_pullOver (U : Y.Opens) : f.app U ≫ pullOver f g a ha U = g.app U := by
  subst ha
  rw [pullOver, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE ..
lemma map_pullOver {U V : Y.Opens} (h : U ≤ V) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op ≫ pullOver f g a ha U =
      pullOver f g a ha V ≫ W.presheaf.map (homOfLE (g.preimage_mono h)).op := by
  simp [pullOver]
def invariants (U : Y.Opens) : Subring Γ(X, f ⁻¹ᵁ U) :=
  (pullOver f g a ha U).hom.eqLocus (pullOver f g p hp U).hom
lemma mem_invariants {U : Y.Opens} {x : Γ(X, f ⁻¹ᵁ U)} :
    x ∈ invariants f g a ha p hp U ↔ pullOver f g a ha U x = pullOver f g p hp U x := Iff.rfl
lemma app_mem_invariants {U : Y.Opens} (y : Γ(Y, U)) : f.app U y ∈ invariants f g a ha p hp U := by
  rw [mem_invariants, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, app_pullOver,
    app_pullOver]
lemma map_mem_invariants {U V : Y.Opens} (h : U ≤ V) {x : Γ(X, f ⁻¹ᵁ V)}
    (hx : x ∈ invariants f g a ha p hp V) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op x ∈ invariants f g a ha p hp U := by
  rw [mem_invariants, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, map_pullOver _ _ _ _ h,
    map_pullOver _ _ _ _ h, CommRingCat.comp_apply, CommRingCat.comp_apply,
    (mem_invariants ..).1 hx]
set_option backward.isDefEq.respectTransparency false in

def diagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U := .of (invariants f g a ha p hp U.unop)
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx ↦ map_mem_invariants f g a ha p hp i.unop.le hx)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl
def diagramMap : Y.presheaf ⟶ diagram f g a ha p hp where
  app U := CommRingCat.ofHom ((f.app U.unop).hom.codRestrict (invariants f g a ha p hp U.unop)
    (app_mem_invariants f g a ha p hp))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)
set_option backward.isDefEq.respectTransparency false in
lemma isLocalization_preimage [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens}
    (hU : IsAffineOpen U) (r : Γ(Y, U)) :
    letI := (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
    IsLocalization.Away (f.app U r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
  let : Algebra Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen (f.app _ r)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
  rw! (castMode := .all) [f.preimage_basicOpen r]
  exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage hU.isCompact)
      (f.isQuasiSeparated_preimage hU.isQuasiSeparated) (f.app _ r)
lemma isLocalization_eqLocus {B T B' T' : Type} [CommRing B] [CommRing T] [CommRing B']
    [CommRing T'] [Algebra B B'] [Algebra T T'] (α β : B →+* T) (α' β' : B' →+* T')
    (hα : ∀ x, α' (algebraMap B B' x) = algebraMap T T' (α x))
    (hβ : ∀ x, β' (algebraMap B B' x) = algebraMap T T' (β x))
    (r : α.eqLocus β) [IsLocalization.Away (r : B) B'] [IsLocalization.Away (α r) T']
    [Algebra (α.eqLocus β) (α'.eqLocus β')]
    (h : ∀ x, (algebraMap (α.eqLocus β) (α'.eqLocus β') x : B') = algebraMap B B' x) :
    IsLocalization.Away r (α'.eqLocus β') := by
  have hr : α r = β r := r.2
  refine IsLocalization.Away.mk r ?_ ?_ ?_
  · obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := B') (r : B)).exists_right_inv
    have hT := IsLocalization.Away.algebraMap_isUnit (S := T') (α r)
    have hm : α' u = β' u := by
      apply hT.mul_left_cancel
      have h1 := congr(α' $hu)
      have h2 := congr(β' $hu)
      rw [map_mul, map_one, hα] at h1
      rw [map_mul, map_one, hβ, ← hr] at h2
      rw [h1, h2]
    refine IsUnit.of_mul_eq_one (⟨u, hm⟩ : α'.eqLocus β') (Subtype.ext ?_)
    simpa [h] using hu
  · rintro ⟨z, hz⟩
    obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj (r : B) z
    have hz' : α' z = β' z := hz
    have h1 : algebraMap T T' (α y) = algebraMap T T' (β y) := by
      rw [← hα, ← hβ, ← hy, map_mul, map_mul, map_pow, map_pow, hα, hβ, hr, hz']
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (α r) h1
    refine ⟨m + n, ⟨r ^ m * y, ?_⟩, Subtype.ext ?_⟩
    · change α _ = β _
      rw [map_mul, map_mul, map_pow, map_pow, hm, hr]
    · simp only [h, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ← hy]
      ring
  · intro x y hxy
    have h1 : algebraMap B B' x = algebraMap B B' y := by rw [← h, ← h, hxy]
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (r : B) h1
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false in
lemma coequifibered_diagramMap :
    ((toOpensFunctor Y).op.whiskerLeft (diagramMap f g a ha p hp)).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let := (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  let := (W.presheaf.map (homOfLE (g.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have h1 := isLocalization_preimage f U.2 r
  have h2 := isLocalization_preimage g U.2 r
  rw [← app_pullOver f g a ha] at h2
  exact @isLocalization_eqLocus _ _ _ _ _ _ _ _ _ _ (pullOver f g a ha U.1).hom
    (pullOver f g p hp U.1).hom (pullOver f g a ha (Y.basicOpen r)).hom
    (pullOver f g p hp (Y.basicOpen r)).hom
    (fun x ↦ congr($(map_pullOver f g a ha (Y.basicOpen_le r)) x))
    (fun x ↦ congr($(map_pullOver f g p hp (Y.basicOpen_le r)) x))
    ⟨f.app U.1 r, app_mem_invariants f g a ha p hp r⟩ h1 h2
    ((diagram f g a ha p hp).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra (fun _ ↦ rfl)
def glueData := relativeGluingData (coequifibered_diagramMap f g a ha p hp)
instance : ((glueData f g a ha p hp).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
def quot : Scheme := (glueData f g a ha p hp).glued
def cover : (quot f g a ha p hp).OpenCover := (glueData f g a ha p hp).cover
def invariantsInclusion (U : Y.Opens) :
    (diagram f g a ha p hp).obj (.op U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  CommRingCat.ofHom (invariants f g a ha p hp U).subtype
def toQuotPiece (U : Y.affineOpens) : (f ⁻¹ᵁ U.1).toScheme ⟶ quot f g a ha p hp :=
  (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (invariantsInclusion f g a ha p hp U.1) ≫
    (cover f g a ha p hp).f U
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

def toQuot : X ⟶ quot f g a ha p hp :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦ (pullbackRestrictIsoRestrict f _).hom ≫ toQuotPiece f g a ha p hp U)
    fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Scheme.Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, toQuotPiece, toQuotPiece,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
  dsimp [cover]
  rw [← colimit.w (glueData f g a ha p hp).functor i]
  dsimp [glueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl
def fromQuot : quot f g a ha p hp ⟶ Y := (glueData f g a ha p hp).toBase
set_option backward.isDefEq.respectTransparency false
end GlobalTheory.AffineQuotient


