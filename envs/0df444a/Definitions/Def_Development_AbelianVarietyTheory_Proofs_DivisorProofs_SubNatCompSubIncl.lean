-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:03.416258+00:00
-- url     : https://prove2.me/theorems/d3cb2afc-71d4-4d05-ab9f-7f1a659b845c
-- title:
--   Sub Nat Comp Sub Incl
-- statement:
--   Definitions and structural lemmas for Sub Nat Comp Sub Incl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite
namespace GlobalTheory.QcSub
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
def gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) : Subring (F.obj (op W)) :=
  Subring.closure (Set.range (α.app (op W)).hom ∪ (F.map (homOfLE h).op).hom '' T)
lemma algebraMap_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) (r : Γ(X, W)) :
    (α.app (op W)).hom r ∈ gen F α h T :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)
variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
def sub (W : X.Opens) : Subring (F.obj (op W)) :=
  ⨅ (j : ι) (W' : X.Opens) (_ : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V j),
    (gen F α hV (T j)).comap (F.map (homOfLE hW).op).hom
lemma mem_sub {W : X.Opens} {b : F.obj (op W)} :
    b ∈ sub F α V T W ↔ ∀ (j : ι) (W' : X.Opens), IsAffineOpen W' → ∀ (hW : W' ≤ W)
      (hV : W' ≤ V j), (F.map (homOfLE hW).op).hom b ∈ gen F α hV (T j) := by
  simp only [sub, Subring.mem_iInf, Subring.mem_comap]
lemma algebraMap_mem_sub (W : X.Opens) (r : Γ(X, W)) : (α.app (op W)).hom r ∈ sub F α V T W := by
  rw [mem_sub]
  intro j W' _ hW hV
  have := congr($(α.naturality (homOfLE hW).op).hom r)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _
lemma res_mem_sub {W W₁ : X.Opens} (h : W₁ ≤ W) {b : F.obj (op W)} (hb : b ∈ sub F α V T W) :
    (F.map (homOfLE h).op).hom b ∈ sub F α V T W₁ := by
  rw [mem_sub] at hb ⊢
  intro j W' hW' hW hV
  rw [← CommRingCat.comp_apply, ← F.map_comp]
  exact hb j W' hW' (hW.trans h) hV
def subMap (W : X.Opens) : Γ(X, W) →+* sub F α V T W :=
  (α.app (op W)).hom.codRestrict _ (algebraMap_mem_sub F α V T W)
@[simps obj]
def subFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj W := CommRingCat.of (sub F α V T W.unop.1)
  map {W W₁} f := CommRingCat.ofHom
    ((F.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom.restrict _ _
      (fun _ hb ↦ res_mem_sub F α V T _ hb))
  map_id W := by
    ext b
    change (F.map _).hom b.1 = b.1
    rw [Subsingleton.elim ((Scheme.AffineZariskiSite.toOpensFunctor X).map (𝟙 W).unop).op (𝟙 _)]
    erw [F.map_id]
    rfl
  map_comp {W₁ W₂ W₃} f g := by
    ext b
    change (F.map _).hom b.1 = (F.map _).hom ((F.map _).hom b.1)
    rw [← CommRingCat.comp_apply]
    erw [← F.map_comp]
    rfl
def subNat : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ subFunctor F α V T where
  app W := CommRingCat.ofHom (subMap F α V T W.unop.1)
  naturality {W W₁} f := by
    ext r
    exact Subtype.ext congr($(α.naturality ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom r)
def subIncl : subFunctor F α V T ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F where
  app W := CommRingCat.ofHom (sub F α V T W.unop.1).subtype
  naturality _ _ _ := rfl
end GlobalTheory.QcSub


