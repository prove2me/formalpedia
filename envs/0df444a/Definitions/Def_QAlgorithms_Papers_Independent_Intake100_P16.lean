-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P16
-- name    : QAlgorithms_Papers_Independent_Intake100_P16
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:18:52.422189+00:00
-- url     : https://prove2.me/theorems/adfbbfb1-3762-4b25-be68-b31568282492
-- title:
--   Definitions for Local Theory for 2-Functors on Path 2-Groupoids
-- statement:
--   The objects the formalized statements of *Local Theory for 2-Functors on Path 2-Groupoids* (arXiv:1303.4663) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `UnitFreeStrongTrans`: Definition A.6, PDF pp.43–44: exactly the invertible naturality cells and axioms T1 and T2, without assuming the unit conclusion of Lemma A.7. Mathlib's compositor has the inverse orientation to the paper's compositor.
--   - `forgetUnit`: Forget only the redundant unit axiom from Mathlib's strong transformations; this is not used as the input type of Lemma A.7. PDF pp.43–45.
--   - `IsNormalized`: Appendix A, PDF p.43, (A.2)–(A.3): identities and every strict inverse pair are preserved, with identity unitors and compositors. HEq expresses the identity 2-cells across the stated equalities of 1-cells; there is no assumption of strict preservation of arbitrary composites. The ill-typed printed id_idX in (A.3) is read as id_idF(X).
--   - `PaperDelooping`: Example A.2, PDF pp.39–40: the 1-cell opposite adapts Mathlib's composition order to the paper's g ∘ f = g tensor f. Two-cell directions are preserved; no braiding or symmetry is assumed.
--   - `IsStrictMonoidal`: Strictness of a monoidal category in Example A.2, PDF pp.39–40: strict tensor associativity and units, with the specified coherence isomorphisms equal to the identity 2-cells after endpoint transport.
-- source:
--   Local Theory for 2-Functors on Path 2-Groupoids, arXiv:1303.4663v1, https://arxiv.org/abs/1303.4663v1

import Mathlib

/-!
Statements from Schreiber–Waldorf, arXiv:1303.4663v1, Appendix A.
The differential-geometric constructions of Sections 2–4 are explicitly deferred
in the accompanying GAPS.json rather than represented by abstract placeholders.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P16

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe uS vS wS uT vT wT uC vC

/-- Definition A.6, PDF pp.43–44: exactly the invertible naturality cells
and axioms T1 and T2, without assuming the unit conclusion of Lemma A.7.
Mathlib's compositor has the inverse orientation to the paper's compositor. -/
structure UnitFreeStrongTrans
    {S : Type uS} [Bicategory.{wS, vS} S]
    {T : Type uT} [Bicategory.{wT, vT} T]
    (F G : Pseudofunctor S T) where
  app (X : S) : F.obj X ⟶ G.obj X
  naturality {X Y : S} (f : X ⟶ Y) : F.map f ≫ app Y ≅ app X ≫ G.map f
  naturality_naturality {X Y : S} {f g : X ⟶ Y} (a : f ⟶ g) :
    F.map₂ a ▷ app Y ≫ (naturality g).hom =
      (naturality f).hom ≫ app X ◁ G.map₂ a
  naturality_comp {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (naturality (f ≫ g)).hom ≫ app X ◁ (G.mapComp f g).hom =
      (F.mapComp f g).hom ▷ app Z ≫ (Bicategory.associator _ _ _).hom ≫
        F.map f ◁ (naturality g).hom ≫ (Bicategory.associator _ _ _).inv ≫
        (naturality f).hom ▷ G.map g ≫ (Bicategory.associator _ _ _).hom

/-- Forget only the redundant unit axiom from Mathlib's strong transformations;
this is not used as the input type of Lemma A.7. PDF pp.43–45. -/
def forgetUnit
    {S : Type uS} [Bicategory.{wS, vS} S]
    {T : Type uT} [Bicategory.{wT, vT} T]
    {F G : Pseudofunctor S T} (r : Pseudofunctor.StrongTrans F G) :
    UnitFreeStrongTrans F G where
  app := r.app
  naturality := r.naturality
  naturality_naturality := r.naturality_naturality
  naturality_comp := r.naturality_comp

/-- The identity transformation has identity object components, including
when the source bicategory has no objects. -/
example {S : Type uS} [Bicategory.{wS, vS} S]
    {T : Type uT} [Bicategory.{wT, vT} T]
    (F : Pseudofunctor S T) (X : S) :
    (forgetUnit (Pseudofunctor.StrongTrans.id F)).app X = 𝟙 (F.obj X) := by
  simp only [forgetUnit, Pseudofunctor.StrongTrans.id]

/-- Appendix A, PDF p.43, (A.2)–(A.3): identities and every strict
inverse pair are preserved, with identity unitors and compositors.
HEq expresses the identity 2-cells across the stated equalities of 1-cells;
there is no assumption of strict preservation of arbitrary composites.
The ill-typed printed id_idX in (A.3) is read as id_idF(X). -/
def IsNormalized
    {S : Type uS} [Bicategory.{wS, vS} S]
    {T : Type uT} [Bicategory.{wT, vT} T]
    (F : Pseudofunctor S T) : Prop :=
  (∀ X : S, F.map (𝟙 X) = 𝟙 (F.obj X)) ∧
  (∀ X : S, HEq (F.mapId X).hom (𝟙 (𝟙 (F.obj X)))) ∧
  (∀ {X Y : S} (f : X ⟶ Y) (g : Y ⟶ X), f ≫ g = 𝟙 X →
    F.map f ≫ F.map g = 𝟙 (F.obj X) ∧
      HEq (F.mapComp f g).hom (𝟙 (𝟙 (F.obj X))))

/-- Sanity check: a strictly preserved identity inverse pair is included in
normalization, rather than only objectwise identity preservation. -/
example {S : Type uS} [Bicategory.{wS, vS} S]
    {T : Type uT} [Bicategory.{wT, vT} T]
    (F : Pseudofunctor S T) (h : IsNormalized F) (X : S)
    (e : (𝟙 X : X ⟶ X) ≫ 𝟙 X = 𝟙 X) :
    F.map (𝟙 X) ≫ F.map (𝟙 X) = 𝟙 (F.obj X) := by
  exact (h.2.2 (𝟙 X) (𝟙 X) e).1

/-- Example A.2, PDF pp.39–40: the 1-cell opposite adapts Mathlib's
composition order to the paper's g ∘ f = g tensor f. Two-cell directions
are preserved; no braiding or symmetry is assumed. -/
abbrev PaperDelooping (C : Type uC) [Category.{vC} C] [MonoidalCategory C] :=
  (MonoidalSingleObj C)ᵒᵖ

/-- The delooping really has a single object. -/
example (C : Type uC) [Category.{vC} C] [MonoidalCategory C] :
    Subsingleton (PaperDelooping C) := by
  change Subsingleton Unitᵒᵖ
  exact ⟨fun a b => congrArg Opposite.op (Subsingleton.elim a.unop b.unop)⟩

/-- The identity at the single object is exactly the tensor unit. -/
example (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    (X : PaperDelooping C) :
    ((𝟙 X : X ⟶ X).unop : C) = 𝟙_ C := by
  rfl

/-- Strictness of a monoidal category in Example A.2, PDF pp.39–40:
strict tensor associativity and units, with the specified coherence
isomorphisms equal to the identity 2-cells after endpoint transport. -/
def IsStrictMonoidal (C : Type uC) [Category.{vC} C] [MonoidalCategory C] : Prop :=
  (∀ X Y Z : C, (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)) ∧
  (∀ X : C, (𝟙_ C) ⊗ X = X) ∧
  (∀ X : C, X ⊗ (𝟙_ C) = X) ∧
  (∀ X Y Z : C, HEq (MonoidalCategory.associator X Y Z).hom (𝟙 ((X ⊗ Y) ⊗ Z))) ∧
  (∀ X : C, HEq (MonoidalCategory.leftUnitor X).hom (𝟙 ((𝟙_ C) ⊗ X))) ∧
  (∀ X : C, HEq (MonoidalCategory.rightUnitor X).hom (𝟙 (X ⊗ (𝟙_ C))))

/-- Strict monoidal left-unit coherence includes the tensor unit itself. -/
example (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    (h : IsStrictMonoidal C) : (𝟙_ C) ⊗ (𝟙_ C) = 𝟙_ C := by
  exact h.2.1 (𝟙_ C)

end QAlgorithms.Papers.Independent.Intake100.P16


