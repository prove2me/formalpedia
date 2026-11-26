-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:12:28.28628+00:00
-- url     : https://prove2.me/theorems/164b62ef-313c-5a93-85b0-c96412d4e1dc
-- title:
--   The pro-completion of a morphism property
-- statement:
--   For a morphism property $P$, the property `MorphismProperty.pro P` of morphisms $f : X \to Y$ for which $X$ is the limit of a small cofiltered diagram $(X_j)$ equipped with compatible morphisms $t_j : X_j \to Y$ in $P$, such that $f$ is the composite $X \to X_j \to Y$ for every $j$. It is dual to the ind-completion and contains $P$.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/Ind.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## TODOs:

- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

universe s t w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)


open Opposite


namespace MorphismProperty


lemma ind_coconeι {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    (j : J) (H : ∀ {i : J} (f : j ⟶ i), P (D.map f)) :
    ind.{w} P (c.ι.app j) := by
  refine ⟨Under j, inferInstance, inferInstance, Under.post D ⋙ CategoryTheory.Under.forget _,
      ?_, ?_, ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · exact
      { app i := D.map i.hom
        naturality := by simp [← Functor.map_comp] }
  · exact ((CategoryTheory.Under.forget _).mapCocone (c.underPost j)).ι
  · exact isColimitOfPreserves (CategoryTheory.Under.forget _) (hc.underPost j)
  · apply H
  · simp

variable {P}


/--
Let `P` be a property of morphisms. `P.Pro` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : Xᵢ ⟶ Y` and `sᵢ : X ⟶ Xᵢ` indexed by `J`
such that
- `J` is cofiltered
- `X = lim Xᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = sᵢ ≫ tᵢ` for all `i`.
-/
def pro (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCofiltered J)
    (D : J ⥤ C) (t : D ⟶ (Functor.const J).obj Y) (s : (Functor.const J).obj X ⟶ D)
    (_ : IsLimit (Cone.mk _ s)), ∀ j, P (t.app j) ∧ s.app j ≫ t.app j = f

lemma pro_eq_unop_ind_op : pro.{w} P = (ind.{w} P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, isColimitOfUnop hs, fun j ↦ ⟨(hst j.1).1, by simp [← (hst j.1).2]⟩⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isLimitOfCoconeRightOpOfCone D.leftOp hs, fun j ↦ ⟨(hst _).1,
      op_injective (hst _).2⟩⟩


@[gcongr]
lemma unop_mono {P Q : MorphismProperty Cᵒᵖ} (h : P ≤ Q) : P.unop ≤ Q.unop :=
  fun _ _ _ hf ↦ h _ hf


variable (P) in
lemma le_pro : P ≤ pro.{w} P := by
  rw [pro_eq_unop_ind_op]
  conv_lhs => rw [← unop_op P]
  exact unop_mono P.op.le_ind


lemma pro_coneπ {J : Type w} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c)
    (j : J) (H : ∀ {i : J} (f : i ⟶ j), P (D.map f)) :
    pro.{w} P (c.π.app j) := by
  rw [pro_eq_unop_ind_op]
  exact ind_coconeι P.op hc.op _ (fun _ ↦ H _)


end CategoryTheory.MorphismProperty


