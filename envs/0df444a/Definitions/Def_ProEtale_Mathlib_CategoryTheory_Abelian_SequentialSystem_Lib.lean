-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib
-- name    : ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:43.327242+00:00
-- url     : https://prove2.me/theorems/468885e8-5e55-40a0-aaab-7ffd2644dbb8
-- title:
--   Inverse systems indexed by the natural numbers: cones from compatible maps and the extension-by-zero systems
-- statement:
--   This file continues the published file on inverse systems $F\colon \mathbb N^{\mathrm{op}} \to \mathcal C$, whose transition maps are $F(n+1) \to F(n)$. For an object $M$ of a category $\mathcal C$ with zero object and zero morphisms, the published file defines the **extension-by-zero system** $E_n(M)$: it equals $M$ in degrees $k \le n$, with identity transition maps, and $0$ in degrees $k > n$.
--
--   This part provides:
--
--   1. A construction of natural transformations from a constant system: given an object $Z$ and maps $a_n\colon Z \to F(n)$ with $\tau_n \circ a_{n+1} = a_n$ for every $n$, where $\tau_n\colon F(n+1) \to F(n)$ is the transition map, they assemble into a morphism from the constant system on $Z$ to $F$.
--   2. The canonical morphism $\iota\colon E_n(M) \to E_{n+1}(M)$, the identity in degrees $\le n$ and zero above, which is a monomorphism.
--   3. Functoriality of $E_n$ in $M$: a map $h\colon M \to M'$ induces $E_n(h)\colon E_n(M) \to E_n(M')$, which is a monomorphism whenever $h$ is.
--
--   These are the ingredients for the module's main results. Those results, stated in the shared module docstring, are that transition maps of an injective object of the functor category are split epimorphisms and that its components are injective. They are used for derived limits of inverse systems such as $n \mapsto H^m(X_{\mathrm{et}}, \mathbb Z/\ell^n)$.
--
--   **Formalization Note** The declarations are `CategoryTheory.SequentialSystem.natTransOfSucc` (stated with a constant functor `(Functor.const ℕᵒᵖ).obj Z`), `extendSystemι`, `extendSystemMap` and the two `Mono` instances. The hypotheses are `[HasZeroMorphisms C] [HasZeroObject C]` for the extension constructions, and $\mathcal C$ is an arbitrary category `C : Type u` with `Category.{v}`. The split-epimorphism and injectivity results named in the docstring are not part of this file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Abelian/SequentialSystem.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem of the same module.

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Inverse systems indexed by `ℕᵒᵖ`

We study functors `F : ℕᵒᵖ ⥤ C` ("inverse systems") in a category `C` with zero object
and zero morphisms. The *transition maps* of `F` are the maps
`F.obj (op (n + 1)) ⟶ F.obj (op n)`.

The key results concern injective objects of the functor category:

- `CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective`: the transition
  maps of an injective inverse system are split epimorphisms.
- `CategoryTheory.SequentialSystem.injective_obj_of_injective`: the objects of an
  injective inverse system are injective.

Both are proved using the "extension by zero" systems `extendSystem n M`, which take the
value `M` in degrees `≤ n` (with identity transitions) and `0` above, together with the
natural identification `(extendSystem n M ⟶ F) ≃ (M ⟶ F.obj (op n))` and the
monomorphism `extendSystem n M ⟶ extendSystem (n + 1) M`.

We also record stability properties of the class of systems with epimorphic transition
maps.
-/

universe w v v' u u'

open CategoryTheory Limits Opposite

open scoped ZeroObject

namespace CategoryTheory
namespace SequentialSystem

variable {C : Type u} [Category.{v} C]

section Transition


/-- A natural transformation from a constant functor to an inverse system is determined
by components compatible with the successive transition maps. -/
@[simps]
def natTransOfSucc {F : ℕᵒᵖ ⥤ C} {Z : C} (app : ∀ n, Z ⟶ F.obj (op n))
    (h : ∀ n, app (n + 1) ≫ transition F n = app n) :
    (Functor.const ℕᵒᵖ).obj Z ⟶ F where
  app k := app k.unop
  naturality {k k'} f := by
    have key : ∀ (m p : ℕ) (hmp : m ≤ p), app p ≫ F.map (homOfLE hmp).op = app m := by
      intro m p hmp
      induction p with
      | zero =>
        obtain rfl : m = 0 := Nat.le_zero.mp hmp
        rw [Subsingleton.elim (homOfLE hmp) (𝟙 (0 : ℕ)), op_id, F.map_id, Category.comp_id]
      | succ p ih =>
        by_cases hm : m = p + 1
        · subst hm
          rw [Subsingleton.elim (homOfLE hmp) (𝟙 (p + 1 : ℕ)), op_id, F.map_id,
            Category.comp_id]
        · have hmp' : m ≤ p := Nat.lt_succ_iff.mp (lt_of_le_of_ne hmp hm)
          have htr : app (p + 1) ≫ F.map (homOfLE (Nat.le_succ p)).op = app p := h p
          rw [Subsingleton.elim (homOfLE hmp) (homOfLE hmp' ≫ homOfLE (Nat.le_succ p)), op_comp,
            F.map_comp, ← Category.assoc, htr, ih hmp']
    have hf : f = (homOfLE (leOfHom f.unop)).op :=
      f.op_unop.symm.trans (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
    rw [hf]
    exact (Category.id_comp _).trans (key k'.unop k.unop (leOfHom f.unop)).symm


end Transition

section Extend

variable [HasZeroMorphisms C] [HasZeroObject C]


variable (n : ℕ) (M : C) (F : ℕᵒᵖ ⥤ C)


/-- The canonical monomorphism `extendSystem n M ⟶ extendSystem (n + 1) M`. -/
noncomputable def extendSystemι : extendSystem n M ⟶ extendSystem (n + 1) M where
  app k :=
    if h : k.unop ≤ n then
      eqToHom (if_pos h) ≫ eqToHom (if_pos (h.trans (Nat.le_succ n))).symm
    else 0
  naturality := by
    intro k k' f
    have hf := leOfHom f.unop
    dsimp only [extendSystem]
    by_cases h1 : k.unop ≤ n
    · have h2 : k'.unop ≤ n := le_trans hf h1
      have h3 : k.unop ≤ n + 1 := h1.trans (Nat.le_succ n)
      simp [dif_pos h1, dif_pos h2, dif_pos h3]
    · simp [dif_neg h1]

instance inst_MathlibCategoryTheoryAbelianSequentialSystem_L241 : Mono (extendSystemι n M) := by
  haveI : ∀ k, Mono ((extendSystemι n M).app k) := by
    intro k
    by_cases h : k.unop ≤ n
    · have e : (extendSystemι n M).app k =
          eqToHom (if_pos h) ≫ eqToHom (if_pos (h.trans (Nat.le_succ n))).symm := dif_pos h
      rw [e]
      infer_instance
    · exact mono_of_source_iso_zero _ (eqToIso (if_neg h))
  exact NatTrans.mono_of_mono_app _


/-- The functoriality of `extendSystem n` in the object. -/
noncomputable def extendSystemMap {M M' : C} (h : M ⟶ M') :
    extendSystem n M ⟶ extendSystem n M' where
  app k :=
    if hk : k.unop ≤ n then eqToHom (if_pos hk) ≫ h ≫ eqToHom (if_pos hk).symm
    else 0
  naturality := by
    intro k k' f
    have hf := leOfHom f.unop
    dsimp only [extendSystem]
    by_cases h1 : k.unop ≤ n
    · have h2 : k'.unop ≤ n := le_trans hf h1
      simp [dif_pos h1, dif_pos h2]
    · simp [dif_neg h1]

instance inst_MathlibCategoryTheoryAbelianSequentialSystem_L287 {M M' : C} (h : M ⟶ M') [Mono h] : Mono (extendSystemMap n h) := by
  haveI : ∀ k, Mono ((extendSystemMap n h).app k) := by
    intro k
    by_cases hk : k.unop ≤ n
    · have e : (extendSystemMap n h).app k =
          eqToHom (if_pos hk) ≫ h ≫ eqToHom (if_pos hk).symm := dif_pos hk
      rw [e]
      infer_instance
    · exact mono_of_source_iso_zero _ (eqToIso (if_neg hk))
  exact NatTrans.mono_of_mono_app _


end Extend


end SequentialSystem
end CategoryTheory


