-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Finite
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_Finite
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:43.264936+00:00
-- url     : https://prove2.me/theorems/378b9338-cb7b-5195-9115-0885ead89df3
-- title:
--   The singleton precoverage, its inclusion in the finite precoverage, and stability of finite covers under union
-- statement:
--   For a category $\mathcal C$, the *finite precoverage* declares a presieve on $X$ covering when it consists of finitely many arrows.
--
--   Contents:
--   1. The finite precoverage is stable under unions: the union of two finite covering presieves on $X$ is again covering.
--   2. Definition of the **singleton precoverage**: a presieve on $X$ is covering if it consists of a single morphism $f\colon Y \to X$.
--   3. Every singleton presieve $\{f\}$ is covering for the singleton precoverage.
--   4. The singleton precoverage is contained in the finite precoverage.
--
--   **Formalization Note** The declarations are an instance `(Precoverage.finite C).IsStableUnderSup`, the definition `CategoryTheory.Precoverage.singleton C`, the lemma `Precoverage.singleton_mem_singleton` and `Precoverage.singleton_le_finite` (stated as a `def`, though it is a proof of `≤`).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/Finite.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.Finite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

variable {C : Type*} [Category C]

instance inst_MathlibCategoryTheorySitesFinite_L7 : (Precoverage.finite C).IsStableUnderSup where
  sup_mem_coverings hR hS := hR.union hS

def Precoverage.singleton (C : Type*) [Category* C] : Precoverage C where
  coverings X R := ∃ (Y : C) (f : Y ⟶ X), R = .singleton f

@[simp, grind .]
lemma Precoverage.singleton_mem_singleton {X Y : C} (f : Y ⟶ X) :
    Presieve.singleton f ∈ Precoverage.singleton C X :=
  ⟨_, _, rfl⟩

def Precoverage.singleton_le_finite (C : Type*) [Category* C] :
    Precoverage.singleton C ≤ Precoverage.finite _ :=
  fun X R ⟨Y, f, hf⟩ ↦ by subst hf; simp

end CategoryTheory


