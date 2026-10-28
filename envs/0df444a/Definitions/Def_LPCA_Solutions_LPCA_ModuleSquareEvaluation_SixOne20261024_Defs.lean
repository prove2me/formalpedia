-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:44.828985+00:00
-- url     : https://prove2.me/theorems/ff76d0de-1bf9-4e13-90fa-43b3506bae9d
-- title:
--   Module Square Evaluation — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for module square evaluation used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ModuleSquareEvaluation.lean, selected declarations in lines 11–14; source SHA-256 e5b1f0555446d14f2bf429043d15da2a18f6c56981fab40dbdc1e22580b4fb43; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

theorem moduleSquare_apply (R : Type u) [Ring R] (A B C D : ModuleCat.{u} R)
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (i : C ⟶ D)
    (hs : f ≫ g = h ≫ i) (x : A) : g (f x) = i (h x) :=
  congrArg (fun p => p x) hs

end LPCA


