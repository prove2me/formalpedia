-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
-- name    : ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:10:17.150908+00:00
-- url     : https://prove2.me/theorems/f58bd1e1-52ff-52cf-8926-66d1ece997d1
-- title:
--   Exactness of short complexes of functors, checked objectwise
-- statement:
--   A short complex in a functor category $J \to C$ is exact if and only if its evaluation at every object of $J$ is exact, under existence hypotheses on limits and colimits in $C$ stated in the file.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/ShortComplex/Exact.lean (declarations kept unchanged, unused ones removed).

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

open Limits

instance {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C]
    [HasLimitsOfShape WalkingParallelPair C] [HasColimitsOfShape WalkingParallelPair C] (j : J) :
    ((evaluation J C).obj j).PreservesHomology where

lemma ShortComplex.exact_iff_evaluation {J : Type*} [Category J] {C : Type*}
    [Category C] [Preadditive C] [HasZeroObject C] [HasLimitsOfShape WalkingParallelPair C]
    [HasColimitsOfShape WalkingParallelPair C] (S : ShortComplex (J ⥤ C)) [S.HasHomology] :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  rw [exact_iff_isZero_homology, Functor.isZero_iff]
  refine forall_congr' fun j ↦ ?_
  let e : S.homology.obj j ≅ _ := (mapHomologyIso S ((evaluation J C).obj j)).symm
  rw [e.isZero_iff, exact_iff_isZero_homology]

end CategoryTheory


