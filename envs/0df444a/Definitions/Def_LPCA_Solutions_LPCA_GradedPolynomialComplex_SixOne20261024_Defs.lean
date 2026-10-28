-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialComplex_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_GradedPolynomialComplex_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:59.949587+00:00
-- url     : https://prove2.me/theorems/a08b798d-24da-4df7-834f-fff4a45f80e2
-- title:
--   Graded Polynomial Complex — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for graded polynomial complex used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Zero maps preserve every specified homogeneous subgroup, so the existing
--   graded polynomial category supports literal cochain complexes.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_GradedPolynomialComplex.lean, selected declarations in lines 16–27; source SHA-256 57a62c00be635583a387b08b67c191da07b5bffc95afe4bec4233636f2033894; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Definitions.Def_LPCA_Solutions_LPCA_GradedPolynomialModuleCat_SixOne20261024_Defs

set_option autoImplicit false

namespace LPCA.GradedPolynomialModule

open CategoryTheory CategoryTheory.Limits

universe u

variable {V W : Type u} [DecidableEq V] [Fintype V] [DecidableEq W]
variable {k : Type u} [Field k] {e : W ↪ V}

/-- Zero maps preserve every specified homogeneous subgroup, so the existing
graded polynomial category supports literal cochain complexes. -/
noncomputable instance : HasZeroMorphisms (GradedPolynomialModule k e) where
  zero A B := ⟨⟨0, fun a x _ => by
    change (0 : B.module) ∈ B.piece a
    exact (B.piece a).zero_mem⟩⟩
  comp_zero {X Y} f Z := by
    apply hom_ext
    exact CategoryTheory.Limits.comp_zero
  zero_comp X {Y Z} f := by
    apply hom_ext
    exact CategoryTheory.Limits.zero_comp





end LPCA.GradedPolynomialModule


