-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CochainNextIso_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CochainNextIso_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:46.080096+00:00
-- url     : https://prove2.me/theorems/e499576a-ddea-450d-a831-3a422afabf62
-- title:
--   Cochain Next Iso — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for cochain next iso used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Assemble successor differential squares while all cochain objects are
--   abstract. This prevents concrete scalar-view reductions in shape proofs.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CochainNextIso.lean, selected declarations in lines 11–26; source SHA-256 1a8fa5b42363582555235c8a2ec4e47d2ae5e60ef21abf1ed9974f6af87f6506; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.HomologicalComplex

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u v

/-- Assemble successor differential squares while all cochain objects are
abstract. This prevents concrete scalar-view reductions in shape proofs. -/
noncomputable def cochainNextIso {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X Y : ℕ → C) (dX : ∀ p, X p ⟶ X (p + 1)) (dY : ∀ p, Y p ⟶ Y (p + 1))
    (hX : ∀ p, dX p ≫ dX (p + 1) = 0) (hY : ∀ p, dY p ≫ dY (p + 1) = 0)
    (E : ∀ p, X p ≅ Y p)
    (hE : ∀ p, (E p).hom ≫ dY p = dX p ≫ (E (p + 1)).hom) :
    CochainComplex.of X dX hX ≅ CochainComplex.of Y dY hY := by
  refine HomologicalComplex.Hom.isoOfComponents E ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  change (E p).hom ≫ CochainComplex.of.d Y dY p (p + 1) =
    CochainComplex.of.d X dX p (p + 1) ≫ (E (p + 1)).hom
  rw [CochainComplex.of_d, CochainComplex.of_d]
  exact hE p

end LPCA


