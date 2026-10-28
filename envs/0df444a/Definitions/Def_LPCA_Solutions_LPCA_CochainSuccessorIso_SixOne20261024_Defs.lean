-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_CochainSuccessorIso_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_CochainSuccessorIso_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:54.993534+00:00
-- url     : https://prove2.me/theorems/001a1ce5-151e-4091-8c2d-cd8293cd74b9
-- title:
--   Cochain Successor Iso — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for cochain successor iso used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_CochainSuccessorIso.lean, selected declarations in lines 11–23; source SHA-256 cccf46e336e38b45a91015259a9daf14f832fb00bf5d4255f2e47e4a5b6505c3; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.HomologicalComplex

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable def cochainSuccessorIso {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X Y : CochainComplex C ℕ) (E : ∀ p, X.X p ≅ Y.X p)
    (h : ∀ p, (E p).hom ≫ Y.d p (p + 1) = X.d p (p + 1) ≫ (E (p + 1)).hom) : X ≅ Y := by
  refine HomologicalComplex.Hom.isoOfComponents E ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  exact h p

@[simp] theorem cochainSuccessorIso_hom_f {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X Y : CochainComplex C ℕ) (E : ∀ p, X.X p ≅ Y.X p)
    (h : ∀ p, (E p).hom ≫ Y.d p (p + 1) = X.d p (p + 1) ≫ (E (p + 1)).hom) (p : ℕ) :
    (cochainSuccessorIso X Y E h).hom.f p = (E p).hom := rfl

end LPCA


