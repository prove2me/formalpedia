-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgradeSquare_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_PolynomialFieldIsoUpgradeSquare_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:19.882957+00:00
-- url     : https://prove2.me/theorems/f901f144-7620-48ad-adfc-9cc34a6c536a
-- title:
--   Polynomial Field Iso Upgrade Square — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for polynomial field iso upgrade square used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_PolynomialFieldIsoUpgradeSquare.lean, selected declarations in lines 13–28; source SHA-256 cc36560207960bc606d47e111b5c9328e951b59863ee17cd9944e50a63f71858; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

theorem polynomialFieldIsoUpgrade_square (k W : Type u) [CommRing k]
    (M N : ModuleCat.{u} (MvPolynomial W k)) (P Q : ModuleCat.{u} k)
    (α : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M ≅ P)
    (β : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj N ≅ Q)
    (E : P ≅ Q) (vP : W → (P ⟶ P)) (vQ : W → (Q ⟶ Q))
    (hα : ∀ j, polynomialVariableFieldHom k W M j ≫ α.hom = α.hom ≫ vP j)
    (hβ : ∀ j, polynomialVariableFieldHom k W N j ≫ β.hom = β.hom ≫ vQ j)
    (hE : ∀ j, E.hom ≫ vQ j = vP j ≫ E.hom) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map
        (polynomialFieldIsoUpgrade k W M N P Q α β E vP vQ hα hβ hE).hom ≫ β.hom =
      α.hom ≫ E.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change β.hom (β.inv (E.hom (α.hom x))) = E.hom (α.hom x)
  exact β.toLinearEquiv.apply_symm_apply _

end LPCA


