-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_PolynomialFieldIsoUpgrade_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:59.133741+00:00
-- url     : https://prove2.me/theorems/9a8a924b-d307-42e0-8afa-351add0a2ba8
-- title:
--   Polynomial Field Iso Upgrade — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for polynomial field iso upgrade used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Upgrade an existing field comparison using intertwining squares for
--   the original native polynomial actions on both sides.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_PolynomialFieldIsoUpgrade.lean, selected declarations in lines 17–58; source SHA-256 feddd4407b175e272a0d5d88cc12c1ed1cc31ca83621e60f13aabd651a997ff6; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Definitions.Def_LPCA_Solutions_LPCA_ModuleSquareEvaluation_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_PolynomialLinearity_SixOne20261024_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable (k W : Type u) [CommRing k]

noncomputable def polynomialVariableFieldHom (M : ModuleCat.{u} (MvPolynomial W k)) (j : W) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M ⟶
      (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M :=
  (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).map
    (ModuleCat.ofHom (R := MvPolynomial W k) (X := M) (Y := M)
      (LinearMap.lsmul (MvPolynomial W k) M (MvPolynomial.X j)))

/-- Upgrade an existing field comparison using intertwining squares for
the original native polynomial actions on both sides. -/
noncomputable def polynomialFieldIsoUpgrade
    (M N : ModuleCat.{u} (MvPolynomial W k)) (P Q : ModuleCat.{u} k)
    (α : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj M ≅ P)
    (β : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial W k)).obj N ≅ Q)
    (E : P ≅ Q) (vP : W → (P ⟶ P)) (vQ : W → (Q ⟶ Q))
    (hα : ∀ j, polynomialVariableFieldHom k W M j ≫ α.hom = α.hom ≫ vP j)
    (hβ : ∀ j, polynomialVariableFieldHom k W N j ≫ β.hom = β.hom ≫ vQ j)
    (hE : ∀ j, E.hom ≫ vQ j = vP j ≫ E.hom) : M ≅ N := by
  let e := α ≪≫ E ≪≫ β.symm
  have hv : ∀ j, polynomialVariableFieldHom k W M j ≫ e.hom =
      e.hom ≫ polynomialVariableFieldHom k W N j := by
    intro j
    have hb : vQ j ≫ β.inv = β.inv ≫ polynomialVariableFieldHom k W N j := by
      apply (cancel_mono β.hom).mp
      simp only [Category.assoc, β.inv_hom_id, Category.comp_id]
      rw [hβ j, β.inv_hom_id_assoc]
    change polynomialVariableFieldHom k W M j ≫ α.hom ≫ E.hom ≫ β.inv =
      (α.hom ≫ E.hom ≫ β.inv) ≫ polynomialVariableFieldHom k W N j
    calc
      _ = (polynomialVariableFieldHom k W M j ≫ α.hom) ≫ E.hom ≫ β.inv := by
        simp only [Category.assoc]
      _ = (α.hom ≫ vP j) ≫ E.hom ≫ β.inv := by rw [hα j]
      _ = α.hom ≫ (vP j ≫ E.hom) ≫ β.inv := by simp only [Category.assoc]
      _ = α.hom ≫ (E.hom ≫ vQ j) ≫ β.inv := by rw [← hE j]
      _ = α.hom ≫ E.hom ≫ (vQ j ≫ β.inv) := by simp only [Category.assoc]
      _ = α.hom ≫ E.hom ≫ β.inv ≫ polynomialVariableFieldHom k W N j := by rw [hb]
      _ = _ := by simp only [Category.assoc]
  exact (polynomialLinearEquivOfGenerators (k := k) (W := W) (M := M) (N := N)
    e.toLinearEquiv.toAddEquiv
    (fun a x => e.toLinearEquiv.map_smul a x)
    (fun j x => by
      have h := moduleSquare_apply k _ _ _ _ _ _ _ _ (hv j) x
      exact h)).toModuleIso

end LPCA


