-- Prove2me | Definitions.Def_WeilConjectures_Etale_Pullback
-- name    : WeilConjectures_Etale_Pullback
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:55:28.399301+00:00
-- url     : https://prove2.me/theorems/426a21ff-9f86-45df-a209-480a7def7d54
-- title:
--   Pullback on étale cohomology with constant coefficients, $g^*\colon H^i(X,A)\to H^i(Y,A)$
-- statement:
--   For a scheme $X$ and an abelian group $A$, $\underline A_X$ denotes the constant étale sheaf with value $A$. For a morphism $g\colon Y\to X$:
--
--   * the inverse image $g^{-1}$ is additive, and $g^{-1}\underline A_X\cong\underline A_Y$;
--   * the **pullback** $g^*\colon H^i(X_{\mathrm{et}},A)\to H^i(Y_{\mathrm{et}},A)$ is the homomorphism induced on $\operatorname{Ext}^i(\underline{\mathbb Z},-)$ by the exact functor $g^{-1}$, followed by this identification;
--   * $g^*$ is natural in the coefficient group $A$.
-- source:
--   The Stacks Project, Chapter 59 (Étale Cohomology), Section 59.50 (Étale cohomology) and Section 59.36 (Inverse image); E. Freitag, R. Kiehl, Étale Cohomology and the Weil Conjecture, Chapter I.

import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_ConstantPullback
import Definitions.Def_FiniteFields_Etale_ExactPullback
import Definitions.Def_FiniteFields_Etale_FiniteCoefficients
import Definitions.Def_FiniteFields_Etale_Functoriality
import Definitions.Def_FiniteFields_Etale_Sites

noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian AlgebraicGeometry FiniteFields.Etale

namespace WeilConjectures.Etale

universe u

set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Le faisceau constant de valeur `A` sur le petit site étale. -/
abbrev const (X : Scheme.{u}) (A : Ab.{u + 1}) : SmallEtaleAbelianSheaf X :=
  (constantSheaf (smallEtaleSiteTopology X) Ab.{u + 1}).obj A

/-- `g^*` est additif (exact à droite). -/
instance pullback_additive : (smallEtalePullback g).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ (by
    simp only [rightExactFunctor_iff]
    infer_instance)

/-- `g^* (A_X) ≅ A_Y`. -/
def constIso (A : Ab.{u + 1}) : (smallEtalePullback g).obj (const X A) ≅ const Y A :=
  (smallEtalePullbackConstantIso g).app A

/-- **D3.** `g^* : Hⁱ(X, A) →+ Hⁱ(Y, A)`. -/
def pullbackH (A : Ab.{u + 1}) (i : ℕ) :
    SmallEtaleCohomology X (const X A) i →+ SmallEtaleCohomology Y (const Y A) i where
  toFun e := (Ext.mk₀ (constIso g (AddCommGrpCat.of (ULift ℤ))).inv).comp
    ((Ext.mapExactFunctor (smallEtalePullback g) (e : Ext _ _ i)).comp (Ext.mk₀ (constIso g A).hom) (add_zero i))
    (zero_add i)
  map_zero' := by simp [Ext.mapExactFunctor_zero]
  map_add' a b := by simp [Ext.mapExactFunctor_add, Ext.add_comp, Ext.comp_add]

/-- **Naturalité en les coefficients** : `g^*` commute à `H.map` d'un morphisme de groupes. -/
theorem pullbackH_naturality {A B : Ab.{u + 1}} (φ : A ⟶ B) (i : ℕ)
    (e : SmallEtaleCohomology X (const X A) i) :
    pullbackH g B i (Sheaf.H.map ((constantSheaf _ _).map φ) i e) =
      Sheaf.H.map ((constantSheaf _ _).map φ) i (pullbackH g A i e) := by
  have hnat := (smallEtalePullbackConstantIso g).hom.naturality φ
  simp only [Functor.comp_map] at hnat
  simp only [pullbackH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, constIso, Iso.app_hom]
  rw [hnat]

end WeilConjectures.Etale


