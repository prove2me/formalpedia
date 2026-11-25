-- Prove2me | Definitions.Def_FiniteFields_Etale_Cohomology
-- name    : FiniteFields_Etale_Cohomology
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:19:04.289886+00:00
-- url     : https://prove2.me/theorems/28e5f135-3347-4470-beac-120eac97d7d6
-- title:
--   Abelian sheaves on the small étale site and their cohomology $H^n(X_{\mathrm{et}},F)$
-- statement:
--   For a scheme $X$ (in universe $u$), an **abelian sheaf on the small étale site** of $X$ is a sheaf of abelian groups (in universe $u+1$) on the site of `FiniteFields_Etale_Sites`; likewise for the pro-étale site. The category of such sheaves is a Grothendieck abelian category (Mathlib's general result for essentially small sites), and the small étale site has a terminal object (the identity of $X$).
--
--   The **étale cohomology** $H^n(X_{\mathrm{et}}, F)$ of an abelian sheaf $F$ is Mathlib's sheaf cohomology `F.H n`, that is $\operatorname{Ext}^n$ from the constant sheaf $\mathbb Z$ to $F$; in degree $0$ it is the group of global sections. This is the right derived functor of the global sections functor.
-- source:
--   The Stacks Project, Chapter 59 (Étale Cohomology), Section 59.50 (Étale cohomology), and Chapter 21 (Cohomology on Sites).

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_FiniteFields_Etale_Sites

noncomputable section

open CategoryTheory

namespace FiniteFields.Etale

open AlgebraicGeometry CategoryTheory.Abelian CategoryTheory.Limits

universe u

/-- Abelian sheaves on the genuine native small etale site of `X`.

The coefficient universe is chosen one level above `X`, matching the universe of morphisms in
`X.Etale` and giving Ext groups in `Type (u + 1)`. -/
abbrev SmallEtaleAbelianSheaf (X : Scheme.{u}) :=
  Sheaf (smallEtaleSiteTopology X) Ab.{u + 1}

/-- Abelian sheaves on the genuine native small pro-etale site of `X`. -/
abbrev ProEtaleAbelianSheaf (X : Scheme.{u}) :=
  Sheaf (proEtaleSiteTopology X) Ab.{u + 1}

/-- The native small-etale abelian-sheaf category is Grothendieck abelian.

This is the general mathlib theorem for an essentially small site, not a separately postulated
cohomological property. -/
instance smallEtaleAbelianSheaf_isGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (SmallEtaleAbelianSheaf X) := by
  have : EssentiallySmall.{u + 1} (SmallEtaleSite X) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (smallEtaleSiteTopology X) Ab.{u + 1}

/-- The native small-pro-etale abelian-sheaf category is Grothendieck abelian. -/
instance proEtaleAbelianSheaf_isGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (ProEtaleAbelianSheaf X) := by
  have : EssentiallySmall.{u + 1} (ProEtaleSite X) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (proEtaleSiteTopology X) Ab.{u + 1}

/-- The identity etale morphism supplies the terminal object needed by degree-zero cohomology.

`Scheme.Etale` is a protected definition, so this explicit bridge makes the generic
`MorphismProperty.Over` terminal instance available without choosing a new site model. -/
noncomputable instance smallEtaleSite_hasTerminal (X : Scheme.{u}) :
    HasTerminal (SmallEtaleSite X) :=
  -- Portage v4.33 : Mathlib `0df444a` fournit directement l'instance sur `X.Etale`.
  inferInstance





/-- Ordinary Ext cohomology of an abelian sheaf on the small etale site. -/
abbrev SmallEtaleCohomology (X : Scheme.{u}) (F : SmallEtaleAbelianSheaf X)
    (n : ℕ) : Type (u + 1) :=
  F.H n















end FiniteFields.Etale


