-- Prove2me | Definitions.Def_KontsevichHMS_DbCoh
-- name    : KontsevichHMS_DbCoh
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T02:51:06.377501+00:00
-- url     : https://prove2.me/theorems/996944cd-0461-41d0-a8c2-6e752c735068
-- title:
--   $D^b_{\mathrm{coh}}(X)$: bounded complexes with coherent cohomology
-- statement:
--   The B-side of the Homological Mirror Conjecture is the bounded derived category of coherent sheaves $D^b(\mathrm{Coh}\,W)$ on a complex algebraic variety $W$.
--
--   Mathlib provides the abelian category of sheaves of $\mathcal{O}_X$-modules on a scheme $X$ and the derived category of an abelian category, but no abelian category of coherent sheaves. This file therefore uses the standard equivalent description of $D^b(\mathrm{Coh})$ for a scheme: the full subcategory
--
--   $$D^b_{\mathrm{coh}}(X) \subseteq D(\mathcal{O}_X\text{-}\mathrm{Mod})$$
--
--   consisting of those complexes $K$ whose cohomology sheaves $H^n(K)$ vanish for all but finitely many $n$ and are coherent — here taken in the form 'quasi-coherent of finite presentation', which is Mathlib's `IsFinitePresentation` for sheaves of modules and agrees with coherence on a locally noetherian scheme.
--
--   A choice of derived category is fixed once and for all as a scoped instance, so that $D(\mathcal{O}_X\text{-}\mathrm{Mod})$ and its triangulated shift are available for every scheme $X$ without further hypotheses.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, p. 18, section 'Homological Mirror Conjecture'

import Mathlib

/-!
# The bounded derived category with coherent cohomology of a scheme

This is the "B-side" of Kontsevich's Homological Mirror Conjecture
(M. Kontsevich, *Homological algebra of mirror symmetry*, ICM 1994, alg-geom/9411018, p. 18):
the bounded derived category of coherent sheaves `D^b(Coh W)` on a complex algebraic
variety `W`.

Since Mathlib has the abelian category `SheafOfModules` of `O_W`-modules and its derived
category, but no abelian category of coherent sheaves, `D^b(Coh W)` is realised here in the
standard equivalent way, as the full subcategory `D^b_coh(W)` of the derived category of all
`O_W`-modules consisting of the complexes with bounded, coherent (that is, quasi-coherent
and of finite presentation) cohomology sheaves.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace KontsevichHMS

/-- The abelian category of `O_X`-modules on a scheme `X`. -/
abbrev SchemeModules (X : Scheme.{u}) := SheafOfModules.{u} X.ringCatSheaf

/-- A choice of derived category of `O_X`-modules. -/
noncomputable scoped instance hasDerivedCategorySchemeModules (X : Scheme.{u}) :
    HasDerivedCategory.{max u (u + 1)} (SchemeModules X) :=
  HasDerivedCategory.standard _

/-- A complex of `O_X`-modules has bounded coherent cohomology when all but finitely many of
its cohomology sheaves vanish and each of them is quasi-coherent of finite presentation. -/
def IsBoundedCoherent (X : Scheme.{u}) (K : DerivedCategory (SchemeModules X)) : Prop :=
  (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor (SchemeModules X) n).obj K)) ∧
    ∀ n : ℤ, ((DerivedCategory.homologyFunctor (SchemeModules X) n).obj K).IsFinitePresentation

/-- `D^b_coh(X)`: the bounded derived category of coherent sheaves on the scheme `X`,
realised as a full subcategory of the derived category of all `O_X`-modules. -/
abbrev DbCoh (X : Scheme.{u}) := ObjectProperty.FullSubcategory (IsBoundedCoherent X)

end KontsevichHMS


