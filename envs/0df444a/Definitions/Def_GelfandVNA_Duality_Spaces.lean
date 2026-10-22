-- Prove2me | Definitions.Def_GelfandVNA_Duality_Spaces
-- name    : GelfandVNA_Duality_Spaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:06.999015+00:00
-- url     : https://prove2.me/theorems/75cc2c92-b9f2-427e-bdf1-c63ac7353833
-- title:
--   Def 2.66, p. 20 — hyperstonean spaces and the category HStonean of hyperstonean spaces and open maps
-- statement:
--   A topological space $S$ is **sober** if closure is a bijection from its points to its irreducible closed subsets (Definition 2.7). Write $\Omega(S)$ for the locale of open subsets of $S$.
--
--   A **hyperstonean space** (Definition 2.66 of Pavlov, *Gelfand-type duality for commutative von Neumann algebras*) is a sober space $S$ such that $\Omega(S)$ is a hyperstonean locale (Definition 2.61): $\Omega(S)$ is a Stonean locale and every nonempty open $U\subseteq S$ carries a finite positive normal valuation $\nu\colon\Omega(S)\to[0,\infty)$ with $\nu(U)\neq0$.
--
--   The category **HStonean** is the full subcategory of the category Stonean of Stonean spaces (Definition 2.46), whose morphisms are the **open continuous maps**:
--   $$\mathrm{Hom}_{\mathsf{HStonean}}(S,T)=\{f\colon S\to T \text{ continuous} \mid f(U)\text{ is open for every open }U\}.$$
--   It comes with its forgetful functor to topological spaces.
--
--   This is the topological end of the chain of equivalences of Theorem 1.1; by Dixmier, hyperstonean spaces are exactly the Gelfand spectra of commutative von Neumann algebras.
--
--   **Formalization Note** Sobriety is Mathlib's `QuasiSober` together with `T0Space` (surjectivity and injectivity of the closure map). The hyperstonean condition is stated literally on the frame `TopologicalSpace.Opens S`, using the definitions of the Locales module. The empty space is allowed.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, pp. 9, 15, 20, Definitions 2.7, 2.46, 2.66

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_Locales

namespace GelfandVNA.Duality

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20

universe u

/-- Definition 2.66, p. 20: a hyperstonean space is a sober topological space `S` (Definition 2.7:
closure is a bijection from points to irreducible closed sets, i.e. `QuasiSober` and `T0Space`)
whose locale of opens `Ω(S)` is a hyperstonean locale (Definition 2.61). -/
structure HStonean : Type (u + 1) where
  /-- The underlying topological space. -/
  toTop : TopCat.{u}
  [quasiSober : QuasiSober toTop]
  [t0 : T0Space toTop]
  hyperstonean : IsHyperstoneanLocale (TopologicalSpace.Opens toTop)

attribute [instance] HStonean.quasiSober HStonean.t0

/-- Definitions 2.46 and 2.66, pp. 15, 20: `HStonean` is the full subcategory of `Stonean` on
hyperstonean spaces, and morphisms of `Stonean` are the open continuous maps. -/
instance : Category.{u} HStonean.{u} where
  Hom S T := {f : C(S.toTop, T.toTop) // IsOpenMap f}
  id S := ⟨ContinuousMap.id S.toTop, IsOpenMap.id⟩
  comp f g := ⟨g.1.comp f.1, g.2.comp f.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The forgetful functor `HStonean ⥤ Top`. -/
def HStonean.toTopFunctor : HStonean.{u} ⥤ TopCat.{u} where
  obj S := S.toTop
  map f := TopCat.ofHom f.1
  map_id _ := rfl
  map_comp _ _ := rfl

end GelfandVNA.Duality


