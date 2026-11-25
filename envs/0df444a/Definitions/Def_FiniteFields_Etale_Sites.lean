-- Prove2me | Definitions.Def_FiniteFields_Etale_Sites
-- name    : FiniteFields_Etale_Sites
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T11:12:11.015878+00:00
-- url     : https://prove2.me/theorems/1b7c97d9-0f78-4369-aba4-8b1ee95dd895
-- title:
--   Small étale and pro-étale sites of a scheme
-- statement:
--   For a scheme $X$, this file fixes the sites used throughout the étale-cohomology layer of the Weil conjectures project.
--
--   * The **small étale site** of $X$ is the category of schemes étale over $X$ (Mathlib's `X.Etale`), with the étale Grothendieck topology (Mathlib's `Scheme.smallEtaleTopology X`).
--   * The **small pro-étale site** of $X$ is the category of schemes weakly étale over $X$ (Mathlib's `X.ProEt`), with its pro-étale topology.
--
--   No new construction is introduced: these are abbreviations for the sites already in Mathlib, so that later files can refer to them by a stable name.
-- source:
--   The Stacks Project, Chapter 59 (Étale Cohomology), Section 59.25 (The étale site); B. Bhatt, P. Scholze, The pro-étale topology for schemes, Astérisque 369 (2015), §4.

import Mathlib.AlgebraicGeometry.Sites.Proetale

open CategoryTheory

namespace FiniteFields.Etale

open AlgebraicGeometry

universe u

/-- The native mathlib category of schemes etale over `X`. -/
abbrev SmallEtaleSite (X : Scheme.{u}) : Type (u + 1) :=
  X.Etale

/-- The native mathlib category of schemes weakly etale over `X`. -/
abbrev ProEtaleSite (X : Scheme.{u}) : Type (u + 1) :=
  X.ProEt

/-- The native Grothendieck topology on the small etale site. -/
abbrev smallEtaleSiteTopology (X : Scheme.{u}) : GrothendieckTopology (SmallEtaleSite X) :=
  Scheme.smallEtaleTopology X

/-- The native Grothendieck topology on the small pro-etale site. -/
abbrev proEtaleSiteTopology (X : Scheme.{u}) : GrothendieckTopology (ProEtaleSite X) :=
  Scheme.ProEt.topology X

















-- Portage v4.33 : option nécessaire avec Mathlib `0df444a` (comme dans `Sites/Etale.lean`).












end FiniteFields.Etale


