-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineRefinement
-- name    : ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineRefinement
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:07.383911+00:00
-- url     : https://prove2.me/theorems/6d18e2e4-f6f0-57d2-aac1-fe630e2eca0f
-- title:
--   Pointwise refinement of an open-immersion cover of an affine scheme by basic opens
-- statement:
--   Let $X$ be an affine scheme and $(f_i : Y_i \to X)_{i \in \iota}$ a family of open immersions whose images cover $X$.
--
--   Principal results:
--   1. There are functions $i : X \to \iota$ and $g : X \to \Gamma(X, \mathcal O_X)$ such that, for every point $x \in X$,
--   $$x \in D(g(x)) \quad\text{and}\quad D(g(x)) \subseteq f_{i(x)}(Y_{i(x)}).$$
--   Here $D(g)$ denotes the basic open set where $g$ does not vanish.
--   2. Moreover, for each $x$ there is a morphism of schemes $e_x : D(g(x)) \to Y_{i(x)}$ with $f_{i(x)} \circ e_x$ equal to the open inclusion $D(g(x)) \hookrightarrow X$, together with $x \in D(g(x))$.
--
--   This lets one refine open covers of affine schemes by standard (basic open) covers, which is needed when comparing topologies on affine sites.
--
--   **Formalization Note** The lemmas are `AlgebraicGeometry.exists_basicOpen_refinement_of_isAffine_cover` and `AlgebraicGeometry.exists_basicOpen_lift_of_isAffine_cover`, for `X : Scheme.{u}` with `[IsAffine X]` and an arbitrary index type. The covering hypothesis is `⋃ i, Set.range (f i).base = Set.univ`, and containment is stated as `X.basicOpen (g x) ≤ (f (i x)).opensRange`. The choices are given as functions of the point, with no finiteness asserted.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/Sites/AffineRefinement.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Basic-open refinement of an open-immersion cover of an affine scheme

Given an affine scheme `X` covered by a family of open immersions `f i : Y i ⟶ X`,
this file produces a pointwise refinement by basic opens of `X`: for every `x : X`
there is an index `i x` and a global section `g x : Γ(X, ⊤)` such that
`x ∈ D(g x)` and `D(g x)` factors through `f (i x)`.

The variant `exists_basicOpen_lift_of_isAffine_cover` additionally packages the
inclusions `D(g x) ⟶ Y (i x)` as morphisms of schemes.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Pointwise basic-open refinement of an open-immersion cover of an affine scheme.

Given an affine scheme `X` and an open-immersion family `f i : Y i ⟶ X` whose
ranges cover `X`, for each point `x : X` we extract an index `i x : ι` (a chart
containing `x`) and a global section `g x : Γ(X, ⊤)` whose basic open `D(g x)`
contains `x` and is contained in the range of `f (i x)`. -/
lemma exists_basicOpen_refinement_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, X.basicOpen (g x) ≤ (f (i x)).opensRange) := by
  choose i hi using fun x : X ↦ show ∃ j, x ∈ (f j).opensRange by
    have hx : x ∈ ⋃ j, Set.range (f j).base := hcov ▸ Set.mem_univ _
    obtain ⟨_, ⟨j, rfl⟩, hxj⟩ := hx
    exact ⟨j, hxj⟩
  choose g hle hg using fun x : X ↦
    (isAffineOpen_top X).exists_basicOpen_le (V := (f (i x)).opensRange) ⟨x, hi x⟩ trivial
  exact ⟨i, g, hg, hle⟩

/-- Variant of `exists_basicOpen_refinement_of_isAffine_cover` packaging the basic
opens as `Scheme` morphisms factoring through the cover: for each `x : X` we
get a lift `e x : D(g x) ⟶ Y (i x)` satisfying `e x ≫ f (i x) = (D(g x)).ι`. -/
lemma exists_basicOpen_lift_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤))
      (e : ∀ x, (X.basicOpen (g x) : Scheme) ⟶ Y (i x)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, e x ≫ f (i x) = (X.basicOpen (g x)).ι) := by
  obtain ⟨i, g, hmem, hle⟩ :=
    exists_basicOpen_refinement_of_isAffine_cover f hcov
  refine ⟨i, g, fun x ↦ IsOpenImmersion.lift (f (i x)) (X.basicOpen (g x)).ι ?_, hmem,
    fun x ↦ IsOpenImmersion.lift_fac (f (i x)) (X.basicOpen (g x)).ι _⟩
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
  exact_mod_cast hle x

end AlgebraicGeometry


