-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Grothendieck
-- name    : ProEtale_Mathlib_CategoryTheory_Sites_Grothendieck
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:58:52.68796+00:00
-- url     : https://prove2.me/theorems/dba0aeb5-f637-48bd-8f0f-e02a75a79842
-- title:
--   Grothendieck topologies: transitivity tested on a generating presieve, and pushforward sieves along isomorphic functors
-- statement:
--   Results:
--
--   1. Let $J$ be a Grothendieck topology on $\mathcal C$, $X$ an object, and $R$ a presieve on $X$ whose generated sieve is $J$-covering. Let $S$ be a sieve on $X$ such that for every morphism $g\colon Y \to X$ in $R$ the pullback $g^*S$ is $J$-covering. Then $S$ is $J$-covering. This is transitivity, checked only on the generators.
--   2. Let $K$ be a Grothendieck topology on $\mathcal D$, and $F_1 \cong F_2\colon \mathcal C \to \mathcal D$ naturally isomorphic functors. If $R$ is a sieve on $U$ in $\mathcal C$ whose pushforward $F_1 R$ is $K$-covering on $F_1(U)$, then $F_2 R$ is $K$-covering on $F_2(U)$. So covering of pushforward sieves depends on the functor only up to natural isomorphism.
--
--   These are used to verify continuity and cover-preservation of functors between sites.
--
--   **Formalization Note** The declarations are `CategoryTheory.GrothendieckTopology.transitive_of_presieve` and `GrothendieckTopology.functorPushforward_mem_of_iso`. Pushforward sieves are `Sieve.functorPushforward`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/Grothendieck.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Sites.Grothendieck

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory

lemma GrothendieckTopology.transitive_of_presieve {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {X : C} (R : Presieve X) (hR : Sieve.generate R ∈ J X)
    (S : Sieve X) (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → S.pullback g ∈ J Y) :
    S ∈ J X := by
  refine J.transitive hR _ ?_
  rintro Y f ⟨W, g, v, hv, rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable _ (h _ hv)

/-- Membership of pushforward sieves in a Grothendieck topology only depends on the
functor up to natural isomorphism. -/
lemma GrothendieckTopology.functorPushforward_mem_of_iso {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (K : GrothendieckTopology D) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {U : C} (R : Sieve U)
    (h : R.functorPushforward F₁ ∈ K (F₁.obj U)) :
    R.functorPushforward F₂ ∈ K (F₂.obj U) := by
  refine K.superset_covering ?_ (K.pullback_stable (e.inv.app U) h)
  rintro Z g ⟨V, a, h', ha, hfac⟩
  refine ⟨V, a, h' ≫ e.hom.app V, ha, ?_⟩
  have hg : g = (g ≫ e.inv.app U) ≫ e.hom.app U := by
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hg, hfac, Category.assoc, Category.assoc, NatTrans.naturality]

end CategoryTheory


