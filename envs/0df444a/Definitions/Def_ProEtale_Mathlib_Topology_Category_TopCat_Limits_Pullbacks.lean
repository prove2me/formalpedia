-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
-- name    : ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:13.081837+00:00
-- url     : https://prove2.me/theorems/840fcb52-3442-5f68-bc03-7a7835a4756a
-- title:
--   Over a Hausdorff base, the fibre product embeds as a closed subspace of the product
-- statement:
--   Let $f : X \to Z$ and $g : Y \to Z$ be continuous maps of topological spaces with $Z$ Hausdorff. The file proves that the canonical map from the fibre product to the product,
--   $$X \times_Z Y \longrightarrow X \times Y, \qquad p \mapsto (\mathrm{pr}_1(p), \mathrm{pr}_2(p)),$$
--   is a closed embedding. Its image is the preimage of the diagonal of $Z$ under $f \times g$, which is closed because $Z$ is Hausdorff. Two auxiliary lemmas say that the categorical projections of a product in the category of topological spaces are the coordinate projections.
--
--   This is a basic tool for fibre products of compact Hausdorff and profinite spaces.
--
--   **Formalization Note** Main declaration: `TopCat.isClosedEmbedding_pullback_to_prod`, stated in `TopCat.{u}` for the map `prod.lift (pullback.fst f g) (pullback.snd f g)`, tagged with Stacks 08ZH; auxiliary `TopCat.prodFst_apply`, `TopCat.prodSnd_apply`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 08ZH. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Category/TopCat/Limits/Pullbacks.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u

open CategoryTheory Limits

lemma TopCat.prodFst_apply {X Y : TopCat.{u}} (x : X × Y) : TopCat.prodFst x = x.1 := by
  rfl

lemma TopCat.prodSnd_apply {X Y : TopCat.{u}} (x : X × Y) : TopCat.prodSnd x = x.2 := by
  rfl

-- use the following lemma: `t2Space_iff_diagonal_closed`
-- after `TopCat.isEmbedding_pullback_to_prod`
@[stacks 08ZH]
theorem TopCat.isClosedEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    Topology.IsClosedEmbedding ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  refine ⟨isEmbedding_pullback_to_prod f g, ?_⟩
  suffices s1 : Set.range (prod.lift (pullback.fst f g) (pullback.snd f g)) =
      (homeoOfIso (prodIsoProd X Y)) ⁻¹' (Prod.map f.hom g.hom ⁻¹' Set.range fun x ↦ (x, x)) by
    rw [s1, (TopCat.homeoOfIso (TopCat.prodIsoProd X Y)).isClosed_preimage]
    exact .preimage (.prodMap (map_continuous f.hom) (map_continuous g.hom))
      (t2Space_iff_diagonal_closed.mp ‹T2Space Z›)
  ext x
  simp only [Set.mem_range,
    show (Set.range fun x : ↑Z ↦ (x, x)) = Set.diagonal Z from Set.range_diag, Set.mem_preimage, Set.mem_diagonal_iff, Prod.map_fst,
    Prod.map_snd]
  constructor
  · rintro ⟨a, rfl⟩
    rw [← TopCat.prodFst_apply, ← TopCat.prodSnd_apply, homeoOfIso_apply]
    simp only [← ConcreteCategory.comp_apply]
    simp [pullback.condition]
  · intro ha
    -- TODO: replace this by `range_pullback_to_prod` after updating mathlib
    use (pullbackIsoProdSubtype f g).inv ⟨(X.prodIsoProd Y).hom x , ha⟩
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;>
       rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] <;>
        -- This used to be `simp` before https://github.com/leanprover/lean4/pull/2644
    cat_disch


