-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
-- name    : ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:03.985276+00:00
-- url     : https://prove2.me/theorems/121510f7-a3ec-4b4a-bda7-c3728cb34af6
-- title:
--   A flat module is faithfully flat if its reductions modulo all maximal ideals are nonzero
-- statement:
--   **Lemma.** Let $R$ be a commutative ring and $M$ a flat $R$-module. Suppose that for every maximal ideal $\mathfrak m \subset R$ the module
--   $$(R/\mathfrak m) \otimes_R M$$
--   is nontrivial (not the zero module). Then $M$ is faithfully flat over $R$.
--
--   This is the usual criterion: flat with $\mathfrak m M \ne M$ for all maximal $\mathfrak m$. It is used to show that filtered colimits of faithfully flat algebras are faithfully flat.
--
--   **Formalization Note** The lemma is `Module.FaithfullyFlat.of_nontrivial_tensor_quotient`. Here $M$ is an additive commutative group with an $R$-module structure, and flatness is an instance argument `[Module.Flat R M]`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
open TensorProduct

lemma Module.FaithfullyFlat.of_nontrivial_tensor_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (H : ∀ (m : Ideal R), m.IsMaximal → Nontrivial ((R ⧸ m) ⊗[R] M)) :
    Module.FaithfullyFlat R M where
  submodule_ne_top m hm := by
    rw [ne_eq, ← Submodule.Quotient.subsingleton_iff, not_subsingleton_iff_nontrivial,
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.nontrivial_congr]
    exact H m hm


