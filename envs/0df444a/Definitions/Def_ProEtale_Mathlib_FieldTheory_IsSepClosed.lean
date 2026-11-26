-- Prove2me | Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
-- name    : ProEtale_Mathlib_FieldTheory_IsSepClosed
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:46.465519+00:00
-- url     : https://prove2.me/theorems/4cf84ad5-bc71-59b7-89e4-1a0895f8d7f6
-- title:
--   Separable closedness of a field is invariant under ring isomorphism
-- statement:
--   Let $k$ and $k'$ be fields and $e : k \to k'$ a ring isomorphism. If $k$ is separably closed (every separable polynomial over $k$ splits), then $k'$ is separably closed.
--
--   This is used to transport separable closedness of residue fields along isomorphisms, e.g. for strictly henselian local rings.
--
--   **Formalization Note** The statement is `IsSepClosed.of_ringEquiv` for `e : k ≃+* k'`, with Mathlib's `IsSepClosed`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/FieldTheory/IsSepClosed.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.FieldTheory.IsSepClosed

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-- `IsSepClosed` transfers along a ring isomorphism of fields. -/
theorem IsSepClosed.of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') [IsSepClosed k] : IsSepClosed k' := by
  refine ⟨fun p hp => ?_⟩
  have hsplit : (p.map e.symm.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp.map
  have hpush := hsplit.map e.toRingHom
  rwa [Polynomial.map_map, e.toRingHom_comp_symm_toRingHom, Polynomial.map_id] at hpush


