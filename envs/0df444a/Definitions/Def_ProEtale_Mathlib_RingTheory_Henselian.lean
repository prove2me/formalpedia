-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
-- name    : ProEtale_Mathlib_RingTheory_Henselian
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:14:54.109257+00:00
-- url     : https://prove2.me/theorems/cbeb6558-8d31-51a0-921f-28a7255b93d7
-- title:
--   Strictly henselian local rings
-- statement:
--   A local ring is **strictly henselian** (`IsStrictlyHenselianLocalRing`) if it is henselian and its residue field is separably closed.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Section 2.2. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Henselian.lean (declarations kept unchanged, unused ones removed).

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- Rename `HenselianRing` to `IsHenselianRing`, ``HenselianLocalRing` to `IsHenselianLocalRing`.

class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)


universe u v


