-- Prove2me | Definitions.Def_ProEtale_Algebra_WLocal
-- name    : ProEtale_Algebra_WLocal
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:17:08.790001+00:00
-- url     : https://prove2.me/theorems/1e7e7653-b05e-4e72-94b3-46c1b7b34298
-- title:
--   W-local and w-strictly local rings
-- statement:
--   A commutative ring is **w-local** (`IsWLocalRing`) if its prime spectrum is a w-local spectral space. It is **w-strictly local** (`IsWStrictlyLocalRing`) if in addition its localization at every maximal ideal is a strictly henselian local ring. The second notion is the characterization of the paper's Lemma 2.2.9; the paper's Definition 2.2.1(2) asks that every faithfully flat étale map out of the ring have a section.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 2.2.1(1),(2) and Lemma 2.2.9. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WLocal.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/

/-- A ring is w-local if it has a w-local prime spectrum. -/
@[mk_iff]
class IsWLocalRing (R : Type*) [CommSemiring R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

attribute [instance] IsWLocalRing.wLocalSpace_primeSepectrum

variable {R S : Type*} [CommRing R] [CommRing S]


/-- A w-strictly-local ring is a w-local ring whose stalks at maximal ideals are strictly Henselian
local rings. -/
class IsWStrictlyLocalRing (R : Type*) [CommRing R] : Prop extends IsWLocalRing R where
  isStrictlyHenselianLocalRing_localization (m : Ideal R) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m)


