-- Prove2me | Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
-- name    : ProEtale_Topology_SpectralSpace_WLocal_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:16:39.321526+00:00
-- url     : https://prove2.me/theorems/ea5db315-56d5-5710-92e8-2a456414c4dc
-- title:
--   W-local spectral spaces
-- statement:
--   A spectral space is **w-local** (`WLocalSpace`) if every point specializes to a unique closed point and the set of closed points is closed. This is the characterization of the paper's Lemma 2.1.4; Definition 2.1.1 asks instead that every open cover split and that the closed points form a closed subset.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 2.1.1 and Lemma 2.1.4. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/WLocal/Basic.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# w-local spaces

In this file we define w-local spaces. These are spectral spaces in which every point
specializes to a unique closed point and where the set of closed points is closed.
-/

/--
A spectral space is w-local if every point specializes to a unique closed point
and the set of closed points is closed.
Note: In a spectral space, every point specializes to a closed point, so we only require
the uniqueness.
-/
class WLocalSpace (X : Type*) [TopologicalSpace X] : Prop extends SpectralSpace X where
  /-- Any two closed specializations of a point are equal. -/
  eq_of_specializes {x c c' : X} (hc : IsClosed {c}) (hc' : IsClosed {c'})
    (hxc : x ⤳ c) (hxc' : x ⤳ c') : c = c'
  /-- The set of closed points is closed. -/
  isClosed_closedPoints : IsClosed (closedPoints X)

attribute [instance] WLocalSpace.isClosed_closedPoints


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Topology


