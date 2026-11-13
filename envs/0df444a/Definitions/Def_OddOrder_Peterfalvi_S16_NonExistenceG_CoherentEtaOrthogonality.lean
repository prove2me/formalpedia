-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:19:05.225752+00:00
-- url     : https://prove2.me/theorems/2b6e64d6-ea99-407b-bd26-072fd27635d7
-- title:
--   Peterfalvi (13.19): coherent images and the $\eta$-grid
-- statement:
--   Formalizes the generic type I coherent-image orthogonality and Dade-support avoidance results used on both the $L$- and $M$-sides of Section 16 (Peterfalvi, pp. 85-87).
--
--   Main declarations: `coherentBeta` (The canonical §7.8 beta attached to a coherent type-I bundle, exposed as a class function…).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentEtaOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The canonical §7.8 beta attached to a coherent type-I bundle, exposed as a class function
independent of later choices of `Fintype G`. -/
noncomputable def coherentBeta [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (dataM : TypeICoherent78Data M) : ClassFunction G ℂ :=
  (dataM.h78 hG).beta

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16


