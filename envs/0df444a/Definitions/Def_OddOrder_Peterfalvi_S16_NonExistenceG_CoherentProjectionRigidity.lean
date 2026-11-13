-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:02:31.626187+00:00
-- url     : https://prove2.me/theorems/d41fab59-8a8f-48bf-8450-24226b192442
-- title:
--   Peterfalvi (13.19.c)/(14.11.2): coherent projection rigidity
-- statement:
--   Isolates the Hilbert-space calculation used in Peterfalvi (13.19.c) and (14.11.2), for the projection of an integer coefficient grid onto the full $\eta$-grid.
--
--   Main declarations: `etaGridProjection` (The integer linear combination of the full `eta`-grid with coefficient matrix `m`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped BigOperators

variable {G : Type*} [Group G]

/-- The integer linear combination of the full `eta`-grid with coefficient matrix `m`. -/
noncomputable def etaGridProjection
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ) : ClassFunction G ℂ :=
  ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j : ℂ) • hyp.eta i j

end OddOrder.Peterfalvi.S16


