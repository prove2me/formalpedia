-- Prove2me | Definitions.Def_StableMarriageF6_F6ConvexWindowFull
-- name    : StableMarriageF6_F6ConvexWindowFull
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:31:02.155171+00:00
-- url     : https://prove2.me/theorems/70886f3a-d6e1-4658-9253-3969094a4075
-- title:
--   F6 Convex Window Full
-- statement:
--   Definitions and structural lemmas for F6 Convex Window Full, from insammael (insammael/stable-marriage-f6; see pinned Apache-2.0 LICENSE and lean/third_party provenance)'s pinned Small rotation blocks and antichain bound for width-3 CI2 posets (Stable Marriage F6) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/lean/StableMarriageF6/F6ConvexWindowFull.lean

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
set_option autoImplicit true
noncomputable section
namespace F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]
end F6ConvexWindow
namespace F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]
end F6ConvexWindowFull


