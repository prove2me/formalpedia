-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:59.417395+00:00
-- url     : https://prove2.me/theorems/0ca12b1b-2454-4000-9aa6-51b852d9e612
-- title:
--   Span Schwartz Bruhat Product Eq Top
-- statement:
--   Definitions and structural lemmas for Span Schwartz Bruhat Product Eq Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SpanSchwartzBruhatProductEqTop.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open Filter Topology
noncomputable section
namespace GlobalTheory.LocFlat.CFac.Span
def S (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Submodule ℂ (X × Y → ℂ) :=
  Submodule.span ℂ (Set.range fun q : SB X × SB Y => prodFn q.1.1 q.2.1)
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
def IsBox (r : Set X × Set Y) : Prop := IsCompact r.1 ∧ IsClopen r.1 ∧ IsCompact r.2 ∧ IsClopen r.2
def U (L : List (Set X × Set Y)) : Set (X × Y) := ⋃ r ∈ L, r.1 ×ˢ r.2
end GlobalTheory.LocFlat.CFac.Span


