-- Prove2me | Definitions.Def_Snaky35Core
-- name    : Snaky35Core
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T11:58:30.573459+00:00
-- url     : https://prove2.me/theorems/6e805370-34a9-4ab0-9bc7-3c71e2114c4c
-- title:
--   Snaky35Core
-- statement:
--   Auxiliary predicates for the original 35-move finite certificate: row subset/origin/height conditions and table-entry index/nonempty/backward-reference conditions, with the structural three-field extensionality lemma for RowData. No certificate correctness or game-winning result is assumed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean; Proposition 10, original 35-move finite certificate.

import Definitions.Def_SnakyCertificate
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem row_ext {c d : RowData} (hA : c.A = d.A)
    (hH : c.H = d.H) (hh : c.height = d.height) : c = d := by
  cases c; cases d; cases hA; cases hH; cases hh; rfl

def Good (d : RowData) : Prop :=
  d.A ⊆ d.H ∧ origin ∈ d.H ∧ origin ∉ d.A ∧ d.height ≤ 34

def EntryGood (i : ℕ) : Prop :=
  let e := entryAt i
  e.index = i ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < i


end OAI.SnakyCertificate.MilestoneChecks


