-- Prove2me | Definitions.Def_TC433_Compat4331_CompactElement_2ab93b518d
-- name    : TC433_Compat4331_CompactElement_2ab93b518d
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:09:49.181659+00:00
-- url     : https://prove2.me/theorems/890fde3b-cc3b-4241-9197-1eb505e43a12
-- title:
--   TauCeti: Compat4331 / CompactElement
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Compat4331.CompactElement for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   Compatibility lemma for Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; source and proof included.

module
public import Mathlib.Order.CompactlyGenerated.Basic
@[expose] public section
theorem IsCompactElement.exists_finset_of_le_iSup {α : Type*} [CompleteLattice α]
    {k : α} (hk : IsCompactElement k) {ι : Type*} (f : ι → α)
    (h : k ≤ ⨆ i, f i) : ∃ s : Finset ι, k ≤ ⨆ i ∈ s, f i :=
  CompleteLattice.IsCompactElement.exists_finset_of_le_iSup α hk f h


