-- Prove2me | Definitions.Def_AutomataTheory_Sequences_Segments
-- name    : AutomataTheory_Sequences_Segments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:01.228296+00:00
-- url     : https://prove2.me/theorems/7ac4c8f5-4c88-49fb-8bc7-0c9840f35730
-- title:
--   Segments
-- statement:
--   Definitions and structural lemmas for Segments, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean

import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set
section Segments
open Classical
noncomputable def Segment (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k ∈ range φ then Nat.count (· ∈ range φ) k else Nat.count (· ∈ range φ) k - 1
variable {φ : ℕ → ℕ}
end Segments
section Segments'
noncomputable def Segment' (φ : ℕ → ℕ) (k : ℕ) : ℕ :=
  Segment (φ · - φ 0) (k - φ 0)
variable {φ : ℕ → ℕ}
end Segments'


