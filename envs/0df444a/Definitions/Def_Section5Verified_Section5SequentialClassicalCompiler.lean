-- Prove2me | Definitions.Def_Section5Verified_Section5SequentialClassicalCompiler
-- name    : Section5Verified_Section5SequentialClassicalCompiler
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:20.991584+00:00
-- url     : https://prove2.me/theorems/eb6df8a9-aea7-506b-b13c-f0edf750e537
-- title:
--   Section5SequentialClassicalCompiler — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5SequentialClassicalCompiler; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Sequential clean-workspace compilation when each output becomes the next
step's input. Earlier registers are retained, so the entire computation is reversible. -/

def section5_classical_stage_prefix {m K : ℕ} (c : Fin K → Circuit gatesRev m) :
    (k : ℕ) → k ≤ K → Circuit gatesRev m
  | 0,_ => []
  | k+1,hk => section5_classical_stage_prefix c k (by omega)++c ⟨k,by omega⟩

def section5_left_iteration {V : Type*} (F : V → V → V) (a : V) : ℕ → V
  | 0 => a
  | k+1 => F (section5_left_iteration F a k) a







end


