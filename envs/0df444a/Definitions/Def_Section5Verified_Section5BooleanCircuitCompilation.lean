-- Prove2me | Definitions.Def_Section5Verified_Section5BooleanCircuitCompilation
-- name    : Section5Verified_Section5BooleanCircuitCompilation
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:01:25.101021+00:00
-- url     : https://prove2.me/theorems/84e39ea9-1b62-4bff-bfc6-a1a6492c5796
-- title:
--   Section5BooleanCircuitCompilation — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5BooleanCircuitCompilation; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Every well-formed Boolean straight-line program has a linear-size reversible implementation. -/

def section5_boolean_memory (m : ℕ) (v : List Bool) : Qubits m :=
  fun i => v.getD i.val false



def section5_boolean_values (l : List BoolGate) (v : List Bool) : List Bool :=
  l.foldl (fun vals g => vals++[g.value vals]) v





end


