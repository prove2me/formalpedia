-- Prove2me | Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
-- name    : Section5Verified_Section5ClassicalArithmeticRealization
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T18:59:49.966136+00:00
-- url     : https://prove2.me/theorems/2bb1e8db-28f5-56fd-83b5-da6ec9468fa0
-- title:
--   Section5ClassicalArithmeticRealization — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ClassicalArithmeticRealization; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Reusing the accepted arithmetic circuits in the actual classical postprocessing gate set. -/

def section5_RevRealizable {m : ℕ} (lc : LayeredCircuit m) : Prop :=
  ∃ c : Circuit gatesRev m, c.size ≤ lc.size ∧ c.unitary=lc.unitary

def section5_rev_map_wires {m n : ℕ} (e : Fin m ↪ Fin n) (c : Circuit gatesRev m) : Circuit gatesRev n :=
  c.map (fun g => ⟨g.gate,g.mem,g.wires.trans e⟩)



























end


