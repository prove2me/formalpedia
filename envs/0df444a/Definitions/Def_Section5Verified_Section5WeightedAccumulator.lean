-- Prove2me | Definitions.Def_Section5Verified_Section5WeightedAccumulator
-- name    : Section5Verified_Section5WeightedAccumulator
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:59.47593+00:00
-- url     : https://prove2.me/theorems/a2967c65-b063-4cda-8573-416e89433146
-- title:
--   Section5WeightedAccumulator — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5WeightedAccumulator; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! A clean reversible accumulator for an arbitrary binary weighted sum. The gate count
is linear in the accumulator width and the number of summands. -/

noncomputable def section5_weighted_step {m w : ℕ} (p : Fin w ↪ Fin m)
    (a : Fin m × ℕ) (z : Qubits m) : Qubits m :=
  if z a.1 then updateOn p z (natToBitsLSB w (a.2 % 2^w+bitsToNatLSB (z ∘ p))) else z

noncomputable def section5_weighted_eval {m w : ℕ} (p : Fin w ↪ Fin m)
    (ops : List (Fin m × ℕ)) (z : Qubits m) : Qubits m :=
  ops.foldl (fun x a => section5_weighted_step p a x) z









def section5_binary_weighted_sum {m : ℕ} (ops : List (Fin m × ℕ)) (z : Qubits m) : ℕ :=
  (ops.map (fun a => if z a.1 then a.2 else 0)).sum



end


