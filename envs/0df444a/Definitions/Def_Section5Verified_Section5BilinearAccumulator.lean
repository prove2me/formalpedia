-- Prove2me | Definitions.Def_Section5Verified_Section5BilinearAccumulator
-- name    : Section5Verified_Section5BilinearAccumulator
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:00:46.103548+00:00
-- url     : https://prove2.me/theorems/ec248e61-2cc2-4072-883b-409a9f096c29
-- title:
--   Section5BilinearAccumulator — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5BilinearAccumulator; mechanically extracted with exact Lean declaration spans.

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

/-! A product of two input bits can control the linear-size modular accumulator.
The temporary AND bit and all arithmetic workspace are returned to zero. -/





noncomputable def section5_bilinear_step {m w : ℕ} (p : Fin w ↪ Fin m)
    (a b : Fin m) (v : ℕ) (z : Qubits m) : Qubits m :=
  if z a && z b then updateOn p z (natToBitsLSB w (v%2^w+bitsToNatLSB (z ∘ p))) else z





structure Section5BilinearTerm (m : ℕ) where
  a : Fin m
  b : Fin m
  weight : ℕ

noncomputable def section5_bilinear_eval {m w : ℕ} (p : Fin w ↪ Fin m)
    (ops : List (Section5BilinearTerm m)) (z : Qubits m) : Qubits m :=
  ops.foldl (fun x a => section5_bilinear_step p a.a a.b a.weight x) z





def section5_bilinear_sum {m : ℕ} (ops : List (Section5BilinearTerm m)) (z : Qubits m) : ℕ :=
  (ops.map (fun a => if z a.a && z a.b then a.weight else 0)).sum





end


