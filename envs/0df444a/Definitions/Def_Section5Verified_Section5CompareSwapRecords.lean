-- Prove2me | Definitions.Def_Section5Verified_Section5CompareSwapRecords
-- name    : Section5Verified_Section5CompareSwapRecords
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:03.609219+00:00
-- url     : https://prove2.me/theorems/b7f3d2bb-3d3e-4995-80ec-47d35c6dab4e
-- title:
--   Section5CompareSwapRecords — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CompareSwapRecords; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Comparing a score subregister and conditionally exchanging its complete record.
This is the reversible step in the maximum-column scan. -/





def section5_record_compare_wires {m R w : ℕ} (score : Fin w ↪ Fin R)
    (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) :
    Fin (w+w+1) ↪ Fin m :=
  combineEmb (combineEmb (score.trans A) (score.trans B) (fun i j => hAB (score i) (score j)))
    (section5_boolean_wire1 ctrl) (by
      intro i j
      induction i using Fin.addCases with
      | left i =>
        have he : (combineEmb (score.trans A) (score.trans B) (fun i j => hAB (score i) (score j)))
            (Fin.castAdd w i)=A (score i) := combineEmb_castAdd _ _ _ i
        intro h
        exact hcA (score i) (h.symm.trans he)
      | right i =>
        have he : (combineEmb (score.trans A) (score.trans B) (fun i j => hAB (score i) (score j)))
            (Fin.natAdd w i)=B (score i) := combineEmb_natAdd _ _ _ i
        intro h
        exact hcB (score i) (h.symm.trans he))









def section5_record_swap_wires {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) :
    Fin (1+R+R) ↪ Fin m :=
  combineEmb (combineEmb (section5_boolean_wire1 ctrl) A (fun _ i => hcA i)) B (by
    intro i j
    induction i using Fin.addCases with
    | left i =>
      have he : (combineEmb (section5_boolean_wire1 ctrl) A (fun _ i => hcA i))
          (Fin.castAdd R i)=ctrl := combineEmb_castAdd _ _ _ i
      intro h
      exact hcB j (he.symm.trans h)
    | right i =>
      have he : (combineEmb (section5_boolean_wire1 ctrl) A (fun _ i => hcA i))
          (Fin.natAdd 1 i)=A i := combineEmb_natAdd _ _ _ i
      intro h
      exact hAB i j (he.symm.trans h))

















end


