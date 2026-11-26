-- Prove2me | Definitions.Def_Section5Verified_Section5OrientationPostprocessor
-- name    : Section5Verified_Section5OrientationPostprocessor
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:58.054873+00:00
-- url     : https://prove2.me/theorems/6f0707bd-78be-5cd5-a251-ebd16e170cb8
-- title:
--   Section5OrientationPostprocessor — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5OrientationPostprocessor; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

noncomputable def section5_register_tips {m w : ℕ} (p : Fin 3 → Fin w ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, p i e ≠ p j b) (tip : Fin w) : Fin 3 ↪ Fin m :=
  ⟨fun i => p i tip,fun i j h => by
    by_contra hij
    exact hpair i j hij tip tip h⟩

/-! All classical orientation work in one actual circuit: three comparisons,
label disagreements, majority, and signed vector output. The circuit is fixed
before the target and examples; its gate bound is independent of grid precision. -/



end


