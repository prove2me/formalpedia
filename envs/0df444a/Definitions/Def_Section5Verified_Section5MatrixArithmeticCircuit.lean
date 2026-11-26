-- Prove2me | Definitions.Def_Section5Verified_Section5MatrixArithmeticCircuit
-- name    : Section5Verified_Section5MatrixArithmeticCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:27.579492+00:00
-- url     : https://prove2.me/theorems/1c9c4e6f-4dd5-4e76-852a-e454cd620ddf
-- title:
--   Section5MatrixArithmeticCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5MatrixArithmeticCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5BilinearAccumulator
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A signed bilinear circuit with coefficients that may vary by summand. This
includes both components of complex matrix multiplication: use 2*n summands,
with negative coefficients on the imaginary-imaginary real-part contribution. -/

noncomputable def section5_general_dot_terms {m n a b : ℕ} (w : ℕ)
    (c : Fin n → Fin a → ℤ) (d : Fin n → Fin b → ℤ)
    (u : Fin n → Fin a → Fin m) (x : Fin n → Fin b → Fin m) :
    List (Section5BilinearTerm m) :=
  (Finset.univ : Finset (Fin n × Fin a × Fin b)).toList.map
    (fun j => ⟨u j.1 j.2.1,x j.1 j.2.2,
      section5_residue_coefficient w (c j.1 j.2.1*d j.1 j.2.2)⟩)











end


