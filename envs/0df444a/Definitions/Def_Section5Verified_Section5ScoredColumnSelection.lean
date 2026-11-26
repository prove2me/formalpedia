-- Prove2me | Definitions.Def_Section5Verified_Section5ScoredColumnSelection
-- name    : Section5Verified_Section5ScoredColumnSelection
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:26.501797+00:00
-- url     : https://prove2.me/theorems/6ceee75b-a000-4f01-8e7f-fee6822ce0e6
-- title:
--   Section5ScoredColumnSelection — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ScoredColumnSelection; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Score computation and the complete maximum-column scan in one circuit.
Each record carries one complex integer column and a fresh score field. -/

def section5_record_payload_index (n b : ℕ) :
    Fin (n*((n+n)*(b+1))) ≃ Fin n × (Fin (n+n) × Fin (b+1)) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

def section5_record_payload_wire {m n R b : ℕ} (p : Fin n → Fin R ↪ Fin m)
    (re im : Fin n → Fin (b+1) → Fin R) (x : Fin (n*((n+n)*(b+1)))) : Fin m :=
  let y := section5_record_payload_index n b x
  p y.1 (Fin.addCases re im y.2.1 y.2.2)

def section5_record_real_source (n b : ℕ) (i j : Fin n) (e : Fin (b+1)) :
    Fin (n*((n+n)*(b+1))) :=
  (section5_record_payload_index n b).symm (j,(i.castAdd n,e))

def section5_record_imag_source (n b : ℕ) (i j : Fin n) (e : Fin (b+1)) :
    Fin (n*((n+n)*(b+1))) :=
  (section5_record_payload_index n b).symm (j,(Fin.natAdd n i,e))

def section5_record_column_square {m n R b : ℕ} (p : Fin n → Fin R ↪ Fin m)
    (re im : Fin n → Fin (b+1) → Fin R) (j : Fin n) (z : Qubits m) : ℤ :=
  ∑ i : Fin n,
    ((section5_integer_bit_value (section5_twos_coefficient (b+1))
      (fun e => z (p j (re i e))))^2+
     (section5_integer_bit_value (section5_twos_coefficient (b+1))
      (fun e => z (p j (im i e))))^2)







end


