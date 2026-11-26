-- Prove2me | Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
-- name    : Section5Verified_Section5FixedPointOutputCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:31.26697+00:00
-- url     : https://prove2.me/theorems/cdc924b7-c907-552e-86a6-3fd917dad33d
-- title:
--   Section5FixedPointOutputCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5FixedPointOutputCircuit; mechanically extracted with exact Lean declaration spans.

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

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

/-! A complete reversible sign-output circuit for the public fixed-point encoding.
One extra output bit avoids overflow at the most negative input endpoint. -/

def section5_widen_bits (a : ℕ) (x : Qubits (a+1)) : Qubits (a+2) :=
  Fin.snoc (Fin.snoc (fun i : Fin a => x i.castSucc) (!(x (Fin.last a)))) (x (Fin.last a))



def section5_widen_source {m : ℕ} (a : ℕ) (p : Fin (a+1) ↪ Fin m) :
    Fin (a+2) → Fin m :=
  Fin.lastCases (p (Fin.last a)) (fun i => p i)

def section5_widen_invert (a : ℕ) : Fin (a+2) → Bool :=
  Fin.lastCases false (fun i => decide (i=Fin.last a))



def section5_msb_register {m w : ℕ} (p : Fin w ↪ Fin m) : Fin w ↪ Fin m :=
  ⟨fun i => p i.rev,fun _ _ h => Fin.rev_injective (p.injective h)⟩







end


