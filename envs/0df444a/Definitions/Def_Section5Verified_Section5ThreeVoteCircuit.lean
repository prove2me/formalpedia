-- Prove2me | Definitions.Def_Section5Verified_Section5ThreeVoteCircuit
-- name    : Section5Verified_Section5ThreeVoteCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:13.959049+00:00
-- url     : https://prove2.me/theorems/924cc7bc-9dbf-58ad-95a7-6a53a072859d
-- title:
--   Section5ThreeVoteCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ThreeVoteCircuit; mechanically extracted with exact Lean declaration spans.

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

inductive Section5VoteInput (n q a : ℕ) where
  | estimate (i : Fin n) (e : Fin (a+1))
  | example (i : Fin 3) (e : Fin (n*q))
  | label (i : Fin 3)
  deriving DecidableEq, Fintype

noncomputable def section5_vote_input_code (n q a : ℕ) :
    Section5VoteInput n q a ≃ Fin (Fintype.card (Section5VoteInput n q a)) := Fintype.equivFin _

noncomputable def section5_pack_vote_inputs {m n q a : ℕ}
    (ov : Fin n → Fin (a+1) ↪ Fin m) (ex : Fin 3 → Fin (n*q) ↪ Fin m)
    (label : Fin 3 ↪ Fin m) : Fin (Fintype.card (Section5VoteInput n q a)) → Fin m :=
  fun j => match (section5_vote_input_code n q a).symm j with
    | .estimate i e => ov i e
    | .example i e => ex i e
    | .label i => label i

noncomputable def section5_vote_input_vector {n q a : ℕ} (f : ℕ)
    (z : Qubits (Fintype.card (Section5VoteInput n q a))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => fpVal (a+1) f (fun e => z (section5_vote_input_code n q a (.estimate i e)))

noncomputable def section5_vote_input_example {n q a : ℕ} (i : Fin 3)
    (z : Qubits (Fintype.card (Section5VoteInput n q a))) : Qubits (n*q) :=
  fun e => z (section5_vote_input_code n q a (.example i e))



end


