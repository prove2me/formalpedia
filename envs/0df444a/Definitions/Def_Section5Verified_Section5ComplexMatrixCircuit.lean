-- Prove2me | Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
-- name    : Section5Verified_Section5ComplexMatrixCircuit
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:41.426092+00:00
-- url     : https://prove2.me/theorems/3ccb381b-328b-4004-b998-b4c20ef37128
-- title:
--   Section5ComplexMatrixCircuit — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ComplexMatrixCircuit; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! A full complex integer matrix multiplication compiled to the actual reversible
gate set. The input and shared workspace are preserved. -/

noncomputable def section5_complex_entry_index (n : ℕ) :
    Fin (2*n*n) ≃ Bool × Fin n × Fin n :=
  Fintype.equivOfCardEq (by simp [Nat.mul_assoc,Nat.mul_comm])

def section5_read_integer_matrix {r n a : ℕ} (c : Fin a → ℤ)
    (re im : Fin n → Fin n → Fin a → Fin r) (z : Qubits r) : Section5IntegerMatrix n :=
  ⟨fun i j => section5_integer_bit_value c (z ∘ re i j),
    fun i j => section5_integer_bit_value c (z ∘ im i j)⟩

def section5_complex_product_component {n : ℕ} (A B : Section5IntegerMatrix n)
    (i : Bool × Fin n × Fin n) : ℤ :=
  if i.1 then (A.mul B).im i.2.1 i.2.2 else (A.mul B).re i.2.1 i.2.2

noncomputable def section5_complex_mul_u {r n a : ℕ}
    (Are Aim : Fin n → Fin n → Fin a → Fin r) (i : Fin (2*n*n)) :
    Fin (n+n) → Fin a → Fin r :=
  Fin.addCases (fun k => Are (section5_complex_entry_index n i).2.1 k)
    (fun k => Aim (section5_complex_entry_index n i).2.1 k)

noncomputable def section5_complex_mul_x {r n b : ℕ}
    (Bre Bim : Fin n → Fin n → Fin b → Fin r) (i : Fin (2*n*n)) :
    Fin (n+n) → Fin b → Fin r :=
  if (section5_complex_entry_index n i).1 then
    Fin.addCases (fun k => Bim k (section5_complex_entry_index n i).2.2)
      (fun k => Bre k (section5_complex_entry_index n i).2.2)
  else Fin.addCases (fun k => Bre k (section5_complex_entry_index n i).2.2)
    (fun k => Bim k (section5_complex_entry_index n i).2.2)

noncomputable def section5_complex_mul_coeff {n a : ℕ} (c : Fin a → ℤ) (i : Fin (2*n*n)) :
    Fin (n+n) → Fin a → ℤ :=
  if (section5_complex_entry_index n i).1 then fun _ => c else
    Fin.addCases (fun _ => c) (fun _ j => -c j)











end


