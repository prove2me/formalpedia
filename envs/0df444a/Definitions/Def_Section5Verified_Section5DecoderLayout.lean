-- Prove2me | Definitions.Def_Section5Verified_Section5DecoderLayout
-- name    : Section5Verified_Section5DecoderLayout
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:55.714702+00:00
-- url     : https://prove2.me/theorems/9ccca50c-1cac-49b9-9813-1b7d8ff9a1b2
-- title:
--   Section5DecoderLayout — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5DecoderLayout; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

namespace Section5DecoderLayout

abbrev scoreWidth (N b : ℕ) := 2*(N+1)+b+b+1
abbrev payloadWidth (N b : ℕ) := (N+1)*(b+1)
abbrev recordWidth (N b : ℕ) := scoreWidth N b+(payloadWidth N b+payloadWidth N b)

/-- Distinct constructors reserve all workspaces before circuit construction. -/
inductive Wire (N K b f : ℕ) where
  | matrix (stage : Fin (K+1)) (entry : Fin (2*(N+1)*(N+1))) (bit : Fin (b+1))
  | score (column : Fin (N+1)) (bit : Fin (scoreWidth N b))
  | scoreAnc (bit : Fin (scoreWidth N b+1))
  | scoreScratch
  | scanControl (index : Fin N)
  | scanCarry
  | normAccumulator (bit : Fin ((N+1)+b+b+1+1))
  | normAnc (bit : Fin ((N+1)+b+b+1+1+1))
  | normScratch
  | output (coordinate : Fin (N+1)) (bit : Fin (f+2))
  | powerAnc (bit : Fin (b+1+1))
  | powerScratch
  deriving DecidableEq, Fintype

@[irreducible] def width (N K b f : ℕ) : ℕ := Fintype.card (Wire N K b f)

noncomputable def code (N K b f : ℕ) : Wire N K b f ≃ Fin (width N K b f) := by
  unfold width
  exact Fintype.equivFin _

noncomputable def wires {N K b f r : ℕ} (g : Fin r → Wire N K b f)
    (hg : Function.Injective g) : Fin r ↪ Fin (width N K b f) :=
  ⟨fun i => code N K b f (g i),(code N K b f).injective.comp hg⟩



noncomputable def matrix {N K b f : ℕ} (s : Fin (K+1)) (i : Fin (2*(N+1)*(N+1))) :
    Fin (b+1) ↪ Fin (width N K b f) :=
  wires (Wire.matrix s i) (by intro e g h; exact (Wire.matrix.inj h).2.2)

noncomputable def scores {N K b f : ℕ} (j : Fin (N+1)) :
    Fin (scoreWidth N b) ↪ Fin (width N K b f) :=
  wires (Wire.score j) (by intro e g h; exact (Wire.score.inj h).2)

noncomputable def scoreAnc (N K b f : ℕ) : Fin (scoreWidth N b+1) ↪ Fin (width N K b f) :=
  wires Wire.scoreAnc (by intro e g h; exact Wire.scoreAnc.inj h)

noncomputable def scanControl (N K b f : ℕ) : Fin N ↪ Fin (width N K b f) :=
  wires Wire.scanControl (by intro e g h; exact Wire.scanControl.inj h)

noncomputable def scanCarry (N K b f : ℕ) : Fin 1 ↪ Fin (width N K b f) :=
  wires (fun _ => Wire.scanCarry) (by intro e g h; exact Subsingleton.elim e g)

noncomputable def normAccumulator (N K b f : ℕ) :
    Fin ((N+1)+b+b+1+1) ↪ Fin (width N K b f) :=
  wires Wire.normAccumulator (by intro e g h; exact Wire.normAccumulator.inj h)

noncomputable def normAnc (N K b f : ℕ) :
    Fin ((N+1)+b+b+1+1+1) ↪ Fin (width N K b f) :=
  wires Wire.normAnc (by intro e g h; exact Wire.normAnc.inj h)

noncomputable def output (N K b f : ℕ) (i : Fin (N+1)) : Fin (f+2) ↪ Fin (width N K b f) :=
  wires (Wire.output i) (by intro e g h; exact (Wire.output.inj h).2)

noncomputable def powerAnc (N K b f : ℕ) : Fin (b+1+1) ↪ Fin (width N K b f) :=
  wires Wire.powerAnc (by intro e g h; exact Wire.powerAnc.inj h)

noncomputable def part {N K b f : ℕ} (imaginary : Bool) (j : Fin (N+1)) :
    Fin (payloadWidth N b) ↪ Fin (width N K b f) :=
  wires (fun x => Wire.matrix (Fin.last K)
    ((section5_complex_entry_index (N+1)).symm (imaginary,(finProdFinEquiv.symm x).1,j))
    (finProdFinEquiv.symm x).2) (by
      intro x y h
      have hh := Wire.matrix.inj h
      have he := (section5_complex_entry_index (N+1)).symm.injective hh.2.1
      have hr := congrArg (fun v : Bool × Fin (N+1) × Fin (N+1) => v.2.1) he
      exact finProdFinEquiv.symm.injective (Prod.ext hr hh.2.2))



theorem parts_disjoint {N K b f : ℕ} (a a' : Bool) (j j' : Fin (N+1))
    (h : a ≠ a' ∨ j ≠ j') : ∀ x y, part (K:=K) (b:=b) (f:=f) a j x ≠ part a' j' y := by
  intro x y heq
  have heq' := (code N K b f).injective heq
  have hc := (Wire.matrix.inj heq').2.1
  have hp := (section5_complex_entry_index (N+1)).symm.injective hc
  rcases h with ha | hj
  · exact ha (congrArg Prod.fst hp)
  · exact hj (congrArg (fun v : Bool × Fin (N+1) × Fin (N+1) => v.2.2) hp)

theorem scores_parts_disjoint {N K b f : ℕ} (j j' : Fin (N+1)) (a : Bool) :
    ∀ x y, scores (K:=K) (b:=b) (f:=f) j x ≠ part a j' y := by
  intro x y h
  have hh := (code N K b f).injective h
  cases hh

noncomputable def records {N K b f : ℕ} (j : Fin (N+1)) :
    Fin (recordWidth N b) ↪ Fin (width N K b f) :=
  combineEmb (scores j)
    (combineEmb (part false j) (part true j) (parts_disjoint _ _ _ _ (Or.inl Bool.false_ne_true)))
    (by
      intro x y
      induction y using Fin.addCases with
      | left y => simpa only [combineEmb_castAdd] using scores_parts_disjoint j j false x y
      | right y => simpa only [combineEmb_natAdd] using scores_parts_disjoint j j true x y)

def scoreField (N b : ℕ) : Fin (scoreWidth N b) ↪ Fin (recordWidth N b) :=
  Fin.castAddEmb (payloadWidth N b+payloadWidth N b)

def realField (N b : ℕ) : Fin (payloadWidth N b) ↪ Fin (recordWidth N b) :=
  (Fin.castAddEmb (payloadWidth N b)).trans (Fin.natAddEmb (scoreWidth N b))

def imagField (N b : ℕ) : Fin (payloadWidth N b) ↪ Fin (recordWidth N b) :=
  (Fin.natAddEmb (payloadWidth N b)).trans (Fin.natAddEmb (scoreWidth N b))

end Section5DecoderLayout

end


