-- Prove2me | Definitions.Def_Section5Verified_Section5OrientationLayout
-- name    : Section5Verified_Section5OrientationLayout
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:40:28.114233+00:00
-- url     : https://prove2.me/theorems/7981518c-7374-55a8-823c-8f0007ff3b47
-- title:
--   Section5OrientationLayout — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5OrientationLayout; mechanically extracted with exact Lean declaration spans.

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
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

namespace Section5OrientationLayout

abbrev voteWidth (n a : ℕ) := n+a+(2*section5_window_precision n+1)+1

inductive DataWire (n a : ℕ) where
  | estimate (i : Fin n) (e : Fin (a+1))
  | comparator (i : Fin 3) (e : Fin (voteWidth n a))
  | comparisonAnc (e : Fin (voteWidth n a+1))
  | scratch
  | signAnc (e : Fin (a+3))
  | flip
  | output (i : Fin n) (e : Fin (a+2))
  deriving DecidableEq, Fintype

abbrev Wire (n q a : ℕ) := DataWire n a ⊕ (Fin 3 × Fin (n*q+1))

@[irreducible] def width (n q a : ℕ) : ℕ := Fintype.card (Wire n q a)

noncomputable def code (n q a : ℕ) : Wire n q a ≃ Fin (width n q a) := by
  unfold width
  exact Fintype.equivFin _

noncomputable def dataWires {n q a r : ℕ} (g : Fin r → DataWire n a) (hg : Function.Injective g) :
    Fin r ↪ Fin (width n q a) :=
  ⟨fun e => code n q a (.inl (g e)),fun _ _ h => hg (Sum.inl.inj ((code n q a).injective h))⟩

noncomputable def input {n q a : ℕ} (i : Fin n) : Fin (a+1) ↪ Fin (width n q a) :=
  dataWires (DataWire.estimate i) (by intro e b h; exact (DataWire.estimate.inj h).2)

noncomputable def comparator {n q a : ℕ} (i : Fin 3) : Fin (voteWidth n a) ↪ Fin (width n q a) :=
  dataWires (DataWire.comparator i) (by intro e b h; exact (DataWire.comparator.inj h).2)

noncomputable def comparisonAnc (n q a : ℕ) : Fin (voteWidth n a+1) ↪ Fin (width n q a) :=
  dataWires DataWire.comparisonAnc (by intro e b h; exact DataWire.comparisonAnc.inj h)

noncomputable def signAnc (n q a : ℕ) : Fin (a+3) ↪ Fin (width n q a) :=
  dataWires DataWire.signAnc (by intro e b h; exact DataWire.signAnc.inj h)

noncomputable def output {n q a : ℕ} (i : Fin n) : Fin (a+2) ↪ Fin (width n q a) :=
  dataWires (DataWire.output i) (by intro e b h; exact (DataWire.output.inj h).2)

noncomputable def examples {n q a : ℕ} (i : Fin 3) : Fin (n*q) ↪ Fin (width n q a) :=
  ⟨fun e => code n q a (.inr (i,e.castSucc)),fun _ _ h =>
    Fin.castSucc_injective (n*q) (Prod.mk.inj (Sum.inr.inj ((code n q a).injective h))).2⟩

noncomputable def labels (n q a : ℕ) : Fin 3 ↪ Fin (width n q a) :=
  ⟨fun i => code n q a (.inr (i,Fin.last (n*q))),fun _ _ h =>
    (Prod.mk.inj (Sum.inr.inj ((code n q a).injective h))).1⟩

noncomputable def split : ∀ n q a : ℕ, Qubits (width n q a) ≃
    (DataWire n a → Bool) × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1))
  | n,q,a =>
    { toFun := fun z => (fun d => z (code n q a (.inl d)),
        fun e => z (code n q a (.inr (0,e))),fun e => z (code n q a (.inr (1,e))),
        fun e => z (code n q a (.inr (2,e))))
      invFun := fun p z => match (code n q a).symm z with
        | .inl d => p.1 d
        | .inr (i,e) => ![p.2.1,p.2.2.1,p.2.2.2] i e
      left_inv := by
        intro z
        dsimp only
        funext v
        have hv : code n q a ((code n q a).symm v)=v := Equiv.apply_symm_apply _ _
        generalize hd : (code n q a).symm v=d at hv ⊢
        rcases d with d | ⟨i,e⟩
        · exact congrArg z hv
        · fin_cases i <;> exact congrArg z hv
      right_inv := by
        rintro ⟨d,s0,s1,s2⟩
        ext e <;> simp [Equiv.symm_apply_apply] }





def estimateBits {n a : ℕ} (x : Fin n → Qubits (a+1)) : DataWire n a → Bool
  | .estimate i e => x i e
  | _ => false

noncomputable def estimateVector {n a : ℕ} (f : ℕ) (x : Fin n → Qubits (a+1)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => fpVal (a+1) f (section5_lsb_to_msb (x i))

noncomputable def readout {n q a : ℕ} (f : ℕ) (z : Qubits (width n q a)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => readFp (section5_msb_register (output (q:=q) i)) f z

end Section5OrientationLayout

end


