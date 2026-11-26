-- Prove2me | Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
-- name    : Section5Verified_Section5ReversibleBooleanCompiler
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:37:19.445598+00:00
-- url     : https://prove2.me/theorems/264c5a1c-dfb6-57c4-bd6c-0e2106efa1ee
-- title:
--   Section5ReversibleBooleanCompiler — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5ReversibleBooleanCompiler; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/

noncomputable def section5_replace_wires {k m : ℕ} (e : Fin k ↪ Fin m)
    (x : Qubits m) (v : Qubits k) : Qubits m :=
  fun i => if h : ∃ j, e j=i then v h.choose else x i

theorem section5_replace_wires_on {k m : ℕ} (e : Fin k ↪ Fin m)
    (x : Qubits m) (v : Qubits k) (j : Fin k) : section5_replace_wires e x v (e j)=v j := by
  classical
  unfold section5_replace_wires
  rw [dif_pos ⟨j,rfl⟩]
  congr 1
  exact e.injective (Exists.choose_spec (show ∃ j', e j'=e j from ⟨j,rfl⟩))

theorem section5_replace_wires_off {k m : ℕ} (e : Fin k ↪ Fin m)
    (x : Qubits m) (v : Qubits k) (i : Fin m) (hi : i ∉ Set.range e) :
    section5_replace_wires e x v i=x i := by
  classical
  unfold section5_replace_wires
  exact dif_neg hi







def section5_toffoli_gate : Gate :=
  ⟨3,Matrix.of fun y z => if y 0=z 0 ∧ y 1=z 1 ∧ y 2=xor (z 2) (z 0 && z 1) then 1 else 0⟩



def section5_rev_not {m : ℕ} (e : Fin 1 ↪ Fin m) : GateApp gatesRev m :=
  ⟨Gate.ofMatrix1 pauliX,by simp [gatesRev],e⟩

def section5_rev_cnot {m : ℕ} (e : Fin 2 ↪ Fin m) : GateApp gatesRev m :=
  ⟨Gate.ofMatrix2 cnot,by simp [gatesRev],e⟩

def section5_rev_toffoli {m : ℕ} (e : Fin 3 ↪ Fin m) : GateApp gatesRev m :=
  ⟨section5_toffoli_gate,by simp [section5_toffoli_gate,gatesRev],e⟩







def section5_boolean_wire1 {m : ℕ} (a : Fin m) : Fin 1 ↪ Fin m :=
  ⟨fun _ => a,fun _ _ _ => Subsingleton.elim _ _⟩

def section5_boolean_wire2 {m : ℕ} (a b : Fin m) (hab : a ≠ b) : Fin 2 ↪ Fin m :=
  ⟨![a,b],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

def section5_boolean_wire3 {m : ℕ} (a b t : Fin m) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Fin 3 ↪ Fin m :=
  ⟨![a,b,t],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩













def section5_bool_value (op : BoolOp) (a b : Bool) : Bool :=
  match op with
  | .and => a && b
  | .or => a || b
  | .not => !a

def section5_boolean_gate_circuit {m : ℕ} (op : BoolOp) (a b t : Fin m) (hat : a ≠ t) (hbt : b ≠ t) :
    Circuit gatesRev m :=
  match op with
  | .not => [section5_rev_not (section5_boolean_wire1 t),section5_rev_cnot (section5_boolean_wire2 a t hat)]
  | .and => if hab : a=b then [section5_rev_cnot (section5_boolean_wire2 a t hat)] else
      [section5_rev_toffoli (section5_boolean_wire3 a b t hab hat hbt)]
  | .or => if hab : a=b then [section5_rev_cnot (section5_boolean_wire2 a t hat)] else
      [section5_rev_cnot (section5_boolean_wire2 a t hat),section5_rev_cnot (section5_boolean_wire2 b t hbt),
        section5_rev_toffoli (section5_boolean_wire3 a b t hab hat hbt)]





structure Section5BooleanInstruction (m : ℕ) where
  op : BoolOp
  a : Fin m
  b : Fin m
  target : Fin m
  a_ne_target : a ≠ target
  b_ne_target : b ≠ target

def Section5BooleanInstruction.compile {m : ℕ} (g : Section5BooleanInstruction m) : Circuit gatesRev m :=
  section5_boolean_gate_circuit g.op g.a g.b g.target g.a_ne_target g.b_ne_target

def Section5BooleanInstruction.eval {m : ℕ} (g : Section5BooleanInstruction m) (x : Qubits m) : Qubits m :=
  Function.update x g.target (xor (x g.target) (section5_bool_value g.op (x g.a) (x g.b)))





def section5_compile_boolean_program {m : ℕ} (l : List (Section5BooleanInstruction m)) : Circuit gatesRev m :=
  (l.map Section5BooleanInstruction.compile).flatten

def section5_eval_boolean_program {m : ℕ} (l : List (Section5BooleanInstruction m)) (x : Qubits m) : Qubits m :=
  l.foldl (fun y g => g.eval y) x





end


