-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:22:30.187714+00:00
-- url     : https://prove2.me/theorems/2bb94720-1211-4dad-b25f-bdf84503fcff
-- title:
--   Raw encodings of tape machines and a universal partial function
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A finite deterministic tape machine has states $0,\dots,m$ and symbols $0,\dots,s$, an initial state and a blank symbol. Its transition table gives, for each state and read symbol, either nothing (halt) or a next state, a written symbol and a head move. This module encodes runs by natural-number data.
--
--   1. **Serialization.** A machine becomes a tuple: state count, symbol count, initial state, blank, and the transition table as nested lists.
--   2. **Raw runs.** A raw run consists of the serialized machine, the input word, the current state, the head position in $\mathbb Z$, and the list of writes so far. The tape content at position $z$ is the last write at $z$, else the input symbol at $z$, else blank.
--   3. **Steps.** A raw step looks up the transition. It halts if there is none; otherwise it updates the state and head and appends the write.
--   4. **Initialization.** A natural number $n$ is decoded as a pair (machine code, input word), and the run starts in the initial state at position $0$ with no writes.
--   5. **Simulation relation.** A raw run represents a tape configuration when state, head and every tape cell agree.
--   6. **Universal partial function.** $n\mapsto0$, defined exactly when the decoded raw run halts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineRecursion.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineRecursion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Effectivity
open Effectivity.ComputableRules

abbrev RawInstruction := ℕ × ℕ × ℕ

abbrev RawMachine := ℕ × ℕ × ℕ × ℕ × List (List (Option RawInstruction))

abbrev RawState := ℕ × ℤ × List (ℤ × ℕ)

abbrev RawRun := RawMachine × List ℕ × RawState

def serialize (M : FiniteMachine) : RawMachine :=
  (M.states, M.symbols, M.initial.val, M.blank.val,
    (List.finRange (M.states + 1)).map fun q =>
      (List.finRange (M.symbols + 1)).map fun a =>
        (M.transition q a).map fun v => (v.state.val, v.write.val, v.move.number))

def rawBase (blank : ℕ) (w : List ℕ) (z : ℤ) : ℕ :=
  if (z.toNat : ℤ) = z then w.getD z.toNat blank else blank

def rawRead (blank : ℕ) (w : List ℕ) (writes : List (ℤ × ℕ)) (z : ℤ) : ℕ :=
  writes.foldl (fun value p => if z = p.1 then p.2 else value) (rawBase blank w z)

def rawMove (d : ℕ) : ℤ := if d = 0 then 0 else if d = 1 then -1 else 1

def rawStep (r : RawRun) : Option RawRun :=
  let m := r.1
  let w := r.2.1
  let c := r.2.2
  ((m.2.2.2.2.getD c.1 []).getD (rawRead m.2.2.2.1 w c.2.2 c.2.1) none).map
    fun v => (m, w, v.1, c.2.1 + rawMove v.2.2, c.2.2 ++ [(c.2.1, v.2.1)])

def rawInit (n : ℕ) : RawRun :=
  let p := (Encodable.decode (α := ℕ × List ℕ) n).getD (0, [])
  let m := (Encodable.decode (α := RawMachine) p.1).getD (0,0,0,0,[])
  (m, p.2, m.2.2.1, 0, [])

@[fun_prop] lemma computable_int_toNat : Computable Int.toNat := primrec_int_toNat.to_comp

@[fun_prop] lemma computable_int_ofNat : Computable (Int.ofNat : ℕ → ℤ) := primrec_int_ofNat.to_comp

@[fun_prop] lemma computable_int_add : Computable (fun p : ℤ × ℤ => p.1 + p.2) := primrec_int_add.to_comp

@[simp] lemma rawInit_inputCode (M : FiniteMachine) (w : Input M) :
    rawInit (inputCode M w) = (serialize M, w.map Fin.val, M.initial.val, 0, []) := by
  simp [rawInit, inputCode, FiniteMachine.code, serialize]

@[simp] lemma rawMove_number (d : Recorder.Direction) : rawMove d.number =
    match d with | .stay => 0 | .left => -1 | .right => 1 := by
  cases d <;> simp [rawMove, Recorder.Direction.number]

def RawRel (M : FiniteMachine) (w : Input M) (c : TapeConfiguration M) (r : RawRun) : Prop :=
  r.1 = serialize M ∧ r.2.1 = w.map Fin.val ∧ r.2.2.1 = c.state.val ∧ r.2.2.2.1 = c.head ∧
    ∀ z, rawRead M.blank.val (w.map Fin.val) r.2.2.2.2 z = (c.tape z).val

def universalPartial (n : ℕ) : Part ℕ :=
  (StateTransition.eval rawStep (rawInit n)).map (fun _ => 0)

end BalancedTransport.Universal
end

end OAI


