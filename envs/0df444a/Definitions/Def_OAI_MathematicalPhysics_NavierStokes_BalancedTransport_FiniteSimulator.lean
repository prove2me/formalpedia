-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:01:34.4791+00:00
-- url     : https://prove2.me/theorems/2396aed1-877f-453f-9143-0b8a06ab4735
-- title:
--   Finite tape machines from Turing machines with finite support
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A Turing machine in the standard library may have infinitely many states, but its relevant behaviour lives on a finite set $S$ of states that it supports. This module converts such a machine into a finite deterministic tape machine.
--
--   1. **Indexing.** Elements of a finite type $\alpha$ are numbered $0,\dots,|\alpha|-1$ inside $\{0,\dots,|\alpha|\}$. Unindexing inverts this and sends the extra value to a default element.
--   2. **States and symbols.** The new machine has the indexed states of $S$ and the indexed tape symbols. Its initial state is the index of the default state, and its blank is the index of the default symbol.
--   3. **Transitions.** A write instruction becomes "write and stay". A move instruction becomes "keep the symbol and move left or right". The machine halts exactly when the original does.
--   4. **Correspondence.** A configuration of the original machine corresponds to one of the finite machine when the state lies in $S$, the state indices agree, and every tape cell, read relative to the head, has the matching index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FiniteSimulator.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FiniteSimulator.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedThreeStack mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {α : Type*} [Fintype α]

def finiteIndex (a : α) : Fin (Fintype.card α + 1) := (Fintype.equivFin α a).castSucc

def finiteUnindex (a₀ : α) (i : Fin (Fintype.card α + 1)) : α :=
  if h : i.val < Fintype.card α then (Fintype.equivFin α).symm ⟨i.val,h⟩ else a₀

@[simp] lemma finiteUnindex_index (a₀ a : α) : finiteUnindex a₀ (finiteIndex a) = a := by
  simp [finiteUnindex, finiteIndex]

end BalancedTransport.Universal
end

noncomputable section
namespace BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)

def stateIndex (q : Λ) : Fin (Fintype.card {q : Λ // q ∈ S} + 1) :=
  finiteIndex (if h : q ∈ S then (⟨q,h⟩ : {q : Λ // q ∈ S}) else ⟨default,ss.1⟩)

def postInstruction (a : Fin (Fintype.card Γ + 1)) (v : Λ × TM0.Stmt Γ) :
    Recorder.Transition (Fin (Fintype.card {q : Λ // q ∈ S} + 1)) (Fin (Fintype.card Γ + 1)) :=
  ⟨stateIndex P S ss v.1,
    (match v.2 with | .write b => finiteIndex b | .move _ => a),
    (match v.2 with | .write _ => .stay | .move .left => .left | .move .right => .right)⟩

abbrev finitePostMachine : FiniteMachine where
  states := Fintype.card {q : Λ // q ∈ S}
  symbols := Fintype.card Γ
  initial := stateIndex P S ss default
  blank := finiteIndex (default : Γ)
  transition q a := (P (finiteUnindex ⟨default,ss.1⟩ q : {q : Λ // q ∈ S}).val (finiteUnindex default a)).map
    (postInstruction P S ss a)

def PostRel (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss)) : Prop :=
  c.q ∈ S ∧ d.state = stateIndex P S ss c.q ∧
    ∀ i : ℤ, d.tape (d.head + i) = finiteIndex (c.Tape.nth i)

end BalancedTransport.Universal
end

end OAI


