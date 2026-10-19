-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:51:59.1313+00:00
-- url     : https://prove2.me/theorems/b984612d-8951-4b99-9402-13f6f1f766df
-- title:
--   Normalized recorder machines and represented tape configurations
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A finite deterministic tape machine $M$ has states $0,\dots,m$, symbols $0,\dots,s$, and a partial transition table; it halts when no transition applies.
--
--   1. **Normalization.** The recorder machine with states $\{\bot\}\cup\{0,\dots,m\}$, where $\bot$ is the halting state. A missing transition of $M$ becomes a move to $\bot$ that keeps the symbol and the head.
--   2. **Initial work configuration.** The initial checkpoint of the normalized machine on an input word, started in the initial state of $M$.
--   3. **Advancing.** Applying a transition to a tape configuration: write at the head, move the head by $0$, $-1$ or $+1$, and change the state.
--   4. **Representation.** A checkpoint represents a tape configuration with head at $h$ when its scanned symbol is the tape symbol at $h$, its $n$-th left symbol is the symbol at $h-n-1$, and its $n$-th right symbol (blank beyond the stored list) is the symbol at $h+n+1$.
--   5. **Correspondence.** In addition, either the checkpoint state is the state of $M$, or it is $\bot$ and $M$ has halted.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineHalting.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineHalting.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine

def normalized (M : FiniteMachine) :
    Recorder.Machine (Option (Fin (M.states + 1))) (Fin (M.symbols + 1)) where
  halt := none
  blank := M.blank
  transition q a := match q with
    | none => ⟨none, a, .stay⟩
    | some q => match M.transition q a with
      | none => ⟨none, a, .stay⟩
      | some v => ⟨some v.state, v.write, v.move⟩

abbrev WorkConfiguration (M : FiniteMachine) :=
  Recorder.Checkpoint (Option (Fin (M.states + 1))) (Fin (M.symbols + 1))

def initialWork (M : FiniteMachine) (w : Input M) : WorkConfiguration M :=
  Recorder.Checkpoint.initial M.normalized (some M.initial) w

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.TapeConfiguration

def advance {M : FiniteMachine} (c : TapeConfiguration M)
    (v : Recorder.Transition (Fin (M.states + 1)) (Fin (M.symbols + 1))) :
    TapeConfiguration M :=
  ⟨v.state, c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1),
    Function.update c.tape c.head v.write⟩

end BalancedTransport.TapeConfiguration
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
open Stream'

structure Represents (M : FiniteMachine) (w : M.WorkConfiguration)
    (c : TapeConfiguration M) : Prop where
  current : w.current = c.tape c.head
  left : ∀ n : ℕ, w.left n = c.tape (c.head - ((n : ℤ) + 1))
  right : ∀ n : ℕ, w.right[n]?.getD M.blank = c.tape (c.head + ((n : ℤ) + 1))

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'
variable {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}

end BalancedTransport.FiniteMachine.Represents
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
variable {M : FiniteMachine}

def Corresponds (M : FiniteMachine) (w : M.WorkConfiguration)
    (c : TapeConfiguration M) : Prop :=
  Represents M w c ∧
    (w.state = some c.state ∨ (w.state = none ∧ machineStep M c = none))

end BalancedTransport.FiniteMachine
end

end OAI


