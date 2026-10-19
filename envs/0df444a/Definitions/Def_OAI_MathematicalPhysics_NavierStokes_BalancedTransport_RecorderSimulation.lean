-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:47:37.554732+00:00
-- url     : https://prove2.me/theorems/71024018-3d33-4c4e-a981-b48ab7674bd5
-- title:
--   Coding recorder configurations and Turing machine checkpoints
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   The recorder is a three-stack machine that simulates a Turing machine $M$ reversibly. A configuration has a control state and three infinite stacks: left, right and history. Stack letters are work symbols $a$, marked symbols $\hat a$, a boundary marker, and records of executed transitions. Each step replaces finite prefixes of the three stacks and the control according to one row of a finite table.
--
--   1. **Codes.** A configuration is coded by the point whose coordinates are the base-$B$ stream codes of its three stacks, shifted by the origin $(4k,0,0)$ attached to its control state. The full map of an instruction is the box map from its source box to its target box, with ratio $1/B$.
--   2. **Checkpoints.** A checkpoint is a Turing machine configuration together with a history. It has a state, an infinite left part of the tape, the scanned symbol, a finite right part, and a history stack. Its expansion is the recorder configuration in the ready state whose right stack is the scanned symbol, then the right part, then a boundary marker and blanks forever.
--   3. **Machine steps.** The next checkpoint performs one transition of $M$ and pushes a record of it onto the history. When the head moves right past the finite right part, a blank is supplied. A work step is a next step from a non-halting state.
--   4. **Rational codes.** A word $w$ followed by the letter $a$ repeated forever has the rational code
--   $$
--   \sum_{j<|w|}\delta(w_j)B^{-(j+1)}+B^{-|w|}\frac{\delta(a)}{B-1}.
--   $$
--   5. **Initial checkpoints.** For an input word, the initial checkpoint has blank left part, the first input letter scanned, the rest of the input on the right, and an all-blank history. Its code has rational coordinates, computed explicitly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RecorderSimulation.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RecorderSimulation.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

def Configuration.stacks (c : Configuration Q Γ) : Fin 3 → Stream' (Letter Q Γ) :=
  ![c.left, c.right, c.history]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]
variable [DecidableEq Q]

def Configuration.code (M : Machine Q Γ) (c : Configuration Q Γ) : Space :=
  Coding.codedPoint digit (Coding.origin (placement M c.control)) c.stacks

def Instruction.fullMap (M : Machine Q Γ) (inst : Instruction Q Γ) : Space → Space :=
  Coding.boxMap (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ))
    (Coding.origin (placement M inst.sourceControl))
    (Coding.origin (placement M inst.targetControl)) inst.sourcePrefixes inst.targetPrefixes

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

structure Checkpoint (Q Γ : Type*) where
  state : Q
  left : Stream' Γ
  current : Γ
  right : List Γ
  history : Stream' (Letter Q Γ)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control

def expand (M : Machine Q Γ) (c : Checkpoint Q Γ) : Configuration Q Γ :=
  ⟨ready c.state, Stream'.map work c.left,
    work c.current :: (c.right.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
    c.history⟩

def next (M : Machine Q Γ) (c : Checkpoint Q Γ) : Checkpoint Q Γ :=
  let v := M.transition c.state c.current
  match v.move with
  | .stay => ⟨v.state, c.left, v.write, c.right, record (.stay c.state c.current) :: c.history⟩
  | .left => ⟨v.state, c.left.tail, c.left.head, v.write :: c.right,
      record (.left c.state c.current c.left.head) :: c.history⟩
  | .right =>
      match c.right with
      | [] => ⟨v.state, v.write :: c.left, M.blank, [],
          record (.extend c.state c.current) :: c.history⟩
      | List.cons a w => ⟨v.state, v.write :: c.left, a, w,
          record (.right c.state c.current a) :: c.history⟩

def WorkStep (M : Machine Q Γ) (c d : Checkpoint Q Γ) : Prop :=
  c.state ≠ M.halt ∧ d = c.next M

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ] {M : Machine Q Γ}

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ]

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def rationalWord {B : ℕ} (digit : S → Fin B) : List S → ℚ
  | [] => 0
  | a :: w => (B : ℚ)⁻¹ * ((digit a : ℚ) + rationalWord digit w)

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

def rationalTailCode {B : ℕ} (digit : S → Fin B) (w : List S) (a : S) : ℚ :=
  rationalWord digit w + (B : ℚ)⁻¹ ^ w.length * ((digit a : ℚ) / ((B : ℚ) - 1))

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter

def initial (M : Machine Q Γ) (q₀ : Q) (w : List Γ) : Checkpoint Q Γ :=
  ⟨q₀, Stream'.const M.blank, w.headD M.blank, w.tail, Stream'.const (work M.blank)⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

def rationalInitial (M : Machine Q Γ) (q₀ : Q) (w : List Γ) : Fin 3 → ℚ :=
  let b := Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) [] (work M.blank : Letter Q Γ)
  let v : List (Letter Q Γ) := work (w.headD M.blank) :: (w.tail.map work ++ [boundary])
  ![4 * (placement M (.ready q₀) : ℚ) + b,
    Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) v (work M.blank), b]

end BalancedTransport.Recorder.Checkpoint
end

end OAI


