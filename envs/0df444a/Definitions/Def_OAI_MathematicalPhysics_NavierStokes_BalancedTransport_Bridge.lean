-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:57:10.136426+00:00
-- url     : https://prove2.me/theorems/899e4a12-c66b-4187-a0e1-5ecdd6b9f16d
-- title:
--   Velocity templates that realize every recorder step
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   The recorder is a three-stack machine that simulates a Turing machine $M$ reversibly. A configuration has a control state and three infinite stacks: left, right and history. Stack letters are work symbols $a$, marked symbols $\hat a$, a boundary marker, and records of executed transitions. Each step replaces finite prefixes of the three stacks and the control according to one row of a finite table.
--
--   Let the observer be the open cube $(-1,2)^3$. A velocity $v$ is a guarded template for a machine $M$ when, for every valid row and every point $x$ of the row's source box, there is a path $\gamma:[0,1]\to\mathbb R^3$ such that:
--
--   1. $\gamma(0)=x$ and $\gamma(1)$ is the image of $x$ under the row's box map, which rewrites the prefixes in base $1/B$;
--   2. $\gamma'(t)=v(t,\gamma(t))$ for $t\in[0,1]$;
--   3. if the target control is not the halting ready state, then $\gamma$ stays outside the observer.
--
--   Such a template moves coded configurations one recorder step per unit of time, and it reaches the observer only when the machine halts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Bridge.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Bridge.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*} {M : Machine Q Γ}

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*} {M : Machine Q Γ}

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} {M : Machine Q Γ}
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

def GuardedTemplate (M : Machine Q Γ) (v : Velocity) : Prop :=
  ∀ r : Row Q Γ, r.valid M → ∀ x,
    x ∈ (r.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
      (fun a => (digit a : ℝ)) (placement M) →
    ∃ γ : ℝ → Space,
      γ 0 = x ∧ γ 1 = (r.instruction M).fullMap M x ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (v t (γ t)) (Set.Icc 0 1) t) ∧
      ((r.instruction M).targetControl ≠ .ready M.halt →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ observer)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set
open scoped NNReal

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q]
variable {M : Machine Q Γ} {v load : Velocity} {X : MaterialFlow} {L : ℝ≥0}

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Geometry
open Set

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open BalancedTransport.Geometry

end BalancedTransport.FiniteMachine
end

end OAI


