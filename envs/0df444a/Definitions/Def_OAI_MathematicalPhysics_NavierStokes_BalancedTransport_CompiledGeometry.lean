-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:00:54.854187+00:00
-- url     : https://prove2.me/theorems/7fc4d39a-7256-4c01-8fe8-cfc0b36f355a
-- title:
--   Box layouts of the recorder's source and target boxes
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   1. **Coded layouts.** For a ratio $r$, digits $\delta$, origins $o_i$ and triples of words $u_i$, the box layout with centres $o_{ik}+\mathrm{word}(u_{ik})+\frac12r^{|u_{ik}|}$ and half-widths $\frac12r^{|u_{ik}|}$. Box $i$ is the product of the coding intervals of $u_{i0},u_{i1},u_{i2}$, shifted by $o_i$.
--   2. **Active rows.** The valid rows of the recorder's table for a machine $M$.
--   3. **Source and target layouts.** Using ratio $1/B$, the letter digits and the origins $(4k,0,0)$ attached to control states: the layout of the source boxes of all active rows and the layout of their target boxes.
--   4. **Safe rows.** The active rows whose target control is not the halting ready state; the motion must keep their boxes away from the observer.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/CompiledGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/CompiledGeometry.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Coding
open BalancedTransport.Geometry
variable {S ι : Type*}

def layout (r : ℝ) (digit : S → ℝ) (o : ι → Space) (u : ι → Fin 3 → List S) :
    BoxLayout ι where
  center i k := o i k + word r digit (u i k) + r ^ (u i k).length / 2
  width i k := r ^ (u i k).length / 2

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
open BalancedTransport.Geometry
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

abbrev ActiveRow (M : Machine Q Γ) := {r : Row Q Γ // r ∈ table M}

def sourceLayout (M : Machine Q Γ) : BoxLayout (ActiveRow M) :=
  Coding.layout (base Q Γ : ℝ)⁻¹ (fun a : Letter Q Γ => (digit a : ℝ))
    (fun i => Coding.origin (placement M (i.val.instruction M).sourceControl))
    (fun i => (i.val.instruction M).sourcePrefixes)

def targetLayout (M : Machine Q Γ) : BoxLayout (ActiveRow M) :=
  Coding.layout (base Q Γ : ℝ)⁻¹ (fun a : Letter Q Γ => (digit a : ℝ))
    (fun i => Coding.origin (placement M (i.val.instruction M).targetControl))
    (fun i => (i.val.instruction M).targetPrefixes)

def safeRows (M : Machine Q Γ) : Set (ActiveRow M) :=
  {i | (i.val.instruction M).targetControl ≠ .ready M.halt}

end BalancedTransport.Recorder
end

end OAI


