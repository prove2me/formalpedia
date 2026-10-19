-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:30:55.051648+00:00
-- url     : https://prove2.me/theorems/8e5c3dc8-474f-4f9a-a84a-ecd6b25bffb2
-- title:
--   The loading flow carrying the fixed label to a coded point
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   Let $p_*=(4,0,0)$ be the fixed label. For a target point $z\in\mathbb R^3$ and a margin $\eta>0$:
--
--   1. **Switch.** $\sigma(t)=S(2t-\frac12)$, where $S$ is a smooth transition from $0$ to $1$. So $\sigma=0$ for $t\le\frac14$ and $\sigma=1$ for $t\ge\frac34$.
--   2. **Centre.** $\sigma(t)(z-p_*)$.
--   3. **Loading velocity.** The moving-box velocity of the degenerate box $\{p_*\}$, translated by this centre with unit scaling and margin $\eta$. It translates a neighbourhood of $p_*$ rigidly.
--   4. **Loading path.** $t\mapsto p_*+\sigma(t)(z-p_*)$. It carries the particle starting at $p_*$ to $z$ during $\frac14\le t\le\frac34$.
--   5. **Support.** The closed $2\eta$-enlargement of the box with opposite corners $p_*$ and $z$, which contains the support of the loading velocity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Loading.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Loading.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set

def loadingSwitch (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

def loadingCenter (z : Space) (t : ℝ) : Space := loadingSwitch t • (z - fixedLabel)

def loadingVelocity (z : Space) (η : ℝ) : Velocity :=
  movingBoxVelocity fixedLabel fixedLabel (loadingCenter z) (fun _ => 1) η

def loadingPath (z : Space) : ℝ → Space :=
  affinePath (loadingCenter z) (fun _ => 1) fixedLabel

def loadingSupport (z : Space) (η : ℝ) : Set Space :=
  closedEnlargement (fun i => min (fixedLabel i) (z i))
    (fun i => max (fixedLabel i) (z i)) (2 * η)

end BalancedTransport.Geometry
end

end OAI


