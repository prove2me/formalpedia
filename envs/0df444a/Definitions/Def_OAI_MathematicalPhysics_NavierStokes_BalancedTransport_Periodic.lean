-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:32:30.026065+00:00
-- url     : https://prove2.me/theorems/9a0d17b4-4623-4bf6-abb4-1045d06b9e64
-- title:
--   Periodic repetition of a template velocity after loading
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   1. **Time collars.** A field has time collars when $v(t,\cdot)=0$ for $t<\frac14$ and for $t>\frac34$.
--   2. **Repetition.** The repeated template is the $1$-periodic field
--   $$
--   \tilde v(t,x)=\sum_{n\in\mathbb Z}v(t-n,x).
--   $$
--   For a template with time collars, at most one term is nonzero at each time.
--   3. **Gate.** $g(t)=S(4t-3)$, where $S$ is a smooth transition from $0$ to $1$. So $g=0$ for $t\le\frac34$ and $g=1$ for $t\ge1$.
--   4. **Loaded repetition.** $u=\ell+g\,\tilde v$, the loading velocity $\ell$ during the first unit of time followed by periodic repetition of the template.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Periodic.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Periodic.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set

def TimeCollars {F : Type*} [Zero F] (v : Field F) : Prop :=
  ∀ t, t < 1 / 4 ∨ 3 / 4 < t → v t = 0

def repeatTemplate (v : Velocity) : Velocity :=
  fun t x => ∑' n : ℤ, v (t - n) x

def afterLoadingGate (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 3)

def loadedRepeat (load template : Velocity) : Velocity :=
  fun t x => load t x + afterLoadingGate t • repeatTemplate template t x

end BalancedTransport.Geometry
end

end OAI


