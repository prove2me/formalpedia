-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:24:32.052983+00:00
-- url     : https://prove2.me/theorems/71727d8d-5299-4870-bbfb-bfc4868b3afc
-- title:
--   Kinetic energy of square-integrable vector fields
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   Let $L^2$ denote square-integrable fields $\mathbb R^3\to\mathbb R^3$ with respect to Lebesgue measure. The coordinate maps $V\mapsto V_i$ from $L^2(\mathbb R^3;\mathbb R^3)$ to $L^2(\mathbb R^3;\mathbb R)$ are continuous and linear. The energy and the energy rate are
--   $$
--   \mathcal E(V)=\sum_{i=0}^2\|V_i\|_{L^2}^2,\qquad \mathcal E'(V;W)=2\sum_{i=0}^2\langle V_i,W_i\rangle_{L^2}.
--   $$
--   If $V(t)$ is a differentiable curve in $L^2$ with derivative $W(t)$, then $\mathcal E(V(t))$ has derivative $\mathcal E'(V(t);W(t))$. This is the basis of the energy argument for uniqueness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergyCurve.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EnergyCurve.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

def coordinateL2 (i : Fin 3) :
    Lp Space 2 (volume : Measure Space) →L[ℝ] Lp ℝ 2 (volume : Measure Space) :=
  ContinuousLinearMap.compLpL 2 volume (ContinuousLinearMap.proj i)

def l2Energy (V : Lp Space 2 (volume : Measure Space)) : ℝ :=
  ∑ i : Fin 3, ‖coordinateL2 i V‖ ^ 2

def l2EnergyRate (V W : Lp Space 2 (volume : Measure Space)) : ℝ :=
  2 * ∑ i : Fin 3, inner ℝ (coordinateL2 i V) (coordinateL2 i W)

end BalancedTransport.Analysis
end

end OAI


