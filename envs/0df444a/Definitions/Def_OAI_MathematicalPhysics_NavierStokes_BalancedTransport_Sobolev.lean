-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:27:26.039975+00:00
-- url     : https://prove2.me/theorems/4807f895-2349-4d82-9d31-a64143233336
-- title:
--   Compactly supported smooth fields as curves in $L^2$
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   Let $K\subseteq\mathbb R^3$ be compact. A jointly smooth field $v$ that vanishes outside $K$ at every time has compactly supported slices $v(t,\cdot)$, and each slice is square integrable. This module defines:
--
--   1. **The $L^2$ curve.** $t\mapsto v(t,\cdot)$ as a curve in $L^2(\mathbb R^3)$.
--   2. **The size of the support.** The $L^2$ norm of the indicator function of $K$, which equals $|K|^{1/2}$. It converts uniform bounds into $L^2$ bounds, via $\|f\|_{L^2}\le\sup|f|\cdot|K|^{1/2}$ for $f$ supported in $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Sobolev.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Sobolev.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
lemma SpatiallySupported.hasCompactSupport {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hs : SpatiallySupported K v) (t : ℝ) : HasCompactSupport (v t) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (fun x hx => by
    by_contra hn
    exact hx (hs t x hn)) hK.isClosed

lemma JointSmooth.memLp {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) (t : ℝ) :
    MemLp (v t) 2 (volume : Measure Space) :=
  (hv.slice t).continuous.memLp_of_hasCompactSupport (hs.hasCompactSupport hK t)

def supportedL2Curve {K : Set Space} (hK : IsCompact K) {v : Field F}
    (hv : JointSmooth v) (hs : SpatiallySupported K v) : ℝ → Lp F 2 (volume : Measure Space) :=
  fun t => (hv.memLp hK hs t).toLp (v t)

def supportL2Size (K : Set Space) (hK : IsCompact K) : ℝ :=
  ‖indicatorConstLp (μ := (volume : Measure Space)) 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖

end BalancedTransport.Geometry
end

end OAI


