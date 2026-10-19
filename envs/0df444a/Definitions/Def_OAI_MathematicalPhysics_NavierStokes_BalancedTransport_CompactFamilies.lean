-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:47:08.22918+00:00
-- url     : https://prove2.me/theorems/1db47a51-1b21-451d-a4a0-b991e794b676
-- title:
--   Finite sums of moving-box velocities
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   For a finite index set $\iota$, reference boxes $[a_i,b_i]$, curves $c_i(t)$ and positive scalings $d_i(t)$, and a margin $\eta$, the family velocity is
--   $$
--   u(t,x)=\sum_{i\in\iota}u_i(t,x),
--   $$
--   where $u_i$ is the moving-box velocity of the box $c_i(t)+d_i(t)[a_i,b_i]$ with margin $\eta$. When the enlarged boxes are disjoint, $u$ moves each box by its own affine motion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/CompactFamilies.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/CompactFamilies.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

def familyVelocity (a b : ι → Space) (c d : ι → ℝ → Space) (η : ℝ) : Velocity :=
  fun t x => ∑ i, movingBoxVelocity (a i) (b i) (c i) (d i) η t x

end BalancedTransport.Geometry
end

end OAI


