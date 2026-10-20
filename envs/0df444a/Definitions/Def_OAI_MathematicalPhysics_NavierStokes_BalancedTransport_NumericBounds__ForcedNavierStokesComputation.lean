-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:28:02.847836+00:00
-- url     : https://prove2.me/theorems/1744a5eb-b394-4dad-ae2d-3df9f5ed2545
-- title:
--   Register estimates for numeric programs
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   Let $s$ be a list of real registers, $q$ a list of rational registers and $b$ a list of pairs of natural numbers $(B_j,E_j)$, all read with default values $0$. The triple satisfies the register estimate at precision $p$ when, for every index $j$,
--   $$
--   |s_j|\le B_j\qquad\text{and}\qquad|q_j-s_j|\le E_j\,2^{-p}.
--   $$
--   So $B_j$ bounds the size of register $j$ and $E_j$ is the multiplier of the error of its rational approximation. Each program operation preserves the estimate, which yields error bounds for whole programs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput__ForcedNavierStokesComputation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

structure RegisterEstimate (p : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ)) : Prop where
  magnitude : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ)
  accuracy : ∀ j, |(q.getD j 0 : ℝ) - s.getD j 0| ≤ ((b.getD j (0,0)).2 : ℝ) * error p

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

end OAI


