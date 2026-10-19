-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:23:18.367462+00:00
-- url     : https://prove2.me/theorems/54c73f6c-a650-4752-9797-411e66d3d6fe
-- title:
--   Elementary functions computed by numeric programs
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A numeric program is a list of operations on a stack of registers. Each operation pushes one new value computed from a rational literal, a coordinate $x_a$ of the input point, or earlier registers. The nine operations are: literal, coordinate, sum, product, negation, inverse, the $a$-th derivative of the flat function $\rho(x)=e^{-1/x}$, exponential, and the logarithm of a positive rational literal. The value of the program is the last register.
--
--   A function $f:\mathbb R^d\to\mathbb R$, with $d\ge1$, is elementary when some nonempty closed numeric program is valid at every point of $\mathbb R^d$ and has real value $f(x)$ at every $x$. Elementary functions are differentiable, and their partial derivatives are again elementary. They are closed under sums, products, negation, composition with $\exp$ and with the derivatives of $e^{-1/x}$, and inversion of functions bounded below by $\frac1{n+1}$. Their values and derivatives at rational points can be approximated to any precision by running the program rationally.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Elementary.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Elementary.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

def Elementary {d : ℕ} [NeZero d] (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ p : NumericProgram, p ≠ [] ∧ p.Closed ∧ (∀ x : Fin d → ℝ, p.Valid x) ∧ p.real = f

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

end BalancedTransport.Effectivity.Elementary
end

end OAI


