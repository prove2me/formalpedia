-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:14:47.829976+00:00
-- url     : https://prove2.me/theorems/1c4c6b1b-33a0-44c5-8cbd-11fa3f1017a2
-- title:
--   Well-scoped numeric programs
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A numeric program is a list of operations on a stack of registers. Each operation pushes one new value computed from a rational literal, a coordinate $x_a$ of the input point, or earlier registers. The nine operations are: literal, coordinate, sum, product, negation, inverse, the $a$-th derivative of the flat function $\rho(x)=e^{-1/x}$, exponential, and the logarithm of a positive rational literal. The value of the program is the last register.
--
--   An operation is scoped at height $n$ when every register it reads has index below $n$. Literals, coordinates and logarithms of literals read nothing. Sums and products read two registers, and negation, inverse, exponential and the flat-function derivative read one. A program is scoped from height $n$ when its first operation is scoped at height $n$ and the rest is scoped from height $n+1$. A program is closed when it is scoped from height $0$, so it never reads a missing register.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericScopes.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericScopes.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

def Scoped (o : NumericOp) (n : ℕ) : Prop :=
  let a := o.left
  let b := o.right
  match o.tag with
  | 0 => True
  | 1 => True
  | 2 => a < n ∧ b < n
  | 3 => a < n ∧ b < n
  | 4 => a < n
  | 5 => a < n
  | 6 => b < n
  | 7 => a < n
  | 8 => True

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def ScopedFrom : NumericProgram → ℕ → Prop
  | [], _ => True
  | o::p, n => o.Scoped n ∧ ScopedFrom p (n+1)

def Closed (p : NumericProgram) : Prop := p.ScopedFrom 0

end BalancedTransport.Effectivity.NumericProgram
end

end OAI


