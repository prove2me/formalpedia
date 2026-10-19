-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:12:00.191422+00:00
-- url     : https://prove2.me/theorems/97ccbe8c-05b0-451e-8131-ef2128280c59
-- title:
--   Forward-mode differentiation of numeric operations
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A numeric program is a list of operations on a stack of registers. Each operation pushes one new value computed from a rational literal, a coordinate $x_a$ of the input point, or earlier registers. The nine operations are: literal, coordinate, sum, product, negation, inverse, the $a$-th derivative of the flat function $\rho(x)=e^{-1/x}$, exponential, and the logarithm of a positive rational literal. The value of the program is the last register.
--
--   1. **Differentials.** For a coordinate direction $k$, registers $s$ and their derivatives $v$, the derivative of each operation is given by the usual rules. Constants and logarithms of literals give $0$, the coordinate $x_a$ gives $1$ if $a=k$ and $0$ otherwise, $(s_as_b)'=v_as_b+s_av_b$, $(s_a^{-1})'=-v_as_a^{-2}$, $(\rho^{(a)}(s_b))'=\rho^{(a+1)}(s_b)v_b$ and $(e^{s_a})'=e^{s_a}v_a$.
--   2. **Dual blocks.** Each operation is replaced by a block of five operations. In the transformed program, register $5j+4$ holds the value of original register $j$ and register $5j$ holds its derivative in direction $k$; the remaining registers hold intermediate products.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericDifferentiation.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericDifferentiation.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

def differential (k : Fin d) (o : NumericOp) (s v : ℕ → ℝ) : ℝ :=
  let a := o.left
  let b := o.right
  match o.tag with
  | 0 => 0
  | 1 => if Fin.ofNat d a = k then 1 else 0
  | 2 => v a + v b
  | 3 => v a * s b + s a * v b
  | 4 => -v a
  | 5 => -(v a * (s a)⁻¹ ^ 2)
  | 6 => rhoJet (a+1) (s b) * v b
  | 7 => Real.exp (s a) * v a
  | 8 => 0

def dualCase (k : Fin d) (j : Fin 9) (o : NumericOp) : NumericProgram :=
  let a := o.left
  let b := o.right
  let z : NumericOp := (0,0,0,0)
  match j with
  | 0 => [o,z,z,z,z]
  | 1 => [o,z,z,z,(0,(if Fin.ofNat d a = k then 1 else 0),0,0)]
  | 2 => [(2,0,5*a+4,5*b+4),z,z,z,(2,0,5*a+4,5*b+4)]
  | 3 => [(3,0,5*a+4,5*b+4),(3,0,5*a+1,5*b+5),
      (3,0,5*a+6,5*b+2),z,(2,0,2,1)]
  | 4 => [(4,0,5*a+4,0),z,z,z,(4,0,5*a+4,0)]
  | 5 => [(5,0,5*a+4,b),z,(3,0,1,1),(3,0,5*a+3,0),(4,0,0,0)]
  | 6 => [(6,0,a,5*b+4),(6,0,a+1,5*b+5),z,z,(3,0,2,5*b+4)]
  | 7 => [(7,0,5*a+4,0),z,z,z,(3,0,3,5*a+4)]
  | 8 => [o,z,z,z,z]

def dual (k : Fin d) (o : NumericOp) : NumericProgram := dualCase d k o.tag o

end BalancedTransport.Effectivity.NumericOp
end

end OAI


