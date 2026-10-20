-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:29:52.987427+00:00
-- url     : https://prove2.me/theorems/9ae40d81-13ff-4262-b14a-53b8c249b4e7
-- title:
--   Running numeric programs
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A numeric program is a list of operations on a stack of registers. Each operation pushes one new value computed from a rational literal, a coordinate $x_a$ of the input point, or earlier registers. The nine operations are: literal, coordinate, sum, product, negation, inverse, the $a$-th derivative of the flat function $\rho(x)=e^{-1/x}$, exponential, and the logarithm of a positive rational literal. The value of the program is the last register. Fix a dimension $d\ge1$.
--
--   1. **Runs.** Starting from a register list, the real, rational and bound semantics of the operations are applied in order, each pushing its result.
--   2. **Validity.** A program is valid at $x\in\mathbb R^d$ when every inverse operation it executes from the empty register list is valid.
--   3. **Values.** The real value of a program at $x$ is its last real register. Its bound is the last pair of the bound run, where $C$ bounds the coordinates.
--   4. **Approximation.** At a rational point $x$ and precision $n$, the program is run rationally at precision $n+E$, where $E$ is the error multiplier of its bound. The result is the last register. The register estimates then give error at most $2^{-n}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericEvaluation.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def realFrom (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) : List ℝ :=
  p.foldl (fun s o => o.real d x s :: s) s

def rationalFrom (p : NumericProgram) (x : Fin d → ℚ) (n : ℕ) (s : List ℚ) : List ℚ :=
  p.foldl (fun s o => o.rational d x n s :: s) s

def boundFrom (p : NumericProgram) (C : ℕ) (s : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  p.foldl (fun s o => o.bound C s :: s) s

def ValidFrom (x : Fin d → ℝ) : NumericProgram → List ℝ → Prop
  | [], _ => True
  | o :: p, s => o.Valid s ∧ ValidFrom x p (o.real d x s :: s)

def Valid (p : NumericProgram) (x : Fin d → ℝ) : Prop := ValidFrom x p []

def real (p : NumericProgram) (x : Fin d → ℝ) : ℝ := (p.realFrom x []).getD 0 0

def bound (p : NumericProgram) (C : ℕ) : ℕ × ℕ := (p.boundFrom C []).getD 0 (0,0)

def approximation (p : NumericProgram) (C : ℕ) (x : Fin d → ℚ) (n : ℕ) : ℚ :=
  (p.rationalFrom x (n + (p.bound C).2) []).getD 0 0

end BalancedTransport.Effectivity.NumericProgram
end

end OAI


