-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:55:07.063455+00:00
-- url     : https://prove2.me/theorems/b81b76ac-0355-4bd3-977c-ff7884ddf85d
-- title:
--   Straight-line numeric programs and their interpretations
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A numeric program is a list of operations on a stack of registers. Each operation pushes one new value computed from a rational literal, a coordinate $x_a$ of the input point, or earlier registers. The nine operations are: literal, coordinate, sum, product, negation, inverse, the $a$-th derivative of the flat function $\rho(x)=e^{-1/x}$, exponential, and the logarithm of a positive rational literal. The value of the program is the last register.
--
--   1. **Real semantics.** Each operation acts on the real registers. The inverse is $s\mapsto s^{-1}$ and the flat-function operation gives $\rho^{(a)}$.
--   2. **Rational semantics at precision $p$.** Each operation acts on rational registers, using the rational approximations of $\rho^{(a)}$, $\exp$ and $\log$ at precision $p$. An inverse operation carrying a bound $b$ inverts $\max\bigl(\frac1{b+1},s\bigr)$.
--   3. **Bounds.** Each operation propagates a pair (magnitude bound, error multiplier) from the pairs of its operands. For example, a product with operand pairs $(A,E)$ and $(B,F)$ gets $\bigl(AB,(A+E)F+BE\bigr)$.
--   4. **Validity.** An inverse operation with bound $b$ is valid when its operand is at least $\frac1{b+1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

abbrev NumericOp := Fin 9 × ℚ × ℕ × ℕ

abbrev NumericProgram := List NumericOp

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

def tag (o : NumericOp) : Fin 9 := o.1

def rat (o : NumericOp) : ℚ := o.2.1

def left (o : NumericOp) : ℕ := o.2.2.1

def right (o : NumericOp) : ℕ := o.2.2.2

noncomputable def real (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s : List ℝ) : ℝ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  match o.tag with
  | 0 => q
  | 1 => x (Fin.ofNat d a)
  | 2 => s.getD a 0 + s.getD b 0
  | 3 => s.getD a 0 * s.getD b 0
  | 4 => -s.getD a 0
  | 5 => (s.getD a 0)⁻¹
  | 6 => rhoJet a (s.getD b 0)
  | 7 => Real.exp (s.getD a 0)
  | 8 => if 0 < q then Real.log (q : ℝ) else 0

noncomputable def rationalCase (d : ℕ) [NeZero d] (j : Fin 9) (o : NumericOp) (x : Fin d → ℚ)
    (p : ℕ) (s : List ℚ) : ℚ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  match j with
  | 0 => q
  | 1 => x (Fin.ofNat d a)
  | 2 => s.getD a 0 + s.getD b 0
  | 3 => s.getD a 0 * s.getD b 0
  | 4 => -s.getD a 0
  | 5 => (max ((b + 1 : ℕ) : ℚ)⁻¹ (s.getD a 0))⁻¹
  | 6 => rhoApprox a (s.getD b 0) p
  | 7 => expApprox (s.getD a 0) p
  | 8 => logApprox q p

noncomputable def rational (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p : ℕ) (s : List ℚ) : ℚ := rationalCase d o.tag o x p s

def boundCase (j : Fin 9) (o : NumericOp) (C : ℕ) (s : List (ℕ × ℕ)) : ℕ × ℕ :=
  let a := o.left
  let b := o.right
  let q := o.rat
  let A := (s.getD a (0,0)).1
  let E := (s.getD a (0,0)).2
  let B := (s.getD b (0,0)).1
  let F := (s.getD b (0,0)).2
  match j with
  | 0 => (q.num.natAbs, 0)
  | 1 => (C, 0)
  | 2 => (A + B, E + F)
  | 3 => (A * B, (A + E) * F + B * E)
  | 4 => (A, E)
  | 5 => (b + 1, (b + 1)^2 * E)
  | 6 => (rhoBound a 0, 1 + rhoBound (a+1) 0 * F)
  | 7 => (3^A, 1 + 3^(A+E) * E)
  | 8 => (q.num.natAbs + q⁻¹.num.natAbs, 1)

def bound (o : NumericOp) (C : ℕ) (s : List (ℕ × ℕ)) : ℕ × ℕ :=
  boundCase o.tag o C s

def Valid (o : NumericOp) (s : List ℝ) : Prop :=
  o.tag = 5 → ((o.right + 1 : ℕ) : ℝ)⁻¹ ≤ s.getD o.left 0

end BalancedTransport.Effectivity.NumericOp
end

end OAI


