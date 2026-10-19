-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:04:27.339434+00:00
-- url     : https://prove2.me/theorems/f054751c-9d51-4f4f-9f9c-bb4f8eae9218
-- title:
--   Elementary pieces of an effective velocity family
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   1. **Rational floor and phase.** For rational $q\ge0$, the floor $\lfloor q\rfloor$ is computed from numerator and denominator. The phase of $q$ is $q$ if $q<1$ and $q-\lfloor q\rfloor$ otherwise.
--   2. **Rational arguments.** The rational vector $(t,x,p)\in\mathbb Q^{4+d}$.
--   3. **Elementary pieces.** Fix two parametrized velocities: a loading part $L(p)$ and a template $V(p)$. Fix also rational parameters $\kappa(n)\in\mathbb Q^d$ indexed by codes $n$. A family $F$ of velocities, one for each machine $M$ and input $w$, is built from these pieces when, for every $t\ge0$ and with $p=\kappa(\mathrm{code}(M,w))$:
--      - if $t<1$, $F(M,w)$ agrees with $L(p)$ on a neighbourhood of $t$;
--      - if $t\ge1$, $F(M,w)$ agrees near $t$ with the shifted template $s\mapsto V(p)(s-\lfloor t\rfloor)$.
--   4. **Grid radius.** $C+1+\sum_i|\mathrm{num}(x_i)|$ for a rational point $x$ and a bound $C$.
--
--   Gluing results show that such families are effective when $L$, $V$ and $\kappa$ are.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveGluing.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveGluing.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryJets

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

def rationalNatFloor (q : ℚ) : ℕ := q.num.toNat / q.den

def rationalPhase (q : ℚ) : ℚ := if q < 1 then q else q - rationalNatFloor q

def fieldRationalArgs {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) :
    Fin (4+d) → ℚ := Fin.addCases (Fin.cases t x) p

def ElementaryPieces {d : ℕ} (L V : (Fin d → ℝ) → Velocity)
    (κ : ℕ → Fin d → ℚ) (F : Family Velocity) : Prop :=
  ∀ M w t, 0 ≤ t →
    if t < 1 then
      F M w =ᶠ[𝓝 t] L (fun i => (κ (inputCode M w) i : ℝ))
    else F M w =ᶠ[𝓝 t]
      (fun s => V (fun i => (κ (inputCode M w) i : ℝ)) (s - (⌊t⌋ : ℤ)))

def gridRadius (C : ℕ) (x : Fin 3 → ℚ) : ℕ := C + 1 + ∑ i, (x i).num.natAbs

end BalancedTransport.Effectivity
end

end OAI


