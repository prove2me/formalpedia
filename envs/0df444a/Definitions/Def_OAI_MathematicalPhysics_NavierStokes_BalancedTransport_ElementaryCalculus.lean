-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:44:52.093085+00:00
-- url     : https://prove2.me/theorems/711f40a7-4214-43a8-addf-b8d2f29541e0
-- title:
--   Elementary scalar and vector fields depending on parameters
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A function of several real variables is elementary when it is computed by a straight-line numeric program built from rational constants, coordinates, sums, products, negation, guarded inverses, $\exp$, logarithms of rationals and derivatives of $e^{-1/x}$.
--
--   1. **Arguments.** For parameters $p\in\mathbb R^d$, time $t$ and position $x\in\mathbb R^3$, the argument vector is $(t,x_0,x_1,x_2,p_0,\dots,p_{d-1})\in\mathbb R^{4+d}$. Projections recover $p$, $t$ and $x$ from it.
--   2. **Elementary scalar fields.** A parametrized scalar field $f(p)(t,x)$ is elementary when $(t,x,p)\mapsto f(p)(t,x)$ is elementary on $\mathbb R^{4+d}$.
--   3. **Elementary vector fields.** A parametrized velocity is elementary when each of its three components is an elementary scalar field.
--
--   Time and space derivatives of elementary scalar fields are again elementary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryCalculus.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

def fieldArgs {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) : Fin (4+d) → ℝ :=
  Fin.append (Fin.cons t x) p

def fieldParam {d : ℕ} (z : Fin (4+d) → ℝ) : Fin d → ℝ := fun k => z (Fin.natAdd 4 k)

def fieldTime {d : ℕ} (z : Fin (4+d) → ℝ) : ℝ := z (Fin.castAdd d 0)

def fieldSpace {d : ℕ} (z : Fin (4+d) → ℝ) : Space := fun k => z (Fin.castAdd d k.succ)

@[simp] lemma fieldParam_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldParam (fieldArgs p t x) = p := by ext k; simp [fieldParam,fieldArgs]

@[simp] lemma fieldTime_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldTime (fieldArgs p t x) = t := by simp [fieldTime,fieldArgs]

@[simp] lemma fieldSpace_args {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    fieldSpace (fieldArgs p t x) = x := by ext k; simp [fieldSpace,fieldArgs]

@[simp] lemma fieldArgs_parts {d : ℕ} (z : Fin (4+d) → ℝ) :
    fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z) = z := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [fieldArgs,fieldTime]
    · simp [fieldArgs,fieldTime,fieldSpace]
  · intro j
    simp [fieldArgs,fieldParam,fieldTime]

def ElementaryScalar {d : ℕ} (f : (Fin d → ℝ) → Field ℝ) : Prop :=
  Elementary (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z))

def ElementaryField {d : ℕ} (f : (Fin d → ℝ) → Velocity) : Prop :=
  ∀ i, ElementaryScalar (fun p t x => f p t x i)

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI


