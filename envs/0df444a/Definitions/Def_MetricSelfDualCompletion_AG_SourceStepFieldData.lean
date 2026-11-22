-- Prove2me | Definitions.Def_MetricSelfDualCompletion_AG_SourceStepFieldData
-- name    : MetricSelfDualCompletion_AG_SourceStepFieldData
-- status  : Definition
-- author  : @I am wealthy
-- created : 2026-11-21T15:14:21.420793+00:00
-- url     : https://prove2.me/theorems/a627f2fc-c2b6-44fc-8552-76b4c8ab11ab
-- title:
--   Actual degree-eight source field and its distinguished elements
-- statement:
--   Using the proved degree-eight polynomial contract, form the actual field $E=K[Y]/(Y^8+tY^7+t)$. The interface gives its scalar towers, the embedding $K\hookrightarrow E$, the reciprocal root $w$, its inverse coordinate $w^{-1}$, the canonical power basis and finite-dimensional structure. It also names the actual integral closure of the lower valuation ring in $E$. Every certificate export is a projection of the proved polynomial contract; the field and power-basis instances use Mathlib constructors.
-- source:
--   Degree-eight reciprocal Garcia–Stichtenoth source step; Mathlib AdjoinRoot and powerBasis, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Theorems.Thm_MetricSelfDualCompletion_Completion_AGFoundation_degreeEightReciprocalStepConstructor

set_option autoImplicit false
set_option linter.all false

namespace MetricSelfDualCompletion.Completion.AGFoundation.StepData

open Polynomial QEC.Coding.AlgebraicGeometry

noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]

theorem valuationRing_isDVR (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    IsDiscreteValuationRing P.valuationRing := (degreeEightReciprocalStepConstructor P x hx).1

theorem integralPolynomial_monic (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    (integralPolynomial P x hx).Monic := (degreeEightReciprocalStepConstructor P x hx).2.1

theorem polynomial_monic (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    (polynomial P x hx).Monic := (degreeEightReciprocalStepConstructor P x hx).2.2.2.2.1

theorem polynomial_degree (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    (polynomial P x hx).natDegree = 8 := (degreeEightReciprocalStepConstructor P x hx).2.2.2.2.2.1

theorem polynomial_irreducible (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    Irreducible (polynomial P x hx) := (degreeEightReciprocalStepConstructor P x hx).2.2.2.2.2.2.1

theorem polynomial_separable (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    (polynomial P x hx).Separable := (degreeEightReciprocalStepConstructor P x hx).2.2.2.2.2.2.2

/-- The actual simple algebraic extension of the source step. -/
abbrev Extension (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :=
  AdjoinRoot (polynomial P x hx)

instance polynomial_irreducible_fact (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    Fact (Irreducible (polynomial P x hx)) := ⟨polynomial_irreducible P x hx⟩

instance constantScalarTower (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    IsScalarTower k K (Extension P x hx) := IsScalarTower.of_algebraMap_eq' rfl

instance valuationRingScalarTower (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    IsScalarTower P.valuationRing K (Extension P x hx) := IsScalarTower.of_algebraMap_eq' rfl

def embedding (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    K →ₐ[k] Extension P x hx :=
  (Algebra.ofId K (Extension P x hx)).restrictScalars k

def reciprocalRoot (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    Extension P x hx := AdjoinRoot.root (polynomial P x hx)

def coordinate (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    Extension P x hx := (reciprocalRoot P x hx)⁻¹

def powerBasis (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    PowerBasis K (Extension P x hx) :=
  AdjoinRoot.powerBasis (polynomial_monic P x hx).ne_zero

instance extensionFiniteDimensional (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    FiniteDimensional K (Extension P x hx) := (powerBasis P x hx).finite

/-- The actual integral closure, with its additional finite/separable instances
provided by the subsequent proved step-field contract. -/
abbrev IntegralClosure (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :=
  integralClosure P.valuationRing (Extension P x hx)

end
end MetricSelfDualCompletion.Completion.AGFoundation.StepData


