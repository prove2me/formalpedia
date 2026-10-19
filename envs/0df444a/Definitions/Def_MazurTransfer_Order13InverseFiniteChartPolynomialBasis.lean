-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteChartPolynomialBasis
-- name    : MazurTransfer_Order13InverseFiniteChartPolynomialBasis
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:41:11.094602+00:00
-- url     : https://prove2.me/theorems/fabf7269-a7a7-4187-9bd0-d758666d307a
-- title:
--   The actual inverse-chart polynomial basis of rank three
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $V$ be the actual inverse finite chart and $g$ its specified inverse parameter section. The structural section ring $\Gamma(V)$ has the specified three-element basis over $R[S]$, where $S$ acts as $g$. The polynomial map defined by $g$ is finite. This basis is the actual inverse coordinate basis transported through the structural section comparison, and supplies all positive inverse-parameter powers for integral FiniteMapData.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Three closed declarations following the original Order13InverseParameterCurvePolynomialBasis.lean transport and the structural parameter-finiteness consequence. Uses the original published inverse finite-algebra basis, the actual inverse affine-open presentation and the structural section R-algebra comparison. Named downstream consumers: inverse parameter powers and finite_g in unchanged actual integral FiniteMapData. Native, strict and full frontend checks pass with standard axioms only.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse-chart sections have their specified three-element basis for the literal inverse parameter action.
Named downstream consumers: inverse parameter powers and finite_g in unchanged actual integral FiniteMapData. The transport follows Order13InverseParameterCurvePolynomialBasis.lean. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartSections
import Definitions.Def_MazurTransfer_Order13ActualInverseFiniteBasis
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial Module
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13InverseParameterFiniteAlgebra
namespace MazurTransfer.Order13InverseFiniteChartFromPublicTheorems
open Order13InverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def polynomialAlgEquiv (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
      (aeval (parameterSection R h104)).toRingHom.toAlgebra
    Γ(curveScheme R, inverseChartOpen R) ≃ₐ[Polynomial R] candidateAlgebra R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  let E := sectionsAlgEquiv R h104
  refine { E.toRingEquiv with commutes' := ?_ }
  intro P
  change E (aeval (parameterSection R h104) P) = algebraMap (Polynomial R) (candidateAlgebra R) P
  rw [← aeval_algHom_apply E]
  rw [sectionsAlgEquiv_parameter]
  exact (eval_unique (IsScalarTower.toAlgHom R (Polynomial R) (candidateAlgebra R)) P).symm

def polynomialBasis (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
      (aeval (parameterSection R h104)).toRingHom.toAlgebra
    Basis (Fin 3) (Polynomial R) Γ(curveScheme R, inverseChartOpen R) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  exact (candidateBasis R h104).map (polynomialAlgEquiv R h104).symm.toLinearEquiv

theorem parameter_finite (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    (aeval (parameterSection R h104) : Polynomial R →ₐ[R]
      Γ(curveScheme R, inverseChartOpen R)).toRingHom.Finite := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  exact Module.Finite.of_basis (polynomialBasis R h104)

end MazurTransfer.Order13InverseFiniteChartFromPublicTheorems
#print axioms MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.polynomialAlgEquiv
#print axioms MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.polynomialBasis
#print axioms MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameter_finite


