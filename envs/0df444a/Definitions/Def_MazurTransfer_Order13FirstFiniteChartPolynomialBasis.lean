-- Prove2me | Definitions.Def_MazurTransfer_Order13FirstFiniteChartPolynomialBasis
-- name    : MazurTransfer_Order13FirstFiniteChartPolynomialBasis
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:01:49.967571+00:00
-- url     : https://prove2.me/theorems/187c3f62-fcb5-4fd9-88cf-30583045952e
-- title:
--   The actual first-chart polynomial basis of rank three
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible, let $U$ be the actual first finite chart of the order-thirteen curve, and let $f$ be its specified parameter section. The structural section ring $\Gamma(U)$ has the specified three-element basis over $R[T]$, where $T$ acts as $f$. The constructor transports the actual coordinate basis along the structural section comparison. This basis supplies finite free level sets in the unchanged integral FiniteMapData existence contract.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. The two data constructors follow the original Order13SingleSectionComplementPolynomialBasis.lean transport argument, applied to the fresh public first-chart presentation. The specified sections R-action and parameter are retained. Native, strict and full frontend checks pass with standard axioms only, and both constructor types are closed. Named downstream consumers are finite free evaluated level sets and the unchanged arbitrarily-large FiniteMapData existence contract.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the actual first finite coordinate basis to the chosen first chart with its structural R-action and parameter section.
Named downstream consumer: finite free evaluated level sets and the unchanged arbitrarily-large FiniteMapData existence contract. The transport follows Order13SingleSectionComplementPolynomialBasis.lean. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartSections
import Definitions.Def_MazurTransfer_Order13ActualSingleSectionFiniteBasis
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial Module
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13SingleSectionFiniteAlgebra
namespace MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def polynomialAlgEquiv (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, chartOpen R) :=
      (aeval (parameterSection R h104)).toRingHom.toAlgebra
    Γ(curveScheme R, chartOpen R) ≃ₐ[Polynomial R]
      Order13SingleSectionFiniteAlgebra.candidateAlgebra R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, chartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  let E := sectionsAlgEquiv R h104
  refine { E.toRingEquiv with commutes' := ?_ }
  intro P
  change E (aeval (parameterSection R h104) P) =
    algebraMap (Polynomial R) (Order13SingleSectionFiniteAlgebra.candidateAlgebra R) P
  rw [← aeval_algHom_apply E]
  rw [sectionsAlgEquiv_parameter]
  exact (eval_unique (IsScalarTower.toAlgHom R (Polynomial R)
    (Order13SingleSectionFiniteAlgebra.candidateAlgebra R)) P).symm

def polynomialBasis (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, chartOpen R) :=
      (aeval (parameterSection R h104)).toRingHom.toAlgebra
    Basis (Fin 3) (Polynomial R) Γ(curveScheme R, chartOpen R) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (chartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, chartOpen R) :=
    (aeval (parameterSection R h104)).toRingHom.toAlgebra
  exact (Order13SingleSectionFiniteAlgebra.candidateBasis R
    (Order13InverseParameterFiniteAlgebra.two_isUnit_of_104 R h104)).map
      (polynomialAlgEquiv R h104).symm.toLinearEquiv

end MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.polynomialAlgEquiv
#print axioms MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.polynomialBasis


