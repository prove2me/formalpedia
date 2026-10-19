-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteAffineOpenPresentation
-- name    : MazurTransfer_Order13InverseFiniteAffineOpenPresentation
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:36:29.248471+00:00
-- url     : https://prove2.me/theorems/4f61dc2d-d692-4c16-84f6-5ca7cdce0721
-- title:
--   The original affine-open presentation of the actual inverse chart
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. The original inverse finite-model comparison identifies the actual finite coordinate scheme with its specified inverse-chart open $V$ in the order-thirteen curve: $$\operatorname{Spec}(R[S][a,b])\cong V.$$ This is the original chosen affine-open isomorphism, with its literal inclusion identities. In particular $V$ is affine.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Five original declarations from Order13InverseParameterAffineOpen.lean. The isomorphism constructor body is unchanged. Its affineness proof additionally unfolds the kernel-equal public finite-scheme alias for instance synthesis. Both imported image and open-immersion assertions are Proved public theorems. All five original closed types and the original isomorphism value are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: actual first/inverse chart overlap, structural section R-algebra comparisons, and unchanged integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite model is isomorphic to its
literal affine-open image in the original curve.
Named downstream consumer: the second chart of whole single-section
FiniteMapData and the integral Picard representation inputs.
-/
import Definitions.Def_MazurTransfer_Order13InverseChartOpen
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
import Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteModelToCurve_range
import Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteModelToCurve_isOpenImmersion

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]







variable [IsDomain R] [IsNoetherianRing R]











theorem finiteModelToCurve_opensRange (h104 : IsUnit (104 : R)) :
    letI := finiteModelToCurve_isOpenImmersion R h104
    (finiteModelToCurve R h104).opensRange = inverseChartOpen R := by
  let := finiteModelToCurve_isOpenImmersion R h104
  apply SetLike.ext'
  exact finiteModelToCurve_range R h104

def finiteModelInverseChartIso (h104 : IsUnit (104 : R)) :
    inverseFiniteAffineScheme R ≅ (inverseChartOpen R).toScheme := by
  let := finiteModelToCurve_isOpenImmersion R h104
  exact IsOpenImmersion.isoOfRangeEq (finiteModelToCurve R h104)
    (inverseChartOpen R).ι (by
      rw [Scheme.Opens.range_ι]
      exact finiteModelToCurve_range R h104)

theorem finiteModelInverseChartIso_hom_ι (h104 : IsUnit (104 : R)) :
    (finiteModelInverseChartIso R h104).hom ≫ (inverseChartOpen R).ι =
      finiteModelToCurve R h104 := by
  let := finiteModelToCurve_isOpenImmersion R h104
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (by
    rw [Scheme.Opens.range_ι]
    exact finiteModelToCurve_range R h104)

theorem finiteModelInverseChartIso_inv_comp (h104 : IsUnit (104 : R)) :
    (finiteModelInverseChartIso R h104).inv ≫ finiteModelToCurve R h104 =
      (inverseChartOpen R).ι := by
  let := finiteModelToCurve_isOpenImmersion R h104
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ (by
    rw [Scheme.Opens.range_ι]
    exact finiteModelToCurve_range R h104)

theorem inverseChartOpen_isAffineOpen (h104 : IsUnit (104 : R)) :
    IsAffineOpen (inverseChartOpen R) := by
  let : IsAffine (inverseFiniteAffineScheme R) := by
    unfold inverseFiniteAffineScheme
      InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseFiniteAffineScheme
    infer_instance
  exact IsAffine.of_isIso (finiteModelInverseChartIso R h104).inv

end MazurTransfer.Order13InverseParameterFiniteAlgebra



#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelInverseChartIso
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseChartOpen_isAffineOpen


