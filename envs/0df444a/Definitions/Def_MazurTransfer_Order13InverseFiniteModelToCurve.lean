-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
-- name    : MazurTransfer_Order13InverseFiniteModelToCurve
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:27:23.694823+00:00
-- url     : https://prove2.me/theorems/b8f90c89-fded-4821-ac81-7a8a1e2cb652
-- title:
--   The original glued inverse finite-model comparison to the actual curve
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. The actual inverse finite algebra $B=R[S][a,b]$ has the specified ordinary-localization and positive-reciprocal atlas. The publicly proved compatibility of its maps to the order-thirteen curve $C$ determines the original glued morphism $\operatorname{Spec}B\to C$. Its restrictions to both atlas members are the retained literal chart maps. The image and open-immersion assertions remain separate theorems.
-- source:
--   Three original declarations from MazurTheorem Order13InverseParameterGlobalComparison.lean, Apache-2.0, Vas and contributors: finiteModelToCurve and its two chart-restriction identities. Every original body is unchanged; imports use the public target-family constructor and Proved overlap-compatibility theorem. All three original closed types and the original glued morphism value are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: the original image and open-immersion theorems, actual inverse affine-chart presentation and integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite coordinate scheme maps to the actual
glued curve with exact ordinary and reciprocal restrictions and exact
union-of-chart image. Named downstream consumer: proving this comparison
an open immersion and constructing the inverse affine-open isomorphism.
-/
import Definitions.Def_MazurTransfer_Order13InverseFiniteAtlasTargetMaps
import Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteScheme_chart_curve_compatibility

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]







def finiteModelToCurve (h104 : IsUnit (104 : R)) : inverseFiniteAffineScheme R ⟶ curveScheme R :=
  (finiteSchemeOpenCover R h104).glueMorphisms (finiteSchemeChartToCurve R)
    (finiteScheme_chart_curve_compatibility R h104)

theorem ordinaryParameterToFiniteAffineScheme_finiteModelToCurve (h104 : IsUnit (104 : R)) :
    ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R h104 = ordinaryParameterCurveMap R :=
  (finiteSchemeOpenCover R h104).ι_glueMorphisms _ _ true

theorem reciprocalToFiniteAffineScheme_finiteModelToCurve (h104 : IsUnit (104 : R)) :
    reciprocalToFiniteAffineScheme R h104 ≫ finiteModelToCurve R h104 = positiveReciprocalCurveMap R :=
  (finiteSchemeOpenCover R h104).ι_glueMorphisms _ _ false




end MazurTransfer.Order13InverseParameterFiniteAlgebra



#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve


