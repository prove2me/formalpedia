-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteAtlasTargetMaps
-- name    : MazurTransfer_Order13InverseFiniteAtlasTargetMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:17:02.935393+00:00
-- url     : https://prove2.me/theorems/a665c30c-4550-4ee9-805f-8674617c830e
-- title:
--   The specified target maps of the actual inverse finite atlas
-- statement:
--   For a commutative ring $R$, the two members of the actual inverse finite coordinate atlas map to the actual order-thirteen curve by the specified ordinary parameter and positive reciprocal chart morphisms. This is the literal two-member family of target maps used by the inverse finite-model gluing construction. Compatibility on overlaps is a separate theorem.
-- source:
--   The original finiteSchemeChartToCurve data constructor from MazurTheorem Order13InverseParameterGlobalComparison.lean, Apache-2.0, Vas and contributors. Constructor body unchanged; only its public Definitions imports differ. Its original closed type and data value are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: finiteScheme_chart_curve_compatibility and original finiteModelToCurve. Proof-only gluing obligations remain separate.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite coordinate scheme maps to the actual
glued curve with exact ordinary and reciprocal restrictions and exact
union-of-chart image. Named downstream consumer: proving this comparison
an open immersion and constructing the inverse affine-open isomorphism.
-/
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartCurveMaps

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]



def finiteSchemeChartToCurve : (b : Bool) → finiteSchemeChart R b ⟶ curveScheme R
  | true => ordinaryParameterCurveMap R
  | false => positiveReciprocalCurveMap R












end MazurTransfer.Order13InverseParameterFiniteAlgebra



#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteSchemeChartToCurve


