-- Prove2me | Definitions.Def_MazurTransfer_Order13LiteralCurveFibreIsomorphism
-- name    : MazurTransfer_Order13LiteralCurveFibreIsomorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T04:07:31.048449+00:00
-- url     : https://prove2.me/theorems/2af09d95-f7ee-48ba-8fe7-b5a942baf340
-- title:
--   The actual literal curve fibre isomorphism over the new base
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. The Cartesian square of the actual order-thirteen curve map supplies the specified isomorphism
--   $$e_{S/R}:C_S\;\xrightarrow{\sim}\;C_R\times_{\operatorname{Spec}R}\operatorname{Spec}S,\qquad\pi_S\circ e_{S/R}=c_S,$$
--   where $c_S:C_S\to\operatorname{Spec}S$ is the actual structure morphism and $\pi_S$ is the second projection.
--
--   The two selected declarations provide this actual fibre isomorphism and its projection identity. They supply the literal curve input to the integral Abel–Jacobi point dictionary; compatibility with the distinguished section is a separate theorem.
-- source:
--   The unchanged literalCurveFibreIso constructor and literalCurveFibreIso_over projection proof from checked MazurTheorem Order13IntegralPicardLiteralFibreRepresentations.lean. Exact Lean syntax-oracle ranges remove the other declarations, replace broad imports by direct public interfaces and remove unused namespace openings. Both complete original kernel types are checked by closed witnesses. The original file header is retained for provenance; the selected interface consists of these two declarations. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every algebra base change of an actual order-13 Picard
representation represents the Picard functor of the literal new-ring curve,
using the genuine whole-curve isomorphism and positive infinity section.
The representing scheme, structural map and zero section are retained.
Named downstream consumer: same-family finite-field Picard cardinalities
and rational arithmetic divisor-class identification.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback


noncomputable section
universe u
namespace MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualCurveBaseChange



variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def literalCurveFibreIso : curveScheme S ≅ pullback (curveToBase R) (specMap R S) :=
  (wholeCurve_isPullback R S).isoPullback

theorem literalCurveFibreIso_over :
    (literalCurveFibreIso R S).hom ≫ baseChange R (curveToBase R) S = curveToBase S :=
  (wholeCurve_isPullback R S).isoPullback_hom_snd







end MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations


#print axioms MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations.literalCurveFibreIso
#print axioms MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations.literalCurveFibreIso_over


