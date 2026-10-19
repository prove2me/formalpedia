-- Prove2me | Definitions.Def_MazurTransfer_CurveModelPointDifference
-- name    : MazurTransfer_CurveModelPointDifference
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T01:42:22.285117+00:00
-- url     : https://prove2.me/theorems/03c44492-5fb6-4388-9770-3b09312c94f4
-- title:
--   Curve-model field points and their associated rational places
-- statement:
--   Let $K$ be algebraically closed and let $F/K$ be an essentially finite-type one-variable function field. Let $M$ be a smooth proper curve model with structure map $M\to\operatorname{Spec}K$. Its relative field points are
--   $$M(K)=\{p:\operatorname{Spec}K\to M : p\text{ lies over }K\}.$$
--   The interface maps each such point $p$ to its corresponding place $v_p$ and records $\deg(v_p)=1$.
--
--   These are only the point and rational-place constructors. The theorem that a genuine point-difference Picard dictionary makes a positive-genus point map injective is a separate proof, used for the actual order-thirteen Abel–Jacobi morphism.
-- source:
--   Exact two constructor declarations from MazurTheorem, CurveModelPointDifferenceInjectivity.lean, lines20–26. Underlying curve model and rational-place equivalence: Apache-2.0 Anthropic FLT, commit6e837e75355538c7f80bab5b956861e86c4eacc2, https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_CurveModel.lean and Theorems/Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace.lean. The extracted definitions preserve the complete original kernel types.

/- Design boundary: actual model field points and their associated rational places.
Named downstream consumer: the point-difference Picard dictionary injection,
then the actual order13 integral Abel-Jacobi map. Apache-2.0. -/
/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: any actual point-difference Picard dictionary on a
positive-genus curve makes its point map injective, with an arbitrary
base point. Named downstream consumer: injectivity of the integral
order13 Abel-Jacobi map on geometric and rational points. -/
import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one


noncomputable section
namespace MazurTransfer.CurveModelPointDifferenceInjectivity
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u v z
variable {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F]
  [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
  (M : CurveModel K F)

abbrev ModelPoint := {p : Spec (.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}

def rationalPointPlace (p : ModelPoint M) : {v : Place K F // v.deg = 1} :=
  ⟨M.pointEquivPlace p, (Place.isRational_iff_deg_eq_one _).mp (M.isRational_pointEquivPlace p)⟩



end MazurTransfer.CurveModelPointDifferenceInjectivity


#print axioms MazurTransfer.CurveModelPointDifferenceInjectivity.ModelPoint
#print axioms MazurTransfer.CurveModelPointDifferenceInjectivity.rationalPointPlace


