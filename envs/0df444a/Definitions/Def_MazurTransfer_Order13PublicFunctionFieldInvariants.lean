-- Prove2me | Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
-- name    : MazurTransfer_Order13PublicFunctionFieldInvariants
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:47:56.99415+00:00
-- url     : https://prove2.me/theorems/b3a53735-2fee-48ca-9ef9-645378809f40
-- title:
--   Public constant-field and genus interfaces for the actual order-thirteen function field
-- statement:
--   Let $K$ be a perfect field in which $104\ne0$, and let $F=K(C_K)$ be the actual function field of the fixed two-chart order-thirteen curve. The established invariants give
--   $$\operatorname{Const}(F/K)=K,\qquad g(F/K)=2,$$
--   and $F$ is essentially of finite type over $K$.
--
--   This lightweight interface exposes projections of the previously proved public function-field theorem in the canonical actual-place namespace. It supplies the genus and constant-field hypotheses of the curve-model point-difference injection.
-- source:
--   Three lightweight interfaces to existing Proved public mathematical results, with kernel-checked closed type equality to the original declarations in AcceptedOrder13GoodCharacteristicPicardCache.lean. The genus and constant-field facts are projections of MazurTransfer.order13_actual_function_field_invariants. Vas and contributors, Apache-2.0; original official Anthropic FLT APIs retain pin 6e837e75355538c7f80bab5b956861e86c4eacc2 and attribution.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal function field uses the already proved public
constant-field and genus invariants, with the same canonical place foundation.
Named downstream consumer: the actual curve-model point-difference injection.
Public mathematical APIs reuse official Anthropic FLT, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Theorems.Thm_MazurTransfer_order13_actual_function_field_invariants
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
noncomputable section
namespace GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
instance actualFunctionFieldEssFiniteType : Algebra.EssFiniteType K (actualCurveFunctionField K) :=
  _root_.AlgebraicCurve.essFiniteType_functionField (curveToBase K)
theorem actual_constantsAreBase_good_characteristic : ConstantsAreBase K (actualCurveFunctionField K) := by
  exact (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).2.2.1
theorem actual_genusFF_eq_two_good_characteristic : genusFF K (actualCurveFunctionField K) = 2 := by
  exact (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).2.2.2.1
end GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
#print axioms GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actual_genusFF_eq_two_good_characteristic


