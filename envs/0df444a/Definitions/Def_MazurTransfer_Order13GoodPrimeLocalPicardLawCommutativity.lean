-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardLawCommutativity
-- name    : MazurTransfer_Order13GoodPrimeLocalPicardLawCommutativity
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T05:09:55.173033+00:00
-- url     : https://prove2.me/theorems/0361771a-038c-4280-80ce-b3e5998fccf5
-- title:
--   Commutativity of the same local Picard group law
-- statement:
--   Let $q$ be a prime not dividing $104$, and equip the selected local Picard model over $\mathbb Z_{(q)}$ with the relative group law supplied by its actual degree-zero Picard representation. This group law is commutative on points over every test scheme.
--
--   This is the structural commutativity fact for the same local model used by the actual norm extensions. It supplies the group-law input for the later local scalar and finite étale norm arguments, with no extra restriction on $q$.
-- source:
--   MazurTheorem, Order13GoodPrimeLocalScalarInputs.lean, structural declaration local_law_isCommutative, complete original type retained; full source SHA-256 d20e5ecfe40427d3548c7528f43c36293522f8c8369a67df4dcd5c545b9c5f2a, Apache-2.0. Official Anthropic FLT Picard interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME local Picard law is the commutative law of its
genuine degree-zero Picard representation. Named downstream consumer:
local multiplication by nineteen and finite etale actual norm factors.
-/
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardModelsData
noncomputable section
namespace MazurTransfer.Order13GoodPrimeLocalScalarInputs
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
variable (q : ℕ) [Fact q.Prime]
theorem local_law_isCommutative (hq : ¬ (q : ℤ) ∣ 104) :
    (localLaw q hq).IsCommutative :=
  (show RepresentsRelSubPic (curveToBase (LocalRing q))
    (positiveInfinitySection (LocalRing q))
    (algEquivZeroGroupCut (curveToBase (LocalRing q))
      (positiveInfinitySection (LocalRing q))).toSubPicCondition (localPicard q hq)
    from localRepresentation q hq).relativeGroupLaw_isCommutative

end MazurTransfer.Order13GoodPrimeLocalScalarInputs
#print axioms MazurTransfer.Order13GoodPrimeLocalScalarInputs.local_law_isCommutative


