-- Prove2me | Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
-- name    : MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T05:33:36.725438+00:00
-- url     : https://prove2.me/theorems/6085b9b1-2ecb-4b3a-9047-5067bdafc08c
-- title:
--   Both actual integral norm composites equal local multiplication by nineteen
-- statement:
--   Let $q$ be a prime not dividing $104$, and let $\mathcal J_q$ be the same selected local Picard model used for the actual rational norm extensions. The integral extension of rational multiplication by nineteen equals multiplication by nineteen for its actual local relative group law. For the two integral norm maps $\Pi$ and $\overline\Pi$,
--
--   $$\Pi\circ\overline\Pi=\overline\Pi\circ\Pi=[19]_{\mathcal J_q}.$$
--
--   These are the three original structural specialization facts obtained from the checked all-natural-numbers scalar identity and the checked composition identities. They supply the precise local scalar relation for the subsequent finite étale norm arguments.
-- source:
--   MazurTheorem, Order13GoodPrimeIntegralScalarNineteen.lean, original declarations integralScalarNineteen_eq_local_schemeNsmul and both integral norm composite equalities, full source SHA-256 9051388adcfa1a4e90b820b12326aae435823a8c1c2ebbddd2e742c43ed7120d, Apache-2.0. All three original declaration types and proof bodies retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: specialize the checked all-n integral scalar identity to
nineteen and the two SAME actual integral norm composites. Named downstream
consumer: finite etale integral norm factors and genuine good-prime inertia.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralScalarNineteen_integralNorm_scalar
noncomputable section
namespace MazurTransfer.Order13GoodPrimeIntegralScalarNineteen
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeIntegralNormComposition
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
theorem integralScalarNineteen_eq_local_schemeNsmul :
    (integralScalarNineteen q hq).val = (localLaw q hq).schemeNsmul 19 :=
  congrArg Subtype.val (integralNorm_scalar q hq 19)

theorem integralPi_comp_integralPiConjugate_eq_local_schemeNsmul :
    (integralPi q hq).val ≫ (integralPiConjugate q hq).val =
      (localLaw q hq).schemeNsmul 19 := by
  have h := congrArg Subtype.val (integralPi_comp_integralPiConjugate q hq)
  exact h.trans (integralScalarNineteen_eq_local_schemeNsmul q hq)

theorem integralPiConjugate_comp_integralPi_eq_local_schemeNsmul :
    (integralPiConjugate q hq).val ≫ (integralPi q hq).val =
      (localLaw q hq).schemeNsmul 19 := by
  have h := congrArg Subtype.val (integralPiConjugate_comp_integralPi q hq)
  exact h.trans (integralScalarNineteen_eq_local_schemeNsmul q hq)

end MazurTransfer.Order13GoodPrimeIntegralScalarNineteen
#print axioms MazurTransfer.Order13GoodPrimeIntegralScalarNineteen.integralScalarNineteen_eq_local_schemeNsmul
#print axioms MazurTransfer.Order13GoodPrimeIntegralScalarNineteen.integralPi_comp_integralPiConjugate_eq_local_schemeNsmul
#print axioms MazurTransfer.Order13GoodPrimeIntegralScalarNineteen.integralPiConjugate_comp_integralPi_eq_local_schemeNsmul


