-- Prove2me | Definitions.Def_OAIQ031A138
-- name    : OAIQ031A138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:15:03.637372+00:00
-- url     : https://prove2.me/theorems/549b27db-3f48-422f-b9f0-b361b548d094
-- title:
--   Definitions bundle OAIQ031A138 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Triangular_ConvertedCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/ConvertedCriterion.lean), [`AuslanderReiten_Triangular_ConvertedTensorCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/ConvertedTensorCriterion.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A098` and `OAIQ031A128` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A189`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A098
import Definitions.Def_OAIQ031A128

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedCriterion
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_finite _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_finite _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison TriangularInduction
open CochainComplex CochainComplex.HomComplex

universe u

variable {k : Type u} [Field k] (q : k) (B : Type u)
variable [AddCommGroup B] [Module k B] [Module (A k q) B] [Module (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q) B] [SMulCommClass (A k q) (A k q)ᵐᵒᵖ B]
variable [IsScalarTower k (A k q) B] [IsScalarTower k (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q)ᵐᵒᵖ B]
variable [Module.Finite k B]
variable [Module.Finite (A k q) B] [Module.Projective (A k q) B]
variable [Module.Finite (A k q)ᵐᵒᵖ B] [Module.Projective (A k q)ᵐᵒᵖ B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : CochainComplex (ModuleCat.{u} (A k q)) ℤ)
variable (φ : jCochain (k := k) (F := B) P ⟶ eCochain (k := k) (F := B) P)

theorem convertedCone_mainConclusions (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (hP : TotallyAcyclicCochain P)
    (hinj : ∀ n : ℕ, 0 < n → Function.Injective (coneComparison φ (n : ℤ)))
    (hsurj : ∀ n : ℕ, Function.Surjective (coneComparison φ (n : ℤ)))
    (hker : ∃ w : CohomologyClass (eCochain (k := k) (F := B) P)
        (eCochain (k := k) (F := B) P) 0 ×
        CohomologyClass (jCochain (k := k) (F := B) P)
        (jCochain (k := k) (F := B) P) 0,
      w ≠ 0 ∧ coneComparison φ 0 w = 0) :
    MainConclusions k (ConvertedAlgebra k q B) (ConeModule φ) := by
  have hJ := jCochain_totallyAcyclic (k := k) (F := B) P hP
  have hE := eCochain_totallyAcyclic (k := k) (F := B) P hP
  obtain ⟨hnp, hgp, hself, hreg⟩ := coneModule_properties (k := k) φ hJ hE
    (eToJCochain_eq_zero k (A k q) B P P) hinj hsurj hker
  have hC := (mappingCone_totallyAcyclic φ hJ hE).to_chain
  let := hC.finite 0
  let : Module.Finite k ((chainOfCochain (mappingCone φ)).X 0) :=
    Module.Finite.trans (ConvertedAlgebra k q B) _
  exact ⟨inferInstance, inferInstance, hnp, hgp, hself, hreg,
    ⟨ConvertedAlgebra.semisimpleQuotientEquiv q B⟩,
    ConvertedAlgebra.jacobson_fourth_ne_bot q B hq hq1⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedTensorCriterion
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_finite _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_finite _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison TriangularInduction
open CochainComplex CochainComplex.HomComplex

universe u

variable {k : Type u} [Field k] (q : k) (B : Type u)
variable [AddCommGroup B] [Module k B] [Module (A k q) B] [Module (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q) B] [SMulCommClass (A k q) (A k q)ᵐᵒᵖ B]
variable [IsScalarTower k (A k q) B] [IsScalarTower k (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q)ᵐᵒᵖ B]
variable [Module.Finite k B]
variable [Module.Finite (A k q) B] [Module.Projective (A k q) B]
variable [Module.Finite (A k q)ᵐᵒᵖ B] [Module.Projective (A k q)ᵐᵒᵖ B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : CochainComplex (ModuleCat.{u} (A k q)) ℤ)
variable (v : P ⟶ tensorCochain (k := k) (F := B) P)

theorem convertedTensorCone_mainConclusions (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (hP : TotallyAcyclicCochain P)
    (hinj : ∀ n : ℕ, 0 < n → Function.Injective (tensorComparison v (n : ℤ)))
    (hsurj : ∀ n : ℕ, Function.Surjective (tensorComparison v (n : ℤ)))
    (hker : ∃ w : CohomologyClass P P 0 × CohomologyClass P P 0,
      w ≠ 0 ∧ tensorComparison v 0 w = 0) :
    MainConclusions k (ConvertedAlgebra k q B) (ConeModule (crossChainMap v)) := by
  apply convertedCone_mainConclusions q B P (crossChainMap v) hq hq1 hP
  · intro n hn
    exact coneComparison_injective_of_tensor v (n : ℤ) (hinj n hn)
  · intro n
    exact coneComparison_surjective_of_tensor v (n : ℤ) (hsurj n)
  · exact coneComparison_nonzero_kernel_of_tensor v 0 hker

end ArExplicit

end

end OAI
end


