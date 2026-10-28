-- Prove2me | Definitions.Def_OAIQ031A118
-- name    : OAIQ031A118
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:52:32.612244+00:00
-- url     : https://prove2.me/theorems/b3df28cf-6016-4e94-a3ab-cfb36093d7ca
-- title:
--   Definitions bundle OAIQ031A118 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 11 definitions and 12 theorems. The definitions and types are `OAI.ArExplicit.A.betaFiniteModule`, `OAI.ArExplicit.A.betaHom`, `OAI.ArExplicit.A.simpleFiniteModule`, `OAI.ArExplicit.BalancedTensor.completeTensor`, `OAI.ArExplicit.FiniteLeftModule.fullHomZeroEquiv`, `OAI.ArExplicit.T.G`, `OAI.ArExplicit.T.barG`, `OAI.ArExplicit.T.bimoduleHighLift`, `OAI.ArExplicit.T.productHighLift`, `OAI.ArExplicit.T.tailMap`, `OAI.ArExplicit.T.tensorHighG`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_TBarHomotopies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TBarHomotopies.lean), [`AuslanderReiten_Cones_ConcreteTwoConeEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConcreteTwoConeEvaluation.lean), [`AuslanderReiten_Coordinates_TensorHighLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorHighLift.lean), [`AuslanderReiten_Coordinates_TensorTailMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTailMap.lean), [`AuslanderReiten_Evaluation_ConcreteBetaHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/ConcreteBetaHom.lean), [`AuslanderReiten_HomComplex_FiniteFullHomZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FiniteFullHomZero.lean), [`AuslanderReiten_HomComplex_HomCochainExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainExt.lean), [`AuslanderReiten_Homology_TBoundaryCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TBoundaryCochain.lean), [`AuslanderReiten_Homology_TNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TNullhomotopy.lean), [`AuslanderReiten_Tensor_BalancedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A096`, `OAIQ031A105` and `OAIQ031A106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A129`, `OAIQ031A130`, `OAIQ031A132`, `OAIQ031A135`, `OAIQ031A136` and `OAIQ031A137`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A105
import Definitions.Def_OAIQ031A106

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TBoundaryCochain
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

variable [CharP k 2]

theorem pB_bottom_linear (H : kˣ) :
    (AbsoluteBar.cochain3Linear k R (CocycleData.p q)).comp
        (AbsoluteBar.casimirInsertion k R (twistedCasimir q H) 3) =
      (AbsoluteBar.oneCochainLinear k R (TrivialExtension.twist H) (CocycleData.z q H)).comp
        (AbsoluteBar.boundary k R 2) := by
  apply TensorProduct.ext'
  intro a x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul b x =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul c d =>
      change AbsoluteBar.cochain3Linear k R (CocycleData.p q)
          (AbsoluteBar.casimirInsertion k R (twistedCasimir q H) 3
            (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d)))) =
        AbsoluteBar.oneCochainLinear k R (TrivialExtension.twist H) (CocycleData.z q H)
          (AbsoluteBar.boundary k R 2 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d))))
      rw [pB_bottom_tmul, AbsoluteBar.oneCochain_boundary_tmul]
      rw [CocycleData.twisted_boundary]
      rfl

theorem pB_bottom (H : kˣ) :
    (AbsoluteBar.cochain3 k R (CocycleData.p q)).comp (B q H 3) =
      (Z q H).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 2) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (pB_bottom_linear q H) x

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TNullhomotopy
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q
local notation "Ae" => AbsoluteBar.Enveloping k R

theorem exists_G (H : kˣ) :
    ∃ G : (n : ℕ) →
      AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 2) →ₗ[Ae]
        AbsoluteBar.moduleObject k R (n + 1),
      (AbsoluteBar.differential k R 0).comp (G 0) = Z q H ∧
      ∀ n, pB q H n = (AbsoluteBar.differential k R (n + 1)).comp (G (n + 1)) +
        (G n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 2)) := by
  apply ProjectiveNullhomotopyAbove.exists_homotopy
    (P := fun n => AbsoluteBar.moduleObject k R (n + 1))
    (Q := fun n => AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 1))
    (fun n => AbsoluteBar.differential k R (n + 1))
    (fun n => AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 1))
    (pB q H) (fun n => AbsoluteBar.twistedProjective k R (TrivialExtension.twist H) n)
  · intro n
    apply LinearMap.ext
    exact AbsoluteBar.boundary_squared k R (n + 1)
  · intro n
    exact AbsoluteBar.differential_exact k R (n + 1)
  · exact pB_comm q H
  · intro x
    exact ⟨AbsoluteBar.contraction k R 0 x, AbsoluteBar.augmentation_contraction k R x⟩
  · exact AbsoluteBar.differential_exact k R 0
  · change (AbsoluteBar.differential k R 0).comp ((P q 0).comp (B q H 3)) = _
    rw [← LinearMap.comp_assoc, P_augmentation, pB_bottom]

def G (H : kˣ) (n : ℕ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 2) →ₗ[Ae]
      AbsoluteBar.moduleObject k R (n + 1) :=
  Classical.choose (exists_G q H) n

theorem G_equation (H : kˣ) (n : ℕ) :
    pB q H n = (AbsoluteBar.differential k R (n + 1)).comp (G q H (n + 1)) +
      (G q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 2)) :=
  (Classical.choose_spec (exists_G q H)).2 n

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TBarHomotopies
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def barG (n : ℕ) : (Q₀).X (n+1) ⟶ (P₀).X n :=
  ModuleCat.ofHom (X := (Q₀).X (n+1)) (Y := (P₀).X n) (G q H n)

theorem barG_equation (n : ℕ) :
    barB q H (n+2) ≫ barComparison q n =
      barG q H (n+1) ≫ (P₀).d (n+1) n + (Q₀).d (n+2) (n+1) ≫ barG q H n := by
  simp only [AbsoluteBar.complex_d, AbsoluteBar.twistedComplex_d]
  apply ModuleCat.hom_ext
  exact G_equation q H n

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorHighLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)
local notation "D" => productTwoConeData q

def tensorHighG (n : ℕ) :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+2) (barG q H (n+2)) (barDb q H)

theorem tensorHighG_homotopy (n : ℕ) :
    ((D).first (n+2)).comp (tensorHighB q H (n+1)) =
      ((D).d (n+2)).comp (tensorHighG q H (n+1)) +
        (tensorHighG q H n).comp ((productTwistedTotal q H).d (n+4) (n+3)).hom := by
  change (ExternalTensor.firstCubic k Te Te P₀ P₀ (barComparison q) (n+2)).comp
      (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+4) (n+5)
        (barB q H (n+4)) (barDb q H)) =
    ((ExternalTensor.complex k Te Te P₀ P₀).d (n+3) (n+2)).hom.comp
      (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+4) (n+3)
        (barG q H (n+3)) (barDb q H)) +
    (ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+2)
      (barG q H (n+2)) (barDb q H)).comp
      ((productTwistedTotal q H).d (n+4) (n+3)).hom
  rw [ExternalTensor.firstCubic_bottomMap, ExternalTensor.bottomMap_d_target,
    ExternalTensor.bottomMap_d_source k Te Te (hg := barDb_cycle q H),
    ← ExternalTensor.bottomMap_add, ← barG_equation]

theorem tensorHighG_second (n : ℕ) :
    ((D).second n).comp (tensorHighG q H (n+1)) = 0 :=
  ExternalTensor.secondCubic_bottomMap k Te Te P₀ Q₀ P₀ Q₀ (barComparison q)
    (n+4) n (barG q H (n+3)) (barDb q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTailMap
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "D" => productTwoConeData q
local notation "Q₀" => productTwistedTotal q H

theorem tensorHighG_signed (n : ℕ) :
    -((D).d (n+2)).comp (tensorHighG q H (n+1)) -
      ((D).first (n+2)).comp (tensorHighB q H (n+1)) =
      (tensorHighG q H n).comp ((Q₀).d (n+4) (n+3)).hom := by
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (tensorHighG_homotopy q H n) x
  change (D).first (n+2) (tensorHighB q H (n+1) x) =
    (D).d (n+2) (tensorHighG q H (n+1) x) +
      tensorHighG q H n ((Q₀).d (n+4) (n+3) x) at hh
  have hn (y : (D).term (n+2)) : -y=y :=
    neg_eq_iff_add_eq_zero.mpr (SparseParity.module_add_self_eq_zero (k := k) y)
  change -((D).d (n+2) (tensorHighG q H (n+1) x)) -
    (D).first (n+2) (tensorHighB q H (n+1) x) = _
  rw [hh, sub_eq_add_neg, hn, hn, ← add_assoc,
    SparseParity.module_add_self_eq_zero (k := k), zero_add]
  rfl

def productHighLift (n : ℕ) :=
  TwoCone.highLift D (Q₀).X (tensorHighG q H) (tensorHighB q H) n

theorem productHighLift_comm (n : ℕ) :
    (TwoCone.d D n).comp (productHighLift q H (n+1)) =
      (productHighLift q H n).comp ((Q₀).d (n+4) (n+3)).hom :=
  TwoCone.highLift_comm D (Q₀).X (fun n => ((Q₀).d (n+1) n).hom)
    (tensorHighG q H) (tensorHighB q H) (tensorHighB_chain q H)
    (tensorHighG_signed q H) (tensorHighG_second q H) (tensorHighB_second q H) n

def bimoduleHighLift (n : ℕ) :=
  TwoCone.restrictedHighLift (ExternalTensor.envelopingEquiv k R R).symm.toRingHom
    D (Q₀).X (productHighLift q H) n

theorem bimoduleHighLift_comm (n : ℕ) :
    (TwoCone.d (bimoduleTwoConeData q) n).comp (bimoduleHighLift q H (n+1)) =
      (bimoduleHighLift q H n).comp (bimoduleTwistedDifferential q H (n+3)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (productHighLift_comm q H n) x

def tailMap : fourthSyzygy q H →ₗ[ExternalTensor.EnvelopingProduct k R R] firstTail q :=
  TwoCone.tailMap (bimoduleTwoConeData q) (bimoduleTwistedTerm q H) (bimoduleTwistedDifferential q H)
    (bimoduleHighLift q H 1) (bimoduleHighLift q H 2) (bimoduleHighLift_comm q H 1)

@[simp] theorem tailMap_mk (x : bimoduleTwistedTerm q H 4) :
    tailMap q H (Submodule.Quotient.mk x) = Submodule.Quotient.mk (bimoduleHighLift q H 1 x) := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConcreteTwoConeEvaluation
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
namespace ArExplicit
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

namespace A

def simpleFiniteModule : FiniteLeftModule k (A k q) where
  carrier := Simple q
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance
end A

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteBetaHom
attribute [-instance] _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.A
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)

def betaFiniteModule : FiniteLeftModule k (A k q) where
  carrier := ModuleCat.of (A k q) (augmentationIdeal q)
  scalar := inferInstance
  tower := inferInstance
  finite := Module.Finite.of_injective ((augmentationIdeal q).subtype.restrictScalars k)
    Subtype.val_injective

def betaHom :
    (HomotopyCategory.quotient _ _).obj ((simpleFiniteModule q).completeCochain (AFrobeniusTrace k q)) ⟶
    (HomotopyCategory.quotient _ _).obj ((betaFiniteModule q).completeCochain (AFrobeniusTrace k q)) :=
  (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap (AFrobeniusTrace k q)
    (M := simpleFiniteModule q) (N := betaFiniteModule q) (beta q))

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FiniteFullHomZero
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]

namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

def fullHomZeroEquiv : CohomologyClass (M.completeCochain τ) (N.completeCochain τ) 0 ≃ₗ[k]
    StableHom R M.carrier N.carrier :=
  (fullHomSourceStableLinearEquiv _ _ 0 (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      ((StableHom.sourceEquiv (k := k) (M.fullCokernelEquiv τ).symm).trans
        (StableHom.targetEquiv (k := k) (N.fullCokernelEquiv τ)))

end FiniteLeftModule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

theorem homCycle_closed (n : ℕ) (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    P.complex.d (n+1) n ≫ ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val = 0 := by
  apply ModuleCat.hom_ext
  let g : P.complex.X n →ₗ[R] Y := f.val
  have hf : (homShort k R (Y := Y) P n).g.hom g = 0 := f.property
  rw [homShort_outgoing] at hf
  exact hf

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open CategoryTheory CompleteComparison
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

abbrev completeTensor :=
  (((functor (k := k) (R := R) (S := R) (F := F)).mapHomologicalComplex _).obj
    (M.completeCochain τ))

end ArExplicit.BalancedTensor

end

end OAI
end


