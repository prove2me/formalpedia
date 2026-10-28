-- Prove2me | Definitions.Def_OAIQ031A110
-- name    : OAIQ031A110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:44:42.567123+00:00
-- url     : https://prove2.me/theorems/4b0043e6-39fe-4dcc-9926-cce51ac085a4
-- title:
--   Definitions bundle OAIQ031A110 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 5 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.zeroEvaluationEquiv`, `OAI.ArExplicit.BarBalanced.zeroModuleEquiv`, `OAI.ArExplicit.CompleteComparison.rawSourceCocycleMap`, `OAI.ArExplicit.CompleteComparison.rawSyzygyEquiv`, `OAI.ArExplicit.FiniteLeftModule.pairModule`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_AugmentedBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/AugmentedBarEvaluation.lean), [`AuslanderReiten_Bar_BarBalancedSuffix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedSuffix.lean), [`AuslanderReiten_Fibers_FiniteEvaluatedFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteEvaluatedFiber.lean), [`AuslanderReiten_Homology_CoefficientComplexValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/CoefficientComplexValues.lean), [`AuslanderReiten_Homology_ShortExactNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactNaturality.lean), [`AuslanderReiten_Resolutions_FiniteResolutionAdditive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionAdditive.lean), [`AuslanderReiten_Resolutions_FiniteResolutionLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionLinear.lean), [`AuslanderReiten_Stable_RawSourceCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/RawSourceCoordinates.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A091`, `OAIQ031A093`, `OAIQ031A096`, `OAIQ031A097` and `OAIQ031A098` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A120`, `OAIQ031A122`, `OAIQ031A123`, `OAIQ031A124` and `OAIQ031A125`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A091
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A097
import Definitions.Def_OAIQ031A098

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_AugmentedBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

def zeroModuleEquiv : ModuleBar.moduleObject k R M 0 ≃ₗ[R] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def zeroEvaluationEquiv : evaluated k R M 0 ≃ₗ[R] M :=
  (equiv k R M 0).trans (zeroModuleEquiv k R M)

@[simp] theorem zeroEvaluationEquiv_tmul (a : bar k R 0) (m : M) :
    zeroEvaluationEquiv k R M (BalancedTensor.tmul a m) = (show R from a.value) • m := rfl

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedSuffix
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem rawEval_suffix_zero (p : AbsoluteBar.Cochain3 k R)
    (x : AbsoluteBar.object k R 3) (m : M) :
    rawEval k R M 0 (AbsoluteBar.suffix3 k R p x ⊗ₜ[k] m) =
      ModuleBar.suffix3 k R M p (rawEval k R M 3 (x ⊗ₜ[k] m)) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  | tmul a x =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, TensorProduct.add_tmul, hx, hy]
    | tmul b x =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, TensorProduct.add_tmul, hx, hy]
      | tmul c d =>
        change (p a b c * d) • m = p a b c • (d • m)
        exact mul_smul _ _ _

theorem rawEval_suffix (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (x : AbsoluteBar.object k R (n+3)) (m : M) :
    rawEval k R M n (AbsoluteBar.suffixComparison k R p n x ⊗ₜ[k] m) =
      ModuleBar.suffixComparison k R M p n (rawEval k R M (n+3) (x ⊗ₜ[k] m)) := by
  induction n with
  | zero => exact rawEval_suffix_zero k R M p x m
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul a x =>
      rw [AbsoluteBar.suffixComparison_succ_tmul k R p n, rawEval_succ,
        rawEval_succ, ModuleBar.suffixComparison_succ_tmul k R M p n, ih]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit
open CompleteComparison

universe u
variable {R : Type u} [Ring R]

namespace CompleteComparison
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainHomotopyRawEquiv_comp_class
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (hM : ExactProjectiveCochain M)
    (f : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L)
    (g : (HomotopyCategory.quotient _ _).obj L ⟶ (HomotopyCategory.quotient _ _).obj M)
    (p : CochainCokernel K →ₗ[R] CochainCokernel L)
    (q : CochainCokernel L →ₗ[R] CochainCokernel M)
    (hf : cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex f =
      StableHom.classOf R _ _ p)
    (hg : cochainHomotopyRawEquiv hL.to_chain hM.to_chain g = StableHom.classOf R _ _ q) :
    cochainHomotopyRawEquiv hK.to_chain hM.to_chain (f ≫ g) =
      StableHom.classOf R _ _ (q.comp p) := by
  rw [cochainHomotopyRawEquiv_comp hK hL hM, hg, hf, StableHom.comp_classOf]

end CompleteComparison

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionLinear
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open scoped ModuleCat.Algebra

namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

namespace CompleteComparison
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainCokernelMap_smul (a : k) (f : K ⟶ L) :
    cochainCokernelMap (a • f) = a • cochainCokernelMap f := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective z
  change (LinearMap.range (L.d (-1) 0).hom).mkQ (a • (f.f 0).hom x) =
    a • (LinearMap.range (L.d (-1) 0).hom).mkQ ((f.f 0).hom x)
  exact ((LinearMap.range (L.d (-1) 0).hom).mkQ.restrictScalars k).map_smul a _
end CompleteComparison

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteEvaluatedFiber
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct
universe u
variable {k S : Type u} [Field k] [Ring S] [Algebra k S] [Module.Finite k S]

def pairModule (U V : FiniteLeftModule k S) : FiniteLeftModule k S where
  carrier := ModuleCat.of S (U.carrier × V.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_CoefficientComplexValues
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable {X Y : ModuleCat.{u} R}
variable [Module k X] [IsScalarTower k R X] [Module k Y] [IsScalarTower k R Y]
variable (e : X ≅ Y) (P : ChainComplex (ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) ℕ)

theorem coefficientComplexIso_f (n : ℕ) :
    (coefficientComplexIso k R e P).hom.f n = (evaluationCoefficientIso k R e).hom.app (P.X n) := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionAdditive
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
namespace CompleteComparison
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
theorem cochainCokernelMap_add (f g : K ⟶ L) :
    cochainCokernelMap (f+g) = cochainCokernelMap f + cochainCokernelMap g := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective z
  exact (LinearMap.range (L.d (-1) 0).hom).mkQ.map_add _ _
end CompleteComparison
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_RawSourceCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def rawSyzygyEquiv : Cokernel (chainOfCochain K) 1 ≃ₗ[R] RawSyzygy K :=
  cokernelLinearCongr _ _
    (K.extendXIso negIndexEmbedding (i := -2) (i' := 2) rfl).toLinearEquiv
    (K.extendXIso negIndexEmbedding (i := -1) (i' := 1) rfl).toLinearEquiv
    (congrArg ModuleCat.Hom.hom
      (reverseShortComplexIso K (-2) (-1) 0 2 1 0 rfl rfl rfl).hom.comm₁₂).symm

@[simp]
theorem rawSyzygyEquiv_symm_mk (z : K.X (-1)) :
    (rawSyzygyEquiv K).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((K.extendXIso negIndexEmbedding (i := -1) (i' := 1) rfl).inv.hom z) := rfl

variable {k : Type u} [Field k] [CharP k 2] [Algebra k R]
variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

def rawSourceCocycleMap (x : Cocycle K L 1) : RawSyzygy K →ₗ[R] CochainCokernel L :=
  (cochainCokernelLinearEquiv L).toLinearMap.comp
    ((sourceCocycleMap x).comp (rawSyzygyEquiv K).symm.toLinearMap)

end ArExplicit.CompleteComparison

end

end OAI
end


