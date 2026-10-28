-- Prove2me | Definitions.Def_OAIQ031A098
-- name    : OAIQ031A098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:34:55.638414+00:00
-- url     : https://prove2.me/theorems/e3646e42-f6cf-42fa-a0fc-6995ccdecc5c
-- title:
--   Definitions bundle OAIQ031A098 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 2 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.EnvelopingBimodule.coefficientComplexIso`, `OAI.ArExplicit.TwoCone.attachingRow`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedRaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedRaw.lean), [`AuslanderReiten_Bar_BarTensorRegularIsoCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarTensorRegularIsoCoordinates.lean), [`AuslanderReiten_Cones_ShortExactConeRaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ShortExactConeRaw.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_CochainStableComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/CochainStableComparison.lean), [`AuslanderReiten_Homology_CochainNullhomotopy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/CochainNullhomotopy.lean), [`AuslanderReiten_Tensor_EnvelopingCoefficientComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingCoefficientComplex.lean), [`AuslanderReiten_Triangular_ConvertedStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/ConvertedStructure.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A078`, `OAIQ031A080`, `OAIQ031A084` and `OAIQ031A086` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A107`, `OAIQ031A110`, `OAIQ031A111`, `OAIQ031A113`, `OAIQ031A115`, `OAIQ031A121` and `OAIQ031A138`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A080
import Definitions.Def_OAIQ031A084
import Definitions.Def_OAIQ031A086

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedRaw
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

theorem rawEval_boundary (n : ℕ) (x : AbsoluteBar.object k R (n+1)) (m : M) :
    rawEval k R M n ((AbsoluteBar.boundary k R n x) ⊗ₜ[k] m) =
      ModuleBar.boundary k R M n (rawEval k R M (n+1) (x ⊗ₜ[k] m)) := by
  induction n with
  | zero =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul a b => exact mul_smul a b m
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    | tmul a x =>
      rw [AbsoluteBar.boundary_succ_tmul k R n, TensorProduct.add_tmul, map_add,
        rawEval_left, rawEval_succ, rawEval_succ, ModuleBar.boundary_succ_tmul k R M n, ih]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarTensorRegularIsoCoordinates
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

@[simp] theorem barTensorZeroIso_tmul (a : AbsoluteBar.moduleObject k A 0)
    (b : AbsoluteBar.moduleObject k B 0) :
    (barTensorZeroEquiv k A B).toModuleIso.hom (a ⊗ₜ[k] b) =
      (show A from a) ⊗ₜ[k] (show B from b) :=
  barTensorZeroEquiv_tmul k A B a b

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_CochainNullhomotopy
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u
variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochain_nullhomotopy_of_cokernel_zero
    (hK : TotallyAcyclicCochain K) (hL : ExactProjectiveCochain L)
    (f : K ⟶ L) (hf : cochainCokernelMap f = 0) :
    ∃ H : Homotopy f 0, H.hom 1 0 = 0 := by
  have hz : cokernelMap (extendMap f negIndexEmbedding) 0 = 0 := by
    apply LinearMap.ext
    intro x
    apply (cochainCokernelLinearEquiv L).injective
    have hh := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural f) x
    rw [hf] at hh
    simpa using hh
  obtain ⟨H, hH⟩ := nullhomotopy_of_cokernel_zero hK.to_chain hL.to_chain
    (extendMap f negIndexEmbedding) hz
  let H' : Homotopy (extendMap f negIndexEmbedding) (extendMap (0 : K ⟶ L) negIndexEmbedding) :=
    H.trans (Homotopy.ofEq (extendMap_zero K L negIndexEmbedding).symm)
  refine ⟨H'.ofExtend, ?_⟩
  change (K.extendXIso negIndexEmbedding (i := 1) (i' := -1) rfl).inv ≫ H'.hom (-1) 0 ≫
    (L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom = 0
  have hs : H'.hom (-1) 0 = 0 := by
    simp [H', Homotopy.trans_hom, hH]
  simp [hs]

theorem cochain_homotopy_of_cokernel_eq
    (hK : TotallyAcyclicCochain K) (hL : ExactProjectiveCochain L)
    (f g : K ⟶ L) (hfg : cochainCokernelMap f = cochainCokernelMap g) :
    ∃ H : Homotopy f g, H.hom 1 0 = 0 := by
  obtain ⟨H, hH⟩ := cochain_nullhomotopy_of_cokernel_zero hK hL (f - g) (by
    rw [cochainCokernelMap_sub, hfg, sub_self])
  exact ⟨Homotopy.equivSubZero.symm H, hH⟩

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_CochainStableComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainHomotopyCokernelEquiv_comp
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (hM : ExactProjectiveComplex (chainOfCochain M))
    (f : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L)
    (g : (HomotopyCategory.quotient _ _).obj L ⟶ (HomotopyCategory.quotient _ _).obj M) :
    cochainHomotopyCokernelEquiv hK hM (f ≫ g) =
      StableHom.comp (cochainHomotopyCokernelEquiv hL hM g)
        (cochainHomotopyCokernelEquiv hK hL.toExactProjectiveComplex f) := by
  change homotopyCokernelEquiv hK hM
    ((negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).map (f ≫ g)) = _
  erw [Functor.map_comp, homotopyCokernelEquiv_comp hK hL hM]
  rfl

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ShortExactConeRaw
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex CochainComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]

namespace CompleteComparison
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainHomotopyRawEquiv_id (hK : TotallyAcyclicComplex (chainOfCochain K)) :
    cochainHomotopyRawEquiv hK hK.toExactProjectiveComplex (𝟙 _) =
      StableHom.classOf R _ _ LinearMap.id := by
  rw [← (HomotopyCategory.quotient _ _).map_id, cochainHomotopyRawEquiv_map]
  congr 1
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (K.d (-1) 0).hom) z
  rfl
end CompleteComparison

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

def attachingRow (n : ℕ) : middleTerm D (n + 1) →ₗ[R] D.term n :=
  (D.first n).coprod (D.second n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingCoefficientComplex
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

def coefficientComplexIso :
    ((evaluationFunctor k R X).mapHomologicalComplex (ComplexShape.down ℕ)).obj P ≅
      ((evaluationFunctor k R Y).mapHomologicalComplex (ComplexShape.down ℕ)).obj P :=
  (NatIso.mapHomologicalComplex (evaluationCoefficientIso k R e) (ComplexShape.down ℕ)).app P

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedStructure
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_finite _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace ConvertedAlgebra

variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]
variable [SMulCommClass (A k q) (A k q)ᵐᵒᵖ F]

theorem jacobson_fourth_ne_bot (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (Ring.jacobson (ConvertedAlgebra k q F)) ^ 4 ≠ ⊥ := by
  have h4 := Ideal.mul_mem_mul
    (Ideal.mul_mem_mul (Ideal.mul_mem_mul (radicalU_mem q F) (radicalT_mem q F))
      (radicalU_mem q F)) (radicalT_mem q F)
  have hmem : ((radicalU q F * radicalT q F) * radicalU q F) * radicalT q F ∈
      (Ring.jacobson (ConvertedAlgebra k q F)) ^ 4 := by
    simpa only [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul] using h4
  intro h
  rw [h] at hmem
  have ht := congrArg Triangular.top (show _ = 0 from hmem)
  exact A.fourfold_product_ne_zero q hq hq1 ht

end ConvertedAlgebra
end ArExplicit

end OAI
end


