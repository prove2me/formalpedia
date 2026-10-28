-- Prove2me | Definitions.Def_OAIQ031A147
-- name    : OAIQ031A147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:27:24.689793+00:00
-- url     : https://prove2.me/theorems/ad2aa53b-2db6-4eda-b20e-a31c4e5e3204
-- title:
--   Definitions bundle OAIQ031A147 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.productRegularEndpoint`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_CompleteTailCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailCanonical.lean), [`AuslanderReiten_Complete_CompleteTailExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailExt.lean), [`AuslanderReiten_Ext_AExtActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/AExtActions.lean), [`AuslanderReiten_Ext_ExternalRegularEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalRegularEvaluation.lean), [`AuslanderReiten_Ext_TTensorActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorActions.lean), [`AuslanderReiten_Homology_AEndHomScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/AEndHomScalar.lean), [`AuslanderReiten_Homology_FullPositiveFunctorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/FullPositiveFunctorAction.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A139`, `OAIQ031A141` and `OAIQ031A142` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A151` and `OAIQ031A152`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A139
import Definitions.Def_OAIQ031A141
import Definitions.Def_OAIQ031A142

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S)

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesProjectiveObjects]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (R := R) (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (R := S) (chainOfCochain (functorComplex F K)))
variable (e : ModuleCat.of S (Cokernel (chainOfCochain (functorComplex F K)) 0) ≅
  F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
variable (hπ : (tailFunctorHom F K).f 0 ≫ F.map (((completeExtResolution (R := R) hK)).π.f 0) = ((completeExtResolution (R := S) hFK)).π.f 0 ≫ e.hom)
include hπ

theorem fullPositiveExtEquiv_functor_mk (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) (R := S) (functorComplex F K) (functorComplex F K) hFK hFK.toExactProjectiveComplex n
      (CohomologyClass.mk (fullHomCocycleMap F K K ((n+1 : ℕ) : ℤ) x)) =
    ((Ext.mk₀ e.hom).comp
      ((fullPositiveExtEquiv (k := k) (R := R) K K hK hK.toExactProjectiveComplex n
        (CohomologyClass.mk x)).mapExactFunctor F) (zero_add _)).comp
          (Ext.mk₀ e.inv) (add_zero _) := by
  rw [fullPositiveExtEquiv_mk, fullPositiveExtEquiv_mk]
  exact restrictedEndExt_functor (k := k) F K hK hFK e hπ (n+1) x

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailCanonical
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

theorem fullPositiveExtEquiv_functor (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) (functorComplex F K) (functorComplex F K)
      hFK hFK.toExactProjectiveComplex n
      (CohomologyClass.mk (fullHomCocycleMap F K K ((n+1 : ℕ) : ℤ) x)) =
    ((Ext.mk₀ (completeFunctorEndpointIso F K hK hFK).hom).comp
      ((fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
        (CohomologyClass.mk x)).mapExactFunctor F) (zero_add _)).comp
          (Ext.mk₀ (completeFunctorEndpointIso F K hK hFK).inv) (add_zero _) :=
  fullPositiveExtEquiv_functor_mk (k := k) F K hK hFK
    (completeFunctorEndpointIso F K hK hFK)
    (completeFunctorEndpointIso_augmentation F K hK hFK) n x

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_AExtActions
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]

omit [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
  [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))] in
theorem aFactorExtClass :
    ModuleBar.extClass3 k T (Simple q) (CocycleData.p q) (CocycleData.p_isCocycle3 q) =
      tExplicitP q := rfl

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalRegularEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.AbsoluteBar.twistedModuleTower _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "UA" => AbsoluteBar.moduleObject k A 0
local notation "UB" => AbsoluteBar.moduleObject k B 0
local notation "XY" => ExternalTensor.moduleObject k A B X Y

def productRegularEndpoint :
    (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB) ⟶ XY :=
  BarBalanced.regularMap k (A ⊗[k] B) XY
    (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB))
    (barTensorZeroEquiv k A B).toModuleIso.hom

theorem productRegularEndpoint_eq_map :
    productRegularEndpoint k A B X Y =
      BarBalanced.regularMap k (A ⊗[k] B) XY
        (ExternalTensor.envelopingObject k A B
          (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) UA UB))
        (barTensorZeroEquiv k A B).toModuleIso.hom := rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorActions
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

theorem tExplicitCoefficientEquiv_succ (n : ℕ) (x : TSelfExt q (3*n)) :
    (tExplicitCoefficientEquiv q hq hq1 h (n+1)).symm (tPMul q (3*n) x) =
      (tExplicitCoefficientEquiv q hq hq1 h n).symm x := by
  change (tExplicitCoefficientEquiv q hq hq1 h n).symm
    ((tPMulEquiv q hq hq1 h (3*n)).symm ((tPMulEquiv q hq hq1 h (3*n)) x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem tTensorScalarEquiv_first (a b : ℕ)
    (z : TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b)) :
    tTensorScalarEquiv q hq hq1 h (a+1) b
      (TensorProduct.map (tPMul q (3*a)) LinearMap.id z) =
      tTensorScalarEquiv q hq hq1 h a b z := by
  induction z using OAI.tensorInductionOn with
  | tmul x y =>
      rw [TensorProduct.map_tmul, tTensorScalarEquiv_tmul, tTensorScalarEquiv_tmul,
        tExplicitCoefficientEquiv_succ]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tTensorScalarEquiv_second (a b : ℕ)
    (z : TSelfExt q (3*a) ⊗[k] TSelfExt q (3*b)) :
    tTensorScalarEquiv q hq hq1 h a (b+1)
      (TensorProduct.map LinearMap.id (tPMul q (3*b)) z) =
      tTensorScalarEquiv q hq hq1 h a b z := by
  induction z using OAI.tensorInductionOn with
  | tmul x y =>
      rw [TensorProduct.map_tmul, tTensorScalarEquiv_tmul, tTensorScalarEquiv_tmul,
        tExplicitCoefficientEquiv_succ]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_AEndHomScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] (q : k) (hq1 : 1+q ≠ 0)
include hq1

theorem aEndHom_scalar (f : ArExplicit.A.Simple q ⟶ ArExplicit.A.Simple q) :
    ∃ c : k, ∀ x : ArExplicit.A.Simple q, f.hom x = (algebraMap k (ArExplicit.A k q) c) • x := by
  refine ⟨ArExplicit.A.endScalar q f.hom, ?_⟩
  intro x
  have hf := DFunLike.congr_fun (ArExplicit.A.end_eq_scalar_id q hq1 f.hom) x
  change f.hom x = ArExplicit.A.endScalar q f.hom • x at hf
  exact hf.trans (IsScalarTower.algebraMap_smul (ArExplicit.A k q) _ _).symm

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_FullPositiveFunctorAction
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

theorem fullPositiveExtEquiv_conjugatedFunctor
    (a : K ⟶ functorComplex F K) (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (Cokernel (chainOfCochain K) 0) ≅
      F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
    (ha : ModuleCat.ofHom (cokernelMap (extendMap a negIndexEmbedding) 0) ≫
      (completeFunctorEndpointIso F K hK hFK).hom = E.hom)
    (hb : (completeFunctorEndpointIso F K hK hFK).inv ≫
      ModuleCat.ofHom (cokernelMap (extendMap b negIndexEmbedding) 0) = E.inv)
    (n : ℕ) (x : CohomologyClass K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
      (fullHomPostcomp b _ (fullHomPrecomp a _ (mapFullHom F K K _ x))) =
    selfExtIso (k := k) E.symm (n+1)
      ((fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n x).mapExactFunctor F) := by
  rw [fullPositiveExtEquiv_postcomp hK hFK.toExactProjectiveComplex hK.toExactProjectiveComplex,
    fullPositiveExtEquiv_precomp hK hFK hFK.toExactProjectiveComplex]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [mapFullHom_mk, fullPositiveExtEquiv_functor F K hK hFK]
  simp only [selfExtIso_apply, Iso.symm_inv, Iso.symm_hom]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀, ha, hb]

theorem fullHom_conjugatedFunctor_scalar
    (a : K ⟶ functorComplex F K) (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (Cokernel (chainOfCochain K) 0) ≅
      F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
    (ha : ModuleCat.ofHom (cokernelMap (extendMap a negIndexEmbedding) 0) ≫
      (completeFunctorEndpointIso F K hK hFK).hom = E.hom)
    (hb : (completeFunctorEndpointIso F K hK hFK).inv ≫
      ModuleCat.ofHom (cokernelMap (extendMap b negIndexEmbedding) 0) = E.inv)
    (n : ℕ) (c : k)
    (hscalar : ∀ z : Ext (ModuleCat.of R (Cokernel (chainOfCochain K) 0))
        (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) (n+1),
      selfExtIso (k := k) E.symm (n+1) (z.mapExactFunctor F) = c • z)
    (x : CohomologyClass K K ((n+1 : ℕ) : ℤ)) :
    fullHomPostcomp b _ (fullHomPrecomp a _ (mapFullHom F K K _ x)) = c • x := by
  apply (fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n).injective
  rw [fullPositiveExtEquiv_conjugatedFunctor F K hK hFK a b E ha hb, hscalar, map_smul]

end ArExplicit.CompleteComparison

end

end OAI
end


