-- Prove2me | Definitions.Def_OAIQ031A132
-- name    : OAIQ031A132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:08:19.17654+00:00
-- url     : https://prove2.me/theorems/bf3e79d8-e92f-47d0-a9e5-e0573faef56c
-- title:
--   Definitions bundle OAIQ031A132 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 12 definitions and 13 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.comparisonIn`, `OAI.ArExplicit.BalancedTensor.comparisonOut`, `OAI.ArExplicit.BalancedTensor.completeActionCokernelIso`, `OAI.ArExplicit.BalancedTensor.completeActionEndpoint`, `OAI.ArExplicit.BalancedTensor.completeActionIn`, `OAI.ArExplicit.BalancedTensor.completeActionOut`, `OAI.ArExplicit.BalancedTensor.completeTensorIso`, `OAI.ArExplicit.BalancedTensor.nativeEvaluationIso`, `OAI.ArExplicit.BalancedTensor.tensorCokernelEquiv`, `OAI.ArExplicit.CompleteComparison.completeFunctorEndpointIso`, `OAI.ArExplicit.CompleteComparison.completeTailResolutionHom`, `OAI.ArExplicit.CompleteComparison.rawFunctorEndpointIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedCanonical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedCanonical.lean), [`AuslanderReiten_Complete_CompleteFunctorRawEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteFunctorRawEndpoint.lean), [`AuslanderReiten_Complete_CompleteTailEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailEndpoint.lean), [`AuslanderReiten_Complete_CompleteTailExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailExt.lean), [`AuslanderReiten_Tensor_BalancedTensorComparisonMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorComparisonMaps.lean), [`AuslanderReiten_Tensor_BalancedTensorCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCompleteAction.lean), [`AuslanderReiten_Tensor_BalancedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A118`, `OAIQ031A120` and `OAIQ031A121` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A141`, `OAIQ031A142` and `OAIQ031A144`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A118
import Definitions.Def_OAIQ031A120
import Definitions.Def_OAIQ031A121

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedCanonical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

theorem canonicalEquiv_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (z : canonicalEvaluated k R X (n+4)) :
    canonicalEquiv k R X (n+1)
      (canonicalMap k R X (cubicHom k R p n) z) =
    ModuleBar.suffixComparisonMap k R X p n (canonicalEquiv k R X (n+4) z) := by
  exact canonicalEquiv_map k R X (m := n+4) (n := n+1)
    (cubicHom k R p n) (ModuleBar.suffixComparisonMap k R X p n)
    (rawEval_cubic_compatibility k R X p n) z

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailEndpoint
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

def completeFunctorEndpointIso :
    ModuleCat.of S (Cokernel (chainOfCochain (functorComplex F K)) 0) ≅
      F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) :=
  ResolutionProducts.resolutionEndpointIso (completeExtResolution hFK)
    (ResolutionProducts.mapResolution F (completeExtResolution hK)) (tailFunctorIso F K)

theorem completeFunctorEndpointIso_augmentation :
    (tailFunctorHom F K).f 0 ≫ F.map ((completeExtResolution hK).π.f 0) =
      (completeExtResolution hFK).π.f 0 ≫ (completeFunctorEndpointIso F K hK hFK).hom := by
  have h := ResolutionProducts.resolutionEndpointIso_augmentation (completeExtResolution hFK)
    (ResolutionProducts.mapResolution F (completeExtResolution hK)) (tailFunctorIso F K)
  erw [ResolutionProducts.mapResolution_π_zero] at h
  rw [tailFunctorIso_hom] at h
  exact h.symm

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorRawEndpoint
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]

theorem rawAugmentation_coordinates (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K)) :
    (completeExtResolution hK).π.f 0 ≫ (cochainCokernelLinearEquiv K).toModuleIso.hom =
      (tailTermIso K 0).hom ≫ rawAugmentation K := by
  erw [nonnegativeTailAugmentation_f_zero]
  rfl

variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

def rawFunctorEndpointIso : ModuleCat.of S (CochainCokernel (functorComplex F K)) ≅
    F.obj (ModuleCat.of R (CochainCokernel K)) :=
  (cochainCokernelLinearEquiv (functorComplex F K)).symm.toModuleIso ≪≫
    completeFunctorEndpointIso F K hK hFK ≪≫ F.mapIso (cochainCokernelLinearEquiv K).toModuleIso

theorem rawFunctorEndpointIso_augmentation :
    F.map (rawAugmentation K) =
      rawAugmentation (functorComplex F K) ≫ (rawFunctorEndpointIso F K hK hFK).hom := by
  have ht := raw_square F (tailTermIso K 0) (tailTermIso (functorComplex F K) 0)
    (Iso.refl (F.obj (K.X 0))) (cochainCokernelLinearEquiv K).toModuleIso
    (cochainCokernelLinearEquiv (functorComplex F K)).toModuleIso
    (completeFunctorEndpointIso F K hK hFK)
    ((completeExtResolution hK).π.f 0) (rawAugmentation K)
    ((completeExtResolution hFK).π.f 0) (rawAugmentation (functorComplex F K))
    (rawAugmentation_coordinates K hK) (rawAugmentation_coordinates (functorComplex F K) hFK)
    (by
      change ((tailTermIso (functorComplex F K) 0).hom ≫
        F.map (tailTermIso K 0).inv) ≫ F.map ((completeExtResolution hK).π.f 0) = _
      exact completeFunctorEndpointIso_augmentation F K hK hFK)
  change (𝟙 _ ≫ F.map (rawAugmentation K)) =
    rawAugmentation (functorComplex F K) ≫ (rawFunctorEndpointIso F K hK hFK).hom at ht
  simpa only [Category.id_comp] using ht

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def completeTailResolutionHom :
    ProjectiveResolution.Hom (completeExtResolution (R := S) hFK) (ResolutionProducts.mapResolution F (completeExtResolution (R := R) hK)) e.hom where
  hom := tailFunctorHom F K
  hom_f_zero_comp_π_f_zero := by
    erw [ResolutionProducts.mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact hπ

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def tensorCokernelEquiv : CochainCokernel (completeTensor (F := F) τ M) ≃ₗ[R]
    BalancedTensor k R F M.carrier :=
  (cochainCokernelEquiv (k := k) (F := F) (S := R) (M.completeCochain τ)).trans
    (mapRightEquiv (k := k) (F := F) (S := R) (M.completeCochainCokernelEquiv τ))

omit [SMulCommClass k Rᵐᵒᵖ F] [Module.Finite R F] [Module.Projective R F] in
@[simp] theorem tensorCokernelEquiv_mk (f : F) (x : (M.completeCochain τ).X 0) :
    tensorCokernelEquiv (F := F) τ M (Submodule.Quotient.mk (tmul f x)) =
      tmul f (M.completeCochainCokernelEquiv τ (Submodule.Quotient.mk x)) := by
  rw [tensorCokernelEquiv, LinearEquiv.trans_apply,
    cochainCokernelEquiv_mk_tmul, mapRightEquiv_tmul]

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem completeTensor_totallyAcyclic : TotallyAcyclicCochain (completeTensor (F := F) τ M) := by
  let := τ.regular_injective
  exact complex_totallyAcyclic (M.completeCochain τ)
    (M.completeCochain_totallyAcyclic τ).toExactProjectiveCochain

def completeTensorIso (e : BalancedTensor k R F M.carrier ≃ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).obj (completeTensor (F := F) τ M) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) :=
  rawCokernelHomotopyIso (completeTensor_totallyAcyclic (F := F) τ M)
    (N.completeCochain_totallyAcyclic τ)
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans (N.completeCochainCokernelEquiv τ).symm)

variable {G : Type u} [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module R G]
variable [IsScalarTower k Rᵐᵒᵖ G] [SMulCommClass k Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [Module.Finite Rᵐᵒᵖ G] [Module.Projective Rᵐᵒᵖ G]
variable [Module.Finite R G] [Module.Projective R G]

omit [SMulCommClass k Rᵐᵒᵖ F] [Module.Finite R F] [Module.Projective R F] in
omit [SMulCommClass k Rᵐᵒᵖ G] [Module.Finite R G] [Module.Projective R G] in
theorem tensorCokernelEquiv_natural (a : F →ₗ[Rᵐᵒᵖ] G)
    (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (z : CochainCokernel (completeTensor (F := F) τ M)) :
    tensorCokernelEquiv (F := G) τ M
      (cochainCokernelMap (complexMap (k := k) a ha (M.completeCochain τ)) z) =
    mapLeft (k := k) (M := M.carrier) a (tensorCokernelEquiv (F := F) τ M z) := by
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((completeTensor (F := F) τ M).d (-1) 0).hom) z
  induction x using induction_on with
  | zero => repeat' erw [map_zero]
  | add x y hx hy =>
    repeat' erw [map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul f m =>
    erw [cochainCokernelMap_mk]
    change tensorCokernelEquiv (F := G) τ M (Submodule.Quotient.mk (tmul (a f) m)) = _
    erw [tensorCokernelEquiv_mk]

variable (N' : FiniteLeftModule k R)

omit [SMulCommClass k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ G] in
theorem completeTensorIso_natural
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (e : BalancedTensor k R F M.carrier ≃ₗ[R] N.carrier)
    (e' : BalancedTensor k R G M.carrier ≃ₗ[R] N'.carrier)
    (b : N.carrier →ₗ[R] N'.carrier)
    (hab : ∀ x, e' (mapLeft (k := k) (M := M.carrier) a x) = b (e x)) :
    (HomotopyCategory.quotient _ _).map (complexMap (k := k) a ha (M.completeCochain τ)) ≫
      (completeTensorIso τ M N' e').hom =
    (completeTensorIso τ M N e).hom ≫
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ b) := by
  apply rawCokernelHomotopyIso_natural
  rw [FiniteLeftModule.resolutionMap_cokernel]
  apply LinearMap.ext
  intro z
  change (N'.completeCochainCokernelEquiv τ).symm
      (e' (tensorCokernelEquiv (F := G) τ M
        (cochainCokernelMap (complexMap (k := k) a ha (M.completeCochain τ)) z))) =
    (N'.completeCochainCokernelEquiv τ).symm
      (b ((N.completeCochainCokernelEquiv τ)
        ((N.completeCochainCokernelEquiv τ).symm (e (tensorCokernelEquiv (F := F) τ M z)))))
  rw [tensorCokernelEquiv_natural, LinearEquiv.apply_symm_apply, hab]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorComparisonMaps
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
open CompleteComparison
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] N.carrier)

def comparisonOut : completeTensor (F := F) τ M ⟶ N.completeCochain τ :=
  cokernelCochainLift (completeTensor_totallyAcyclic (F := F) τ M)
    (N.completeCochain_totallyAcyclic τ)
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans
      (N.completeCochainCokernelEquiv τ).symm).toLinearMap

def comparisonIn : N.completeCochain τ ⟶ completeTensor (F := F) τ M :=
  cokernelCochainLift (N.completeCochain_totallyAcyclic τ)
    (completeTensor_totallyAcyclic (F := F) τ M)
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans
      (N.completeCochainCokernelEquiv τ).symm).symm.toLinearMap

theorem comparisonOut_quotient :
    (HomotopyCategory.quotient _ _).map (comparisonOut τ M N e) =
      (completeTensorIso τ M N e).hom :=
  cokernelCochainLift_quotient _ _ _

theorem comparisonIn_quotient :
    (HomotopyCategory.quotient _ _).map (comparisonIn τ M N e) =
      (completeTensorIso τ M N e).inv :=
  cokernelCochainLift_quotient_inv _ _ _

theorem comparisonOut_bijective (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Bijective (fullHomPostcomp (K := K) (comparisonOut τ M N e) n) := by
  apply fullHomPostcomp_bijective k n (comparisonOut τ M N e) (comparisonIn τ M N e)
  · rw [CategoryTheory.Functor.map_comp, comparisonOut_quotient, comparisonIn_quotient,
      Iso.hom_inv_id]
  · rw [CategoryTheory.Functor.map_comp, comparisonOut_quotient, comparisonIn_quotient,
      Iso.inv_hom_id]

variable {G : Type u} [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module R G]
variable [IsScalarTower k Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [Module.Finite Rᵐᵒᵖ G] [Module.Projective Rᵐᵒᵖ G]
variable [Module.Finite R G] [Module.Projective R G]
variable (N' : FiniteLeftModule k R)

theorem comparisonOut_natural
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (e' : BalancedTensor k R G M.carrier ≃ₗ[R] N'.carrier)
    (b : N.carrier →ₗ[R] N'.carrier)
    (hab : ∀ x, e' (mapLeft (k := k) (M := M.carrier) a x) = b (e x)) :
    (HomotopyCategory.quotient _ _).map
      (complexMap (k := k) a ha (M.completeCochain τ) ≫ comparisonOut τ M N' e') =
    (HomotopyCategory.quotient _ _).map
      (comparisonOut τ M N e ≫ FiniteLeftModule.resolutionMap τ b) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    comparisonOut_quotient, comparisonOut_quotient]
  exact completeTensorIso_natural τ M N N' a ha e e' b hab

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCompleteAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
open CompleteComparison
universe u
variable {k R F : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
variable [HasDerivedCategory (ModuleCat.{u} R)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable [PreservesFiniteLimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [PreservesFiniteColimits (functor (k := k) (R := R) (S := R) (F := F))]
variable [(functor (k := k) (R := R) (S := R) (F := F)).PreservesProjectiveObjects]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)
variable (e : BalancedTensor k R F M.carrier ≃ₗ[R] M.carrier)

def nativeEvaluationIso :
    (functor (k := k) (R := R) (S := R) (F := F)).obj M.carrier ≅ M.carrier :=
  nativeObjectIso (k := k) (R := R) (S := R) (F := F) M.carrier ≪≫ e.toModuleIso

def completeActionEndpoint : ModuleCat.of R (CochainCokernel (M.completeCochain τ)) ≅
    (functor (k := k) (R := R) (S := R) (F := F)).obj
      (ModuleCat.of R (CochainCokernel (M.completeCochain τ))) :=
  (M.completeCochainCokernelEquiv τ).toModuleIso ≪≫ (nativeEvaluationIso M e).symm ≪≫
    (functor (k := k) (R := R) (S := R) (F := F)).mapIso
      (M.completeCochainCokernelEquiv τ).symm.toModuleIso

def completeActionCokernelIso :
    ModuleCat.of R (CochainCokernel (completeTensor (F := F) τ M)) ≅
      ModuleCat.of R (CochainCokernel (M.completeCochain τ)) :=
  rawFunctorEndpointIso (functor (k := k) (R := R) (S := R) (F := F)) (M.completeCochain τ)
    (M.completeCochain_totallyAcyclic τ).to_chain
    (completeTensor_totallyAcyclic (F := F) τ M).to_chain ≪≫
      (completeActionEndpoint τ M e).symm

def completeActionIn : M.completeCochain τ ⟶ completeTensor (F := F) τ M :=
  cokernelCochainLift (M.completeCochain_totallyAcyclic τ)
    (completeTensor_totallyAcyclic (F := F) τ M)
    (completeActionCokernelIso τ M e).inv.hom

def completeActionOut : completeTensor (F := F) τ M ⟶ M.completeCochain τ :=
  cokernelCochainLift (completeTensor_totallyAcyclic (F := F) τ M)
    (M.completeCochain_totallyAcyclic τ) (completeActionCokernelIso τ M e).hom.hom

omit [CharP k 2] [SMulCommClass k Rᵐᵒᵖ F]
  [HasDerivedCategory (ModuleCat.{u} R)] in
theorem completeAction_inverse :
    (HomotopyCategory.quotient _ _).map
      (completeActionIn τ M e ≫ completeActionOut τ M e) = 𝟙 _ := by
  exact cokernelCochainLift_homotopy_inverse (M.completeCochain_totallyAcyclic τ)
    (completeTensor_totallyAcyclic (F := F) τ M)
    (completeActionCokernelIso τ M e).symm.toLinearEquiv

end ArExplicit.BalancedTensor

end

end OAI
end


