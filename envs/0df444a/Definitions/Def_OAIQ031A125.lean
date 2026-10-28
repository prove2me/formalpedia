-- Prove2me | Definitions.Def_OAIQ031A125
-- name    : OAIQ031A125
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:58:43.516444+00:00
-- url     : https://prove2.me/theorems/7ebdc15b-aa95-4f61-823d-1054cbb225d5
-- title:
--   Definitions bundle OAIQ031A125 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 5 definitions and 6 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.shiftedModuleMap`, `OAI.ArExplicit.FiniteLeftModule.shiftedResolutionMap`, `OAI.ArExplicit.ModuleBar.nativeTensorTransportResolutionHom`, `OAI.ArExplicit.ModuleBar.tensorEndpointIso`, `OAI.ArExplicit.T.twistedBarUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTensorEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorEndpoint.lean), [`AuslanderReiten_Bar_ModuleBarTensorExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExact.lean), [`AuslanderReiten_Bar_ModuleBarTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorTransport.lean), [`AuslanderReiten_Coordinates_FiniteShiftedMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteShiftedMap.lean), [`AuslanderReiten_Coordinates_TensorTopComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorTopComparison.lean), [`AuslanderReiten_Duality_FiniteStableResolutionIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/FiniteStableResolutionIso.lean), [`AuslanderReiten_Evaluation_EvaluatedTriangleArrows`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedTriangleArrows.lean), [`AuslanderReiten_Resolutions_FiniteResolutionAdditive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionAdditive.lean), [`AuslanderReiten_Resolutions_FiniteResolutionLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionLinear.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A105`, `OAIQ031A110`, `OAIQ031A113`, `OAIQ031A114` and `OAIQ031A115` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A136`, `OAIQ031A137` and `OAIQ031A153`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A105
import Definitions.Def_OAIQ031A110
import Definitions.Def_OAIQ031A113
import Definitions.Def_OAIQ031A114
import Definitions.Def_OAIQ031A115

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

omit [Module.Finite k R] [Module.Finite k S] [Module.Finite k M] [Module.Finite k N] in
theorem nativeTensorTransport_augmentation :
    (nativeTensorTransport k R S M N h j e f he hf).f 0 ≫
      (ExternalTensor.tensorRestriction k R S h j).map
        ((ExternalTensor.augmentation k R S (nativeResolution k R M) (nativeResolution k S N)).f 0) =
    (ExternalTensor.augmentation k R S (nativeResolution k R M) (nativeResolution k S N)).f 0 ≫
      (nativeTensorEndpointIso k R S M N h j e f he hf).hom := by
  apply ExternalTensor.hom_ext k R S (nativeResolution k R M).complex (nativeResolution k S N).complex
  intro a b hab
  have ha : a=0 := by omega
  have hb : b=0 := by omega
  subst a
  subst b
  change ExternalTensor.inclusion k R S _ _ 0 0 0 _ ≫
      (ExternalTensor.transportTerm k R S h j _ _
        (nativeTransportBase k R M h e he) (nativeTransportBase k S N j f hf)
        (nativeTransportBase_smul k R M h e he) (nativeTransportBase_smul k S N j f hf) 0 ≫ _) = _
  erw [← Category.assoc, ExternalTensor.inclusion_transportTerm, Category.assoc,
    ← Functor.map_comp, ExternalTensor.inclusion_augmentation,
    ← Category.assoc, ExternalTensor.inclusion_augmentation]
  let eP := nativeTransportBase k R M h e he 0
  let fP := nativeTransportBase k S N j f hf 0
  let e₀ := nativeEndpointBase k R M h e he
  let f₀ := nativeEndpointBase k S N j f hf
  have heP := nativeTransportBase_smul k R M h e he 0
  have hfP := nativeTransportBase_smul k S N j f hf 0
  have he₀ := nativeEndpointBase_smul k R M h e he
  have hf₀ := nativeEndpointBase_smul k S N j f hf
  let πM := (nativeResolution k R M).π.f 0
  let πN := (nativeResolution k S N).π.f 0
  have hπM := nativeTransportBase_π k R M h e he
  have hπN := nativeTransportBase_π k S N j f hf
  let := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  let := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  exact ExternalTensor.tensorSemilinear_natural k R S h j eP e₀.toLinearMap fP f₀.toLinearMap
    heP he₀ hfP hf₀ πM πN hπM hπN

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

attribute [local instance] OAI.ArExplicit.ModuleBar.tensorRestrictionEquivalence
def nativeTensorTransportResolutionHom :
    ProjectiveResolution.Hom
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (ResolutionProducts.mapResolution (ExternalTensor.tensorRestriction k R S h j)
        (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N)))
      (nativeTensorEndpointIso k R S M N h j e f he hf).hom where
  hom := nativeTensorTransport k R S M N h j e f he hf
  hom_f_zero_comp_π_f_zero := by
    erw [ResolutionProducts.mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact nativeTensorTransport_augmentation k R S M N h j e f he hf

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorEndpoint
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)

def tensorEndpointIso : ExternalTensor.moduleObject k R S M N ≅
    (ExternalTensor.tensorRestriction k R S h j).obj
      (ExternalTensor.moduleObject k R S M N) :=
  (ExternalTensor.canonicalTensorIso k R S M N).symm ≪≫
    nativeTensorEndpointIso k R S M N h j e f he hf ≪≫
      (ExternalTensor.tensorRestriction k R S h j).mapIso
        (ExternalTensor.canonicalTensorIso k R S M N)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteShiftedMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.FiniteLeftModule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {U M N : FiniteLeftModule k R} (n : ℕ)
variable (e : (HomotopyCategory.quotient _ _).obj (U.completeCochain τ) ≅
  ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(n : ℤ)⟧)
variable (f : M.carrier →ₗ[R] N.carrier)

def shiftedResolutionMap :
    (HomotopyCategory.quotient _ _).obj (U.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj ((N.canonicalCosyzygies n).completeCochain τ) :=
  e.hom ≫
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (n : ℤ)).map
      ((HomotopyCategory.quotient _ _).map (resolutionMap τ f)) ≫
    (canonicalCosyzygiesShiftIso τ N n).inv

def shiftedModuleMap : U.carrier →ₗ[R] (N.canonicalCosyzygies n).carrier :=
  Classical.choose (resolutionMap_surjective τ (shiftedResolutionMap τ n e f))

theorem shiftedModuleMap_spec :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (shiftedModuleMap τ n e f)) =
      shiftedResolutionMap τ n e f :=
  Classical.choose_spec (resolutionMap_surjective τ (shiftedResolutionMap τ n e f))

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTopComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def twistedBarUnit : (Q₀).X 0 := (1 : R) ⊗ₜ[k] (1 : R)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_FiniteStableResolutionIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

variable {M N} {P : FiniteLeftModule k R}

theorem stableResolutionIso_hom_of_class (e : StableIsomorphism R M.carrier N.carrier)
    (f : M.carrier →ₗ[R] N.carrier) (hf : e.hom = StableHom.classOf R _ _ f) :
    (stableResolutionIso τ e).hom =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) := by
  apply (resolutionHomotopyEquiv τ M N).injective
  rw [stableResolutionIso_hom, hf, resolutionHomotopyEquiv_map]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionLinear
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R)
variable {M N : FiniteLeftModule k R}

theorem resolutionMap_smul (a : k) (f : M.carrier →ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (a • f)) =
      a • (HomotopyCategory.quotient _ _).map (resolutionMap τ f) := by
  rw [← Functor.map_smul]
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    resolutionMap_cokernel, cochainCokernelMap_smul, resolutionMap_cokernel,
    resolutionCokernelMap_smul]
end FiniteLeftModule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedTriangleArrows
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]

namespace FiniteLeftModule
variable (X : FiniteLeftModule k R) {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}
variable (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
variable (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P.carrier)]
variable (τ : FrobeniusTrace k R)

theorem evaluationTriangle_second :
    (evaluationTriangle X f g hf hg he τ).mor₂ =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X g)) :=
  resolutionTriangle_second τ (evaluationMap X f) (evaluationMap X g)
    (evaluation_shortExact X f g hf hg he).1
    (evaluation_shortExact X f g hf hg he).2.1
    (evaluation_shortExact X f g hf hg he).2.2
end FiniteLeftModule

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionAdditive
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R)
variable {M N : FiniteLeftModule k R}

theorem resolutionMap_add (f g : M.carrier →ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (f+g)) =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) +
      (HomotopyCategory.quotient _ _).map (resolutionMap τ g) := by
  rw [← Functor.map_add]
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    resolutionMap_cokernel, cochainCokernelMap_add, resolutionMap_cokernel,
    resolutionMap_cokernel, resolutionCokernelMap_add]
end FiniteLeftModule
end ArExplicit

end OAI
end


