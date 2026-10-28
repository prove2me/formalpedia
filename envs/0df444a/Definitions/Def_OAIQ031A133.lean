-- Prove2me | Definitions.Def_OAIQ031A133
-- name    : OAIQ031A133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:08:05.016371+00:00
-- url     : https://prove2.me/theorems/8796343d-3623-473e-a749-d30a5845924d
-- title:
--   Definitions bundle OAIQ031A133 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 2 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.BarBalanced.nativeComplexIso`, `OAI.ArExplicit.BarBalanced.nativeFreeEndpoint`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_CanonicalBarPure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarPure.lean), [`AuslanderReiten_Bar_CanonicalBarTermValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/CanonicalBarTermValues.lean), [`AuslanderReiten_Bar_NativeBarAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarAugmentation.lean), [`AuslanderReiten_Bar_NativeBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarEvaluation.lean), [`AuslanderReiten_Bar_NativeBarFreeEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarFreeEndpoint.lean), [`AuslanderReiten_Complete_CompleteFunctorCokernelAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteFunctorCokernelAction.lean), [`AuslanderReiten_Complete_CompleteTailExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailExt.lean), [`AuslanderReiten_Complete_CompleteTailFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailFunctor.lean), [`AuslanderReiten_Homology_FullPositiveNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/FullPositiveNaturality.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A120` and `OAIQ031A121` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A141`, `OAIQ031A142` and `OAIQ031A143`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A120
import Definitions.Def_OAIQ031A121

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarTermValues
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [charP : CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

omit charP in
/- The characteristic assumption is retained explicitly in the complex-isomorphism interface.
Using its defining linear equivalence avoids expanding the complex module structures. -/
theorem canonicalTermIso_tmul [CharP k 2] (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R (n+1))) (x : X) :
    type_of% (canonicalTermTmulProof k R X n z x) :=
  canonicalTermTmulProof k R X n z x

include charP in
theorem canonicalComplexIso_tmul (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R (n+1))) (x : X) :
    type_of% (canonicalTermIso_tmul k R X n z x) :=
  canonicalTermIso_tmul k R X n z x

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_CanonicalBarPure
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
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

theorem canonicalComplexIso_pure (a b : R) (x : X) :
    type_of% ((canonicalComplexIso_tmul k R X 0
      (⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 1)) x).trans
        (rawEval_pure k R X a b x)) :=
  (canonicalComplexIso_tmul k R X 0
    (⟨a ⊗ₜ[k] b⟩ : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R 1)) x).trans
      (rawEval_pure k R X a b x)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def nativeComplexIso :
    ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R) ≅
      ModuleBar.complex k R M :=
  canonicalComplexIso k R (ModuleCat.of R M) ≪≫ ModuleBar.coefficientScalarIso k R M

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

theorem coefficientScalarIso_augmentation :
    (coefficientScalarIso k R M).hom.f 0 ≫ (nativeResolution k R M).π.f 0 =
      canonicalCoefficientAugmentation k R M := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

end ArExplicit.ModuleBar

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem nativeComplexIso_augmentation :
    (nativeComplexIso k R M).hom.f 0 ≫ (ModuleBar.nativeResolution k R M).π.f 0 =
      nativeEvaluatedAugmentation k R M ≫ (nativeEndpointIso k R M).hom := by
  exact compose_augmentation
    ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0)
    ((ModuleBar.coefficientScalarIso k R M).hom.f 0)
    ((ModuleBar.nativeResolution k R M).π.f 0)
    (ModuleBar.canonicalCoefficientAugmentation k R M)
    (nativeEvaluatedAugmentation k R M) (nativeEndpointIso k R M).hom
    (ModuleBar.coefficientScalarIso_augmentation k R M)
    (canonicalComplexIso_augmentation k R M).symm

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarFreeEndpoint
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

@[simp] theorem coefficientScalarIso_tmul (a : R) (m : M) :
    (coefficientScalarIso k R M).hom.f 0 (canonicalCoefficientTensor k R M a m) =
      a ⊗ₜ[k] m := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

end ArExplicit.ModuleBar

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def nativeFreeEndpoint (e : M ≃ₗ[k] k) :
    (ExternalBalanced.factorEvaluation k (ModuleCat.of R M) (AbsoluteBar.complex k R)).X 0 ⟶
      ModuleCat.of R R :=
  (nativeComplexIso k R M).hom.f 0 ≫ (ModuleBar.freeCoordinate k R M e).toModuleIso.hom

omit [Module k M] [IsScalarTower k R M] in
theorem canonicalComplexIso_tensor (a b : R) (m : M) :
    type_of% (canonicalComplexIso_pure k R (ModuleCat.of R M) a b m) :=
  canonicalComplexIso_pure k R (ModuleCat.of R M) a b m

theorem nativeComplexIso_component (n : ℕ) :
    (nativeComplexIso k R M).hom.f n =
      (canonicalComplexIso k R (ModuleCat.of R M)).hom.f n ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f n := rfl

theorem nativeFreeEndpoint_component (e : M ≃ₗ[k] k) :
    nativeFreeEndpoint k R M e =
      ((canonicalComplexIso k R (ModuleCat.of R M)).hom.f 0 ≫
        (ModuleBar.coefficientScalarIso k R M).hom.f 0) ≫
          (ModuleBar.freeCoordinate k R M e).toModuleIso.hom := by
  rw [nativeFreeEndpoint, nativeComplexIso_component]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailFunctor
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
local notation "FK" => functorComplex F K

theorem tailFunctorHom_cochain (r n : ℕ) (x : Cochain K K (r : ℤ)) :
    cochainTailMap FK FK r (x.map F) n ≫ (tailFunctorHom F K).f n =
      (tailFunctorHom F K).f (r+n) ≫ F.map (cochainTailMap K K r x n) := by
  dsimp only [cochainTailMap, tailFunctorHom]
  exact (functor_iso_square F (tailTermIso K (r+n)) (tailTermIso K n)
    (tailTermIso FK (r+n)) (tailTermIso FK n)
    (x.v (-((r+n : ℕ) : ℤ)) (-(n : ℤ)) (by omega))).symm

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

omit [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] in
theorem tailFunctor_augmentation (r : ℕ) (x : Cochain K K (r : ℤ)) :
    ResolutionProducts.natComparisonAugmentation (R := S) (completeExtResolution (R := S) hFK) r (cochainTailMap (functorComplex F K) (functorComplex F K) r (x.map F)) =
      ((tailFunctorHom F K).f r ≫
        F.map (ResolutionProducts.natComparisonAugmentation (R := R) (completeExtResolution (R := R) hK) r (cochainTailMap K K r x))) ≫
          e.inv := by
  exact augmented_square F
    (cochainTailMap (functorComplex F K) (functorComplex F K) r (x.map F) 0)
    (cochainTailMap K K r x 0) ((tailFunctorHom F K).f r) ((tailFunctorHom F K).f 0)
    ((completeExtResolution hK).π.f 0) ((completeExtResolution hFK).π.f 0) e
    (tailFunctorHom_cochain F K r 0 x) hπ

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_FullPositiveNaturality
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem fullPositiveExtEquiv_precomp
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (hM : ExactProjectiveComplex (chainOfCochain M))
    (f : K ⟶ L) (n : ℕ) (x : CohomologyClass L M ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K M hK hM n (fullHomPrecomp f _ x) =
      (Ext.mk₀ (ModuleCat.ofHom (cokernelMap (extendMap f negIndexEmbedding) 0))).comp
        (fullPositiveExtEquiv (k := k) L M hL hM n x) (zero_add _) := by
  apply (positiveExtStableEquiv (k := k) hK
    (ModuleCat.of R (Cokernel (chainOfCochain M) 0)) n).injective
  rw [fullPositiveExtEquiv_stable, positiveExtStableEquiv_precomp hK hL,
    fullPositiveExtEquiv_stable]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPrecomp_mk, fullHomSourceStableLinearEquiv_mk,
    fullHomSourceStableLinearEquiv_mk, StableHom.precomp_classOf,
    sourceCocycleMap_precomp (k := k)]

theorem fullPositiveExtEquiv_postcomp
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L))
    (hM : ExactProjectiveComplex (chainOfCochain M))
    (f : L ⟶ M) (n : ℕ) (x : CohomologyClass K L ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K M hK hM n (fullHomPostcomp f _ x) =
      (fullPositiveExtEquiv (k := k) K L hK hL n x).comp
        (Ext.mk₀ (ModuleCat.ofHom (cokernelMap (extendMap f negIndexEmbedding) 0))) (add_zero _) := by
  apply (positiveExtStableEquiv (k := k) hK
    (ModuleCat.of R (Cokernel (chainOfCochain M) 0)) n).injective
  rw [fullPositiveExtEquiv_stable, positiveExtStableEquiv_postcomp,
    fullPositiveExtEquiv_stable]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPostcomp_mk, fullHomSourceStableLinearEquiv_mk,
    fullHomSourceStableLinearEquiv_mk, StableHom.postcomp_classOf,
    sourceCocycleMap_postcomp (k := k)]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorCokernelAction
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
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

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem cokernelMap_coordinates {L M : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ M) :
    ModuleCat.ofHom (cokernelMap (extendMap f negIndexEmbedding) 0) ≫
      (cochainCokernelLinearEquiv M).toModuleIso.hom =
    (cochainCokernelLinearEquiv L).toModuleIso.hom ≫ ModuleCat.ofHom (cochainCokernelMap f) := by
  apply ModuleCat.hom_ext
  exact cochainCokernelLinearEquiv_natural f

end ArExplicit.CompleteComparison

end

end OAI
end


