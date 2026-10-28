-- Prove2me | Definitions.Def_OAIQ031A114
-- name    : OAIQ031A114
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:49:44.417334+00:00
-- url     : https://prove2.me/theorems/16582e12-4db0-4960-9dfb-d16db0daf802
-- title:
--   Definitions bundle OAIQ031A114 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 7 definitions and 13 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.twistedEvaluationEquiv`, `OAI.ArExplicit.ModuleBar.canonicalHomTransport`, `OAI.ArExplicit.ModuleBar.nativeHomTransport`, `OAI.ArExplicit.ModuleBar.nativeTensorTransport`, `OAI.ArExplicit.ModuleBar.nativeTransportBase`, `OAI.ArExplicit.TwistedBimodule.tensorUntwist`, `OAI.ArExplicit.twistedEvaluationCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarHomTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarHomTwist.lean), [`AuslanderReiten_Bar_ModuleBarNativeTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNativeTransport.lean), [`AuslanderReiten_Bar_ModuleBarNativeTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNativeTwist.lean), [`AuslanderReiten_Bar_ModuleBarTensorEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorEndpoint.lean), [`AuslanderReiten_Bar_ModuleBarTensorExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExact.lean), [`AuslanderReiten_Bar_ModuleBarTensorHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorHom.lean), [`AuslanderReiten_Bar_ModuleBarTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorTransport.lean), [`AuslanderReiten_Modules_TwistedModuleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedModuleEvaluation.lean), [`AuslanderReiten_Resolutions_EvaluatedOrdinaryResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/EvaluatedOrdinaryResolution.lean), [`AuslanderReiten_Resolutions_FiniteResolutionAdditive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionAdditive.lean), [`AuslanderReiten_Resolutions_FiniteResolutionLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionLinear.lean), [`AuslanderReiten_Tensor_TwistedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A091`, `OAIQ031A093`, `OAIQ031A095`, `OAIQ031A097` and `OAIQ031A101` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A122`, `OAIQ031A125` and `OAIQ031A126`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A091
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A095
import Definitions.Def_OAIQ031A097
import Definitions.Def_OAIQ031A101

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarHomTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
include he

variable [CharP k 2]

def canonicalHomTransport :
    ExternalTensor.canonicalHomCochain k R (complex k R M) (ModuleCat.of R M) ⟶
      ExternalTensor.canonicalHomCochain k R (complex k R M) (ModuleCat.of R M) :=
  (ExternalTensor.homCochainScalarIso k R (complex k R M) M).inv ≫
    homTransport k R M h e he ≫
      (ExternalTensor.homCochainScalarIso k R (complex k R M) M).hom

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarNativeTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

def nativeHomTransport :
    ExternalTensor.canonicalHomCochain k R (nativeResolution k R M).complex (ModuleCat.of R M) ⟶
      ExternalTensor.canonicalHomCochain k R (nativeResolution k R M).complex (ModuleCat.of R M) :=
  canonicalHomTransport k R M h e he

theorem nativeHomTransport_apply (n : ℕ)
    (f : (nativeResolution k R M).complex.X n →ₗ[R] ModuleCat.of R M)
    (x : (nativeResolution k R M).complex.X n) :
    (show (nativeResolution k R M).complex.X n →ₗ[R] ModuleCat.of R M from
      ((nativeHomTransport k R M h e he).f n).hom f) x =
      e.symm (f (transport k R M h e (n+1) x)) := rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarNativeTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def nativeTransportBase (n : ℕ) :
    (nativeResolution k R M).complex.X n →ₗ[k] (nativeResolution k R M).complex.X n where
  toFun := transport k R M h e (n+1)
  map_add' := (transport k R M h e (n+1)).map_add
  map_smul' a x := by
    change transport k R M h e (n+1) (left k R M (n+1) (algebraMap k R a) x) =
      left k R M (n+1) (algebraMap k R a) (transport k R M h e (n+1) x)
    erw [transport_left k R M h e he, h.commutes]

theorem nativeTransportBase_smul (n : ℕ) (a : R)
    (x : (nativeResolution k R M).complex.X n) :
    nativeTransportBase k R M h e he n (a • x) =
      h a • nativeTransportBase k R M h e he n x :=
  transport_left k R M h e he (n+1) a x

theorem nativeTransportBase_d (n : ℕ)
    (x : (nativeResolution k R M).complex.X (n+1)) :
    nativeTransportBase k R M h e he n (((nativeResolution k R M).complex.d (n+1) n).hom x) =
      ((nativeResolution k R M).complex.d (n+1) n).hom
        (nativeTransportBase k R M h e he (n+1) x) := by
  change transport k R M h e (n+1) (((complex k R M).d (n+1) n).hom x) =
    ((complex k R M).d (n+1) n).hom (transport k R M h e (n+2) x)
  rw [complex_d]
  exact transport_boundary k R M h e he (n+1) x

theorem nativeTransportBase_π (x : (nativeResolution k R M).complex.X 0) :
    ((nativeResolution k R M).π.f 0).hom (nativeTransportBase k R M h e he 0 x) =
      nativeEndpointBase k R M h e he (((nativeResolution k R M).π.f 0).hom x) :=
  (transport_boundary k R M h e he 0 x).symm

end ArExplicit.ModuleBar

end

end OAI
end

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

def nativeTensorTransport :
    ExternalTensor.complex k R S (nativeResolution k R M).complex (nativeResolution k S N).complex ⟶
    ((ExternalTensor.tensorRestriction k R S h j).mapHomologicalComplex (.down ℕ)).obj
      (ExternalTensor.complex k R S (nativeResolution k R M).complex (nativeResolution k S N).complex) :=
  ExternalTensor.transportComplex k R S h j
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (nativeTransportBase k R M h e he) (nativeTransportBase k S N j f hf)
    (nativeTransportBase_smul k R M h e he) (nativeTransportBase_smul k S N j f hf)
    (fun n x => (nativeTransportBase_d k R M h e he n x).symm)
    (fun n x => (nativeTransportBase_d k S N j f hf n x).symm)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
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
@[reassoc] theorem nativeTensorTransport_inclusion (a b n : ℕ) (hab : a+b=n) :
    ExternalTensor.inclusion k R S (nativeResolution k R M).complex (nativeResolution k S N).complex
        a b n hab ≫ (nativeTensorTransport k R S M N h j e f he hf).f n =
    ExternalTensor.transportSummand k R S h j
      (nativeResolution k R M).complex (nativeResolution k S N).complex
      (nativeTransportBase k R M h e he) (nativeTransportBase k S N j f hf)
      (nativeTransportBase_smul k R M h e he) (nativeTransportBase_smul k S N j f hf) a b ≫
        (ExternalTensor.tensorRestriction k R S h j).map
          (ExternalTensor.inclusion k R S (nativeResolution k R M).complex
            (nativeResolution k S N).complex a b n hab) :=
  ExternalTensor.inclusion_transportTerm k R S h j _ _ _ _ _ _ a b n hab

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

local instance tensorRestrictionEquivalence :
    (ExternalTensor.tensorRestriction k R S h j).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Algebra.TensorProduct.congr h j).toRingEquiv

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

local instance endpointRestrictionEquivalence :
    (ExternalTensor.tensorRestriction k R S h j).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Algebra.TensorProduct.congr h j).toRingEquiv

end ArExplicit.ModuleBar

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

theorem resolutionCokernelMap_smul (a : k) (f : M.carrier →ₗ[R] N.carrier) :
    resolutionCokernelMap τ (a • f) = a • resolutionCokernelMap τ f := by
  apply LinearMap.ext
  intro x
  exact ((N.completeCochainCokernelEquiv τ).symm.toLinearMap.restrictScalars k).map_smul a _

end FiniteLeftModule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

def tensorUntwist : BalancedTensor k R (TwistedBimodule k R σ) M ≃ₗ[R]
    TwistedLeftModule k R σ M where
  __ := tensorUntwistMap σ
  invFun := untwistInverse σ
  left_inv z := by
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add x y hx hy =>
      change untwistInverse σ (tensorUntwistMap σ (x + y)) = x + y
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy
    | tmul f m =>
      change BalancedTensor.tmul (k := k) (R := R)
        (⟨1⟩ : TwistedBimodule k R σ) (σ.symm f.value • m) =
        BalancedTensor.tmul f m
      rw [← BalancedTensor.balance]
      congr 1
      apply TwistedBimodule.ext
      simp
  right_inv x := by
    apply TwistedLeftModule.ext
    change σ.symm 1 • x.value = x.value
    simp

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedModuleEvaluation
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (σ : R ≃ₐ[k] R)

def twistedEvaluationCoordinates :
    EnvelopingBimodule k R (twistedFiniteModule σ).carrier ≃ₗ[k] TwistedBimodule k R σ :=
  EnvelopingBimodule.scalarEquiv _

 theorem twistedEvaluationCoordinates_right (r : Rᵐᵒᵖ)
    (x : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) :
    twistedEvaluationCoordinates σ (r • x) = r • twistedEvaluationCoordinates σ x := by
  change (1 : R) • (r • (show TwistedBimodule k R σ from x.value)) = r • (show TwistedBimodule k R σ from x.value)
  rw [one_smul]

 theorem twistedEvaluationCoordinates_left (r : R)
    (x : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) :
    twistedEvaluationCoordinates σ (r • x) = r • twistedEvaluationCoordinates σ x := by
  change r • ((1 : Rᵐᵒᵖ) • (show TwistedBimodule k R σ from x.value)) = r • (show TwistedBimodule k R σ from x.value)
  rw [one_smul]

namespace FiniteLeftModule
variable (X : FiniteLeftModule k R)

def twistedEvaluationEquiv : (evaluated X (twistedFiniteModule σ)).carrier ≃ₗ[R]
    TwistedLeftModule k R σ X.carrier :=
  (BalancedTensor.congrLeft (twistedEvaluationCoordinates σ) (LinearEquiv.refl k X.carrier)
    (twistedEvaluationCoordinates_right σ) (fun _ _ => rfl)
    (twistedEvaluationCoordinates_left σ)).trans (TwistedBimodule.tensorUntwist σ)

@[simp] theorem twistedEvaluationEquiv_tmul
    (r : EnvelopingBimodule k R (twistedFiniteModule σ).carrier) (x : X.carrier) :
    twistedEvaluationEquiv σ X (BalancedTensor.tmul r x) =
      ⟨σ.symm r.value.value • x⟩ := rfl

end FiniteLeftModule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_EvaluatedOrdinaryResolution
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)

theorem evaluation_zero {M N : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)} :
    FiniteLeftModule.evaluationMap X (0 : M.carrier →ₗ[_] N.carrier) = 0 :=
  EnvelopingBimodule.tensorMap_zero X.carrier

end ArExplicit.TwoCone

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
theorem resolutionCokernelMap_add (f g : M.carrier →ₗ[R] N.carrier) :
    resolutionCokernelMap τ (f+g) = resolutionCokernelMap τ f + resolutionCokernelMap τ g := by
  ext x
  exact (N.completeCochainCokernelEquiv τ).symm.map_add _ _

end FiniteLeftModule
end ArExplicit

end OAI
end


