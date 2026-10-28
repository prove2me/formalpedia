-- Prove2me | Definitions.Def_OAIQ031A153
-- name    : OAIQ031A153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:34:56.10082+00:00
-- url     : https://prove2.me/theorems/d430de76-246c-45e9-8060-98505800f315
-- title:
--   Definitions bundle OAIQ031A153 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 3 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.ModuleBar.tensorTwist`, `OAI.ArExplicit.Resolution.tInverseTwistExt`, `OAI.ArExplicit.Resolution.tTensorInverseTwist`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTensorEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorEndpoint.lean), [`AuslanderReiten_Bar_ModuleBarTensorExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExact.lean), [`AuslanderReiten_Bar_ModuleBarTensorTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorTwist.lean), [`AuslanderReiten_Coordinates_FiniteConnectingProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteConnectingProducts.lean), [`AuslanderReiten_Coordinates_FiniteExtSourceComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteExtSourceComparison.lean), [`AuslanderReiten_Ext_TTensorTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorTwist.lean), [`AuslanderReiten_Ext_TTwistExtPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTwistExtPolynomial.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A125`, `OAIQ031A146`, `OAIQ031A148` and `OAIQ031A149` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A155` and `OAIQ031A156`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A125
import Definitions.Def_OAIQ031A146
import Definitions.Def_OAIQ031A148
import Definitions.Def_OAIQ031A149

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem nativeTensorTwist_kunneth (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) (p : ExternalTensor.Diagonal n) :
    nativeTensorKunneth k R S M N n (nativeTensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (twistExtAction k R M h e he p.val.1)
        (twistExtAction k S N j f hf p.val.2)
        (nativeTensorKunneth k R S M N n x p) := by
  unfold nativeTensorKunneth nativeTensorTwist
  have ht := ExternalTensor.extKunnethEquiv_tensorHomEndExt k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf) n x p
  rw [nativeHomTransport_ext, nativeHomTransport_ext] at ht
  exact ht

def tensorTwist (n : ℕ) :
    Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n →ₗ[k]
      Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n :=
  (ExternalTensor.selfExtScalarEquiv k R S M N n).symm.toLinearMap.comp
    ((nativeTensorTwist k R S M N h j e f he hf n).comp
      (ExternalTensor.selfExtScalarEquiv k R S M N n).toLinearMap)

theorem tensorTwist_kunneth (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n)
    (p : ExternalTensor.Diagonal n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (twistExtAction k R M h e he p.val.1)
        (twistExtAction k S N j f hf p.val.2) (tensorKunneth k R S M N n x p) := by
  unfold tensorKunneth tensorTwist
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact nativeTensorTwist_kunneth k R S M N h j e f he hf n _ p

variable (α : ∀ n, Ext (ModuleCat.of R M) (ModuleCat.of R M) n →ₗ[k]
  Ext (ModuleCat.of R M) (ModuleCat.of R M) n)
variable (β : ∀ n, Ext (ModuleCat.of S N) (ModuleCat.of S N) n →ₗ[k]
  Ext (ModuleCat.of S N) (ModuleCat.of S N) n)
variable (hα : ∀ n, twistExtAction k R M h e he n = α n)
variable (hβ : ∀ n, twistExtAction k S N j f hf n = β n)
include hα hβ

theorem tensorTwist_kunneth_of_factors (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n)
    (p : ExternalTensor.Diagonal n) :
    tensorKunneth k R S M N n (tensorTwist k R S M N h j e f he hf n x) p =
      TensorProduct.map (α p.val.1) (β p.val.2) (tensorKunneth k R S M N n x p) := by
  rw [← hα, ← hβ]
  exact tensorTwist_kunneth k R S M N h j e f he hf n x p

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
theorem nativeTensorTwist_eq_exactFunctor (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorTwist k R S M N h j e f he hf n x =
      ((Ext.mk₀ (nativeTensorEndpointIso k R S M N h j e f he hf).hom).comp
        (x.mapExactFunctor (ExternalTensor.tensorRestriction k R S h j)) (zero_add n)).comp
          (Ext.mk₀ (nativeTensorEndpointIso k R S M N h j e f he hf).inv) (add_zero n) := by
  let P := ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N)
  let H := nativeTensorHomTransport k R S M N h j e f he hf
  let E := nativeTensorEndpointIso k R S M N h j e f he hf
  let φ := nativeTensorTransportResolutionHom k R S M N h j e f he hf
  have hcomparison := nativeTensorHomTransport_apply k R S M N h j e f he hf
  let := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  let := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  let U := ExternalTensor.moduleObject k R S (ModuleCat.of R M) (ModuleCat.of S N)
  let : AddCommGroup U := U.isAddCommGroup
  let : Module (R ⊗[k] S) U := U.isModule
  let : Module k U := ExternalTensor.baseModule k R S (ModuleCat.of R M) (ModuleCat.of S N)
  let : IsScalarTower k (R ⊗[k] S) U :=
    ExternalTensor.tower k R S (ModuleCat.of R M) (ModuleCat.of S N)
  have ht := ExternalTensor.nativeHomEndExt_eq_exactFunctor k (R ⊗[k] S)
    U (addY := U.isAddCommGroup) (modY := U.isModule)
    (baseY := ExternalTensor.baseModule k R S (ModuleCat.of R M) (ModuleCat.of S N))
    (towerY := ExternalTensor.tower k R S (ModuleCat.of R M) (ModuleCat.of S N))
    P H (ExternalTensor.tensorRestriction k R S h j) E φ hcomparison n x
  exact ht

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

attribute [local instance] OAI.ArExplicit.ModuleBar.endpointRestrictionEquivalence
theorem tensorTwist_eq_exactFunctor (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) n) :
    tensorTwist k R S M N h j e f he hf n x =
      ((Ext.mk₀ (tensorEndpointIso k R S M N h j e f he hf).hom).comp
        (x.mapExactFunctor (ExternalTensor.tensorRestriction k R S h j)) (zero_add n)).comp
          (Ext.mk₀ (tensorEndpointIso k R S M N h j e f he hf).inv) (add_zero n) := by
  unfold tensorTwist
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [ExternalTensor.selfExtScalarEquiv_symm_eq_iso,
    nativeTensorTwist_eq_exactFunctor, ExternalTensor.selfExtScalarEquiv_eq_iso]
  exact selfExtIso_conjugated_functor (k := k)
    (ExternalTensor.tensorRestriction k R S h j)
    (ExternalTensor.canonicalTensorIso k R S M N)
    (nativeTensorEndpointIso k R S M N h j e f he hf) n x

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteConnectingProducts
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]
variable (τ : FrobeniusTrace k R)

variable {S L M N : FiniteLeftModule k R}
variable (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)

theorem resolutionConnecting_product_source (n : ℤ)
    (u : CohomologyClass (S.completeCochain τ) (L.completeCochain τ) n)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] L.carrier)
    (hs : resolutionSourceAtStableEquiv τ S L n u = StableHom.classOf R _ _ s)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier)
    (t : RawCokernelAt (S.completeCochain τ) (n+1) →ₗ[R] M.carrier)
    (hA : g.comp A = s.comp (LinearMap.range ((S.completeCochain τ).d (-(n+1)) (-n)).hom).mkQ)
    (ht : f.comp t = A.comp (rawCokernelAtInclusion (S.completeCochain τ) n)) :
    resolutionSourceAtStableEquiv τ S M (n+1)
      (fullHomProduct u
        ((fullHomShiftedHomotopyEquiv k (L.completeCochain τ) (M.completeCochain τ) 1).symm
          (resolutionConnecting τ f g hf hg hex))) = StableHom.classOf R _ _ t := by
  let := τ.regular_injective
  let s' := (L.completeCochainCokernelEquiv τ).symm.toLinearMap.comp s
  let A' := (N.completeCochainCokernelEquiv τ).symm.toLinearMap.comp A
  let t' := (M.completeCochainCokernelEquiv τ).symm.toLinearMap.comp t
  have hs' : rawSourceAtStableEquiv (k := k) _ _ n
      (S.completeCochain_totallyAcyclic τ).to_chain
      (L.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex u =
        StableHom.classOf R _ _ s' := by
    apply (StableIsomorphism.ofLinearEquiv (L.completeCochainCokernelEquiv τ)).targetAddEquiv.injective
    change resolutionSourceAtStableEquiv τ S L n u = _
    rw [hs]
    simp only [StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
    apply congrArg (StableHom.classOf R _ _)
    apply LinearMap.ext
    intro z
    simp [s']
  have hA' : (resolutionCokernelMap τ g).comp A' =
      s'.comp (LinearMap.range ((S.completeCochain τ).d (-(n+1)) (-n)).hom).mkQ := by
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hA z
    simpa only [resolutionCokernelMap, A', s', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        congrArg (L.completeCochainCokernelEquiv τ).symm hz
  have ht' : (cochainCokernelMap (resolutionMap τ f)).comp t' =
      A'.comp (rawCokernelAtInclusion (S.completeCochain τ) n) := by
    rw [resolutionMap_cokernel]
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun ht z
    simpa only [resolutionCokernelMap, t', A', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        congrArg (N.completeCochainCokernelEquiv τ).symm hz
  change (StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ)).targetAddEquiv
    (rawSourceAtStableEquiv (k := k) _ _ (n+1)
      (S.completeCochain_totallyAcyclic τ).to_chain
      (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex _) = _
  dsimp only [resolutionConnecting, resolutionTriangle]
  rw [shortExactConnecting_product_source
    (hK := S.completeCochain_totallyAcyclic τ) (s := s') (hs := hs')
    (A := A') (t := t') (hA := hA') (ht := ht')]
  simp only [StableIsomorphism.targetAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  simp [t']

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteExtSourceComparison
attribute [-instance] _root_.OAI.ArExplicit.FiniteLeftModule.resolutionPairHasBiproduct _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

theorem moduleExtSourceStableEquiv_precomp_extMk (L N : ModuleCat.{u} R)
    (g : M.carrier ⟶ L) (P : ProjectiveResolution L)
    (φ : ProjectiveResolution.Hom
      (completeExtResolution (M.completeCochain_totallyAcyclic τ).to_chain) P
      ((M.fullCokernelEquiv τ).toModuleIso.hom ≫ g))
    (n : ℕ) (f : P.complex.X (n+1) ⟶ N)
    (hf : P.complex.d (n+2) (n+1) ≫ f = 0)
    (t : RawCokernelAt (M.completeCochain τ) ((n+1 : ℕ) : ℤ) →ₗ[R] N)
    (ht : ∀ z : (M.completeCochain τ).X (-((n+1 : ℕ) : ℤ)),
      t (Submodule.Quotient.mk z) = f.hom ((φ.hom.f (n+1)).hom
        ((tailTermIso (M.completeCochain τ) (n+1)).inv.hom z))) :
    moduleExtSourceStableEquiv τ M N n
      ((Ext.mk₀ g).comp (P.extMk f (n+2) rfl hf) (zero_add _)) =
      StableHom.classOf R _ _ t := by
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain N n
      ((Ext.mk₀ (M.fullCokernelEquiv τ).toModuleIso.hom).comp
        ((Ext.mk₀ g).comp (P.extMk f (n+2) rfl hf) (zero_add _)) (zero_add _))) = _
  rw [Ext.mk₀_comp_mk₀_assoc, ProjectiveResolution.mk₀_comp_extMk f (n+2) rfl hf φ,
    positiveExtStableEquiv_extMk]
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (StableHom.classOf R _ _ _) = _
  simp only [StableIsomorphism.sourceAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((M.completeCochain τ).d (-(((n+1 : ℕ) : ℤ)+1))
      (-((n+1 : ℕ) : ℤ))).hom) z
  exact (ht z).symm

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTwistExtPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "T" => ArExplicit.T k q
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tInverseTwistExt (n : ℕ) : TSelfExt q n →ₗ[k] TSelfExt q n :=
  ModuleBar.twistExtAction k T (Simple q) (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H) n

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorTwist
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tTensorInverseTwist (n : ℕ) : tTensorCoefficients q n →ₗ[k] tTensorCoefficients q n where
  toFun x p := TensorProduct.map (tInverseTwistExt q H p.val.1)
    (tInverseTwistExt q H p.val.2) (x p)
  map_add' x y := by funext p; exact map_add _ _ _
  map_smul' a x := by
    funext p
    exact (TensorProduct.map (tInverseTwistExt q H p.val.1)
      (tInverseTwistExt q H p.val.2)).map_smul a (x p)

end ArExplicit.Resolution

end

end OAI
end


