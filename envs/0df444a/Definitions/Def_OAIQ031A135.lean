-- Prove2me | Definitions.Def_OAIQ031A135
-- name    : OAIQ031A135
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:11:02.341199+00:00
-- url     : https://prove2.me/theorems/2cefbc59-e39c-4eb8-b542-a1842ac1934d
-- title:
--   Definitions bundle OAIQ031A135 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 8 definitions and 15 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.fiberEvaluationInclusion`, `OAI.ArExplicit.T.productSourceData`, `OAI.ArExplicit.T.sourceData`, `OAI.ArExplicit.T.sourceFourthEquiv`, `OAI.ArExplicit.T.sourceTwist`, `OAI.ArExplicit.T.twistedTensorBarResolution`, `OAI.ArExplicit.TwoCone.skeletonCokernelCoordinates`, `OAI.ArExplicit.TwoCone.skeletonCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTensorHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorHom.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Fibers_FiberEvaluationMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberEvaluationMap.lean), [`AuslanderReiten_Fibers_FiniteFiberComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteFiberComponents.lean), [`AuslanderReiten_Homology_ShortExactConnecting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactConnecting.lean), [`AuslanderReiten_Resolutions_FiniteResolutionEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionEvaluation.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProduct.lean), [`AuslanderReiten_Tensor_TwistedTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensorResolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A107`, `OAIQ031A118`, `OAIQ031A122` and `OAIQ031A124` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A140`, `OAIQ031A142`, `OAIQ031A143`, `OAIQ031A144` and `OAIQ031A145`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A107
import Definitions.Def_OAIQ031A118
import Definitions.Def_OAIQ031A122
import Definitions.Def_OAIQ031A124

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

theorem nativeTensorHomTransport_forward (n : ℕ)
    (x : (ExternalTensor.complex k R S (nativeResolution k R M).complex
      (nativeResolution k S N).complex).X n ⟶ ExternalTensor.canonicalTensorObject k R S M N) :
    ModuleCat.ofHom
      (X := (ExternalTensor.complex k R S (nativeResolution k R M).complex
        (nativeResolution k S N).complex).X n)
      (Y := ExternalTensor.canonicalTensorObject k R S M N)
      (((nativeTensorHomTransport k R S M N h j e f he hf).f n).hom x.hom) ≫
        (nativeTensorEndpointIso k R S M N h j e f he hf).hom =
    (nativeTensorTransport k R S M N h j e f he hf).f n ≫
      (ExternalTensor.tensorRestriction k R S h j).map x := by
  apply ExternalTensor.hom_ext k R S (nativeResolution k R M).complex (nativeResolution k S N).complex
  intro a b hab
  erw [nativeTensorTransport_inclusion_assoc, Category.assoc, ← Functor.map_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let y := (ExternalTensor.homCochainTermEquiv k R S
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (ModuleCat.of R M) (ModuleCat.of S N) n).symm x.hom
  let c := ExternalTensor.homCochainTermCoordinates k R S
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (ModuleCat.of R M) (ModuleCat.of S N) n y ⟨(a,b),hab⟩
  have hout := ExternalTensor.homCochainTermEquiv_restrict k R S
    (nativeResolution k R M).complex (nativeResolution k S N).complex
    (ModuleCat.of R M) (ModuleCat.of S N) n y ⟨(a,b),hab⟩
  dsimp only [y] at hout
  erw [LinearEquiv.apply_symm_apply] at hout
  have htrans := ExternalTensor.homTensorMap_restrict k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf) n x.hom ⟨(a,b),hab⟩
  let e₀ := nativeEndpointBase k R M h e he
  let f₀ := nativeEndpointBase k S N j f hf
  let a₀ := nativeTransportBase k R M h e he a
  let b₀ := nativeTransportBase k S N j f hf b
  let α := ((nativeHomTransport k R M h e he).f a).hom
  let β := ((nativeHomTransport k S N j f hf).f b).hom
  have hα := nativeHomTransport_apply k R M h e he a
  have hβ := nativeHomTransport_apply k S N j f hf b
  let mapped : (ExternalTensor.complex k R S (nativeResolution k R M).complex
      (nativeResolution k S N).complex).X n →ₗ[R ⊗[k] S]
      ExternalTensor.canonicalTensorObject k R S M N :=
    ((nativeTensorHomTransport k R S M N h j e f he hf).f n).hom x.hom
  let inc := ExternalTensor.inclusion k R S (nativeResolution k R M).complex
    (nativeResolution k S N).complex a b n hab
  let := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  let := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  let := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  have hp := ExternalTensor.homMap_transport k R S a₀ b₀ e₀ f₀ α β hα hβ c z
  have hpf := congrArg (TensorProduct.congr e₀ f₀) hp
  erw [LinearEquiv.apply_symm_apply] at hpf
  change (TensorProduct.congr e₀ f₀) (mapped (inc.hom z)) = _
  erw [show mapped (inc.hom z) =
      ExternalTensor.homMap k R S (TensorProduct.map α β c) z from
        LinearMap.congr_fun htrans z]
  erw [hpf]
  exact (LinearMap.congr_fun hout (TensorProduct.map a₀ b₀ z)).symm

theorem nativeTensorHomTransport_apply (n : ℕ)
    (x : (ExternalTensor.complex k R S (nativeResolution k R M).complex
      (nativeResolution k S N).complex).X n ⟶ ExternalTensor.canonicalTensorObject k R S M N) :
    ModuleCat.ofHom
      (X := (ExternalTensor.complex k R S (nativeResolution k R M).complex
        (nativeResolution k S N).complex).X n)
      (Y := ExternalTensor.canonicalTensorObject k R S M N)
      (((nativeTensorHomTransport k R S M N h j e f he hf).f n).hom x.hom) =
    ((nativeTensorTransport k R S M N h j e f he hf).f n ≫
      (ExternalTensor.tensorRestriction k R S h j).map x) ≫
        (nativeTensorEndpointIso k R S M N h j e f he hf).inv := by
  apply (cancel_mono (nativeTensorEndpointIso k R S M N h j e f he hf).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact nativeTensorHomTransport_forward k R S M N h j e f he hf n x

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem topAttaching_comm (n : ℕ) :
    (skeletonD D n).comp (topAttaching D (n + 1)) =
      (topAttaching D n).comp (-(D.d (n + 5))) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change D.d n 0 + (D.first n (D.second (n + 3) x) +
      D.second n (-D.first (n + 3) x)) = 0
    rw [map_zero, zero_add, map_neg]
    rw [show D.first n (D.second (n + 3) x) = D.second n (D.first (n + 3) x)
      from DFunLike.congr_fun (D.comparisons_comm n) x, add_neg_cancel]
  · apply Prod.ext
    · change -D.d (n + 2) (D.second (n + 3) x) = D.second (n + 2) (-D.d (n + 5) x)
      rw [map_neg]
      exact congrArg Neg.neg (DFunLike.congr_fun (D.second_comm (n + 2)) x)
    · change -D.d (n + 2) (-D.first (n + 3) x) = -D.first (n + 2) (-D.d (n + 5) x)
      rw [map_neg, map_neg, neg_neg, neg_neg]
      exact DFunLike.congr_fun (D.first_comm (n + 2)) x

def skeletonCoordinates (n : ℕ) : term D n ≃ₗ[R] (skeletonTerm D n × D.term (n + 4)) where
  toFun x := ((x.1.1, (x.1.2, x.2.1)), x.2.2)
  invFun x := ((x.1.1, x.1.2.1), (x.1.2.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem skeletonCoordinates_d (n : ℕ) :
    (skeletonCoordinates D n).toLinearMap.comp (d D n) =
      (coneBlock (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n)).comp
        (skeletonCoordinates D (n + 1)).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩
  simp [skeletonCoordinates, d, firstD, secondOnFirst, coneBlock_apply, skeletonD,
    middleD, attachingRow, topAttaching, add_assoc]
  abel

def skeletonCokernelCoordinates (n : ℕ) : Cokernel D n ≃ₗ[R]
    ConeCokernel.Middle (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n) :=
  cokernelLinearCongr _ _ (skeletonCoordinates D (n + 1)) (skeletonCoordinates D n)
    (skeletonCoordinates_d D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberEvaluationMap
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier)

def fiberEvaluationInclusion : (evaluated X (fiber U₁ U₂ Y g₁ g₂)).carrier →ₗ[R]
    (evaluated X (fiberSource U₁ U₂ Y)).carrier :=
  evaluationMap X (M := fiber U₁ U₂ Y g₁ g₂) (N := fiberSource U₁ U₂ Y)
    (fiberInclusion U₁ U₂ Y g₁ g₂).hom

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteFiberComponents
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k S : Type u} [Field k] [Ring S] [Algebra k S] [Module.Finite k S]
variable (U V Y : FiniteLeftModule k S)

section Evaluation
variable {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y₀ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

theorem middlePairMap_inl :
    (middlePairMap X U₁ U₂ Y₀).comp
      (evaluationMap X (fiberSourceInl U₁ U₂ Y₀)) =
        LinearMap.inl R (evaluated X U₁).carrier (evaluated X U₂).carrier := by
  apply BalancedTensor.leftHom_ext (k := k)
  intro m x
  change (BalancedTensor.tmul (k := k) (R := R) m x,
    BalancedTensor.tmul (k := k) (R := R) (0 : EnvelopingBimodule k R U₂.carrier) x) =
      (BalancedTensor.tmul (k := k) (R := R) m x, 0)
  rw [BalancedTensor.zero_tmul]

theorem middlePairMap_inr :
    (middlePairMap X U₁ U₂ Y₀).comp
      (evaluationMap X (fiberSourceInr U₁ U₂ Y₀)) =
        LinearMap.inr R (evaluated X U₁).carrier (evaluated X U₂).carrier := by
  apply BalancedTensor.leftHom_ext (k := k)
  intro m x
  change (BalancedTensor.tmul (k := k) (R := R) (0 : EnvelopingBimodule k R U₁.carrier) x,
    BalancedTensor.tmul (k := k) (R := R) m x) =
      (0, BalancedTensor.tmul (k := k) (R := R) m x)
  rw [BalancedTensor.zero_tmul]

end Evaluation
end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactConnecting
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)
variable (κ : H ⟶ mappingCone φ)
variable (hκ : (HomotopyCategory.quotient _ _).map κ =
  (shortExactConeIso φ p he hF hG hH hi hp).inv)

include hκ in

theorem shortExactConeKernel_stable
    (A : H.X 0 →ₗ[R] CochainCokernel G) (t : RawSyzygy H →ₗ[R] CochainCokernel F)
    (hA : p.comp A = (LinearMap.range (H.d (-1) 0).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawSyzygyInclusion H)) :
    StableHom.classOf R _ _ (coneLiftKernel φ κ hi) = StableHom.classOf R _ _ t := by
  let := hH.finite 0
  let := hH.projective 0
  apply stable_connecting_congr (rawSyzygyInclusion H)
    (LinearMap.range (H.d (-1) 0).hom).mkQ (rawSyzygyInclusion_cover H)
    (cochainCokernelMap φ) p hi hp (LinearMap.exact_iff.mp he).symm
    ((rawConeQuotient φ p he).comp (cochainCokernelMap κ)) LinearMap.id
    (coneLiftMiddle φ κ) A (coneLiftKernel φ κ hi) t
  · exact coneLiftMiddle_square φ κ p he
  · simpa only [LinearMap.id_comp] using hA
  · exact coneLiftKernel_square φ κ hi
  · exact ht
  · exact shortExactConeInverse_stable_identity φ p he hF hG hH hi hp κ hκ

include hκ in

theorem shortExactConnecting_cone_class :
    fullHomShiftedHomotopyEquiv k H F 1
      (CohomologyClass.mk (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ))) =
      (shortExactTriangle φ p he hF hG hH hi hp).mor₃ := by
  have hn : -(mappingCone.fst φ) = mappingCone.fst φ := by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul k, show (2:k)=0 from CharP.cast_eq_zero k 2, zero_smul]
  rw [fullHomShiftedHomotopyEquiv_mk, coneProjectionCocycle_hom,
    Functor.map_comp, Category.assoc, hκ]
  change _ = (shortExactConeIso φ p he hF hG hH hi hp).inv ≫
    ((HomotopyCategory.quotient _ _).map
      (Cocycle.equivHomShift.symm (-(mappingCone.fst φ))) ≫
      ((HomotopyCategory.quotient _ _).commShiftIso (1:ℤ)).hom.app F)
  rw [hn]
  rfl

include k hκ in

theorem shortExactConnecting_source
    (A : H.X 0 →ₗ[R] CochainCokernel G) (t : RawSyzygy H →ₗ[R] CochainCokernel F)
    (hA : p.comp A = (LinearMap.range (H.d (-1) 0).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawSyzygyInclusion H)) :
    StableHom.classOf R _ _
      (rawSourceCocycleMap (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ))) =
        StableHom.classOf R _ _ t := by
  rw [rawSourceCocycleMap_cone (k := k) φ κ hi]
  exact shortExactConeKernel_stable φ p he hF hG hH hi hp κ hκ A t hA ht

theorem shortExactConnecting_source_equiv
    (A : H.X 0 →ₗ[R] CochainCokernel G) (t : RawSyzygy H →ₗ[R] CochainCokernel F)
    (hA : p.comp A = (LinearMap.range (H.d (-1) 0).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawSyzygyInclusion H)) :
    rawSourceStableEquiv (k := k) H F hH.to_chain hF.to_chain.toExactProjectiveComplex
      ((fullHomShiftedHomotopyEquiv k H F 1).symm
        (shortExactTriangle φ p he hF hG hH hi hp).mor₃) = StableHom.classOf R _ _ t := by
  obtain ⟨κ, hκ⟩ := Functor.map_surjective (HomotopyCategory.quotient _ _)
    (shortExactConeIso φ p he hF hG hH hi hp).inv
  rw [← shortExactConnecting_cone_class (k := k) φ p he hF hG hH hi hp κ hκ,
    LinearEquiv.symm_apply_apply, rawSourceStableEquiv_mk]
  exact shortExactConnecting_source (k := k) φ p he hF hG hH hi hp κ hκ A t hA ht

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionEvaluation
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R) (τe : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ))
variable (τ : FrobeniusTrace k R)
variable {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}

@[simp] theorem evaluationResolutionMap_id :
    evaluationResolutionMap X τe τ (𝟙 ((HomotopyCategory.quotient _ _).obj (M.completeCochain τe))) = 𝟙 _ := by
  rw [← resolutionMap_id (M := M) τe, evaluationResolutionMap_lift,
    evaluationMap_id, resolutionMap_id]

theorem evaluationResolutionMap_triangle
    (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
    (g : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
    (t : (HomotopyCategory.quotient _ _).obj (N.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (P.completeCochain τe))
    (h : (HomotopyCategory.quotient _ _).map (resolutionMap τe f) ≫ t =
      (HomotopyCategory.quotient _ _).map (resolutionMap τe g)) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X f)) ≫
        evaluationResolutionMap X τe τ t =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X g)) := by
  have he := congrArg (evaluationResolutionMap X τe τ) h
  erw [evaluationResolutionMap_comp X τe τ (M := M) (N := N) (P := P)
      ((HomotopyCategory.quotient _ _).map (resolutionMap τe f)) t,
    evaluationResolutionMap_lift X τe τ (M := M) (N := N) f,
    evaluationResolutionMap_lift X τe τ (M := M) (N := P) g] at he
  exact he

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionProduct
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
variable {M N : FiniteLeftModule k R}

theorem homotopyResolutionMap_zero :
    (Q).map (resolutionMap τ (0 : M.carrier →ₗ[R] N.carrier)) = 0 := by
  apply (resolutionHomotopyEquiv τ M N).injective
  rw [map_zero, resolutionHomotopyEquiv_map]
  exact map_zero (StableHom.classOf R M.carrier N.carrier)

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "Q₀" => productTwistedTotal q H

def sourceTwist : (R ⊗[k] R) ≃ₐ[k] (R ⊗[k] R) :=
  Algebra.TensorProduct.congr (TrivialExtension.twist H) (TrivialExtension.twist H)

def twistedTensorBarResolution : ProjectiveResolution
    (ExternalTensor.moduleObject k Te Te
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0)
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0)) := by
  letI (n : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).complex.X n) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) n
  exact ExternalTensor.projectiveResolution k Te Te
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))

abbrev productSourceData : TwoCone.Data (Te ⊗[k] Te) where
  term := (Q₀).X
  d n := ((Q₀).d (n+1) n).hom
  first _ := 0
  second _ := 0
  square n := congrArg ModuleCat.Hom.hom ((Q₀).d_comp_d (n+2) (n+1) n)
  first_comm _ := by simp
  second_comm _ := by simp
  comparisons_comm _ := by simp

abbrev sourceData := (productSourceData q H).restrict
  (ExternalTensor.envelopingEquiv k R R).symm.toRingHom

def sourceFourthEquiv : fourthSyzygy q H ≃ₗ[ExternalTensor.EnvelopingProduct k R R]
    TwoCone.BaseCokernel (sourceData q H) 4 := LinearEquiv.refl _ _

theorem source_product_finite (n : ℕ) :
    Module.Finite (Te ⊗[k] Te) ((productSourceData q H).term n) := by
  let (i : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)).X i) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) i
  exact ExternalTensor.term_finite k Te Te
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)) n

theorem source_finite (n : ℕ) :
    Module.Finite (ExternalTensor.EnvelopingProduct k R R) ((sourceData q H).term n) := by
  let := source_product_finite q H n
  exact Module.Finite.of_surjective
    (ExternalTensor.envelopingSemilinear k R R ((productSourceData q H).term n)).toLinearMap
    (ExternalTensor.envelopingSemilinear k R R ((productSourceData q H).term n)).surjective

end ArExplicit.T

end

end OAI
end


