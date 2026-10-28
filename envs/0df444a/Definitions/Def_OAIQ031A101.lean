-- Prove2me | Definitions.Def_OAIQ031A101
-- name    : OAIQ031A101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:36:16.944291+00:00
-- url     : https://prove2.me/theorems/c0e93f29-5491-41cb-8ffd-2991d0e8ad8c
-- title:
--   Definitions bundle OAIQ031A101 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 3 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.ModuleBar.homTransport`, `OAI.ArExplicit.ModuleBar.nativeEndpointBase`, `OAI.ArExplicit.ModuleBar.nativeTensorEndpointIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarHomTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarHomTwist.lean), [`AuslanderReiten_Bar_ModuleBarNativeTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNativeTransport.lean), [`AuslanderReiten_Bar_ModuleBarTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorTransport.lean), [`AuslanderReiten_Cones_MappingConeNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeNaturality.lean), [`AuslanderReiten_Ext_ExternalEvaluationPure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationPure.lean), [`AuslanderReiten_HomComplex_NativeHomExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/NativeHomExtAction.lean), [`AuslanderReiten_Tensor_ExternalTensorHomTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomTransport.lean), [`AuslanderReiten_Tensor_ExternalTensorResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorResolution.lean), [`AuslanderReiten_Tensor_ExternalTensorZeroEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorZeroEquiv.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A080`, `OAIQ031A085`, `OAIQ031A087` and `OAIQ031A088` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A112`, `OAIQ031A114` and `OAIQ031A115`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A080
import Definitions.Def_OAIQ031A085
import Definitions.Def_OAIQ031A087
import Definitions.Def_OAIQ031A088

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

def homTransport : ExternalTensor.homCochain k R (complex k R M) M ⟶
    ExternalTensor.homCochain k R (complex k R M) M where
  f n := ModuleCat.ofHom (transportHom k R M h e he (n+1))
  comm' i j hij := by
    have hj : i+1=j := hij
    subst j
    rw [ExternalTensor.homCochain_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (transportHom_differential k R M h e he (i+1) f).symm

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

def nativeEndpointBase :
    letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
    ModuleCat.of R M ≃ₗ[k] ModuleCat.of R M := by
  letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  exact {
    toFun := fun x => e x
    invFun := fun x => e.symm x
    left_inv := fun x => e.symm_apply_apply x
    right_inv := fun x => e.apply_symm_apply x
    map_add' := fun x y => e.map_add x y
    map_smul' := by
      intro a x
      change e ((algebraMap k R a) • x) = (algebraMap k R a) • e x
      rw [he, h.commutes] }

omit [IsScalarTower k R M] [CharP k 2] in
theorem nativeEndpointBase_smul (a : R) (x : ModuleCat.of R M) :
    nativeEndpointBase k R M h e he (a • x) = h a • nativeEndpointBase k R M h e he x :=
  he a x

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]

theorem differential_exact (n : ℕ) :
    Function.Exact ((complex k A B P.complex Q.complex).d (n+2) (n+1)).hom
      ((complex k A B P.complex Q.complex).d (n+1) n).hom := by
  have h := (projectiveResolution k A B P Q).exact_succ n
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h

end ArExplicit.ExternalTensor

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

def nativeTensorEndpointIso : ExternalTensor.canonicalTensorObject k R S M N ≅
    (ExternalTensor.tensorRestriction k R S h j).obj
      (ExternalTensor.canonicalTensorObject k R S M N) := by
  let e₀ := nativeEndpointBase k R M h e he
  let f₀ := nativeEndpointBase k S N j f hf
  have he₀ := nativeEndpointBase_smul k R M h e he
  have hf₀ := nativeEndpointBase_smul k S N j f hf
  letI := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI := moduleCatBaseModule (k := k) (R := S) (ModuleCat.of S N)
  letI := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  letI := moduleCatBaseTower (k := k) (R := S) (ModuleCat.of S N)
  exact (ExternalTensor.tensorSemilinearEquiv k R S h j e₀ f₀ he₀ hf₀).toModuleIso

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {F₁ G₁ F₂ G₂ : CochainComplex (ModuleCat.{u} R) ℤ}
variable {φ₁ : F₁ ⟶ G₁} {φ₂ : F₂ ⟶ G₂} {a : F₁ ⟶ F₂} {b : G₁ ⟶ G₂}
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (hH : H.hom 1 0 = 0)

variable {L₁ L₂ : Type u} [AddCommGroup L₁] [Module R L₁]
  [AddCommGroup L₂] [Module R L₂]
variable (p₁ : CochainCokernel G₁ →ₗ[R] L₁) (p₂ : CochainCokernel G₂ →ₗ[R] L₂)
variable (hex₁ : Function.Exact (cochainCokernelMap φ₁) p₁)
  (hex₂ : Function.Exact (cochainCokernelMap φ₂) p₂)
variable (c : L₁ →ₗ[R] L₂)

include hH in

theorem rawConeQuotient_natural
    (hc : p₂.comp (cochainCokernelMap b) = c.comp p₁) :
    (rawConeQuotient φ₂ p₂ hex₂).comp (cochainCokernelMap (mappingCone.mapOfHomotopy H)) =
      c.comp (rawConeQuotient φ₁ p₁ hex₁) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range ((mappingCone φ₁).d (-1) 0).hom).mkQ_surjective x
  change p₂ (Submodule.Quotient.mk
    (((mappingCone.snd φ₂).v 0 0 (add_zero 0)).hom (((mappingCone.mapOfHomotopy H).f 0).hom x))) =
      c (p₁ (Submodule.Quotient.mk (((mappingCone.snd φ₁).v 0 0 (add_zero 0)).hom x)))
  have hs := congrArg (fun f : (mappingCone φ₁).X 0 ⟶ G₂.X 0 => f.hom x)
    (mappingCone_map_snd_zero H hH)
  change ((mappingCone.snd φ₂).v 0 0 (add_zero 0)).hom
      (((mappingCone.mapOfHomotopy H).f 0).hom x) =
    (b.f 0).hom (((mappingCone.snd φ₁).v 0 0 (add_zero 0)).hom x) at hs
  rw [hs]
  exact DFunLike.congr_fun hc (Submodule.Quotient.mk
    (((mappingCone.snd φ₁).v 0 0 (add_zero 0)).hom x))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationPure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B) (Z : ModuleCat.{u} (A ⊗[k] B))
variable (f : (EnvelopingBimodule.evaluationFunctor k A X).obj M ⟶ U)
  (g : (EnvelopingBimodule.evaluationFunctor k B Y).obj N ⟶ V)
  (h : ExternalTensor.moduleObject k A B U V ⟶ Z)

theorem postShuffle_pure (a : EnvelopingBimodule k A M)
    (b : EnvelopingBimodule k B N) (x : X) (y : Y) :
    ((shuffle k A B M N X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B f g ≫ h)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      h (ExternalTensor.canonicalTmul k A B U V
        (f (BalancedTensor.tmul a x)) (g (BalancedTensor.tmul b y))) := by
  change h (ExternalTensor.mapHom k A B f g (shuffle k A B M N X Y
    (BalancedTensor.tmul
      ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))))) = _
  rw [shuffle_pure]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_NativeHomExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]
variable (H : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)

theorem nativeHomEnd_closed (n : ℕ) (f : P.complex.X n →ₗ[R] Y)
    (hf : f.comp (P.complex.d (n+1) n).hom = 0) :
    (show P.complex.X n →ₗ[R] Y from (H.f n).hom f).comp
      (P.complex.d (n+1) n).hom = 0 := by
  have hh := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (H.comm n (n+1))) f
  change ((homCochain k R P.complex Y).d n (n+1)).hom ((H.f n).hom f) =
    (H.f (n+1)).hom (((homCochain k R P.complex Y).d n (n+1)).hom f) at hh
  rw [homCochain_d] at hh
  change (show P.complex.X n →ₗ[R] Y from (H.f n).hom f).comp
      (P.complex.d (n+1) n).hom =
    (H.f (n+1)).hom (f.comp (P.complex.d (n+1) n).hom) at hh
  rw [hf] at hh
  exact hh.trans (H.f (n+1)).hom.map_zero

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (f : homCochain k A P.complex U ⟶ homCochain k A P.complex U)
variable (g : homCochain k B Q.complex V ⟶ homCochain k B Q.complex V)
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

theorem homCochainTermCoordinates_natural (n : ℕ)
    (x : (homCochainTotal k A B P.complex Q.complex U V).X n) (p : Diagonal n) :
    homCochainTermCoordinates k A B P.complex Q.complex U V n
        (((mapBifunctorMap f g T (.up ℕ)).f n).hom x) p =
      TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom
        (homCochainTermCoordinates k A B P.complex Q.complex U V n x p) := by
  exact congrFun (VectorCochain.totalTermCoordinates_natural k f g n x) p

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorZeroEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

theorem zeroEquiv_symm (x : moduleObject k A B (P.X 0) (Q.X 0)) :
    (zeroEquiv k A B P Q).symm x = inclusion k A B P Q 0 0 0 rfl x := by
  change cubicInsert k A B P Q 0 ⟨(0,0),rfl⟩ x = _
  exact (LinearMap.congr_fun (inclusion_eq_directSum k A B P Q 0 0 0 rfl) x).symm

end ArExplicit.ExternalTensor

end

end OAI
end


