-- Prove2me | Definitions.Def_OAIQ031A124
-- name    : OAIQ031A124
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:58:43.48128+00:00
-- url     : https://prove2.me/theorems/09809327-bc3a-4c96-96b2-c78d1651ab14
-- title:
--   Definitions bundle OAIQ031A124 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 12 definitions and 16 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.evaluatedFiberTriangle`, `OAI.ArExplicit.FiniteLeftModule.evaluatedMiddleStableIso`, `OAI.ArExplicit.FiniteLeftModule.evaluatedPairEquiv`, `OAI.ArExplicit.FiniteLeftModule.evaluationResolutionMap`, `OAI.ArExplicit.FiniteLeftModule.fiberPairProjection`, `OAI.ArExplicit.FiniteLeftModule.fiberPairStableIso`, `OAI.ArExplicit.FiniteLeftModule.fiberReassociate`, `OAI.ArExplicit.FiniteLeftModule.fiberSourceInl`, `OAI.ArExplicit.FiniteLeftModule.fiberSourceInr`, `OAI.ArExplicit.FiniteLeftModule.middlePairMap`, `OAI.ArExplicit.FiniteLeftModule.pairFst`, `OAI.ArExplicit.FiniteLeftModule.pairInl`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Fibers_FiniteEvaluatedFiber`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteEvaluatedFiber.lean), [`AuslanderReiten_Fibers_FiniteFiberComponents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteFiberComponents.lean), [`AuslanderReiten_Homology_ShortExactNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactNaturality.lean), [`AuslanderReiten_Modules_FiniteModuleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleEvaluation.lean), [`AuslanderReiten_Modules_FiniteModuleNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleNaturality.lean), [`AuslanderReiten_Resolutions_FiniteResolutionEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionEvaluation.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProduct.lean), [`AuslanderReiten_Tensor_ExternalTensorHomTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomTransport.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A105`, `OAIQ031A110`, `OAIQ031A111`, `OAIQ031A112` and `OAIQ031A113` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A129`, `OAIQ031A131`, `OAIQ031A134` and `OAIQ031A135`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A105
import Definitions.Def_OAIQ031A110
import Definitions.Def_OAIQ031A111
import Definitions.Def_OAIQ031A112
import Definitions.Def_OAIQ031A113

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

@[simp]
theorem topAttaching_apply (n : ℕ) (x : D.term (n + 5)) :
    topAttaching D n x = (0, (D.second (n + 2) x, -D.first (n + 2) x)) := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactNaturality
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

variable [Module.Injective R R]
variable {F G K : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel K)
variable (hex : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G)
variable (hK : TotallyAcyclicCochain K)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

variable {F₁ G₁ K₁ F₂ G₂ K₂ : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ₁ : F₁ ⟶ G₁) (φ₂ : F₂ ⟶ G₂)
variable (p₁ : CochainCokernel G₁ →ₗ[R] CochainCokernel K₁)
  (p₂ : CochainCokernel G₂ →ₗ[R] CochainCokernel K₂)
variable (hex₁ : Function.Exact (cochainCokernelMap φ₁) p₁)
  (hex₂ : Function.Exact (cochainCokernelMap φ₂) p₂)
variable (hF₁ : TotallyAcyclicCochain F₁) (hG₁ : TotallyAcyclicCochain G₁)
  (hK₁ : TotallyAcyclicCochain K₁)
variable (hF₂ : TotallyAcyclicCochain F₂) (hG₂ : TotallyAcyclicCochain G₂)
  (hK₂ : TotallyAcyclicCochain K₂)
variable (hi₁ : Function.Injective (cochainCokernelMap φ₁)) (hp₁ : Function.Surjective p₁)
  (hi₂ : Function.Injective (cochainCokernelMap φ₂)) (hp₂ : Function.Surjective p₂)
variable (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂) (c : K₁ ⟶ K₂)
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (hH : H.hom 1 0 = 0)
variable (hc : p₂.comp (cochainCokernelMap b) = (cochainCokernelMap c).comp p₁)

include hH hc in

theorem shortExactConeIso_natural :
    (HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H) ≫
        (shortExactConeIso φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂).hom =
      (shortExactConeIso φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁).hom ≫
        (HomotopyCategory.quotient _ _).map c := by
  apply (cochainHomotopyRawEquiv (mappingCone_totallyAcyclic φ₁ hF₁ hG₁).to_chain
    hK₂.to_chain.toExactProjectiveComplex).injective
  have hl := cochainHomotopyRawEquiv_comp_class
    (mappingCone_totallyAcyclic φ₁ hF₁ hG₁) (mappingCone_totallyAcyclic φ₂ hF₂ hG₂)
    hK₂.toExactProjectiveCochain
    ((HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H))
    (shortExactConeIso φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂).hom
    (cochainCokernelMap (mappingCone.mapOfHomotopy H)) (rawConeQuotient φ₂ p₂ hex₂)
    (cochainHomotopyRawEquiv_map _ _ _) (shortExactConeIso_raw_hom φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂)
  have hr := cochainHomotopyRawEquiv_comp_class
    (mappingCone_totallyAcyclic φ₁ hF₁ hG₁) hK₁ hK₂.toExactProjectiveCochain
    (shortExactConeIso φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁).hom
    ((HomotopyCategory.quotient _ _).map c)
    (rawConeQuotient φ₁ p₁ hex₁) (cochainCokernelMap c)
    (shortExactConeIso_raw_hom φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁) (cochainHomotopyRawEquiv_map _ _ _)
  exact hl.trans ((congrArg (StableHom.classOf R _ _)
    (rawConeQuotient_natural H hH p₁ p₂ hex₁ hex₂ (cochainCokernelMap c) hc)).trans hr.symm)

include hc in

theorem shortExactTriangle_connecting_natural
    (hab : cochainCokernelMap (φ₁ ≫ b) = cochainCokernelMap (a ≫ φ₂)) :
    (HomotopyCategory.quotient _ _).map c ≫
        (shortExactTriangle φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂).mor₃ =
      (shortExactTriangle φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁).mor₃ ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map a) := by
  obtain ⟨H, hH⟩ := cochain_homotopy_of_cokernel_eq hF₁ hG₂.toExactProjectiveCochain
    (φ₁ ≫ b) (a ≫ φ₂) hab
  let E₁ := shortExactConeIso φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁
  let E₂ := shortExactConeIso φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂
  have hn : (HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H) ≫ E₂.hom =
      E₁.hom ≫ (HomotopyCategory.quotient _ _).map c :=
    shortExactConeIso_natural φ₁ φ₂ p₁ p₂ hex₁ hex₂ hF₁ hG₁ hK₁ hF₂ hG₂ hK₂
      hi₁ hp₁ hi₂ hp₂ a b c H hH hc
  have hi : (HomotopyCategory.quotient _ _).map c ≫ E₂.inv =
      E₁.inv ≫ (HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H) := by
    apply (cancel_mono E₂.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp
  change (HomotopyCategory.quotient _ _).map c ≫
      (E₂.inv ≫ (mappingCone.triangleh φ₂).mor₃) =
    (E₁.inv ≫ (mappingCone.triangleh φ₁).mor₃) ≫ _
  erw [← Category.assoc, hi, Category.assoc,
    ← (mappingCone.trianglehMapOfHomotopy H).comm₃]
  exact (Category.assoc E₁.inv (mappingCone.triangleh φ₁).mor₃
    ((CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
      ((HomotopyCategory.quotient _ _).map a))).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.FiniteLeftModule
open CompleteComparison

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N L : FiniteLeftModule k R}

variable (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)

variable {M₁ N₁ L₁ M₂ N₂ L₂ : FiniteLeftModule k R}
variable (f₁ : M₁.carrier →ₗ[R] N₁.carrier) (g₁ : N₁.carrier →ₗ[R] L₁.carrier)
  (f₂ : M₂.carrier →ₗ[R] N₂.carrier) (g₂ : N₂.carrier →ₗ[R] L₂.carrier)
variable (hf₁ : Function.Injective f₁) (hg₁ : Function.Surjective g₁) (hex₁ : Function.Exact f₁ g₁)
  (hf₂ : Function.Injective f₂) (hg₂ : Function.Surjective g₂) (hex₂ : Function.Exact f₂ g₂)
variable (a : M₁.carrier →ₗ[R] M₂.carrier) (b : N₁.carrier →ₗ[R] N₂.carrier)
  (c : L₁.carrier →ₗ[R] L₂.carrier)

theorem resolutionConnecting_natural
    (hab : b.comp f₁ = f₂.comp a) (hbc : g₂.comp b = c.comp g₁) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ c) ≫
        resolutionConnecting τ f₂ g₂ hf₂ hg₂ hex₂ =
      resolutionConnecting τ f₁ g₁ hf₁ hg₁ hex₁ ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (resolutionMap τ a)) := by
  let := τ.regular_injective
  apply shortExactTriangle_connecting_natural
  · rw [resolutionMap_cokernel, ← resolutionCokernelMap_comp,
      resolutionMap_cokernel, ← resolutionCokernelMap_comp, hbc]
  · rw [cochainCokernelMap_comp, cochainCokernelMap_comp,
      resolutionMap_cokernel, resolutionMap_cokernel, resolutionMap_cokernel, resolutionMap_cokernel,
      ← resolutionCokernelMap_comp, ← resolutionCokernelMap_comp, hab]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleEvaluation
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct

namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

variable {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}

variable (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
  (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P.carrier)]

variable (τ : FrobeniusTrace k R)

section Naturality
variable {M₁ N₁ P₁ M₂ N₂ P₂ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}
variable (f₁ : M₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N₁.carrier)
  (g₁ : N₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P₁.carrier)
  (f₂ : M₂.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N₂.carrier)
  (g₂ : N₂.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P₂.carrier)
variable (hf₁ : Function.Injective f₁) (hg₁ : Function.Surjective g₁) (he₁ : Function.Exact f₁ g₁)
  (hf₂ : Function.Injective f₂) (hg₂ : Function.Surjective g₂) (he₂ : Function.Exact f₂ g₂)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P₁.carrier)]
  [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P₂.carrier)]
variable (a : M₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] M₂.carrier)
  (b : N₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N₂.carrier)
  (c : P₁.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P₂.carrier)

theorem evaluationConnecting_natural
    (hab : b.comp f₁ = f₂.comp a) (hbc : g₂.comp b = c.comp g₁) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X c)) ≫
      (evaluationTriangle X f₂ g₂ hf₂ hg₂ he₂ τ).mor₃ =
    (evaluationTriangle X f₁ g₁ hf₁ hg₁ he₁ τ).mor₃ ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
        ((HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X a))) := by
  apply resolutionConnecting_natural
  · rw [← evaluationMap_comp, ← evaluationMap_comp, hab]
  · rw [← evaluationMap_comp, ← evaluationMap_comp, hbc]
end Naturality

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteEvaluatedFiber
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

variable (U V Y : FiniteLeftModule k S)

def fiberReassociate : (fiberSource U V Y).carrier ≃ₗ[S]
    ((pairModule U V).carrier × Y.canonicalFreeCover.carrier) where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun z := (z.1.1, z.1.2, z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fiberPairProjection : (fiberSource U V Y).carrier →ₗ[S] (pairModule U V).carrier :=
  (LinearMap.fst S U.carrier (V.carrier × Y.canonicalFreeCover.carrier)).prod
    ((LinearMap.fst S V.carrier Y.canonicalFreeCover.carrier).comp
      (LinearMap.snd S U.carrier (V.carrier × Y.canonicalFreeCover.carrier)))

def fiberPairStableIso : StableIsomorphism S (fiberSource U V Y).carrier (pairModule U V).carrier := by
  letI := Y.canonicalFreeCover_projective
  letI := Y.canonicalFreeCover_finite
  exact (StableIsomorphism.ofLinearEquiv (fiberReassociate U V Y)).trans
    (StableIsomorphism.dropRight (R := S))

@[simp] theorem fiberPairStableIso_hom : (fiberPairStableIso U V Y).hom =
    StableHom.classOf S _ _ (fiberPairProjection U V Y) := by
  change StableHom.comp (StableHom.classOf S _ _ (LinearMap.fst S _ _))
    (StableHom.classOf S _ _ (fiberReassociate U V Y).toLinearMap) = _
  rw [StableHom.comp_classOf]
  rfl

section Evaluation
variable {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y₀ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

def evaluatedPairEquiv : (evaluated X (pairModule U₁ U₂)).carrier ≃ₗ[R]
    ((evaluated X U₁).carrier × (evaluated X U₂).carrier) :=
  EnvelopingBimodule.tensorProdEquiv U₁.carrier U₂.carrier X.carrier

def middlePairMap : (evaluated X (fiberSource U₁ U₂ Y₀)).carrier →ₗ[R]
    ((evaluated X U₁).carrier × (evaluated X U₂).carrier) :=
  (evaluatedPairEquiv X U₁ U₂).toLinearMap.comp
    (evaluationMap X (fiberPairProjection U₁ U₂ Y₀))

def evaluatedMiddleStableIso : StableIsomorphism R
    (evaluated X (fiberSource U₁ U₂ Y₀)).carrier
    ((evaluated X U₁).carrier × (evaluated X U₂).carrier) :=
  (evaluationStableIso X (fiberPairStableIso U₁ U₂ Y₀)).trans
    (StableIsomorphism.ofLinearEquiv (evaluatedPairEquiv X U₁ U₂))

@[simp] theorem evaluatedMiddleStableIso_hom : (evaluatedMiddleStableIso X U₁ U₂ Y₀).hom =
    StableHom.classOf R _ _ (middlePairMap X U₁ U₂ Y₀) := by
  change StableHom.comp (StableHom.classOf R _ _ (evaluatedPairEquiv X U₁ U₂).toLinearMap)
    (EnvelopingBimodule.stableEvaluation X.carrier (fiberPairStableIso U₁ U₂ Y₀).hom) = _
  rw [fiberPairStableIso_hom, EnvelopingBimodule.stableEvaluation_classOf]
  erw [StableHom.comp_classOf]

variable (g₁ : U₁.carrier ⟶ Y₀.carrier) (g₂ : U₂.carrier ⟶ Y₀.carrier)

theorem fiberFunctionExact : Function.Exact
    (fiberInclusion U₁ U₂ Y₀ g₁ g₂).hom (fiberMap U₁ U₂ Y₀ g₁ g₂).hom := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R Y₀.carrier)]

def evaluatedFiberTriangle (τ : FrobeniusTrace k R) :
    Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  evaluationTriangle X (fiberInclusion U₁ U₂ Y₀ g₁ g₂).hom (fiberMap U₁ U₂ Y₀ g₁ g₂).hom
    Subtype.val_injective (fiberMap_surjective U₁ U₂ Y₀ g₁ g₂)
    (fiberFunctionExact U₁ U₂ Y₀ g₁ g₂) τ

 theorem evaluatedFiberTriangle_distinguished (τ : FrobeniusTrace k R) :
    evaluatedFiberTriangle X U₁ U₂ Y₀ g₁ g₂ τ ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  evaluationTriangle_distinguished _ _ _ _ _ _ _

end Evaluation
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

def fiberSourceInl : U.carrier →ₗ[S] (fiberSource U V Y).carrier :=
  (LinearMap.id : U.carrier →ₗ[S] U.carrier).prod (0 : U.carrier →ₗ[S] V.carrier × Y.canonicalFreeCover.carrier)

def fiberSourceInr : V.carrier →ₗ[S] (fiberSource U V Y).carrier :=
  (0 : V.carrier →ₗ[S] U.carrier).prod
    ((LinearMap.id : V.carrier →ₗ[S] V.carrier).prod (0 : V.carrier →ₗ[S] Y.canonicalFreeCover.carrier))

theorem fiberMap_inl (g : U.carrier ⟶ Y.carrier) (h : V.carrier ⟶ Y.carrier) :
    (fiberMap U V Y g h).hom.comp (fiberSourceInl U V Y) = g.hom := by
  ext x
  change g.hom x + (h.hom 0 + Y.canonicalFreeCoverMap.hom 0) = g.hom x
  simp

theorem fiberMap_inr (g : U.carrier ⟶ Y.carrier) (h : V.carrier ⟶ Y.carrier) :
    (fiberMap U V Y g h).hom.comp (fiberSourceInr U V Y) = h.hom := by
  ext x
  change g.hom 0 + (h.hom x + Y.canonicalFreeCoverMap.hom 0) = h.hom x
  simp

section Evaluation
variable {R : Type u} [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (U₁ U₂ Y₀ : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

theorem evaluatedFiberMap_inl (g : U₁.carrier ⟶ Y₀.carrier) (h : U₂.carrier ⟶ Y₀.carrier) :
    (evaluationMap X (fiberMap U₁ U₂ Y₀ g h).hom).comp
      (evaluationMap X (fiberSourceInl U₁ U₂ Y₀)) = evaluationMap X g.hom := by
  rw [← evaluationMap_comp, fiberMap_inl]

theorem evaluatedFiberMap_inr (g : U₁.carrier ⟶ Y₀.carrier) (h : U₂.carrier ⟶ Y₀.carrier) :
    (evaluationMap X (fiberMap U₁ U₂ Y₀ g h).hom).comp
      (evaluationMap X (fiberSourceInr U₁ U₂ Y₀)) = evaluationMap X h.hom := by
  rw [← evaluationMap_comp, fiberMap_inr]

end Evaluation
end ArExplicit.FiniteLeftModule

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

def evaluationResolutionMap
    (f : (HomotopyCategory.quotient _ _).obj (M.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τe)) :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj ((X.evaluated N).completeCochain τ) :=
  (resolutionHomotopyEquiv τ (X.evaluated M) (X.evaluated N)).symm
    (EnvelopingBimodule.stableEvaluation X.carrier (resolutionHomotopyEquiv τe M N f))

@[simp] theorem evaluationResolutionMap_lift (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier) :
    evaluationResolutionMap X τe τ
      ((HomotopyCategory.quotient _ _).map (resolutionMap τe f)) =
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (evaluationMap X f)) := by
  apply (resolutionHomotopyEquiv τ (X.evaluated M) (X.evaluated N)).injective
  simp only [evaluationResolutionMap, resolutionHomotopyEquiv_map]
  erw [AddEquiv.apply_symm_apply]
  rfl

theorem evaluationResolutionMap_comp
    (f : (HomotopyCategory.quotient _ _).obj (M.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τe))
    (g : (HomotopyCategory.quotient _ _).obj (N.completeCochain τe) ⟶
      (HomotopyCategory.quotient _ _).obj (P.completeCochain τe)) :
    evaluationResolutionMap X τe τ (f ≫ g) =
      evaluationResolutionMap X τe τ f ≫ evaluationResolutionMap X τe τ g := by
  obtain ⟨f, rfl⟩ := resolutionMap_surjective τe f
  obtain ⟨g, rfl⟩ := resolutionMap_surjective τe g
  rw [← resolutionMap_comp, evaluationResolutionMap_lift,
    evaluationResolutionMap_lift, evaluationResolutionMap_lift,
    ← resolutionMap_comp, evaluationMap_comp]

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
variable {M N : FiniteLeftModule k R}

variable (M N)

def pairFst : (pairModule M N).carrier →ₗ[R] M.carrier := LinearMap.fst R _ _
def pairInl : M.carrier →ₗ[R] (pairModule M N).carrier := LinearMap.inl R _ _

end ArExplicit.FiniteLeftModule

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

variable [∀ degree, Module.Finite A (P.complex.X degree)]
  [∀ degree, Module.Finite B (Q.complex.X degree)]

theorem homTensorMap_restrict (n : ℕ)
    (x : (homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).X n) (p : Diagonal n) :
    (((homTensorMap k A B P Q U V f g).f n).hom x).comp
        (inclusion k A B P.complex Q.complex p.val.1 p.val.2 n p.property).hom =
      homMap k A B (TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom
        (homCochainTermCoordinates k A B P.complex Q.complex U V n
          ((homCochainTermEquiv k A B P.complex Q.complex U V n).symm x) p)) := by
  change (homCochainTermEquiv k A B P.complex Q.complex U V n
      (((mapBifunctorMap f g T (.up ℕ)).f n).hom
        ((homCochainTermEquiv k A B P.complex Q.complex U V n).symm x))).comp _ = _
  rw [homCochainTermEquiv_restrict, homCochainTermCoordinates_natural]

end ArExplicit.ExternalTensor

end

end OAI
end


