-- Prove2me | Definitions.Def_OAIQ031A113
-- name    : OAIQ031A113
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:50:27.518749+00:00
-- url     : https://prove2.me/theorems/4e95b712-590f-45a2-bad7-a38697f1c631
-- title:
--   Definitions bundle OAIQ031A113 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 6 definitions and 10 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.canonicalCosyzygiesShiftIso`, `OAI.ArExplicit.FiniteLeftModule.canonicalCosyzygyQuotient`, `OAI.ArExplicit.FiniteLeftModule.canonicalCosyzygyShiftIso`, `OAI.ArExplicit.FiniteLeftModule.canonicalEnvelopeModule`, `OAI.ArExplicit.FiniteLeftModule.evaluatedCanonicalCosyzygiesShiftIso`, `OAI.ArExplicit.FiniteLeftModule.evaluatedCanonicalCosyzygyShiftIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_MappingConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeCokernel.lean), [`AuslanderReiten_Cones_ShortExactConeRaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ShortExactConeRaw.lean), [`AuslanderReiten_Evaluation_EvaluatedCosyzygyShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/EvaluatedCosyzygyShift.lean), [`AuslanderReiten_Homology_ShortExactNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactNaturality.lean), [`AuslanderReiten_Homology_ShortExactTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactTriangle.lean), [`AuslanderReiten_Modules_FiniteModuleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleEvaluation.lean), [`AuslanderReiten_Modules_FiniteModuleNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleNaturality.lean), [`AuslanderReiten_Stable_CanonicalCosyzygyShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/CanonicalCosyzygyShift.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A091`, `OAIQ031A096`, `OAIQ031A097` and `OAIQ031A098` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A124` and `OAIQ031A125`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A091
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A097
import Definitions.Def_OAIQ031A098

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

variable {L : Type u} [AddCommGroup L] [Module R L]
variable (p : CochainCokernel G →ₗ[R] L)
variable (hex : Function.Exact (cochainCokernelMap φ) p)

theorem completeConeQuotient_inr :
    (completeConeQuotient φ p hex).comp
      (cokernelMap (extendMap (mappingCone.inr φ) negIndexEmbedding) 0) =
      p.comp (cochainCokernelLinearEquiv G).toLinearMap := by
  unfold completeConeQuotient
  rw [LinearMap.comp_assoc, cochainCokernelLinearEquiv_natural,
    ← LinearMap.comp_assoc, rawConeQuotient_inr]

theorem mappingConeStableQuotient_hom [Module.Injective R R]
    (hF : ExactProjectiveCochain F)
    (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p) :
    (mappingConeStableQuotient φ p hex hF hi hp).hom =
      StableHom.classOf R _ _ (completeConeQuotient φ p hex) := by
  change StableHom.comp
    (StableHom.classOf R _ _ (ConeQuotientMap.quotientMap _ _ _ _ _ _ _ _))
    (StableHom.classOf R _ _ (completeConeBlockEquiv φ).toLinearMap) = _
  rw [StableHom.comp_classOf]
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactTriangle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex

namespace ArExplicit

open CompleteComparison

universe u

variable {R : Type u} [Ring R] [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (hex : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G)
variable (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

theorem shortExactConeIso_hom :
    cochainHomotopyCokernelEquiv (mappingCone_totallyAcyclic φ hF hG).to_chain
      hH.to_chain.toExactProjectiveComplex (shortExactConeIso φ p hex hF hG hH hi hp).hom =
    StableHom.classOf R _ _ ((cochainCokernelLinearEquiv H).symm.toLinearMap.comp
      (completeConeQuotient φ p hex)) := by
  unfold shortExactConeIso
  rw [stableCochainHomotopyIso_hom]
  change StableHom.comp
    (StableHom.classOf R _ _ (cochainCokernelLinearEquiv H).symm.toLinearMap)
    (mappingConeStableQuotient φ p hex hF.toExactProjectiveCochain hi hp).hom = _
  rw [mappingConeStableQuotient_hom φ p hex hF.toExactProjectiveCochain hi hp,
    StableHom.comp_classOf]

theorem shortExactTriangle_second (ψ : G ⟶ H) (hψ : cochainCokernelMap ψ = p) :
    (shortExactTriangle φ p hex hF hG hH hi hp).mor₂ =
      (HomotopyCategory.quotient _ _).map ψ := by
  apply (cochainHomotopyCokernelEquiv hG.to_chain hH.to_chain.toExactProjectiveComplex).injective
  change cochainHomotopyCokernelEquiv hG.to_chain hH.to_chain.toExactProjectiveComplex
    (((HomotopyCategory.quotient _ _).map (mappingCone.inr φ)) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).hom) = _
  rw [cochainHomotopyCokernelEquiv_comp hG.to_chain
    (mappingCone_totallyAcyclic φ hF hG).to_chain hH.to_chain.toExactProjectiveComplex,
    shortExactConeIso_hom, cochainHomotopyCokernelEquiv_map, cochainHomotopyCokernelEquiv_map,
    StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  rw [LinearMap.comp_assoc, completeConeQuotient_inr]
  apply LinearMap.ext
  intro x
  apply (cochainCokernelLinearEquiv H).injective
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural ψ) x
  rw [hψ] at h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h.symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem shortExactConeIso_raw_hom :
    cochainHomotopyRawEquiv (mappingCone_totallyAcyclic φ hF hG).to_chain
      hK.to_chain.toExactProjectiveComplex (shortExactConeIso φ p hex hF hG hK hi hp).hom =
    StableHom.classOf R _ _ (rawConeQuotient φ p hex) := by
  simp only [cochainHomotopyRawEquiv, AddEquiv.trans_apply, shortExactConeIso_hom,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro x
  simp [completeConeQuotient]

end ArExplicit

end

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

variable [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

theorem shortExactConeInverse_stable_identity (κ : H ⟶ mappingCone φ)
    (hκ : (HomotopyCategory.quotient _ _).map κ =
      (shortExactConeIso φ p he hF hG hH hi hp).inv) :
    StableHom.classOf R _ _ ((rawConeQuotient φ p he).comp (cochainCokernelMap κ)) =
      StableHom.classOf R _ _ LinearMap.id := by
  have h : (HomotopyCategory.quotient _ _).map κ ≫
      (shortExactConeIso φ p he hF hG hH hi hp).hom = 𝟙 _ := by
    rw [hκ, Iso.inv_hom_id]
  have h' := congrArg (cochainHomotopyRawEquiv hH.to_chain hH.to_chain.toExactProjectiveComplex) h
  rw [cochainHomotopyRawEquiv_comp hH
    (mappingCone_totallyAcyclic φ hF hG) hH.toExactProjectiveCochain,
    shortExactConeIso_raw_hom, cochainHomotopyRawEquiv_map,
    StableHom.comp_classOf, cochainHomotopyRawEquiv_id] at h'
  exact h'

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem resolutionTriangle_second :
    (resolutionTriangle τ f g hf hg hex).mor₂ =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ g) := by
  let := τ.regular_injective
  apply shortExactTriangle_second
  exact resolutionMap_cokernel τ g

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleEvaluation
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

theorem evaluationTriangle_distinguished : evaluationTriangle X f g hf hg he τ ∈
    distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  resolutionTriangle_distinguished _ _ _ _ _ _

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_CanonicalCosyzygyShift
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.FiniteLeftModule

open CompleteComparison

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

def canonicalEnvelopeModule : FiniteLeftModule k R where
  carrier := M.canonicalEnvelope
  scalar := inferInstanceAs (Module k (CoinducedModule k R M.carrier))
  tower := inferInstanceAs (IsScalarTower k R (CoinducedModule k R M.carrier))
  finite := inferInstanceAs (Module.Finite k (CoinducedModule k R M.carrier))

def canonicalCosyzygyQuotient : (M.canonicalEnvelopeModule).carrier →ₗ[R]
    M.canonicalCosyzygy.carrier :=
  (LinearMap.range (M.canonicalEmbedding).hom).mkQ

theorem canonicalCosyzygyQuotient_surjective : Function.Surjective M.canonicalCosyzygyQuotient :=
  (LinearMap.range (M.canonicalEmbedding).hom).mkQ_surjective

theorem canonicalCosyzygy_exact : Function.Exact (M.canonicalEmbedding).hom
    M.canonicalCosyzygyQuotient := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

def canonicalCosyzygyShiftIso :
    (HomotopyCategory.quotient _ _).obj (M.canonicalCosyzygy.completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective R M.canonicalEnvelopeModule.carrier :=
    CoinducedModule.projective (M := M.carrier) τ
  exact projectiveMiddleShiftIso τ (M.canonicalEmbedding).hom M.canonicalCosyzygyQuotient
    CoinducedModule.embedding_injective M.canonicalCosyzygyQuotient_surjective
    M.canonicalCosyzygy_exact

def canonicalCosyzygiesShiftIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((M.canonicalCosyzygies n).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(n : ℤ)⟧ := by
  induction n with
  | zero =>
    exact ((shiftFunctorZero (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ).app _).symm
  | succ n ih =>
    exact canonicalCosyzygyShiftIso τ (M.canonicalCosyzygies n) ≪≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).mapIso ih ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        (n : ℤ) 1 ((n + 1 : ℕ) : ℤ) (by omega)).symm.app _

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedCosyzygyShift
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.canonicalCosyzygy.carrier)]

def evaluatedCanonicalCosyzygyShiftIso :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated M.canonicalCosyzygy).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective (R ⊗[k] Rᵐᵒᵖ) M.canonicalEnvelopeModule.carrier :=
    CoinducedModule.projective (M := M.carrier) τe
  exact evaluationSuccessorIso X (M.canonicalEmbedding).hom M.canonicalCosyzygyQuotient
    CoinducedModule.embedding_injective M.canonicalCosyzygyQuotient_surjective
    M.canonicalCosyzygy_exact τ

variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (M.canonicalCosyzygies n).carrier))

def evaluatedCanonicalCosyzygiesShiftIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated (M.canonicalCosyzygies n)).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ))⟦(n : ℤ)⟧ := by
  induction n with
  | zero =>
    exact ((shiftFunctorZero (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ).app _).symm
  | succ n ih =>
    letI : Module.Projective Rᵐᵒᵖ
        (EnvelopingBimodule k R (M.canonicalCosyzygies n).canonicalCosyzygy.carrier) := hr (n+1)
    exact evaluatedCanonicalCosyzygyShiftIso X τe τ (M.canonicalCosyzygies n) ≪≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).mapIso ih ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        (n : ℤ) 1 ((n+1 : ℕ) : ℤ) (by omega)).symm.app _

end ArExplicit.FiniteLeftModule

end

end OAI
end


