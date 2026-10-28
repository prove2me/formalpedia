-- Prove2me | Definitions.Def_OAIQ031A091
-- name    : OAIQ031A091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:29:19.463489+00:00
-- url     : https://prove2.me/theorems/1d121aef-a5e3-4f33-b0f4-0bd74422184b
-- title:
--   Definitions bundle OAIQ031A091 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 13 definitions and 19 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.oneSuffix`, `OAI.ArExplicit.FiniteLeftModule.evaluated`, `OAI.ArExplicit.FiniteLeftModule.evaluationMap`, `OAI.ArExplicit.FiniteLeftModule.evaluationSuccessorIso`, `OAI.ArExplicit.FiniteLeftModule.evaluationTriangle`, `OAI.ArExplicit.FiniteLeftModule.projectiveMiddleShiftIso`, `OAI.ArExplicit.FiniteLeftModule.resolutionConnecting`, `OAI.ArExplicit.FiniteLeftModule.resolutionMap`, `OAI.ArExplicit.FiniteLeftModule.resolutionTriangle`, `OAI.ArExplicit.completeConeBlockEquiv`, `OAI.ArExplicit.mappingConeStableQuotient`, `OAI.ArExplicit.shortExactConeIso`, `OAI.ArExplicit.shortExactTriangle`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_ProjectiveCompleteResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/ProjectiveCompleteResolution.lean), [`AuslanderReiten_Cones_MappingConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeCokernel.lean), [`AuslanderReiten_Homology_ShortExactTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactTriangle.lean), [`AuslanderReiten_Modules_FiniteModuleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleEvaluation.lean), [`AuslanderReiten_Modules_FiniteModuleNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleNaturality.lean), [`AuslanderReiten_Modules_FiniteModuleTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleTriangle.lean), [`AuslanderReiten_Modules_TwistedOneCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedOneCochain.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A077` and `OAIQ031A078` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A105`, `OAIQ031A110`, `OAIQ031A112`, `OAIQ031A113` and `OAIQ031A114`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def completeConeBlockEquiv : Cokernel (chainOfCochain (mappingCone φ)) 0 ≃ₗ[R]
    ConeQuotientMap.Cone (F.d 0 1).hom (G.d (-1) 0).hom (φ.f 0).hom :=
  (cochainCokernelLinearEquiv (mappingCone φ)).trans (rawConeBlockEquiv φ)

variable {L : Type u} [AddCommGroup L] [Module R L]
variable (p : CochainCokernel G →ₗ[R] L)
variable (hex : Function.Exact (cochainCokernelMap φ) p)

def mappingConeStableQuotient [Module.Injective R R]
    (hF : ExactProjectiveCochain F)
    (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p) :
    StableIsomorphism R (Cokernel (chainOfCochain (mappingCone φ)) 0) L := by
  letI := hF.finite 1
  letI := hF.projective 1
  letI : Module.Injective R (F.X 1) := finiteProjective_injective
  exact (StableIsomorphism.ofLinearEquiv (completeConeBlockEquiv φ)).trans
    (ConeQuotientMap.stableIsomorphism (F.d (-1) 0).hom (F.d 0 1).hom
      (G.d (-1) 0).hom (φ.f 0).hom (cochainCokernelMap φ) p
      (rawCokernelMap_comm φ) hex hi
      (congrArg ModuleCat.Hom.hom (F.d_comp_d (-1) 0 1)) hp)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactTriangle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def shortExactConeIso :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj (mappingCone φ) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj H :=
  stableCochainHomotopyIso (mappingCone_totallyAcyclic φ hF hG).to_chain hH.to_chain
    ((mappingConeStableQuotient φ p hex hF.toExactProjectiveCochain hi hp).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv H).symm))

def shortExactTriangle : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  Triangle.mk ((HomotopyCategory.quotient _ _).map φ)
    ((HomotopyCategory.quotient _ _).map (mappingCone.inr φ) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).hom)
    ((shortExactConeIso φ p hex hF hG hH hi hp).inv ≫ (mappingCone.triangleh φ).mor₃)

theorem shortExactTriangle_distinguished :
    shortExactTriangle φ p hex hF hG hH hi hp ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  apply isomorphic_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished φ)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (shortExactConeIso φ p hex hF hG hH hi hp).symm ?_ ?_ ?_
  · change ((HomotopyCategory.quotient _ _).map φ) ≫ 𝟙 _ =
      𝟙 _ ≫ ((HomotopyCategory.quotient _ _).map φ)
    simp only [Category.comp_id, Category.id_comp]
  · change (((HomotopyCategory.quotient _ _).map (mappingCone.inr φ)) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).hom) ≫
      (shortExactConeIso φ p hex hF hG hH hi hp).inv =
      𝟙 _ ≫ ((HomotopyCategory.quotient _ _).map (mappingCone.inr φ))
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · change ((shortExactConeIso φ p hex hF hG hH hi hp).inv ≫ (mappingCone.triangleh φ).mor₃) ≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map (𝟙 _) = _
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleTriangle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def resolutionMap (f : M.carrier →ₗ[R] N.carrier) : M.completeCochain τ ⟶ N.completeCochain τ :=
  Classical.choose (cochainCokernelMap_surjective
    (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
    (resolutionCokernelMap τ f))

@[simp]
theorem resolutionMap_cokernel (f : M.carrier →ₗ[R] N.carrier) :
    cochainCokernelMap (resolutionMap τ f) = resolutionCokernelMap τ f :=
  Classical.choose_spec (cochainCokernelMap_surjective
    (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
    (resolutionCokernelMap τ f))

theorem resolutionCokernelMap_injective (f : M.carrier →ₗ[R] N.carrier)
    (hf : Function.Injective f) : Function.Injective (resolutionCokernelMap τ f) :=
  (N.completeCochainCokernelEquiv τ).symm.injective.comp
    (hf.comp (M.completeCochainCokernelEquiv τ).injective)

theorem resolutionCokernelMap_surjective (f : M.carrier →ₗ[R] N.carrier)
    (hf : Function.Surjective f) : Function.Surjective (resolutionCokernelMap τ f) :=
  (N.completeCochainCokernelEquiv τ).symm.surjective.comp
    (hf.comp (M.completeCochainCokernelEquiv τ).surjective)

theorem resolutionCokernelMap_exact
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (h : Function.Exact f g) : Function.Exact (resolutionCokernelMap τ f) (resolutionCokernelMap τ g) := by
  intro x
  constructor
  · intro hx
    have hx' : g ((N.completeCochainCokernelEquiv τ) x) = 0 := by
      have hh := congrArg (L.completeCochainCokernelEquiv τ) hx
      simpa [resolutionCokernelMap] using hh
    obtain ⟨m, hm⟩ := (h _).mp hx'
    refine ⟨(M.completeCochainCokernelEquiv τ).symm m, ?_⟩
    simp [resolutionCokernelMap, hm]
  · rintro ⟨m, rfl⟩
    change (L.completeCochainCokernelEquiv τ).symm
      (g ((N.completeCochainCokernelEquiv τ)
        ((N.completeCochainCokernelEquiv τ).symm
          (f ((M.completeCochainCokernelEquiv τ) m))))) = 0
    rw [LinearEquiv.apply_symm_apply, (h _).mpr ⟨_, rfl⟩, map_zero]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem resolutionCokernelMap_comp (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier) :
    resolutionCokernelMap τ (g.comp f) = (resolutionCokernelMap τ g).comp (resolutionCokernelMap τ f) := by
  apply LinearMap.ext
  intro x
  simp [resolutionCokernelMap]

@[simp]
theorem resolutionMap_id :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (LinearMap.id : M.carrier →ₗ[R] M.carrier)) = 𝟙 _ := by
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [← (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_id,
    cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map, resolutionMap_cokernel]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range ((M.completeCochain τ).d (-1) 0).hom).mkQ_surjective x
  simp [resolutionCokernelMap, cochainCokernelMap_mk]

theorem resolutionMap_comp (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (g.comp f)) =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) ≫
        (HomotopyCategory.quotient _ _).map (resolutionMap τ g) := by
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (L.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [← Functor.map_comp, cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    cochainCokernelMap_comp, resolutionMap_cokernel, resolutionMap_cokernel, resolutionMap_cokernel,
    resolutionCokernelMap_comp]

theorem resolutionMap_surjective : Function.Surjective
    (fun f : M.carrier →ₗ[R] N.carrier =>
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map (resolutionMap τ f)) := by
  intro h
  let E := cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
  obtain ⟨u, hu⟩ := StableHom.classOf_surjective (E h)
  let f := (N.completeCochainCokernelEquiv τ).toLinearMap.comp
    (u.comp (M.completeCochainCokernelEquiv τ).symm.toLinearMap)
  refine ⟨f, E.injective ?_⟩
  change cochainHomotopyRawEquiv _ _ _ = _
  rw [cochainHomotopyRawEquiv_map, resolutionMap_cokernel]
  have hf : resolutionCokernelMap τ f = u := by
    apply LinearMap.ext
    intro x
    simp [resolutionCokernelMap, f]
  rw [hf]
  exact hu

variable (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)

def resolutionTriangle : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := τ.regular_injective
  exact shortExactTriangle (resolutionMap τ f) (resolutionCokernelMap τ g)
    (by rw [resolutionMap_cokernel]; exact resolutionCokernelMap_exact τ f g hex)
    (M.completeCochain_totallyAcyclic τ) (N.completeCochain_totallyAcyclic τ)
    (L.completeCochain_totallyAcyclic τ)
    (by rw [resolutionMap_cokernel]; exact resolutionCokernelMap_injective τ f hf)
    (resolutionCokernelMap_surjective τ g hg)

theorem resolutionTriangle_distinguished :
    resolutionTriangle τ f g hf hg hex ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := τ.regular_injective
  apply shortExactTriangle_distinguished

@[simp]
theorem resolutionTriangle_first :
    (resolutionTriangle τ f g hf hg hex).mor₁ =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) := rfl

abbrev resolutionConnecting :
    (HomotopyCategory.quotient _ _).obj (L.completeCochain τ) ⟶
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧ :=
  (resolutionTriangle τ f g hf hg hex).mor₃

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_ProjectiveCompleteResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit

open CompleteComparison

universe u

variable {R : Type u} [Ring R]

theorem completeCochain_isZero_of_projectiveCokernel
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : TotallyAcyclicCochain K)
    [Module.Projective R (CochainCokernel K)] :
    Limits.IsZero ((HomotopyCategory.quotient _ _).obj K) := by
  let := hK.finite 0
  let : Module.Finite R (CochainCokernel K) := inferInstance
  rw [Limits.IsZero.iff_id_eq_zero]
  apply (cochainHomotopyRawEquiv hK.to_chain hK.to_chain.toExactProjectiveComplex).injective
  rw [map_zero]
  rw [← (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_id,
    cochainHomotopyRawEquiv_map]
  exact StableHom.eq_zero_of_projective_source _

namespace FiniteLeftModule

variable {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (M : FiniteLeftModule k R)

theorem projective_completeCochain_isZero [Module.Projective R M.carrier] :
    Limits.IsZero ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ)) := by
  let : Module.Projective R (CochainCokernel (M.completeCochain τ)) :=
    Module.Projective.of_equiv (M.completeCochainCokernelEquiv τ).symm
  exact completeCochain_isZero_of_projectiveCokernel _ (M.completeCochain_totallyAcyclic τ)

variable {M} {N L : FiniteLeftModule k R}

def projectiveMiddleShiftIso [Module.Projective R N.carrier]
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    ((HomotopyCategory.quotient _ _).obj (L.completeCochain τ)) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧ := by
  let T := resolutionTriangle τ f g hf hg hex
  have hz : Limits.IsZero T.obj₂ := N.projective_completeCochain_isZero τ
  haveI : IsIso (resolutionConnecting τ f g hf hg hex) :=
    (T.isZero₂_iff_isIso₃ (resolutionTriangle_distinguished τ f g hf hg hex)).mp hz
  exact asIso (resolutionConnecting τ f g hf hg hex)

@[simp]
theorem projectiveMiddleShiftIso_hom [Module.Projective R N.carrier]
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    (projectiveMiddleShiftIso τ f g hf hg hex).hom = resolutionConnecting τ f g hf hg hex := rfl

end FiniteLeftModule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleEvaluation
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

def evaluated : FiniteLeftModule k R where
  carrier := ModuleCat.of R (BalancedTensor k R (EnvelopingBimodule k R M.carrier) X.carrier)
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

variable {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}

def evaluationMap (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier) :
    (evaluated X M).carrier →ₗ[R] (evaluated X N).carrier :=
  EnvelopingBimodule.tensorMap X.carrier (ModuleCat.ofHom f)

omit [Module.Finite k R] in
@[simp] theorem evaluationMap_id : evaluationMap X (LinearMap.id : M.carrier →ₗ[_] M.carrier) =
    LinearMap.id := EnvelopingBimodule.tensorMap_id X.carrier

omit [Module.Finite k R] in
@[simp] theorem evaluationMap_comp (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
    (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier) :
    evaluationMap X (g.comp f) = (evaluationMap X g).comp (evaluationMap X f) :=
  EnvelopingBimodule.tensorMap_comp X.carrier (ModuleCat.ofHom f) (ModuleCat.ofHom g)

omit [Module.Finite k R] in
theorem evaluated_projective [Module.Projective (R ⊗[k] Rᵐᵒᵖ) M.carrier] :
    Module.Projective R (evaluated X M).carrier := by
  let := Module.Finite.of_restrictScalars_finite k (R ⊗[k] Rᵐᵒᵖ) M.carrier
  exact EnvelopingBimodule.tensor_projective X.carrier M.carrier

variable (f : M.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] N.carrier)
  (g : N.carrier →ₗ[R ⊗[k] Rᵐᵒᵖ] P.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R P.carrier)]

include hf hg he in
omit [Module.Finite k R] in

theorem evaluation_shortExact :
    Function.Injective (evaluationMap X f) ∧ Function.Surjective (evaluationMap X g) ∧
      Function.Exact (evaluationMap X f) (evaluationMap X g) := by
  have hr : LinearMap.range f = LinearMap.ker g := by
    ext y
    exact (he y).symm
  obtain ⟨hi, hs, hx⟩ := EnvelopingBimodule.tensorMap_shortExact X.carrier
    (ModuleCat.ofHom f) (ModuleCat.ofHom g) hf hg hr
  change LinearMap.range (evaluationMap X f) = LinearMap.ker (evaluationMap X g) at hx
  refine ⟨hi, hs, ?_⟩
  intro y
  exact (show y ∈ LinearMap.ker (evaluationMap X g) ↔
      y ∈ LinearMap.range (evaluationMap X f) by rw [hx])

variable (τ : FrobeniusTrace k R)

def evaluationTriangle : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  resolutionTriangle τ (evaluationMap X f) (evaluationMap X g)
    (evaluation_shortExact X f g hf hg he).1 (evaluation_shortExact X f g hf hg he).2.1
    (evaluation_shortExact X f g hf hg he).2.2

def evaluationSuccessorIso [Module.Projective (R ⊗[k] Rᵐᵒᵖ) N.carrier] :
    (HomotopyCategory.quotient _ _).obj ((evaluated X P).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((evaluated X M).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := evaluated_projective X (M := N)
  exact projectiveMiddleShiftIso τ (evaluationMap X f) (evaluationMap X g)
    (evaluation_shortExact X f g hf hg he).1 (evaluation_shortExact X f g hf hg he).2.1
    (evaluation_shortExact X f g hf hg he).2.2

@[simp]
theorem evaluationSuccessorIso_hom [Module.Projective (R ⊗[k] Rᵐᵒᵖ) N.carrier] :
    (evaluationSuccessorIso X f g hf hg he τ).hom =
      (evaluationTriangle X f g hf hg he τ).mor₃ := by
  let := evaluated_projective X (M := N)
  exact projectiveMiddleShiftIso_hom _ _ _ _ _ _

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedOneCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.AbsoluteBar

universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def oneSuffix (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) : object k R 1 →ₗ[k] R :=
  TensorProduct.lift (((LinearMap.mul k R).comp z).compl₂ h.symm.toLinearMap)

end ArExplicit.AbsoluteBar

end

end OAI
end


