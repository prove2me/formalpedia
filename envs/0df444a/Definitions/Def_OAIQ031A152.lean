-- Prove2me | Definitions.Def_OAIQ031A152
-- name    : OAIQ031A152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:29:54.56399+00:00
-- url     : https://prove2.me/theorems/0852a691-05c4-4031-9051-cf605c59ca94
-- title:
--   Definitions bundle OAIQ031A152 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 7 theorems. The definitions and types are `OAI.ArExplicit.FiniteCoverTower`, `OAI.ArExplicit.FiniteCoverTower.boundaryClass`, `OAI.ArExplicit.FiniteCoverTower.coverClass`, `OAI.ArExplicit.FiniteCoverTower.coverClassFrom`, `OAI.ArExplicit.FiniteCoverTower.shiftIso`, `OAI.ArExplicit.FiniteCoverTower.stepIso`, `OAI.ArExplicit.FiniteLeftModule.HasSourceCoordinates`, `OAI.ArExplicit.FiniteLeftModule.SourceInclusionSquare`, `OAI.ArExplicit.FiniteLeftModule.SourceQuotientSquare`, `OAI.ArExplicit.TwoCone.middleCokernelEquiv`, `OAI.ArExplicit.TwoCone.singletonCokernelProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_CompleteFunctorCokernelAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteFunctorCokernelAction.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Coordinates_FiniteConnectingProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteConnectingProducts.lean), [`AuslanderReiten_Coordinates_FiniteExtSourceCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteExtSourceCoordinates.lean), [`AuslanderReiten_Coordinates_FiniteSourceCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/FiniteSourceCoordinates.lean), [`AuslanderReiten_Resolutions_FiniteCoverProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCoverProducts.lean), [`AuslanderReiten_Resolutions_FiniteCoverTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCoverTransport.lean), [`AuslanderReiten_Tensor_BalancedTensorCompleteAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCompleteAction.lean), [`AuslanderReiten_Tensor_BalancedTensorPositiveAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorPositiveAction.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A147` and `OAIQ031A148` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A155` and `OAIQ031A156`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A147
import Definitions.Def_OAIQ031A148

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorCokernelAction
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem fullHom_rawFunctor_scalar
    (a : K ⟶ functorComplex F K) (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (CochainCokernel K) ≅ F.obj (ModuleCat.of R (CochainCokernel K)))
    (ha : cochainCokernelMap a =
      (E ≪≫ (rawFunctorEndpointIso F K hK hFK).symm).hom.hom)
    (hb : cochainCokernelMap b =
      (rawFunctorEndpointIso F K hK hFK ≪≫ E.symm).hom.hom)
    (n : ℕ) (c : k)
    (hs : ∀ z : Ext (ModuleCat.of R (CochainCokernel K))
      (ModuleCat.of R (CochainCokernel K)) (n+1),
      selfExtIso (k := k) E.symm (n+1) (z.mapExactFunctor F) = c • z)
    (x : CohomologyClass K K ((n+1 : ℕ) : ℤ)) :
    fullHomPostcomp b _ (fullHomPrecomp a _ (mapFullHom F K K _ x)) = c • x := by
  apply fullHom_conjugatedFunctor_scalar F K hK hFK a b
    ((cochainCokernelLinearEquiv K).toModuleIso ≪≫ E ≪≫
      F.mapIso (cochainCokernelLinearEquiv K).symm.toModuleIso)
    (rawFunctor_precomp_endpoint F K hK hFK a E ha)
    (rawFunctor_postcomp_endpoint F K hK hFK b E hb) n c
  exact exactFunctor_scalar_transport F (cochainCokernelLinearEquiv K).toModuleIso E (n+1) c hs

end ArExplicit.CompleteComparison

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

def middleCokernelEquiv (n : ℕ) : ConeCokernel.Right (middleD D n) ≃ₗ[R]
    BaseCokernel D (n + 2) × BaseCokernel D (n + 2) :=
  cokernelProductEquiv (D.d (n + 2)) (D.d (n + 2))

def singletonCokernelProjection (n : ℕ) : SkeletonCokernel D n →ₗ[R]
    BaseCokernel D (n + 2) × BaseCokernel D (n + 2) :=
  (middleCokernelEquiv D n).toLinearMap.comp
    (ConeCokernel.projection (D.d n) (middleD D n) (attachingRow D n))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteConnectingProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem resolutionSourceAtStableEquiv_postcomp (S M N : FiniteLeftModule k R)
    (n : ℤ) (f : M.carrier →ₗ[R] N.carrier)
    (u : CohomologyClass (S.completeCochain τ) (M.completeCochain τ) n) :
    resolutionSourceAtStableEquiv τ S N n (fullHomPostcomp (resolutionMap τ f) n u) =
      StableHom.postcomp f (resolutionSourceAtStableEquiv τ S M n u) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective u
  rw [fullHomPostcomp_mk, resolutionSourceAtStableEquiv_mk,
    resolutionSourceAtStableEquiv_mk, StableHom.postcomp_classOf,
    rawSourceAt_postcomp (k := k), resolutionMap_cokernel]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  simp [resolutionCokernelMap]

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteExtSourceCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem source_selfExtIso (n : ℕ)
    (z : Ext (ModuleCat.of R (Cokernel (chainOfCochain (M.completeCochain τ)) 0))
      (ModuleCat.of R (Cokernel (chainOfCochain (M.completeCochain τ)) 0)) n) :
    extSourceIso (k := k) (M.fullCokernelEquiv τ).toModuleIso.symm M.carrier n
      (selfExtIso (k := k) (M.fullCokernelEquiv τ).toModuleIso n z) =
        z.comp (Ext.mk₀ (M.fullCokernelEquiv τ).toModuleIso.hom) (add_zero n) := by
  simp [extSourceIso, selfExtIso_apply]
  have hid : ModuleCat.ofHom (M.fullCokernelEquiv τ).toLinearMap ≫
      ModuleCat.ofHom (M.fullCokernelEquiv τ).symm.toLinearMap = 𝟙 _ :=
    (M.fullCokernelEquiv τ).toModuleIso.hom_inv_id
  rw [hid, Ext.mk₀_id_comp]

theorem moduleExtSourceStableEquiv_fullPositive (n : ℕ)
    (u : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ)) :
    moduleExtSourceStableEquiv τ M M.carrier n (fullPositiveModuleExtEquiv τ M n u) =
      resolutionSourceAtStableEquiv τ M M ((n+1 : ℕ) : ℤ) u := by
  change (StableIsomorphism.ofLinearEquiv
      (rawCokernelAtEquiv (M.completeCochain τ) ((n+1 : ℕ) : ℤ)).symm).sourceAddEquiv
    (positiveExtStableEquiv (k := k) (M.completeCochain_totallyAcyclic τ).to_chain M.carrier n
      (extSourceIso (k := k) (M.fullCokernelEquiv τ).toModuleIso.symm M.carrier (n+1)
        (selfExtIso (k := k) (M.fullCokernelEquiv τ).toModuleIso (n+1)
          (fullPositiveExtEquiv (k := k) _ _ _ _ n u)))) = _
  rw [source_selfExtIso, positiveExtStableEquiv_postcomp, fullPositiveExtEquiv_stable]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective u
  rw [fullHomSourceStableLinearEquiv_mk, resolutionSourceAtStableEquiv_mk,
    StableHom.postcomp_classOf]
  simp only [StableIsomorphism.sourceAddEquiv, StableIsomorphism.ofLinearEquiv,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  rfl

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_FiniteSourceCoordinates
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
variable (τ : FrobeniusTrace k R) (S M N L : FiniteLeftModule k R) (n : ℤ)

def HasSourceCoordinates
    (u : CohomologyClass (S.completeCochain τ) (M.completeCochain τ) n)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] M.carrier) : Prop :=
  resolutionSourceAtStableEquiv τ S M n u = StableHom.classOf R _ _ s

def SourceQuotientSquare (g : N.carrier →ₗ[R] L.carrier)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] L.carrier)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier) : Prop :=
  g.comp A = s.comp (LinearMap.range ((S.completeCochain τ).d (-(n+1)) (-n)).hom).mkQ

def SourceInclusionSquare (f : M.carrier →ₗ[R] N.carrier)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier)
    (t : RawCokernelAt (S.completeCochain τ) (n+1) →ₗ[R] M.carrier) : Prop :=
  f.comp t = A.comp (rawCokernelAtInclusion (S.completeCochain τ) n)

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCoverProducts
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]

structure FiniteCoverTower where
  obj : ℕ → FiniteLeftModule k R
  middle : ℕ → FiniteLeftModule k R
  inclusion : ∀ n, (obj (n+1)).carrier →ₗ[R] (middle n).carrier
  quotient : ∀ n, (middle n).carrier →ₗ[R] (obj n).carrier
  injective : ∀ n, Function.Injective (inclusion n)
  surjective : ∀ n, Function.Surjective (quotient n)
  exact : ∀ n, Function.Exact (inclusion n) (quotient n)
  projective : ∀ n, Module.Projective R (middle n).carrier

namespace FiniteCoverTower
variable (τ : FrobeniusTrace k R) (T : FiniteCoverTower (k := k) (R := R))
local notation "K" => FiniteLeftModule.completeCochain τ (T.obj 0)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

def stepIso (n : ℕ) : (Q).obj ((T.obj n).completeCochain τ) ≅
    ((Q).obj ((T.obj (n+1)).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := T.projective n
  exact FiniteLeftModule.projectiveMiddleShiftIso τ (T.inclusion n) (T.quotient n)
    (T.injective n) (T.surjective n) (T.exact n)

def shiftIso (n : ℕ) : (Q).obj K ≅ ((Q).obj ((T.obj n).completeCochain τ))⟦(n : ℤ)⟧ :=
  iteratedShiftIso (fun n => (Q).obj ((T.obj n).completeCochain τ)) (T.stepIso τ) n

def boundaryClass (n : ℕ) :
    CohomologyClass ((T.obj n).completeCochain τ) ((T.obj (n+1)).completeCochain τ) 1 :=
  (fullHomShiftedHomotopyEquiv k _ _ 1).symm
    (FiniteLeftModule.resolutionConnecting τ (T.inclusion n) (T.quotient n)
      (T.injective n) (T.surjective n) (T.exact n))

def coverClass : (n : ℕ) → CohomologyClass K ((T.obj n).completeCochain τ) (n : ℤ)
  | 0 => fullHomIdentity K
  | n+1 => fullHomProduct (coverClass n) (boundaryClass τ T n)

variable (S : FiniteLeftModule k R)
variable (u₀ : CohomologyClass (S.completeCochain τ) ((T.obj 0).completeCochain τ) 0)

def coverClassFrom : (n : ℕ) →
    CohomologyClass (S.completeCochain τ) ((T.obj n).completeCochain τ) (n : ℤ)
  | 0 => u₀
  | n+1 => fullHomProduct (coverClassFrom n) (boundaryClass τ T n)

end FiniteCoverTower
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCoverTransport
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u v w

open scoped ModuleCat.Algebra
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]
namespace FiniteCoverTower
variable (τ : FrobeniusTrace k R) (T : FiniteCoverTower (k := k) (R := R))
variable (S : FiniteLeftModule k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

omit [CharP k 2] in
theorem coverClassFrom_hom (f : S.completeCochain τ ⟶ (T.obj 0).completeCochain τ) (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ)
      (T.coverClassFrom τ S (CohomologyClass.mk (Cocycle.ofHom f)) n) =
        (Q).map f ≫ (T.shiftIso τ n).hom := by
  induction n with
  | zero => exact fullHomShiftedHomotopyEquiv_ofHom k f
  | succ n ih =>
    change fullHomShiftedHomotopyEquiv k _ _ ((n : ℤ)+1)
      (fullHomProduct (T.coverClassFrom τ S (CohomologyClass.mk (Cocycle.ofHom f)) n)
        (T.boundaryClass τ n)) = _
    rw [fullHomShiftedHomotopyEquiv_product, ih]
    simp only [boundaryClass, LinearEquiv.apply_symm_apply]
    simp only [shiftIso, iteratedShiftIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Category.assoc]
    rfl
end FiniteCoverTower
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCompleteAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem completeAction_scalar (n : ℕ) (c : k)
    (hs : ∀ z : Ext M.carrier M.carrier (n+1),
      selfExtIso (k := k) (nativeEvaluationIso M e) (n+1)
        (z.mapExactFunctor (functor (k := k) (R := R) (S := R) (F := F))) = c • z)
    (x : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) ((n+1 : ℕ) : ℤ)) :
    fullHomPostcomp (completeActionOut τ M e) _
      (fullHomPrecomp (completeActionIn τ M e) _
        (mapFullHom (functor (k := k) (R := R) (S := R) (F := F)) _ _ _ x)) = c • x := by
  apply fullHom_rawFunctor_scalar (functor (k := k) (R := R) (S := R) (F := F))
    (M.completeCochain τ) (M.completeCochain_totallyAcyclic τ).to_chain
    (completeTensor_totallyAcyclic (F := F) τ M).to_chain
    (completeActionIn τ M e) (completeActionOut τ M e) (completeActionEndpoint τ M e)
  · exact cokernelCochainLift_map _ _ _
  · exact cokernelCochainLift_map _ _ _
  · exact exactFunctor_scalar_transport (functor (k := k) (R := R) (S := R) (F := F))
      (M.completeCochainCokernelEquiv τ).toModuleIso (nativeEvaluationIso M e).symm (n+1) c hs

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorPositiveAction
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
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

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem completeAction_scalar_positive (d : ℕ) (hd : 0 < d) (c : k)
    (hs : ∀ z : Ext M.carrier M.carrier d,
      selfExtIso (k := k) (nativeEvaluationIso M e) d
        (z.mapExactFunctor (functor (k := k) (R := R) (S := R) (F := F))) = c • z)
    (x : CohomologyClass (M.completeCochain τ) (M.completeCochain τ) (d : ℤ)) :
    fullHomPostcomp (completeActionOut τ M e) _
      (fullHomPrecomp (completeActionIn τ M e) _
        (mapFullHom (functor (k := k) (R := R) (S := R) (F := F)) _ _ _ x)) = c • x := by
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hd)
  | succ n => exact completeAction_scalar τ M e n c hs x

end ArExplicit.BalancedTensor

end

end OAI
end


