-- Prove2me | Definitions.Def_OAIQ031A105
-- name    : OAIQ031A105
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:40:53.517765+00:00
-- url     : https://prove2.me/theorems/39718f8c-b141-4878-b1dd-d06555f0265f
-- title:
--   Definitions bundle OAIQ031A105 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 7 definitions and 15 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.oneCochain`, `OAI.ArExplicit.AbsoluteBar.oneCochainLinear`, `OAI.ArExplicit.FiniteLeftModule.fullCokernelEquiv`, `OAI.ArExplicit.FiniteLeftModule.resolutionHomotopyEquiv`, `OAI.ArExplicit.FiniteLeftModule.resolutionIso`, `OAI.ArExplicit.FiniteLeftModule.stableResolutionIso`, `OAI.ArExplicit.T.Z`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_CompleteStableSourceNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteStableSourceNaturality.lean), [`AuslanderReiten_Coordinates_TensorHighLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TensorHighLift.lean), [`AuslanderReiten_Duality_FiniteStableResolutionIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/FiniteStableResolutionIso.lean), [`AuslanderReiten_HomComplex_FiniteFullHomZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FiniteFullHomZero.lean), [`AuslanderReiten_HomComplex_HomCochainExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainExt.lean), [`AuslanderReiten_Homology_TBoundaryCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TBoundaryCochain.lean), [`AuslanderReiten_Modules_TwistedOneCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedOneCochain.lean), [`AuslanderReiten_Resolutions_FiniteResolutionIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionIso.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A091`, `OAIQ031A092`, `OAIQ031A093` and `OAIQ031A094` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A118`, `OAIQ031A119`, `OAIQ031A120`, `OAIQ031A124`, `OAIQ031A125` and `OAIQ031A126`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A091
import Definitions.Def_OAIQ031A092
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A094

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteStableSourceNaturality
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

@[simp] theorem syzygyInclusion_mk (hP : ExactProjectiveComplex P) (n : ℤ)
    (x : P.X (n+1)) :
    syzygyInclusion hP n (Submodule.Quotient.mk x) = (P.d (n+1) n).hom x := rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedOneCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

@[simp] theorem oneSuffix_tmul (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (b c : R) :
    oneSuffix k R h z (b ⊗ₜ[k] c) = z b * h.symm c := rfl

def oneCochainLinear (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) : object k R 2 →ₗ[k] R :=
  TensorProduct.lift ((LinearMap.mul k R).compl₂ (oneSuffix k R h z))

@[simp] theorem oneCochainLinear_tmul (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a b c : R) :
    oneCochainLinear k R h z (a ⊗ₜ[k] (b ⊗ₜ[k] c)) = a * z b * h.symm c := by
  exact (mul_assoc _ _ _).symm

theorem oneCochainLinear_left (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a : R)
    (x : object k R 2) :
    oneCochainLinear k R h z (left k R 2 a x) = a * oneCochainLinear k R h z x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul b x => exact mul_assoc _ _ _

theorem oneCochainLinear_right (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a : R)
    (x : object k R 2) :
    oneCochainLinear k R h z (right k R 2 (MulOpposite.op (h a)) x) =
      oneCochainLinear k R h z x * a := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul b x =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy, add_mul]
    | tmul c d =>
      change b * (z c * h.symm (d * h a)) = b * (z c * h.symm d) * a
      rw [map_mul, h.symm_apply_apply]
      simp only [mul_assoc]

def oneCochain (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) :
    twistedObject k R h 2 →ₗ[Enveloping k R] moduleObject k R 0 :=
  twistedToOrdinary k R h (oneCochainLinear k R h z)
    (oneCochainLinear_left k R h z) (oneCochainLinear_right k R h z)

theorem oneCochain_boundary_tmul (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a b c d : R) :
    oneCochainLinear k R h z (boundary k R 2 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d)))) =
      a * (b * z c + z (b * c) + z b * h.symm c) * h.symm d := by
  simp only [boundary_succ_tmul k R 1, boundary_succ_tmul k R 0,
    boundary_zero_tmul k R, left_tmul k R 1, left_tmul k R 0,
    TensorProduct.tmul_add, map_add, oneCochainLinear_tmul k R h z,
    map_mul, mul_add, add_mul, mul_assoc, add_assoc]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TBoundaryCochain
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

def Z (H : kˣ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 2 →ₗ[AbsoluteBar.Enveloping k R]
      AbsoluteBar.moduleObject k R 0 :=
  AbsoluteBar.oneCochain k R (TrivialExtension.twist H) (CocycleData.z q H)

theorem casimirMap_right (H : kˣ) (a : R) :
    AbsoluteBar.casimirMap k R (twistedCasimir q H) a =
      AbsoluteBar.right k R 1 (MulOpposite.op ((TrivialExtension.twist H).symm a))
        (twistedCasimir q H) := by
  have hh := twistedCasimir_equivariant q H ((TrivialExtension.twist H).symm a)
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh

theorem pB_bottom_tmul (H : kˣ) (a b c d : R) :
    AbsoluteBar.cochain3Linear k R (CocycleData.p q)
      (AbsoluteBar.casimirInsertion k R (twistedCasimir q H) 3
        (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d)))) =
      a * (∑ i : TIndex, CocycleData.p q b c (TrivialExtension.twist H (vector q i)) *
        vector q i.star) * (TrivialExtension.twist H).symm d := by
  change AbsoluteBar.cochain3Linear k R (CocycleData.p q)
    (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] AbsoluteBar.casimirMap k R (twistedCasimir q H) d))) = _
  rw [casimirMap_right]
  simp only [twistedCasimir, map_sum, AbsoluteBar.right_tmul k R 0,
    AbsoluteBar.right_zero k R, MulOpposite.unop_op,
    TensorProduct.tmul_sum, AbsoluteBar.cochain3Linear_tmul k R (CocycleData.p q)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorHighLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)
local notation "D" => productTwoConeData q

theorem tensorHighB_second (n : ℕ) :
    ((D).second (n+2)).comp (tensorHighB q H (n+1)) = 0 :=
  ExternalTensor.secondCubic_bottomMap k Te Te P₀ Q₀ P₀ Q₀ (barComparison q)
    (n+4) (n+2) (barB q H (n+4)) (barDb q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (τ : FrobeniusTrace k R) {M N : FiniteLeftModule k R}

def resolutionIso (e : M.carrier ≃ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) where
  hom := (HomotopyCategory.quotient _ _).map (resolutionMap τ e.toLinearMap)
  inv := (HomotopyCategory.quotient _ _).map (resolutionMap τ e.symm.toLinearMap)
  hom_inv_id := by
    rw [← resolutionMap_comp, e.symm_comp, resolutionMap_id]
  inv_hom_id := by
    rw [← resolutionMap_comp, e.comp_symm, resolutionMap_id]

@[simp]
theorem resolutionIso_hom (e : M.carrier ≃ₗ[R] N.carrier) :
    (resolutionIso τ e).hom = (HomotopyCategory.quotient _ _).map (resolutionMap τ e.toLinearMap) := rfl

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_FiniteStableResolutionIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def resolutionHomotopyEquiv :
    ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ)) ≃+
    StableHom R M.carrier N.carrier :=
  (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      (((StableIsomorphism.ofLinearEquiv (M.completeCochainCokernelEquiv τ).symm).sourceAddEquiv).trans
        ((StableIsomorphism.ofLinearEquiv (N.completeCochainCokernelEquiv τ)).targetAddEquiv))

@[simp] theorem resolutionHomotopyEquiv_map (f : M.carrier →ₗ[R] N.carrier) :
    resolutionHomotopyEquiv τ M N ((HomotopyCategory.quotient _ _).map (resolutionMap τ f)) =
      StableHom.classOf R _ _ f := by
  simp only [resolutionHomotopyEquiv, AddEquiv.trans_apply, cochainHomotopyRawEquiv_map,
    resolutionMap_cokernel, StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, StableHom.comp_classOf]
  congr 1
  ext x
  simp [resolutionCokernelMap]

variable {M N} {P : FiniteLeftModule k R}

theorem resolutionHomotopyEquiv_comp
    (f : (HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ))
    (g : (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj (P.completeCochain τ)) :
    resolutionHomotopyEquiv τ M P (f ≫ g) =
      StableHom.comp (resolutionHomotopyEquiv τ N P g) (resolutionHomotopyEquiv τ M N f) := by
  obtain ⟨f, rfl⟩ := resolutionMap_surjective τ f
  obtain ⟨g, rfl⟩ := resolutionMap_surjective τ g
  rw [← resolutionMap_comp, resolutionHomotopyEquiv_map, resolutionHomotopyEquiv_map,
    resolutionHomotopyEquiv_map, StableHom.comp_classOf]

@[simp] theorem resolutionHomotopyEquiv_id :
    resolutionHomotopyEquiv τ M M (𝟙 _) = StableHom.identity := by
  rw [← resolutionMap_id (M := M) τ, resolutionHomotopyEquiv_map]
  rfl

def stableResolutionIso (e : StableIsomorphism R M.carrier N.carrier) :
    (HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) where
  hom := (resolutionHomotopyEquiv τ M N).symm e.hom
  inv := (resolutionHomotopyEquiv τ N M).symm e.inv
  hom_inv_id := by
    apply (resolutionHomotopyEquiv τ M M).injective
    rw [resolutionHomotopyEquiv_comp, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, resolutionHomotopyEquiv_id, e.hom_inv_id]
  inv_hom_id := by
    apply (resolutionHomotopyEquiv τ N N).injective
    rw [resolutionHomotopyEquiv_comp, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, resolutionHomotopyEquiv_id, e.inv_hom_id]

@[simp] theorem stableResolutionIso_hom (e : StableIsomorphism R M.carrier N.carrier) :
    resolutionHomotopyEquiv τ M N (stableResolutionIso τ e).hom = e.hom :=
  AddEquiv.apply_symm_apply _ _

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FiniteFullHomZero
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]

namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

def fullCokernelEquiv : Cokernel (chainOfCochain (M.completeCochain τ)) 0 ≃ₗ[R] M.carrier :=
  (cochainCokernelLinearEquiv _).trans (M.completeCochainCokernelEquiv τ)

end FiniteLeftModule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

theorem homShort_outgoing (n : ℕ) :
    (homShort k R (Y := Y) P n).g =
      ModuleCat.ofHom (LinearMap.lcomp k Y (P.complex.d (n+1) n).hom) :=
  homCochain_d k R P.complex Y n

end ArExplicit.ExternalTensor

end

end OAI
end


