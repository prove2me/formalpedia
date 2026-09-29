-- Prove2me | solution 1 for AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e978e3ec-a1eb-5413-a8fb-758eb345691c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

namespace ContNormDet

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def algRK : Algebra ℝ (InfiniteAdeleRing K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

noncomputable def algRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
      mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) := by
  refine continuous_pi fun v => ?_
  by_cases hv : v.IsReal
  · have h : ∀ y : mixedEmbedding.mixedSpace K, (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v =
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      intro y
      have e : InfinitePlace.Completion.ringEquivRealOfIsReal hv
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.1 ⟨v, hv⟩ :=
        congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
      rw [← e]
      exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm_apply_apply _).symm
    rw [show (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) from funext h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h : ∀ y : mixedEmbedding.mixedSpace K, (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v =
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) := by
      intro y
      have e : InfinitePlace.Completion.ringEquivComplexOfIsComplex hv'
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.2 ⟨v, hv'⟩ :=
        congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hv'⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
      rw [← e]
      exact ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm_apply_apply _).symm
    rw [show (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) from funext h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

noncomputable def algEquivK :
    letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
    InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
  AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) (fun r => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _)

end ContNormDet

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    IsScalarTower ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) ∧
    Module.Finite ℝ (InfiniteAdeleRing K) ∧ Module.Finite ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (algebraMap ℝ (InfiniteAdeleRing K)) ∧
    ContinuousSMul ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) ∧
    Continuous (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => Algebra.norm ℝ X.det) := by
  letI iRK : Algebra ℝ (InfiniteAdeleRing K) := ContNormDet.algRK K
  letI iRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) := ContNormDet.algRE K L
  show IsScalarTower ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) ∧
    Module.Finite ℝ (InfiniteAdeleRing K) ∧ Module.Finite ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (algebraMap ℝ (InfiniteAdeleRing K)) ∧
    ContinuousSMul ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) ∧
    Continuous (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => Algebra.norm ℝ X.det)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI hfinK : Module.Finite ℝ (InfiniteAdeleRing K) :=
    Module.Finite.equiv (ContNormDet.algEquivK K).symm.toLinearEquiv
  haveI hST : IsScalarTower ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
    @IsScalarTower.of_algebraMap_eq ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) _ _ _
      iRK inferInstance iRE (fun r => rfl)
  haveI hfinE : Module.Finite ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    Module.Finite.trans (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have hcont_alg : Continuous (algebraMap ℝ (InfiniteAdeleRing K)) := by
    show Continuous (fun r : ℝ => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace K) r))
    exact (ContNormDet.continuous_ringEquiv_mixedSpace_symm K).comp
      (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K))
  haveI : ContinuousSMul (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
    IsModuleTopology.toContinuousSMul (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI hsmul : ContinuousSMul ℝ (L ⊗[K] InfiniteAdeleRing K) := by
    refine ⟨?_⟩
    have : (fun p : ℝ × (L ⊗[K] InfiniteAdeleRing K) => p.1 • p.2) =
        fun p => (algebraMap ℝ (InfiniteAdeleRing K) p.1) • p.2 := by
      funext p; exact (algebraMap_smul (InfiniteAdeleRing K) p.1 p.2).symm
    rw [this]
    exact (hcont_alg.comp continuous_fst).smul continuous_snd
  haveI : IsTopologicalAddGroup (L ⊗[K] InfiniteAdeleRing K) := inferInstance
  have hnorm : Continuous (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) := by
    let b := Module.finBasis ℝ (L ⊗[K] InfiniteAdeleRing K)
    have : (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) =
        fun s => (Algebra.leftMulMatrix b s).det := funext (Algebra.norm_eq_matrix_det b)
    rw [this]
    exact ((Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional).matrix_det
  exact ⟨hST, hfinK, hfinE, hcont_alg, hsmul, hnorm, hnorm.comp (continuous_id.matrix_det)⟩

end S_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
end P2MW
export P2MW.S_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det (solution)
