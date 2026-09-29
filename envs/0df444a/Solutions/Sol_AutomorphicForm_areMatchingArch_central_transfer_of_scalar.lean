-- Prove2me | solution 1 for AutomorphicForm.areMatchingArch_central_transfer_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/251a1647-c1e4-506e-a994-944c551b499d

import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_areMatchingArch_central_transfer_of_scalar
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (hm : AutomorphicForm.AreMatchingArch K L σ φa fa) :
    (∀ γ : GL (Fin 2) (InfiniteAdeleRing K),
      (∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
        (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ →
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' →
        ∀ I I' : ℂ,
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
            (φa ∘ AutomorphicForm.archIdentGL K L) I' →
          AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) γ τ fa I →
          I' = I) :=
  AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom
    K L hprime σ hgen φa hφa fa hfa hm
    (fun μA μL hμA hμL φ hφ f hf c hc hmatch =>
      AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos
        μA μL hμA hμL φ hφ f hf c hc hmatch)
    (fun hσ _ ι μA hμA μL hμL φ hφ f hf c hmatch =>
      AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
        K L hprime σ hσ ι μA hμA μL hμL φ hφ f hf c hmatch)
    (fun hσ _ ι μA hμA μL hμL φ hφ f hf c hmatch =>
      AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
        K L hprime σ hσ ι μA hμA μL hμL φ hφ f hf c hmatch)

end S_AutomorphicForm_areMatchingArch_central_transfer_of_scalar
end P2MW
export P2MW.S_AutomorphicForm_areMatchingArch_central_transfer_of_scalar (solution)
