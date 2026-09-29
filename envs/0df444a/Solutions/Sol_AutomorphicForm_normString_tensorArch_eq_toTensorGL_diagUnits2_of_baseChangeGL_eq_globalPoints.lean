-- Prove2me | solution 1 for AutomorphicForm.normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/69919b34-a668-55e5-a58f-124e3e8294b2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t)
    (hα : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ≠ 0)
    (hβ : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0) :
    AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (diagUnits2
          (Units.map (algebraMap K (InfiniteAdeleRing K) : K →* InfiniteAdeleRing K)
            (Units.mk0 _ hα))
          (Units.map (algebraMap K (InfiniteAdeleRing K) : K →* InfiniteAdeleRing K)
            (Units.mk0 _ hβ))) := by
  obtain ⟨γ, hγ10, hγ01, hγ00, hγ11, hN⟩ :=
    AutomorphicForm.exists_diagonal_normString_eq_toTensorGL_globalPoints_of_baseChangeGL_eq_globalPoints
      K L σ hgen t ht₁ ht₂ δ hδ

  have hcomm : AutomorphicForm.tensorArch K L (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) =
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) := by
    simp only [AutomorphicForm.normString, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    exact Function.Semiconj.iterate_right
      (f := ⇑(AutomorphicForm.tensorArch K L))
      (ga := ⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))
      (gb := ⇑(AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ))
      (fun x => AutomorphicForm.tensorArch_sigmaGL K L σ x) i δ
  rw [← hcomm, hN, AutomorphicForm.tensorArch_toTensorGL]
  congr 1
  have hent : ∀ i j : Fin 2,
      ((NumberField.AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.globalPoints (𝓞 K) K γ) :
          GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
        algebraMap K (InfiniteAdeleRing K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [hent]
  fin_cases i <;> fin_cases j <;>
    simp [hγ10, hγ01, hγ00, hγ11, LanglandsTunnell.CubicInduction.coe_diagUnits2]

end S_AutomorphicForm_normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints
end P2MW
export P2MW.S_AutomorphicForm_normString_tensorArch_eq_toTensorGL_diagUnits2_of_baseChangeGL_eq_globalPoints (solution)
