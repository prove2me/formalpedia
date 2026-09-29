-- Prove2me | solution 1 for AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a74b70a4-6725-56ae-818d-1d082e606ca5

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

noncomputable section

namespace CompactLevel

variable (F : Type) [Field F] [NumberField F]

theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  have hval : ∀ {φ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)},
      Continuous φ → Continuous fun g => AdelicDock.finMat (𝓞 F) F (φ g) := by
    intro φ hφ
    refine continuous_matrix fun i j => ?_
    show Continuous fun g => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, φ g i j) : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (hφ.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hval Units.continuous_val
  · exact hval Units.continuous_coe_inv

theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem coe_levelOne_inf_finiteAdelicGL2Subgroup (N : Ideal (𝓞 F)) :
    ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) =
      AdelicDock.finEmbed (𝓞 F) F '' (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_image]
  constructor
  · rintro ⟨hl, hf⟩
    refine ⟨glFin (𝓞 F) F g, mem_levelOne_iff.mp hl, ?_⟩
    refine eq_of_glArch_eq_of_glFin_eq F ?_ ?_
    · rw [AdelicDock.glArch_finEmbed, (mem_finiteAdelicGL2Subgroup_iff F g).mp hf]
    · rw [AdelicDock.glFin_finEmbed]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F k).mpr hk,
      (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F k)⟩

end CompactLevel

end

theorem solution
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  rw [CompactLevel.coe_levelOne_inf_finiteAdelicGL2Subgroup]
  exact (isCompact_finiteLevelOne (𝓞 F) F N).image (CompactLevel.continuous_finEmbed F)

end S_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
end P2MW
export P2MW.S_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup (solution)
