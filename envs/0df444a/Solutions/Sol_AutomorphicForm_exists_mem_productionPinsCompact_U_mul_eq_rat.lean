-- Prove2me | solution 1 for AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9549d40f-3753-5e9f-a465-45dac79d4de4

import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat

set_option autoImplicit false

noncomputable section

namespace M4aP1R
namespace LevelCoveringDecomp

open Matrix NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem exists_mem_productionPinsCompact_U_mul_eq_rat_impl
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      u ∈ (productionPinsCompact ℚ).U N ∧
        glFin (𝓞 ℚ) ℚ h = 1 ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = globalPoints (𝓞 ℚ) ℚ γ * h * u := by
  obtain ⟨γ, hmem, hpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := globalPoints (𝓞 ℚ) ℚ γ * g with hg'
  set u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g') with hu
  refine ⟨γ⁻¹, g' * u⁻¹, u, ?_, ?_, ?_, ?_⟩
  ·
    rw [productionPinsCompact_U, Subgroup.mem_inf, hu, AdelicDock.finEmbed_mem_levelOne_iff,
      mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
    exact ⟨(mem_levelOne_iff).mp hmem, rfl⟩
  ·
    rw [map_mul, map_inv, hu, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  ·
    intro w hw
    rw [map_mul, map_inv, hu, AdelicDock.glArch_finEmbed, inv_one, mul_one]
    exact hpos w hw
  ·
    rw [mul_assoc, inv_mul_cancel_right, map_inv, hg', inv_mul_cancel_left]

end M4aP1R.LevelCoveringDecomp

theorem solution
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ)
      (h u : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      u ∈ (AutomorphicForm.productionPinsCompact ℚ).U N ∧
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 ∧
        (∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * h * u := by
  first
    | exact M4aP1R.LevelCoveringDecomp.exists_mem_productionPinsCompact_U_mul_eq_rat_impl hN g
    | (apply M4aP1R.LevelCoveringDecomp.exists_mem_productionPinsCompact_U_mul_eq_rat_impl <;> assumption)

end
end S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat (solution)
