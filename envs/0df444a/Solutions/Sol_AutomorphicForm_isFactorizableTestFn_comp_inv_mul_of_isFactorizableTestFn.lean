-- Prove2me | solution 1 for AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0673e8ee-97f0-575a-8c8c-8166bfbf9dfa

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn

open NumberField
open scoped Classical
open IsDedekindDomain AutomorphicForm

namespace TierTranslate

private theorem archEntries_mul (K : Type) [Field K] (a h : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    archEntries K (a * h) i j = ∑ k : Fin 2, archEntries K a i k * archEntries K h k j := by
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

private theorem isArchTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (a : GL (Fin 2) (InfiniteAdeleRing K)) : IsArchTestFactor K (fun h => fa (a * h)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun X => Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * X k j), ?_, ?_⟩, ?_⟩
  · exact hΦ.comp (by fun_prop)
  · intro h
    show fa (a * h) = Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * archEntries K h k j)
    rw [hfaΦ]
    congr 1
    funext i j
    exact archEntries_mul K a h i j
  · exact hsupp.comp_homeomorph (Homeomorph.mulLeft a)

private theorem isFinTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff)
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : IsFinTestFactor K (fun h => ff (b * h)) :=
  ⟨hff.1.comp_continuous (continuous_const_mul b), hff.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

end TierTranslate

open TierTranslate in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by
  obtain ⟨fa, ff, hfa, hff, hfx⟩ := hf
  refine ⟨fun h => fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * h),
    fun h => ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * h),
    isArchTestFactor_comp_mul_left K hfa _, isFinTestFactor_comp_mul_left K hff _, ?_⟩
  intro y
  show f (t⁻¹ * y) = fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * AdelicLevel.glArch (𝓞 K) K y) *
    ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * AdelicLevel.glFin (𝓞 K) K y)
  rw [hfx (t⁻¹ * y), map_mul (AdelicLevel.glArch (𝓞 K) K) t⁻¹ y,
    map_mul (AdelicLevel.glFin (𝓞 K) K) t⁻¹ y]

end S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn (solution)
