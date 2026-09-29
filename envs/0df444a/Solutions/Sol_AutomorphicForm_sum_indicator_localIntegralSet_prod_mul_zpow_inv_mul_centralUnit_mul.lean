-- Prove2me | solution 1 for AutomorphicForm.sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/614399c5-23b1-58e4-b4c0-57bbf4715070

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K)) (k j : ℕ)
    (c : GL (Fin 2) (v.adicCompletion K))
    (hc : ∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
      (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (y : GL (Fin 2) (v.adicCompletion K)) :
    (∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (c * y))) =
      ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * y)  := by
  classical
  obtain ⟨ε, hε, hcε⟩ := hc
  have hε0 : ε ≠ 0 := fun h => by rw [h, map_zero] at hε; exact zero_ne_one hε

  have hcomm : ∀ g : GL (Fin 2) (v.adicCompletion K), g * c = c * g := by
    intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hcε, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

  have hcinv : ((c⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ε⁻¹ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    have h1 : ((c⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((c⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
        = ((c⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
            ((c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * (ε⁻¹ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) := by
          rw [hcε, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hε0, one_smul, Matrix.mul_one]
      _ = ε⁻¹ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

  have hεO : ε ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hε]
  have hεO' : ε⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hε, inv_one]
  have hcK : c ∈ AutomorphicForm.localIntegralSet K v := by
    rw [AutomorphicForm.mem_localIntegralSet]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [hcε, Matrix.smul_apply, Matrix.one_apply]
      split_ifs
      · rw [smul_eq_mul, mul_one]; exact hεO
      · rw [smul_zero]; exact zero_mem _
    · rw [hcinv, Matrix.smul_apply, Matrix.one_apply]
      split_ifs
      · rw [smul_eq_mul, mul_one]; exact hεO'
      · rw [smul_zero]; exact zero_mem _
  have hcK' : c⁻¹ ∈ AutomorphicForm.localIntegralSet K v := ⟨hcK.2, by rw [inv_inv]; exact hcK.1⟩

  have hmulmat : ∀ {M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)},
      M ∈ AutomorphicForm.integralMatrixSet (v.adicCompletionIntegers K : Set (v.adicCompletion K)) →
      N ∈ AutomorphicForm.integralMatrixSet (v.adicCompletionIntegers K : Set (v.adicCompletion K)) →
      M * N ∈ AutomorphicForm.integralMatrixSet (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro M N hM hN i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem (mul_mem (hM i 0) (hN 0 j)) (mul_mem (hM i 1) (hN 1 j))
  have hmul : ∀ {g h : GL (Fin 2) (v.adicCompletion K)}, g ∈ AutomorphicForm.localIntegralSet K v →
      h ∈ AutomorphicForm.localIntegralSet K v → g * h ∈ AutomorphicForm.localIntegralSet K v := by
    intro g h hg hh
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact hmulmat hg.1 hh.1
    · rw [mul_inv_rev, Units.val_mul]; exact hmulmat hh.2 hg.2
  have hiff : ∀ g : GL (Fin 2) (v.adicCompletion K),
      c * g ∈ AutomorphicForm.localIntegralSet K v ↔ g ∈ AutomorphicForm.localIntegralSet K v := by
    intro g
    constructor
    · intro h
      have := hmul hcK' h
      rwa [inv_mul_cancel_left] at this
    · exact hmul hcK
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [show ((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (c * y) = c * (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * y) by
    rw [← mul_assoc, hcomm, mul_assoc]]
  by_cases h : ((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * y ∈ AutomorphicForm.localIntegralSet K v
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hiff _).2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hiff _).1 h'))]

end S_AutomorphicForm_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul
end P2MW
export P2MW.S_AutomorphicForm_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul_centralUnit_mul (solution)
