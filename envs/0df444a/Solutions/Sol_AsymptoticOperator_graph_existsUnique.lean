-- Prove2me | solution 1 for AsymptoticOperator.graph_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T11:39:24.669017+00:00
-- url     : https://prove2.me/submissions/f988cc84-47e3-4013-aeaf-13beeda4c3e8

import Theorems.Thm_AsymptoticOperator_eq_zero_of_coeff_eq_zero
import Theorems.Thm_AsymptoticOperator_graphSet_add_mem
import Theorems.Thm_AsymptoticOperator_graphSet_smul_mem

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

lemma ao_coeff_zero {n : ℕ} : coeff ((0 : L2 n) : UnitAddCircle → Vec n) = 0 := by
  funext k
  simp only [coeff]
  rw [fourierCoeff_congr_ae (g := fun _ => 0)]
  · simp [fourierCoeff]
  · filter_upwards [Lp.coeFn_zero (Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)]
      with t ht
    rw [ht]; funext i; simp [complexify]

lemma ao_coeffMul_zero {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    coeffMul S ((0 : L2 n) : UnitAddCircle → Vec n) = 0 := by
  funext k
  simp only [coeffMul]
  rw [fourierCoeff_congr_ae (g := fun _ => 0)]
  · simp [fourierCoeff]
  · filter_upwards [Lp.coeFn_zero (Vec n) 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)]
      with t ht
    have : complexify (0 : Vec n) = 0 := by funext i; simp [complexify]
    rw [ht]; simp [this]

lemma ao_action_zero_rhs {n : ℕ} (S : C(UnitAddCircle, Mat n)) (k : ℤ) :
    -((2 * Real.pi * k : ℝ) * Complex.I) •
        ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeff ((0 : L2 n) : UnitAddCircle → Vec n) k) -
      coeffMul S ((0 : L2 n) : UnitAddCircle → Vec n) k = 0 := by
  rw [ao_coeff_zero, ao_coeffMul_zero]
  simp

/-- The graph set as a submodule. -/
noncomputable def ao_graphSubmodule {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    Submodule ℝ (L2 n × L2 n) where
  carrier := graphSet S
  zero_mem' := by
    refine ⟨?_, fun k => ?_⟩
    · show Summable fun k : ℤ =>
        (1 + (k : ℝ) ^ 2) * ∑ i, ‖coeff ((0 : L2 n) : UnitAddCircle → Vec n) k i‖ ^ 2
      rw [ao_coeff_zero]
      simp
    · simp only [Prod.fst_zero, Prod.snd_zero]
      rw [ao_action_zero_rhs S k]
      exact congrFun ao_coeff_zero k
  add_mem' := graphSet_add_mem S
  smul_mem' := graphSet_smul_mem S

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) :
    ∃! A : L2 n →ₗ.[ℝ] L2 n, (A.graph : Set (L2 n × L2 n)) = graphSet S := by
  have hg : ∀ (x : L2 n × L2 n) (_hx : x ∈ ao_graphSubmodule S) (_hx' : x.fst = 0),
      x.snd = 0 := by
    rintro ⟨f, g⟩ hx (rfl : f = 0)
    apply eq_zero_of_coeff_eq_zero
    intro k
    have e := hx.2 k
    simp only at e
    rw [e]
    exact ao_action_zero_rhs S k
  refine ⟨(ao_graphSubmodule S).toLinearPMap, ?_, fun A hA => ?_⟩
  · show (((ao_graphSubmodule S).toLinearPMap.graph : Submodule ℝ _) :
        Set (L2 n × L2 n)) = _
    rw [Submodule.toLinearPMap_graph_eq _ hg]; rfl
  · apply LinearPMap.eq_of_eq_graph
    rw [Submodule.toLinearPMap_graph_eq _ hg]
    exact SetLike.coe_injective hA
