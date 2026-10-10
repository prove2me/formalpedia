-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityDiscountedShock_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:27:01.396991+00:00
-- url     : https://prove2.me/submissions/a16541ee-75d0-425d-9d07-e4303e65e988

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
import Definitions.Def_actuarial_finiteMortalityVariance
import Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_orthogonal
import Theorems.Thm_ActuarialValuation_finiteMortalityInnovation_secondMoment
import Theorems.Thm_ActuarialValuation_finiteMortalityDiscountedShock_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (n : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
  :
  finiteMortalityVariance w (finiteMortalityDiscountedShock w K ρ n) =
    ∑ t ∈ Finset.range n, (ρ t) ^ 2 *
      finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by
  let f : ℕ → Ω → ℝ := fun t ω => ρ t * finiteMortalityInnovation w K t ω
  have hmean : (∑ ω : Ω, w ω * finiteMortalityDiscountedShock w K ρ n ω) = 0 :=
    finiteMortalityDiscountedShock_mean_zero w K ρ n hS
  have hpair (i j : ℕ) (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n)
      (hij : i ≠ j) :
      (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω *
        finiteMortalityInnovation w K j ω) = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact finiteMortalityInnovation_orthogonal w K i j hlt (hS j hj)
    · calc
        (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω *
          finiteMortalityInnovation w K j ω) =
          (∑ ω : Ω, w ω * finiteMortalityInnovation w K j ω *
            finiteMortalityInnovation w K i ω) := by
              apply Finset.sum_congr rfl
              intro ω _
              ring
        _ = 0 := finiteMortalityInnovation_orthogonal w K j i hgt (hS i hi)
  have hdiag (t : ℕ) (ht : t ∈ Finset.range n) :
      (∑ ω : Ω, w ω * f t ω * f t ω) =
        (ρ t) ^ 2 * finiteMortalityDeathMass w K t *
          finiteMortalitySurvivalRate w K t := by
    calc
      (∑ ω : Ω, w ω * f t ω * f t ω) =
        (ρ t) ^ 2 *
          (∑ ω : Ω, w ω * (finiteMortalityInnovation w K t ω) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω _
            dsimp [f]
            ring
      _ = (ρ t) ^ 2 * finiteMortalityDeathMass w K t *
          finiteMortalitySurvivalRate w K t := by
            rw [finiteMortalityInnovation_secondMoment w K t hw (hS t ht)]
            ring
  have hoff (i j : ℕ) (hi : i ∈ Finset.range n) (hj : j ∈ Finset.range n)
      (hij : i ≠ j) :
      (∑ ω : Ω, w ω * f i ω * f j ω) = 0 := by
    calc
      (∑ ω : Ω, w ω * f i ω * f j ω) =
        ρ i * ρ j *
          (∑ ω : Ω, w ω * finiteMortalityInnovation w K i ω *
            finiteMortalityInnovation w K j ω) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ω _
              dsimp [f]
              ring
      _ = 0 := by rw [hpair i j hi hj hij]; ring
  have hsum :
      (∑ ω : Ω, w ω * (∑ t ∈ Finset.range n, f t ω) ^ 2) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (∑ ω : Ω, w ω * f i ω * f j ω) := by
    calc
      (∑ ω : Ω, w ω * (∑ t ∈ Finset.range n, f t ω) ^ 2) =
        ∑ ω : Ω, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          w ω * f i ω * f j ω := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [pow_two, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (∑ ω : Ω, w ω * f i ω * f j ω) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
  have hdouble :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (∑ ω : Ω, w ω * f i ω * f j ω)) =
        ∑ i ∈ Finset.range n,
          (ρ i) ^ 2 * finiteMortalityDeathMass w K i *
            finiteMortalitySurvivalRate w K i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ j ∈ Finset.range n, (∑ ω : Ω, w ω * f i ω * f j ω)) =
        ∑ j ∈ Finset.range n, if j = i then
          (ρ i) ^ 2 * finiteMortalityDeathMass w K i *
            finiteMortalitySurvivalRate w K i else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hij : i = j
              · subst j
                simpa using hdiag i hi
              · have hji : j ≠ i := Ne.symm hij
                simp only [if_neg hji]
                exact hoff i j hi hj hij
      _ = (ρ i) ^ 2 * finiteMortalityDeathMass w K i *
            finiteMortalitySurvivalRate w K i := by simp [hi]
  change (∑ ω : Ω,
    w ω * (finiteMortalityDiscountedShock w K ρ n ω -
      (∑ a : Ω, w a * finiteMortalityDiscountedShock w K ρ n a)) ^ 2) =
      ∑ t ∈ Finset.range n,
        (ρ t) ^ 2 * finiteMortalityDeathMass w K t *
          finiteMortalitySurvivalRate w K t
  rw [hmean]
  simp only [sub_zero]
  change (∑ ω : Ω, w ω * (∑ t ∈ Finset.range n, f t ω) ^ 2) =
    ∑ t ∈ Finset.range n,
      (ρ t) ^ 2 * finiteMortalityDeathMass w K t *
        finiteMortalitySurvivalRate w K t
  exact hsum.trans hdouble
