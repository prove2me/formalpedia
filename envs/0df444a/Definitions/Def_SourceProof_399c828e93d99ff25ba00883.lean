-- Prove2me | Definitions.Def_SourceProof_399c828e93d99ff25ba00883
-- name    : SourceProof_399c828e93d99ff25ba00883
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:14:30.064469+00:00
-- url     : https://prove2.me/theorems/dcbb136d-33e4-414d-bcc7-8eefa09768e3
-- title:
--   LevyStochCalc source module: SourceProof_399c828e93d99ff25ba00883
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markSumProcess_isometry` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
import Definitions.Def_SourceProof_115508132628c570aa207f8e
import Definitions.Def_SourceProof_f869d2367bb5fe9e2110213a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_399c828e93d99ff25ba00883
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ i : Fin N₀, ∑ k : Fin K,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hlt : ∀ i : Fin N₀, p i.castSucc < p i.succ := fun i => hpmono Fin.castSucc_lt_succ
  -- mark-sum at time-piece `i`.
  set S : Fin N₀ → Ω → ℝ := fun i ω =>
    ∑ k : Fin K, ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω with hSdef
  -- integrability of `Sᵢ · Sᵢ'` (finite sum of integrable cross terms).
  have hSS : ∀ i i', MeasureTheory.Integrable (fun ω => S i ω * S i' ω) P := by
    intro i i'
    have hbox : ∀ (j : Fin N₀) (k : Fin K),
        MeasurableSet (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ B k) :=
      fun j k => measurableSet_Ioc.prod (hBm k)
    have hboxf : ∀ (j : Fin N₀) (k : Fin K),
        LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ B k) ≠ ⊤ :=
      fun j k => LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top (hBf k)
    have hterm : ∀ k l, MeasureTheory.Integrable
        (fun ω => (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
          * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω)) P := by
      intro k l
      obtain ⟨Mk, hMk⟩ := hξb i k
      obtain ⟨Ml, hMl⟩ := hξb i' l
      have hcross := _root_.Prove2MeSourceProof.h_839c3c586f330ad57afd5326 N (hbox i k) (hbox i' l)
        (hboxf i k) (hboxf i' l)
      rw [show (fun ω => (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
            * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω))
          = (fun ω => (ξ i k ω * ξ i' l ω)
            * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω
              * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω))
          from funext (fun ω => by ring)]
      refine hcross.bdd_mul (c := Mk * Ml) ((hξm i k).mul (hξm i' l)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMk ω) (hMl ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
    rw [show (fun ω => S i ω * S i' ω)
        = fun ω => ∑ k : Fin K, ∑ l : Fin K,
            (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
            * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω) from
      funext (fun ω => by rw [hSdef]; exact Finset.sum_mul_sum _ _ _ _)]
    exact MeasureTheory.integrable_finsetSum _
      (fun k _ => MeasureTheory.integrable_finsetSum _ (fun l _ => hterm k l))
  -- expand `(∑ᵢ Sᵢ)²` and integrate.
  rw [show (fun ω => (∑ i : Fin N₀, ∑ k : Fin K,
          ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2)
      = fun ω => ∑ i : Fin N₀, ∑ i' : Fin N₀, S i ω * S i' ω from
    funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun i' _ => hSS i i'))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun i' _ => hSS i i'), Finset.sum_eq_single i]
  · -- diagonal `i' = i`: `∫ Sᵢ² = markSum_sq_sametime`.
    rw [show (fun ω => S i ω * S i ω) = fun ω => (S i ω) ^ 2 from funext (fun ω => (sq _).symm)]
    exact _root_.Prove2MeSourceProof.h_115508132628c570aa207f8e N ℱ hℱ (hpnn _) (hlt i) B hBm hBf (fun k => ξ i k)
      (fun k => hξb i k) (fun k => hξm i k) (fun k => h_adapt i k)
  · -- off-diagonal `i' ≠ i`: time-ordered, vanishes.
    intro i' _ hi'
    rcases lt_trichotomy i i' with hlt' | hlt' | hlt'
    · have hbc : p i.succ ≤ p i'.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt')
      exact _root_.Prove2MeSourceProof.h_f869d2367bb5fe9e2110213a N ℱ hℱ (hpnn _) (hlt i) hbc (hlt i') B hBm hBf
        (fun k => ξ i k) (fun k => ξ i' k) (fun k => hξb i k) (fun k => hξb i' k)
        (fun k => hξm i k) (fun k => hξm i' k) (fun k => h_adapt i k) (fun k => h_adapt i' k)
    · exact absurd hlt' hi'.symm
    · have hbc : p i'.succ ≤ p i.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt')
      rw [show (fun ω => S i ω * S i' ω) = fun ω => S i' ω * S i ω from funext (fun ω => by ring)]
      exact _root_.Prove2MeSourceProof.h_f869d2367bb5fe9e2110213a N ℱ hℱ (hpnn _) (hlt i') hbc (hlt i) B hBm hBf
        (fun k => ξ i' k) (fun k => ξ i k) (fun k => hξb i' k) (fun k => hξb i k)
        (fun k => hξm i' k) (fun k => hξm i k) (fun k => h_adapt i' k) (fun k => h_adapt i k)
  · intro h; exact absurd (Finset.mem_univ i) h
end LevyStochCalc.Poisson.Compensated


