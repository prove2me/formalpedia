-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointGrid_F001
-- name    : LevyStochCalc_Driver_JointGrid_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:49:36.475682+00:00
-- url     : https://prove2.me/theorems/43f127e5-6b4d-466c-9648-acb27fb2ec7d
-- title:
--   Source declarations: LevyStochCalc.Driver.JointGrid
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointGrid. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointGrid_F000
import Definitions.Def_SourceProof_9515dd3e42bfbfd6da3f4172
import Definitions.Def_SourceProof_c6ee0296156065258c568141

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint character of a grid of cells

Counts are additive over the cells of a grid, so the Poisson character at a grid point is the
product of the characters of the families cut by the cells. Pairing that product with the
character of the Brownian increments along the same grid gives the joint grid character, which
the induction of the joint predictable representation consumes one cell at a time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section CellFamily

end CellFamily

section JointGrid

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The joint character of the Brownian increments and the Poisson counts along the first `n`
cells of a grid. -/
noncomputable def jointGridCharacter (W : LevyStochCalc.Brownian.BrownianMotion P)
    (N : PoissonRandomMeasure P ν) (τ lam : ℕ → ℝ) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n,
    (Complex.exp (Complex.I * ((lam k * (W.W (τ (k + 1)) ω - W.W (τ k) ω) : ℝ) : ℂ))
      * charAt N w (cellFam Bfam τ k) (τ (k + 1)) ω)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_jointGridCharacter (W : LevyStochCalc.Brownian.BrownianMotion P)
    (N : PoissonRandomMeasure P ν) (τ lam : ℕ → ℝ) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (n : ℕ) (ω : Ω) : ‖jointGridCharacter W N τ lam w Bfam n ω‖ = 1 := by
  rw [jointGridCharacter, norm_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, charAt,
    Complex.norm_exp_I_mul_ofReal, one_mul]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The joint character of the first `n` cells is measurable for the filtration at the `n`-th
grid point. -/
theorem measurable_jointGridCharacter {W : LevyStochCalc.Brownian.BrownianMotion P}
    (hℱW : IsBrownianFiltration W ℱ) (N : PoissonRandomMeasure P ν)
    (hℱN : IsPoissonFiltration N ℱ) {τ : ℕ → ℝ} {n : ℕ}
    (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) (lam : ℕ → ℝ) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) :
    Measurable[ℱ (τ n)] (jointGridCharacter W N τ lam w Bfam n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have hk1 : τ (k + 1) ≤ τ n := grid_le hτ hkn (le_refl n)
  have hk0 : τ k ≤ τ n := grid_le hτ hkn.le (le_refl n)
  have hW1 : Measurable[ℱ (τ n)] (W.W (τ (k + 1))) :=
    (hℱW.measurable _).mono (ℱ.mono hk1) le_rfl
  have hW0 : Measurable[ℱ (τ n)] (W.W (τ k)) := (hℱW.measurable _).mono (ℱ.mono hk0) le_rfl
  have hbm : Measurable[ℱ (τ n)] fun ω =>
      Complex.exp (Complex.I * ((lam k * (W.W (τ (k + 1)) ω - W.W (τ k) ω) : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((hW1.sub hW0).const_mul (lam k))))
  have hcount : ∀ j : ι, Measurable[ℱ (τ n)] fun ω =>
      N.N ω (cellFam Bfam τ k j ∩ Set.Ioc (0 : ℝ) (τ (k + 1)) ×ˢ (Set.univ : Set E)) := by
    intro j
    refine (hℱN.measurable (t := τ (k + 1)) ?_ ?_).mono (ℱ.mono hk1) le_rfl
    · exact fun p hp => ⟨hp.2.1.2, Set.mem_univ _⟩
    · exact (measurableSet_cellFam hBm τ k j).inter
        (measurableSet_Ioc.prod MeasurableSet.univ)
  have hpm : Measurable[ℱ (τ n)] (charAt N w (cellFam Bfam τ k) (τ (k + 1))) := by
    refine Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ => ?_)))
    exact ((hcount j).ennreal_toReal).const_mul (w j)
  exact hbm.mul hpm
end JointGrid

section Induction

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

include hℱN hℱW in
/-- **The joint grid induction.** A real square-integrable weight of mean zero, orthogonal to
every Itô integral and every compensated integral, is orthogonal to the joint character of the
Brownian increments and the Poisson counts along any grid. -/
theorem pairing_jointGridCharacter_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (lam : ℕ → ℝ) :
    ∀ n : ℕ, (∀ k, k < n → τ k < τ (k + 1)) → τ n < T →
      ∫ ω, ((Z ω : ℝ) : ℂ) * jointGridCharacter W N τ lam w Bfam n ω ∂P = 0 := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have h1 : ∀ ω : Ω, ((Z ω : ℝ) : ℂ) * jointGridCharacter W N τ lam w Bfam 0 ω
          = ((Z ω : ℝ) : ℂ) := by
        intro ω; rw [jointGridCharacter]; simp
      simp_rw [h1]
      rw [show ∫ ω, ((Z ω : ℝ) : ℂ) ∂P = ((∫ ω, Z ω ∂P : ℝ) : ℂ) from integral_ofReal, hZ0]
      simp
  | succ n ih =>
      intro hlt hTn
      have hlt' : ∀ k, k < n → τ k < τ (k + 1) := fun k hk => hlt k (Nat.lt_succ_of_lt hk)
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt' k hk).le
      have hcell : τ n < τ (n + 1) := hlt n (Nat.lt_succ_self n)
      have hτn0 : 0 ≤ τ n := grid_nonneg hτ0 hle' (le_refl n)
      have hmeas := measurable_jointGridCharacter hℱW N hℱN hle' lam w hBm
      have hstep := _root_.Prove2MeSourceProof.h_c6ee0296156065258c568141 N hℱN W hℱW hℱ0 hnull hτn0 hcell (lam n)
        hT hTn hA hAν w (measurableSet_cellFam hBm τ n)
        (cellFam_subset hBsub τ n) he₀ hZ2 hZito hZcomp
        (V := jointGridCharacter W N τ lam w Bfam n) hmeas.stronglyMeasurable
        (Mv := 1) zero_le_one
        (fun ω => le_of_eq (norm_jointGridCharacter W N τ lam w Bfam n ω))
        (ih hlt' (lt_trans hcell hTn))
      have hrw : ∀ ω : Ω, ((Z ω : ℝ) : ℂ) * jointGridCharacter W N τ lam w Bfam (n + 1) ω
          = ((Z ω : ℝ) : ℂ) * jointGridCharacter W N τ lam w Bfam n ω
            * (Complex.exp (Complex.I
                * ((lam n * (W.W (τ (n + 1)) ω - W.W (τ n) ω) : ℝ) : ℂ))
              * charAt N w (cellFam Bfam τ n) (τ (n + 1)) ω) := by
        intro ω
        rw [jointGridCharacter, jointGridCharacter, Finset.prod_range_succ]
        ring
      simpa only [hrw] using hstep
include hℱN hℱW in
/-- **Value characters along a joint grid.** The weight is orthogonal to the product of a
character of the values of `W` at the grid points and the Poisson character at the last one. -/
theorem pairing_joint_value_character_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) (hTn : τ n < T) :
    ∫ ω, ((Z ω : ℝ) : ℂ)
        * (Complex.exp (Complex.I
            * ((∑ k ∈ Finset.Ico 1 (n + 1), c k * W.W (τ k) ω : ℝ) : ℂ))
          * charAt N w Bfam (τ n) ω) ∂P = 0 := by
  have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt k hk).le
  have hkey := pairing_jointGridCharacter_eq_zero N hℱN W hℱW hℱ0 hnull hτ0 hT hA hAν w hBm
    hBsub he₀ hZ2 hZito hZcomp hZ0
    (fun k => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) n hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [W.initial_zero,
    _root_.Prove2MeSourceProof.h_9515dd3e42bfbfd6da3f4172 N w hBm hA hAν hBsub hτ0 hle'] with ω h0 hprod
  have heq : (∑ k ∈ Finset.Ico 1 (n + 1), c k * W.W (τ k) ω)
      = ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j)
          * (W.W (τ (k + 1)) ω - W.W (τ k) ω) :=
    (_root_.Prove2MeSourceProof.h_3bb40c5e7df4a1af88374480 c (Wv := fun k => W.W (τ k) ω) (by rw [hτ0]; exact h0) n).symm
  rw [heq, hprod, jointGridCharacter, Finset.prod_mul_distrib, ← Complex.exp_sum,
    Complex.ofReal_sum, Finset.mul_sum]
end Induction

end LevyStochCalc.Driver


