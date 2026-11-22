-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F002
-- name    : LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:41:21.260603+00:00
-- url     : https://prove2.me/theorems/0e404c21-7ebf-4fd5-a409-8963c1e0dcfc
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaGeneralShiftCappedChain_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The capped jump chain over a prescribed evaluation path

The pathwise sum of the jumps carried by a mark set over a window reads the jump coefficient at a
prescribed path of states, and capping the arrival times at the horizon turns that sum into the
chain of jumps accumulated up to each arrival time. Over an enumeration of the atoms of the
window the jump sum is the sum of the jump coefficient over the enumerated atoms whose times lie
in the sub-window, so the capped sum gains exactly the jump coefficient carried by each arrival
time inside the window and does not move strictly between consecutive arrival times; a path that
splits at all nonnegative times into a continuous part and that jump sum is therefore the
continuous part translated by the capped jump sum on each such interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Defs

end Defs

section GeneralShift

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (A : Set E)

end GeneralShift

section MarkIdentification

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

end MarkIdentification

section CappedChain

/-- Strictly between consecutive members of a chain of times starting at `0`, a path that splits
at all nonnegative times into a continuous part and the jump sum along a prescribed evaluation
path agrees with that continuous part translated by the value of the jump sum on that
interval. -/
theorem add_shift_eq_of_ae_forall_at_of_path {X : Setting.JumpDiffusion W N coeffs x₀}
    {Y Z : ℝ → Ω → Fin n → ℝ} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumAt X Y A t ω i)
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hc : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → ∀ i : Fin n, jumpSumAt X Y A s ω i = c k ω i) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = Z s ω := by
  have hnn : ∀ (k : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ σ k ω := by
    intro k ω
    induction k with
    | zero => exact le_of_eq (h0 ω).symm
    | succ k ih => exact ih.trans (hmono k ω)
  filter_upwards [hsplit, hc] with ω hs hcω
  intro k s h1 h2
  have hlt : ((0 : ℝ) : WithTop ℝ) < ((s : ℝ) : WithTop ℝ) := lt_of_le_of_lt (hnn k ω) h1
  have hs0 : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hlt)
  funext i
  simp only [Pi.add_apply]
  rw [hs s hs0 i, hcω k s h1 h2 i]
/-- Strictly between consecutive members of a chain of times starting at `0`, a jump diffusion
that splits at all nonnegative times along a prescribed evaluation path agrees with the
continuous part translated by the value of the jump sum on that interval. -/
theorem add_shift_eq_of_ae_forall_at {X : Setting.JumpDiffusion W N coeffs x₀}
    {Y : ℝ → Ω → Fin n → ℝ} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumAt X Y A t ω i)
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hc : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → ∀ i : Fin n, jumpSumAt X Y A s ω i = c k ω i) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X.X s ω :=
  add_shift_eq_of_ae_forall_at_of_path hsplit h0 hmono hc
variable {A : Set E}

end CappedChain

end LevyStochCalc.Ito.JumpFormula


