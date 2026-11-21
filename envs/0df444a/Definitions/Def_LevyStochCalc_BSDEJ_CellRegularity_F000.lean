-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_CellRegularity_F000
-- name    : LevyStochCalc_BSDEJ_CellRegularity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:39:22.972672+00:00
-- url     : https://prove2.me/theorems/34b46db1-16bf-49fd-accd-2435fa95e372
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.CellRegularity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.CellRegularity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F000
import Definitions.Def_LevyStochCalc_BSDEJ_CellAverageRateMarked_F001
import Definitions.Def_LevyStochCalc_BSDEJ_Solves_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Conditional cell averages and the `L²` path-regularity rate

On the uniform grid `t_i = i τ` the conditional cell averages of the integrands of a backward
equation with jumps are the conditional projections

  `Z̄_i = τ⁻¹ E[∫_{t_i}^{t_{i+1}} Z_s ds | 𝔸_{t_i}]`,
  `Ū_i^k = τ⁻¹ E[∫_{t_i}^{t_{i+1}} ∫_{A_k} U_s(e) ν(de) ds | 𝔸_{t_i}]`,

taken over the augmented joint filtration `𝔸 = augJoint D` of a Lévy driver `D`, the marked one
read along a finite family `A : Fin m → Set E` of marks. They are the orthogonal projections
onto the adapted cell-constant processes, and so differ from the pathwise averages
`cellTimeAverage_Z` and `cellTimeAverage_U`, which project onto all cell-constant functions; on
an integrand constant in the sample point the two coincide.

`CellRegularity D T Z U A C` is the `L²` path-regularity rate: the sum over the cells of the
uniform grid of mesh `T / N` of the squared conditional projection errors of `Z`, and of the
marked integrals of `U` along `A`, is at most `C · T / N`. It is a property of the pair
`(Z, U)` alone, carried as a hypothesis: the proofs of the rate in the sources below run
through Malliavin calculus or through a differentiable representation of the solution by a
partial integro-differential equation, and neither is available in this library.

## Main statements

* `condCellAverage_Z`, `condCellAverage_U` — the conditional cell averages.
* `stronglyMeasurable_condCellAverage_Z`, `stronglyMeasurable_condCellAverage_U` — each is
  measurable for the filtration at the left endpoint of its cell.
* `condCellAverage_Z_of_deterministic` — for an integrand constant in the sample point the
  conditional cell average is the cell average of the underlying function of time.
* `condCellAverage_eq_cellTimeAverage_of_deterministic` — for such an integrand the conditional
  cell average agrees with the pathwise average `cellTimeAverage_Z` over the uniform grid.
* `CellRegularity` — the path-regularity rate on the uniform grids of a horizon.

## References

* Zhang, J., *A numerical scheme for BSDEs*, Ann. Appl. Probab. **14(1)**, 2004, pp. 459–488,
  Theorem 3.1.
* Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with
  jumps*, Stochastic Processes Appl. **118(1)**, 2008, pp. 53–75, Theorem 2.1.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

open LevyStochCalc.BSDEJ.Solves (augJoint)
open LevyStochCalc.Driver (LevyDriver)

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d m : ℕ}

section UniformGrid

variable {τ : ℝ} {M : ℕ}

/-- The uniform grid of step `τ` with `M` cells, `n ↦ n τ`. -/
noncomputable def uniformGrid (τ : ℝ) (M : ℕ) : Fin (M + 1) → ℝ := fun n => ((n : ℕ) : ℝ) * τ
/-- The left endpoint of the `n`-th cell of the uniform grid of step `τ`. -/
theorem uniformGrid_castSucc (n : Fin M) :
    uniformGrid τ M n.castSucc = ((n : ℕ) : ℝ) * τ := by
  simp [uniformGrid]
/-- The right endpoint of the `n`-th cell of the uniform grid of step `τ`. -/
theorem uniformGrid_succ (n : Fin M) :
    uniformGrid τ M n.succ = (((n : ℕ) : ℝ) + 1) * τ := by
  simp [uniformGrid, Fin.val_succ]
omit [MeasurableSpace Ω] in
/-- The pathwise cell average over the uniform grid of positive step `τ`, evaluated at a time of
the `i`-th cell, is the average of the integrand over that cell. -/
theorem cellTimeAverage_Z_uniformGrid (hτ : 0 < τ) {i : ℕ} (hi : i < M) {s : ℝ}
    (hs : s ∈ Set.Ioc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ)) (Z : ℝ → Ω → (Fin d → ℝ)) (ω : Ω)
    (k : Fin d) :
    cellTimeAverage_Z (uniformGrid τ M) Z s ω k
      = τ⁻¹ * ∫ u in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), Z u ω k := by
  classical
  simp only [cellTimeAverage_Z]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin M)]
  · have hc : (((⟨i, hi⟩ : Fin M) : ℕ) : ℝ) = (i : ℝ) := rfl
    rw [uniformGrid_castSucc, uniformGrid_succ, hc, if_pos ⟨hs.1, hs.2⟩,
      show (((i : ℝ) + 1) * τ - (i : ℝ) * τ) = τ by ring, one_div]
  · intro b _ hb
    refine if_neg ?_
    rw [uniformGrid_castSucc, uniformGrid_succ]
    rintro ⟨h1, h2⟩
    have hbi : (b : ℕ) ≠ i := fun hbi => hb (Fin.ext hbi)
    rcases Nat.lt_or_ge (b : ℕ) i with hlt | hge
    · have hcast : (((b : ℕ) : ℝ) + 1) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hlt
      nlinarith [hs.1]
    · have hgt : i < (b : ℕ) := lt_of_le_of_ne hge (Ne.symm hbi)
      have hcast : (((i : ℕ) : ℝ) + 1) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hgt
      nlinarith [hs.2]
  · intro hcon
    exact absurd (Finset.mem_univ (⟨i, hi⟩ : Fin M)) hcon
end UniformGrid

section CondCellAverage

variable {τ : ℝ} {i : ℕ}

/-- The conditional cell average of `Z` over the cell `[i τ, (i + 1) τ]` of the uniform grid of
step `τ`: the conditional expectation, for the augmented joint filtration at the left endpoint,
of the integral of `Z` over the cell, divided by `τ`, coordinate by coordinate. -/
noncomputable def condCellAverage_Z (D : LevyDriver P d ν) (τ : ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) (i : ℕ) : Ω → (Fin d → ℝ) := fun ω k =>
  τ⁻¹ * P[fun ω' => ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), Z s ω' k |
    augJoint D ((i : ℝ) * τ)] ω
/-- The conditional cell average of the marked integrand `U` read along the mark family `A`:
the conditional expectation, for the augmented joint filtration at the left endpoint of the cell
`[i τ, (i + 1) τ]`, of the integral over that cell of the `ν`-integrals of `U` over the sets
`A k`, divided by `τ`. It is the projection of the family of marked integrals of `U` along `A`,
not of `U` itself. -/
noncomputable def condCellAverage_U (D : LevyDriver P d ν) (τ : ℝ) (U : ℝ → Ω → E → ℝ)
    (A : Fin m → Set E) (i : ℕ) : Ω → (Fin m → ℝ) := fun ω k =>
  τ⁻¹ * P[fun ω' => ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
    ∫ e in A k, U s ω' e ∂ν | augJoint D ((i : ℝ) * τ)] ω
/-- Each coordinate of the conditional cell average of `Z` is strongly measurable for the
augmented joint filtration at the left endpoint of the cell. -/
theorem stronglyMeasurable_condCellAverage_Z (D : LevyDriver P d ν) (τ : ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) (i : ℕ) (k : Fin d) :
    StronglyMeasurable[augJoint D ((i : ℝ) * τ)] fun ω => condCellAverage_Z D τ Z i ω k :=
  stronglyMeasurable_condExp.const_mul _
/-- Each entry of the conditional cell average of `U` along `A` is strongly measurable for the
augmented joint filtration at the left endpoint of the cell. -/
theorem stronglyMeasurable_condCellAverage_U (D : LevyDriver P d ν) (τ : ℝ)
    (U : ℝ → Ω → E → ℝ) (A : Fin m → Set E) (i : ℕ) (k : Fin m) :
    StronglyMeasurable[augJoint D ((i : ℝ) * τ)] fun ω => condCellAverage_U D τ U A i ω k :=
  stronglyMeasurable_condExp.const_mul _
/-- Two integrands with almost surely equal cell integrals have almost surely equal conditional
cell averages. -/
theorem condCellAverage_Z_congr (D : LevyDriver P d ν) (τ : ℝ)
    {Z Z' : ℝ → Ω → (Fin d → ℝ)} {k : Fin d}
    (hZ : (fun ω => ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), Z s ω k)
      =ᵐ[P] fun ω => ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), Z' s ω k) :
    (fun ω => condCellAverage_Z D τ Z i ω k)
      =ᵐ[P] fun ω => condCellAverage_Z D τ Z' i ω k := by
  filter_upwards [condExp_congr_ae (m := augJoint D ((i : ℝ) * τ)) hZ] with ω hω
  simp only [condCellAverage_Z, hω]
/-- A marked integrand whose cell integral along a mark almost surely vanishes has an almost
surely vanishing conditional cell average at that mark. -/
theorem condCellAverage_U_of_ae_setIntegral_eq_zero (D : LevyDriver P d ν) (τ : ℝ)
    {U : ℝ → Ω → E → ℝ} {A : Fin m → Set E} {k : Fin m}
    (hU : ∀ᵐ ω ∂P, ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      ∫ e in A k, U s ω e ∂ν = 0) :
    (fun ω => condCellAverage_U D τ U A i ω k) =ᵐ[P] fun _ => (0 : ℝ) := by
  have h0 : (fun ω => ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      ∫ e in A k, U s ω e ∂ν) =ᵐ[P] (0 : Ω → ℝ) := by
    filter_upwards [hU] with ω hω using hω
  filter_upwards [condExp_congr_ae (m := augJoint D ((i : ℝ) * τ)) h0] with ω hω
  simp only [condCellAverage_U, hω, condExp_zero, Pi.zero_apply, mul_zero]
/-- For an integrand constant in the sample point the conditional cell average is the cell
average of the underlying function of time. -/
theorem condCellAverage_Z_of_deterministic (D : LevyDriver P d ν) (τ : ℝ) (h : ℝ → ℝ)
    {Z : ℝ → Ω → (Fin d → ℝ)} (hZ : ∀ s ω k, Z s ω k = h s) (i : ℕ) (k : Fin d) :
    (fun ω => condCellAverage_Z D τ Z i ω k)
      = fun _ => τ⁻¹ * ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), h s := by
  have hle : (augJoint D ((i : ℝ) * τ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› :=
    (augJoint D).le ((i : ℝ) * τ)
  funext ω
  simp only [condCellAverage_Z, hZ, condExp_const hle]
/-- For an integrand constant in the sample point the conditional cell average over a cell of the
uniform grid of positive step is the pathwise cell average at any time of that cell. -/
theorem condCellAverage_eq_cellTimeAverage_of_deterministic (D : LevyDriver P d ν) {τ : ℝ}
    (hτ : 0 < τ) {M : ℕ} (hi : i < M) (h : ℝ → ℝ) {Z : ℝ → Ω → (Fin d → ℝ)}
    (hZ : ∀ s ω k, Z s ω k = h s) {s : ℝ}
    (hs : s ∈ Set.Ioc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ)) (ω : Ω) (k : Fin d) :
    condCellAverage_Z D τ Z i ω k = cellTimeAverage_Z (uniformGrid τ M) Z s ω k := by
  have hdet : condCellAverage_Z D τ Z i ω k
      = τ⁻¹ * ∫ u in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), h u :=
    congrFun (condCellAverage_Z_of_deterministic D τ h hZ i k) ω
  rw [cellTimeAverage_Z_uniformGrid hτ hi hs Z ω k, hdet]
  simp only [hZ]
end CondCellAverage

section Rate

/-- The `L²` path-regularity rate of the integrand pair `(Z, U)` on the uniform grids of the
horizon `[0, T]`, the marked integrand being read along the mark family `A`: for every `N ≥ 1`
the sum over the `N` cells of step `T / N` of the squared conditional cell-average errors is at
most `C · T / N`, for `Z` and for the marked integrals of `U` separately.

The pathwise counterpart of the average subtracted here is `cellTimeAverage_Z`. -/
structure CellRegularity (D : LevyDriver P d ν) (T : ℝ) (Z : ℝ → Ω → (Fin d → ℝ))
    (U : ℝ → Ω → E → ℝ) (A : Fin m → Set E) (C : ℝ) : Prop where
  /-- The rate constant is nonnegative. -/
  nonneg : 0 ≤ C
  /-- The conditional cell-average error of `Z` over the uniform grid of `N` cells. -/
  rate_Z : ∀ N : ℕ, 0 < N →
    ∑ i ∈ Finset.range N, ∫⁻ ω,
        ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          ∑ k : Fin d,
            (‖Z s ω k - condCellAverage_Z D (T / (N : ℝ)) Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (C * (T / (N : ℝ)))
  /-- The conditional cell-average error of the marked integrals of `U` along `A`. -/
  rate_U : ∀ N : ℕ, 0 < N →
    ∑ i ∈ Finset.range N, ∫⁻ ω,
        ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          ∑ k : Fin m,
            (‖(∫ e in A k, U s ω e ∂ν)
              - condCellAverage_U D (T / (N : ℝ)) U A i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (C * (T / (N : ℝ)))
end Rate

end LevyStochCalc.BSDEJ.PathRegularity


