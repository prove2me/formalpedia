-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_MarkStepIncrement
-- name    : KLSModular_LevyStochCalc_Poisson_MarkStepIncrement
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:53:13.557255+00:00
-- url     : https://prove2.me/theorems/85f1c3e8-2dc5-401b-b29f-ecb5ee45dcee
-- title:
--   Dyadic mark-step refinement and restriction
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`). `TimeGrid.dyadic` constructs the level-$n$ grid on $[0,T]$, and `MarkStep.dyadicRefine` transfers a mark-step integrand from level $n$ to a finer level $m\ge n$ by assigning each fine piece the coefficient of its coarse piece. `MarkStep.dyadicRestrict` transfers a level-$\ell$ integrand on $[0,T]$ to the level-$(\ell-d)$ grid on $[0,T']$ when $T=T'2^d$ and $d\le\ell$. The bundle proves preservation of evaluations, whole-horizon or partial integrals (the latter almost everywhere where stated), and adaptedness under these operations.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.MarkStepWeight
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (T : ℝ) (hT : 0 < T)
--       (n : ℕ) : TimeGrid where
--     N₀ := 2 ^ n
--     p := fun i => (i : ℝ) * T / (2 ^ n : ℕ)
--     p_zero := by simp
--     p_lt := fun i _ => by
--       have h : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
--       rw [div_lt_div_iff_of_pos_right h]
--       push_cast
--       nlinarith
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/MarkStepWeight`](https://prove2.me/theorems/dc058a24-f207-4301-9fbc-4d6c6710c1e5).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/MarkStepIncrement.lean) · `LevyStochCalc.Poisson.MarkStepIncrement` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/MarkStepIncrement.lean#L36-L194 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.MarkStepIncrement`, definition bundle `KLSModular_LevyStochCalc_Poisson_MarkStepIncrement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_MarkStepWeight

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/MarkStepIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
namespace MarkStep
section Dyadic
variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
/-- The dyadic grid of level `n` on `[0, T]`. -/
noncomputable def _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (T : ℝ) (hT : 0 < T)
    (n : ℕ) : TimeGrid where
  N₀ := 2 ^ n
  p := fun i => (i : ℝ) * T / (2 ^ n : ℕ)
  p_zero := by simp
  p_lt := fun i _ => by
    have h : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    rw [div_lt_div_iff_of_pos_right h]
    push_cast
    nlinarith
lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon (T : ℝ) (hT : 0 < T)
    (n : ℕ) : (TimeGrid.dyadic T hT n).horizon = T := by
  change ((2 ^ n : ℕ) : ℝ) * T / (2 ^ n : ℕ) = T
  field_simp
variable {T : ℝ} {hT : 0 < T} {n m : ℕ}
/-- A mark-step integrand on the level-`n` dyadic grid, re-expressed on the level-`m`
dyadic grid (`n ≤ m`): each fine piece inherits the coefficients of the coarse piece
containing it. -/
def dyadicRefine (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)) (_hnm : n ≤ m) :
    MarkStep Ω E ν (TimeGrid.dyadic T hT m) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k => G.ξ (i / 2 ^ (m - n)) k
  ξ_bounded := fun _ k => G.ξ_bounded _ k
  ξ_measurable := fun _ k => G.ξ_measurable _ k
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)
lemma full_dyadicRefine : (fun ω => (G.dyadicRefine hnm).full N ω) =ᵐ[P] fun ω => G.full N ω := by
  have h := stepIntegral_dyadic_refine_integral N hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) (fun _ k => G.B_measurable k) (fun _ k => G.B_finite k)
  filter_upwards [h] with ω hω
  rw [full_eq_fin, full_eq_fin]
  exact hω
lemma eval_dyadicRefine (s : ℝ) (e : E) (ω : Ω) :
    (G.dyadicRefine hnm).eval s e ω = G.eval s e ω := by
  rw [eval_eq_fin, eval_eq_fin]
  exact stepIntegral_dyadic_refine_eval hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) s ω e
lemma Adapted.dyadicRefine (N : PoissonRandomMeasure P ν)
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)} (hG : G.Adapted ℱ) (hnm : n ≤ m) :
    (G.dyadicRefine hnm).Adapted ℱ := by
  intro i hi k
  exact dyadic_refine_adapted N ℱ hT hnm (Ki := fun _ => G.K) (fun i k => G.ξ i k)
    (fun i k => hG i i.isLt k) ⟨i, hi⟩ k
include hℱ in
/-- The integral of a refined adapted mark-step integrand agrees almost surely with the
integral of the integrand at every time. -/
lemma integral_dyadicRefine (hG : G.Adapted ℱ) (t : ℝ) :
    (fun ω => (G.dyadicRefine hnm).integral N t ω) =ᵐ[P] fun ω => G.integral N t ω := by
  have hfull : (fun ω => (G.dyadicRefine hnm).integral N T ω)
      =ᵐ[P] fun ω => G.integral N T ω := by
    have h1 : ∀ ω, (G.dyadicRefine hnm).integral N T ω = (G.dyadicRefine hnm).full N ω :=
      fun ω => (G.dyadicRefine hnm).integral_eq_full_of_horizon_le N
        (TimeGrid.dyadic_horizon T hT m).le ω
    have h2 : ∀ ω, G.integral N T ω = G.full N ω :=
      fun ω => G.integral_eq_full_of_horizon_le N (TimeGrid.dyadic_horizon T hT n).le ω
    simp only [h1, h2]
    exact G.full_dyadicRefine N hnm
  rcases le_or_gt t T with htT | htT
  · have hM₁ := (G.dyadicRefine hnm).martingale_integral N hℱ (hG.dyadicRefine N hnm)
    have hM₂ := G.martingale_integral N hℱ hG
    exact (hM₁.condExp_ae_eq htT).symm.trans
      ((condExp_congr_ae hfull).trans (hM₂.condExp_ae_eq htT))
  · have h1 : ∀ ω, (G.dyadicRefine hnm).integral N t ω = (G.dyadicRefine hnm).full N ω :=
      fun ω => (G.dyadicRefine hnm).integral_eq_full_of_horizon_le N
        ((TimeGrid.dyadic_horizon T hT m).le.trans htT.le) ω
    have h2 : ∀ ω, G.integral N t ω = G.full N ω :=
      fun ω => G.integral_eq_full_of_horizon_le N
        ((TimeGrid.dyadic_horizon T hT n).le.trans htT.le) ω
    simp only [h1, h2]
    exact G.full_dyadicRefine N hnm
/-- A mark-step integrand on the level-`ℓ` dyadic grid of `[0, T]`, restricted to the
prefix `[0, T']` where `T = T' * 2 ^ d` (`d ≤ ℓ`), which is the level-`(ℓ - d)` dyadic
grid there. -/
def dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (_hd : d ≤ ℓ) (_h : T = T' * 2 ^ d) :
    MarkStep Ω E ν (TimeGrid.dyadic T' hT' (ℓ - d)) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable
lemma dyadic_p_restrict {ℓ d : ℕ} {T' : ℝ} (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d)
    (i : ℕ) : (TimeGrid.dyadic T' hT' (ℓ - d)).p i = (TimeGrid.dyadic T hT ℓ).p i := by
  change (i : ℝ) * T' / ((2 ^ (ℓ - d) : ℕ) : ℝ) = (i : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ)
  have h2 : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h2, h]
  field_simp
lemma dyadic_p_pow {ℓ d : ℕ} {T' : ℝ} (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) :
    (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) = T' := by
  change ((2 ^ (ℓ - d) : ℕ) : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ) = T'
  have h2 : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h2, h]
  field_simp
lemma full_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).full N ω = G.integral N T' ω := by
  have h' : (G.dyadicRestrict hT' hd h).full N ω
      = G.integral N ((TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d))) ω := by
    rw [G.integral_p_eq N _ (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))]
    unfold full
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    change G.ξ i k ω * N.compensated (Set.Ioc
        ((TimeGrid.dyadic T' hT' (ℓ - d)).p i)
        ((TimeGrid.dyadic T' hT' (ℓ - d)).p (i + 1)) ×ˢ G.B k) ω = _
    rw [dyadic_p_restrict (hT := hT) hT' hd h, dyadic_p_restrict (hT := hT) hT' hd h]
  rw [h', dyadic_p_pow (hT := hT) hd h]
lemma eval_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) {s : ℝ} (hs : s ≤ T') (e : E) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).eval s e ω = G.eval s e ω := by
  unfold eval
  simp_rw [dyadic_p_restrict (hT := hT) hT' hd h]
  refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d)))) ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  rw [Set.indicator_of_notMem, zero_mul]
  intro hs'
  have : (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) ≤ (TimeGrid.dyadic T hT ℓ).p i :=
    (TimeGrid.dyadic T hT ℓ).p_mono (not_lt.1 hni) hi.le
  rw [dyadic_p_pow (hT := hT) hd h] at this
  exact absurd (hs.trans this) (not_le.2 hs'.1)
lemma Adapted.dyadicRestrict {ℓ d : ℕ}
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)} (hG : G.Adapted ℱ) {T' : ℝ} (hT' : 0 < T')
    (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) : (G.dyadicRestrict hT' hd h).Adapted ℱ := by
  intro i hi k
  change @StronglyMeasurable Ω ℝ _ (ℱ ((TimeGrid.dyadic T' hT' (ℓ - d)).p i)) (G.ξ i k)
  rw [dyadic_p_restrict (hT := hT) hT' hd h]
  exact hG i (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))) k
end Dyadic
end MarkStep
end Compensated
end Poisson
end LevyStochCalc


