-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
-- name    : LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:50:30.771339+00:00
-- url     : https://prove2.me/theorems/715d9167-c97f-4b19-882f-e0e4d25c7032
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentIncrements
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentIncrements. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraProduct_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001
import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Brownian increment and the partial sums of the elementary integral

The moments of a centred real Gaussian and of a Brownian increment: they scale with the standard
deviation, the odd ones vanish, and a random variable measurable before the increment factors out
of the integral against any power of it. On top of this the elementary integral of a simple
integrand is presented as the partial sums `SimplePredictable.partialSum` of its summands, with
their measurability, adaptedness and `Lᵖ` membership, and the variance budget
`SimplePredictable.varClock c k = ∑_{j < k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient
bound `c`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- A Brownian increment has moments of every order. -/
theorem memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)
end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- The `i`-th summand of the elementary integral, indexed by a natural number. -/
noncomputable def term (i : ℕ) (ω : Ω) : ℝ :=
  if h : i < G.N then
    G.ξ ⟨i, h⟩ ω * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
      - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω)
  else 0
/-- The partial sums of the elementary integral. -/
noncomputable def partialSum (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, G.term W i ω
theorem partialSum_zero (ω : Ω) : G.partialSum W 0 ω = 0 := by simp [partialSum]
theorem partialSum_succ (k : ℕ) (ω : Ω) :
    G.partialSum W (k + 1) ω = G.partialSum W k ω + G.term W k ω :=
  Finset.sum_range_succ _ _
theorem measurable_term (i : ℕ) : Measurable (G.term W i) := by
  unfold term
  split_ifs with h
  · exact (G.ξ_measurable _).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · exact measurable_const
theorem measurable_partialSum (k : ℕ) : Measurable (G.partialSum W k) :=
  Finset.measurable_sum _ fun i _ => G.measurable_term W i
theorem partialSum_card (ω : Ω) : G.partialSum W G.N ω = simpleIntegral W G T ω := by
  rw [simpleIntegral_eq_sum, partialSum, ← Fin.sum_univ_eq_sum_range
    (fun i => G.term W i ω) G.N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term, dif_pos i.isLt]
omit [MeasurableSpace Ω] in
/-- A finite sum of processes measurable for a sub-σ-algebra is measurable for it. -/
private theorem stronglyMeasurable_range_sum {m : MeasurableSpace Ω} {n : ℕ} {f : ℕ → Ω → ℝ}
    (h : ∀ i ∈ Finset.range n, @MeasureTheory.StronglyMeasurable Ω ℝ _ m (f i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ m (fun ω => ∑ i ∈ Finset.range n, f i ω) :=
  @Finset.stronglyMeasurable_fun_sum Ω ℝ _ _ _ m _ _ _ h
theorem memLp_term {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (i : ℕ) : MemLp (G.term W i) p P := by
  by_cases h : i < G.N
  · have hterm : G.term W i = fun ω => G.ξ ⟨i, h⟩ ω
        * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω) := by
      funext ω; rw [term, dif_pos h]
    rw [hterm]
    exact memLp_mul_increment W (G.partition_nonneg _)
      (G.partition_strictMono Fin.castSucc_lt_succ) p hp (G.ξ_measurable _) (hC ⟨i, h⟩)
  · have hterm : G.term W i = fun _ => (0 : ℝ) := by funext ω; rw [term, dif_neg h]
    rw [hterm]; exact memLp_const 0
theorem memLp_partialSum {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (k : ℕ) : MemLp (G.partialSum W k) p P :=
  memLp_finsetSum _ fun i _ => G.memLp_term W hC p hp i
end SimplePredictable

end LevyStochCalc.Brownian.Ito


