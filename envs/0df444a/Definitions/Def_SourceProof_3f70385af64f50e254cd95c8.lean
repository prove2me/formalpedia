-- Prove2me | Definitions.Def_SourceProof_3f70385af64f50e254cd95c8
-- name    : SourceProof_3f70385af64f50e254cd95c8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:40.180044+00:00
-- url     : https://prove2.me/theorems/8a6d10b7-6cd9-4f0a-a4d7-a10c4342cc41
-- title:
--   LevyStochCalc source module: SourceProof_3f70385af64f50e254cd95c8
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_polarQuadVar_le` comes from the `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000
import Definitions.Def_SourceProof_097e4842bb855e3d75971969
import Definitions.Def_SourceProof_0ad6dc3dceb6fd01e9903394
import Definitions.Def_SourceProof_0b802c6f1a6489d52336dde1
import Definitions.Def_SourceProof_33cc866be12cedca71971a8f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cell sums and the error terms of the quadratic-variation Riemann sum

Summing terms attached to the cells of a uniform grid against weights bounded by `Kw` multiplies
a common bound on their first absolute moments by `N·Kw`. Applied to the increments of two
coordinates of a continuous vector Itô process across a grid of `m` cells, weighted by a bounded
function of the process, this bounds the drift–drift term by `O(1/m)` and the drift–martingale
terms, the compensated products on the diagonal in the Brownian index and the cross terms off
that diagonal by `O(m^{-1/2})`.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le` — the `L¹` bound for a weighted
  sum of cell terms with a common first-absolute-moment bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_drift_sq_le` — the
  drift–drift term.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_driftCross_le` — a
  drift–martingale term.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section CellSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end CellSums

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_3f70385af64f50e254cd95c8
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (p q : Fin n) (k : Fin d)
    (hma : Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := by
  have h0 : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.unifGrid T m 0 := le_of_eq (LevyStochCalc.Brownian.Ito.unifGrid_zero T m).symm
  have hgrid : ∀ i : ℕ, LevyStochCalc.Brownian.Ito.unifGrid T m i < LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1) := LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0
  have hg : ∀ i : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (LevyStochCalc.Brownian.Ito.unifGrid T m i))
      (fun ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) := fun i =>
    (hφc.comp_stronglyMeasurable (h.adapted (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mono (ℱ.le_rightCont _)
  have hζmem : ∀ i : ℕ, MemLp (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k)
      (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k)
      (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) 2 P := fun i =>
    _root_.Prove2MeSourceProof.h_0b802c6f1a6489d52336dde1 (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
      (hHp p k) (hHp q k) (hHs p k) (hHs q k) hma hpa hqa hC0 (hCH p k) (hCH q k)
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (hgrid i)
  have hζmeas : ∀ i : ℕ, Measurable (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k)
      (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k)
      (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) := fun i =>
    ((_root_.Prove2MeSourceProof.h_097e4842bb855e3d75971969 (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
      (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) (hgrid i).le).mono
        (ℱ.rightCont.le _)).measurable
  have hYmem : ∀ i : ℕ, MemLp (fun ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
      * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k)
          (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) 2 P := by
    intro i
    refine MeasureTheory.MemLp.mono ((hζmem i).const_mul Kφ)
      (((hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
        (hζmeas i)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hSmem := memLp_finsetSum (Finset.range m) fun i _ => hYmem i
  have hbound := _root_.Prove2MeSourceProof.h_0ad6dc3dceb6fd01e9903394 (W.W k) ℱ (hcoord k) (H p k) (H q k)
    (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) hma hpa hqa hC0
    (hCH p k) (hCH q k) (LevyStochCalc.Brownian.Ito.unifGrid T m) h0 hgrid (fun i ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) hg
    hKφ0 (fun i ω => hφbd _) m
  rw [LevyStochCalc.Brownian.Ito.sum_unifGrid_sq_diff hT hm0] at hbound
  exact ⟨hSmem.integrable (by norm_num),
    _root_.Prove2MeSourceProof.h_33cc866be12cedca71971a8f ((hSmem.integrable (by norm_num)).abs)
      hSmem.integrable_sq hbound⟩
end VectorQuadVar

end LevyStochCalc.Brownian.Ito


