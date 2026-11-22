-- Prove2me | Definitions.Def_SourceProof_283f13154d96adb21fe894f1
-- name    : SourceProof_283f13154d96adb21fe894f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:56:57.594117+00:00
-- url     : https://prove2.me/theorems/da6e574f-0151-44be-a0ed-23ea60891c70
-- title:
--   LevyStochCalc source module: SourceProof_283f13154d96adb21fe894f1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_simpleShift` comes from the `LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaSimpleShiftCells_F001
import Definitions.Def_SourceProof_71f235c6c37a3ef4243fe9d4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for an increment translated by a simple random vector

On a cell where a stopping time and a simple random mark are both constant the translation is by
a fixed vector, so the cell indicator — bounded and known at the deterministic time carried by
the cell — passes inside the Itô integral of the increment, and the Itô integral of the increment
read along the mark splits over the cells. Itô's formula for the increment between the two
stopping times then applies on each cell with a constant shift, and recombining the cells gives
the formula for a function translated by the simple random vector. The cells themselves are
measurable at the deterministic times the stopping time takes as soon as the mark is measurable
at that stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` — the Itô integral of
  that increment splits over the cells.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_simpleShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a simple random vector.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_of_measurable` — a mark measurable at a stopping
  time has cells measurable at the deterministic times that stopping time takes.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*}
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end CellIntegral

section SimpleShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in

theorem _root_.Prove2MeSourceProof.h_283f13154d96adb21fe894f1
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s))
    (hpG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s)
    (hqG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω + v) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ (v : Fin n → ℝ) (p : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + v) * bdrift p ω s))
    (hqD : ∀ (v : Fin n → ℝ) (p : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω + v) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ (v : Fin n → ℝ) (p q : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω + v) * ∑ k : Fin d, H p k ω s * H q k ω s))
    {T : ℝ} (hT : 0 < T)
    (hQint : ∀ v : Fin n → ℝ, ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => coordDeriv₂ f'' p q (X s ω + v) * ∑ k : Fin d, H p k ω s * H q k ω s)
      (Set.Ioc (0 : ℝ) T) volume)
    {c : Ω → Fin n → ℝ} {Vs : Finset (Fin n → ℝ)} (hcVs : ∀ ω, c ω ∈ Vs)
    {J : Finset ℝ} (hJ0 : ∀ a ∈ J, 0 ≤ a) (hJT : ∀ a ∈ J, a < T)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ' a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hconst : ∀ᵐ ω ∂P, ∀ v ∈ Vs,
      f (X (LevyStochCalc.Brownian.Ito.clipTime τ T ω) ω + v) - f (X (LevyStochCalc.Brownian.Ito.clipTime σ T ω) ω + v)
        = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (LevyStochCalc.Probability.stopped τ
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * bdrift p ω s) ω s
              - LevyStochCalc.Probability.stopped σ
                  (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  LevyStochCalc.Probability.stopped τ
                      (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) ω s
                    - LevyStochCalc.Probability.stopped σ
                        (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) ω s)
                (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG v p k))
                (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG v p k))
                (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG v p k) (hqG v p k)) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + v)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω + v)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
    rw [Filter.eventually_all_finset]
    intro v _
    exact LevyStochCalc.Brownian.Ito.itoFormula_between_shift W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hσ hτ hσ0 hτ0
      hfC hf hf' v (hmG v) (hpG v) (hqG v) (hmD v) (hqD v) (hmQ v) hT (hQint v)
  have hitocells : ∀ (p : Fin n) (k : Fin d), ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          LevyStochCalc.Probability.stopped τ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - LevyStochCalc.Probability.stopped σ
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
        (hmSc p k) (hpSc p k) (hqSc p k) T ω
        = ∑ x ∈ J ×ˢ Vs, LevyStochCalc.Brownian.Ito.cellWeight σ c x.1 x.2 ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              LevyStochCalc.Probability.stopped τ
                  (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + x.2) * H p k ω s) ω s
                - LevyStochCalc.Probability.stopped σ
                    (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + x.2) * H p k ω s) ω s)
            (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG x.2 p k))
            (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG x.2 p k))
            (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG x.2 p k) (hqG x.2 p k)) T ω := by
    intro p k
    exact _root_.Prove2MeSourceProof.h_71f235c6c37a3ef4243fe9d4 (W.W k) ℱ' (hcoord k) hσ hτ hστ
      hcVs hJ0 hJT hσJ hcell (fun v ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s)
      (fun v => hmG v p k) (fun v => hpG v p k) (fun v => hqG v p k)
      (Kc := fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) (fun _ _ => rfl)
      (hmSc p k) (hpSc p k) (hqSc p k) hT
  have hito := (MeasureTheory.ae_all_iff (μ := P)).2
    fun p : Fin n => (MeasureTheory.ae_all_iff (μ := P)).2 fun k : Fin d => hitocells p k
  filter_upwards [hconst, hito] with ω hcv hik
  rcases hσJ ω with ⟨a₀, ha₀, hσω⟩ | htop
  · have e2 : (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω' s =>
              LevyStochCalc.Probability.stopped τ
                  (fun ω' s => LevyStochCalc.coordDeriv f' p (X s ω' + c ω) * H p k ω' s) ω' s
                - LevyStochCalc.Probability.stopped σ
                    (fun ω' s => LevyStochCalc.coordDeriv f' p (X s ω' + c ω) * H p k ω' s) ω' s)
            (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG (c ω) p k))
            (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG (c ω) p k))
            (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG (c ω) p k) (hqG (c ω) p k)) T ω)
        = ∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              LevyStochCalc.Probability.stopped τ
                  (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - LevyStochCalc.Probability.stopped σ
                    (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => ?_
      refine ((hik p k).trans ?_).symm
      exact LevyStochCalc.Brownian.Ito.sum_cellWeight_mul σ c J Vs
        (fun v => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
           (fun ω s =>
             LevyStochCalc.Probability.stopped τ
                 (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) ω s
               - LevyStochCalc.Probability.stopped σ
                   (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) ω s)
           (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG v p k))
           (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG v p k))
           (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG v p k) (hqG v p k)) T ω) (hcVs ω) ha₀ hσω
    refine (hcv (c ω) (hcVs ω)).trans ?_
    rw [e2]
    rfl
  · have hτω : τ ω = ⊤ := top_le_iff.mp (htop ▸ hστ ω)
    have hz : ∀ (F : Ω → ℝ → ℝ) (s : ℝ),
        LevyStochCalc.Probability.stopped τ F ω s - LevyStochCalc.Probability.stopped σ F ω s = 0 := by
      intro F s
      simp [LevyStochCalc.Probability.stopped, htop, hτω]
    have hI : (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            LevyStochCalc.Probability.stopped τ
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
              - LevyStochCalc.Probability.stopped σ
                  (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
          (hmSc p k) (hpSc p k) (hqSc p k) T ω) = 0 := by
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun k _ => ?_
      refine (hik p k).trans ?_
      exact LevyStochCalc.Brownian.Ito.sum_cellWeight_mul_of_top σ c J Vs
        (fun v => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
           (fun ω s =>
             LevyStochCalc.Probability.stopped τ
                 (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) ω s
               - LevyStochCalc.Probability.stopped σ
                   (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω + v) * H p k ω s) ω s)
           (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG v p k))
           (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG v p k))
           (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG v p k) (hqG v p k)) T ω) htop
    rw [LevyStochCalc.Brownian.Ito.clipTime_eq_self_of_top htop, LevyStochCalc.Brownian.Ito.clipTime_eq_self_of_top hτω, sub_self, hI]
    simp [hz]
end SimpleShift

section CellFromStoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {α : Type*}

end CellFromStoppingTime

end LevyStochCalc.Brownian.Ito


