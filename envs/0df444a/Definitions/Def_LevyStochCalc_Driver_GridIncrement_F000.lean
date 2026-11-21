-- Prove2me | Definitions.Def_LevyStochCalc_Driver_GridIncrement_F000
-- name    : LevyStochCalc_Driver_GridIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:29:31.312432+00:00
-- url     : https://prove2.me/theorems/ce69e74d-3445-4e2d-87a4-52f43ab5dcb4
-- title:
--   Source declarations: LevyStochCalc.Driver.GridIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.GridIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_VectorIncrement_F000
import Definitions.Def_SourceProof_0a6a993732779fb8032a84b6
import Definitions.Def_SourceProof_8ea16c26ab6d2ef36877b0b6
import Definitions.Def_SourceProof_98d5b80f0fbd482e08c8d6f3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The data of a Lévy driver along a grid

Over one interval the driver's step tuple is independent of the joint filtration at the left
endpoint (`Driver/VectorIncrement.lean`). Along a grid `g 0 < g 1 < ⋯` the tuples of successive
intervals are jointly independent of `ℱ₊ (g 0)`, because each is measurable at the right endpoint
and independent of the filtration at the left one — that is `indep_iSup_lt_of_indep`. Data
measured from `g 0` — Brownian increments from `g 0`, counts on the part of a region lying after
`g 0` — are sums of the successive ones, so they generate a smaller σ-algebra and inherit the
independence.

## Main statements

* `LevyDriver.indep_iSup_stepSigma` — the successive step tuples against `ℱ₊ (g 0)`.
* `LevyDriver.indep_iSup_stepSigma_start` — the tuples measured from `g 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

theorem incrementSigma_le_filtration (j : Fin d) {a b : ℝ} (hab : a ≤ b) :
    D.incrementSigma j a b ≤ D.filtration b :=
  ((((D.isBrownianFiltration j).measurable b).sub
    (((D.isBrownianFiltration j).measurable a).mono (D.filtration.mono hab) le_rfl))).comap_le
theorem regionSigma_le_filtration {C : Set (ℝ × E)} (hC : MeasurableSet C) {b : ℝ}
    (hCb : C ⊆ Set.Iic b ×ˢ Set.univ) : D.regionSigma C ≤ D.filtration b :=
  ((_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D).measurable hCb hC).comap_le
theorem stepSigma_le_filtration {m : ℕ} (C : Fin m → Set (ℝ × E))
    (hCm : ∀ k, MeasurableSet (C k)) {a b : ℝ} (hab : a ≤ b)
    (hCb : ∀ k, C k ⊆ Set.Iic b ×ˢ Set.univ) : D.stepSigma C a b ≤ D.filtration b :=
  sup_le (iSup_le fun j => D.incrementSigma_le_filtration j hab)
    (iSup_le fun k => D.regionSigma_le_filtration (hCm k) (hCb k))
theorem stepSigma_le {m : ℕ} (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k))
    (a b : ℝ) : D.stepSigma C a b ≤ ‹MeasurableSpace Ω› :=
  sup_le (iSup_le fun _ => (Brownian.comap_increment_le_sigmaBrownian _ a b).trans
      (Brownian.sigmaBrownian_le _))
    (iSup_le fun k => (D.regionSigma_le (hCm k)).trans (sigmaPoisson_le _))
/-- **The step tuples of the successive intervals of a grid are jointly independent of the
right-continuous filtration at its left endpoint.** -/
theorem indep_iSup_stepSigma {m : ℕ} (C : Fin m → Set (ℝ × E))
    (hCm : ∀ k, MeasurableSet (C k)) {g : ℕ → ℝ} (hg : StrictMono g) (hg0 : 0 ≤ g 0) (n : ℕ) :
    Indep (⨆ l, ⨆ _ : l < n,
        D.stepSigma (fun k => C k ∩ Set.Ioc (g l) (g (l + 1)) ×ˢ Set.univ) (g l) (g (l + 1)))
      (D.filtration.rightCont (g 0)) P := by
  have hstepm : ∀ l k, MeasurableSet (C k ∩ Set.Ioc (g l) (g (l + 1)) ×ˢ Set.univ) :=
    fun l k => (hCm k).inter (measurableSet_Ioc.prod MeasurableSet.univ)
  refine _root_.Prove2MeSourceProof.h_0a6a993732779fb8032a84b6
    (fun _ _ hab => D.filtration.rightCont.mono (hg.monotone hab))
    (fun l => D.filtration.rightCont.le (g l)) (fun l => D.stepSigma_le _ (hstepm l) _ _)
    (fun l => (D.stepSigma_le_filtration _ (hstepm l) (hg (Nat.lt_succ_self l)).le
      (fun k => Set.inter_subset_right.trans
        (Set.prod_mono Set.Ioc_subset_Iic_self le_rfl))).trans
      (D.filtration.le_rightCont (g (l + 1))))
    (fun l => ((_root_.Prove2MeSourceProof.h_8ea16c26ab6d2ef36877b0b6 D) _ (hstepm l)
      (hg0.trans (hg.monotone (Nat.zero_le l))) (hg (Nat.lt_succ_self l))
      (fun k => Set.inter_subset_right.trans
        (Set.prod_mono Set.Ioc_subset_Ioi_self le_rfl))).symm) n
/-- A Brownian increment measured from the start of the grid is measurable for the σ-algebra of
the successive increments. -/
theorem incrementSigma_start_le (j : Fin d) {g : ℕ → ℝ} {n : ℕ} (l : ℕ) (hl : l < n) :
    D.incrementSigma j (g 0) (g (l + 1))
      ≤ ⨆ i, ⨆ _ : i < n, D.incrementSigma j (g i) (g (i + 1)) := by
  induction l with
  | zero => exact le_iSup₂_of_le 0 hl le_rfl
  | succ l ih =>
    have heq : (fun ω => (D.W.W j).W (g (l + 2)) ω - (D.W.W j).W (g 0) ω)
        = fun ω => ((D.W.W j).W (g (l + 2)) ω - (D.W.W j).W (g (l + 1)) ω)
          + ((D.W.W j).W (g (l + 1)) ω - (D.W.W j).W (g 0) ω) := by
      funext ω; ring
    change MeasurableSpace.comap
      (fun ω => (D.W.W j).W (g (l + 2)) ω - (D.W.W j).W (g 0) ω) inferInstance ≤ _
    rw [heq]
    exact Probability.comap_add_le (le_iSup₂_of_le (l + 1) hl le_rfl)
      (ih (Nat.lt_of_succ_lt hl))
/-- The count on the part of a region after the start of the grid is measurable for the σ-algebra
of the counts on its successive pieces. -/
theorem regionSigma_start_le {C : Set (ℝ × E)} (hC : MeasurableSet C) {g : ℕ → ℝ}
    (hg : Monotone g) {n : ℕ} (l : ℕ) (hl : l < n) :
    D.regionSigma (C ∩ Set.Ioc (g 0) (g (l + 1)) ×ˢ Set.univ)
      ≤ ⨆ i, ⨆ _ : i < n, D.regionSigma (C ∩ Set.Ioc (g i) (g (i + 1)) ×ˢ Set.univ) := by
  induction l with
  | zero => exact le_iSup₂_of_le 0 hl le_rfl
  | succ l ih =>
    have hdisj : Disjoint (C ∩ Set.Ioc (g 0) (g (l + 1)) ×ˢ Set.univ)
        (C ∩ Set.Ioc (g (l + 1)) (g (l + 2)) ×ˢ Set.univ) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx'.2.1.1 (not_lt.2 hx.2.1.2)
    have hunion : C ∩ Set.Ioc (g 0) (g (l + 2)) ×ˢ Set.univ
        = C ∩ Set.Ioc (g 0) (g (l + 1)) ×ˢ Set.univ
          ∪ C ∩ Set.Ioc (g (l + 1)) (g (l + 2)) ×ˢ Set.univ := by
      rw [← Set.inter_union_distrib_left, ← Set.union_prod,
        Set.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le _)) (hg (Nat.le_succ _))]
    have heq : (fun ω => D.N.N ω (C ∩ Set.Ioc (g 0) (g (l + 2)) ×ˢ Set.univ))
        = fun ω => D.N.N ω (C ∩ Set.Ioc (g 0) (g (l + 1)) ×ˢ Set.univ)
          + D.N.N ω (C ∩ Set.Ioc (g (l + 1)) (g (l + 2)) ×ˢ Set.univ) := by
      funext ω
      rw [hunion, measure_union hdisj
        (hC.inter (measurableSet_Ioc.prod MeasurableSet.univ))]
    change MeasurableSpace.comap
      (fun ω => D.N.N ω (C ∩ Set.Ioc (g 0) (g (l + 2)) ×ˢ Set.univ)) inferInstance ≤ _
    rw [heq]
    exact Probability.comap_add_le (ih (Nat.lt_of_succ_lt hl))
      (le_iSup₂_of_le (l + 1) hl le_rfl)
theorem stepSigma_start_le {m : ℕ} (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k))
    {g : ℕ → ℝ} (hg : Monotone g) (n : ℕ) :
    (⨆ l, ⨆ _ : l < n,
        D.stepSigma (fun k => C k ∩ Set.Ioc (g 0) (g (l + 1)) ×ˢ Set.univ) (g 0) (g (l + 1)))
      ≤ ⨆ l, ⨆ _ : l < n,
        D.stepSigma (fun k => C k ∩ Set.Ioc (g l) (g (l + 1)) ×ˢ Set.univ) (g l) (g (l + 1)) := by
  refine iSup₂_le fun l hl => sup_le (iSup_le fun j => ?_) (iSup_le fun k => ?_)
  · exact (D.incrementSigma_start_le j l hl).trans
      (iSup₂_le fun i hi => le_iSup₂_of_le i hi
        (le_sup_of_le_left (le_iSup (fun j => D.incrementSigma j (g i) (g (i + 1))) j)))
  · exact (D.regionSigma_start_le (hCm k) hg l hl).trans
      (iSup₂_le fun i hi => le_iSup₂_of_le i hi
        (le_sup_of_le_right (le_iSup
          (fun k => D.regionSigma (C k ∩ Set.Ioc (g i) (g (i + 1)) ×ˢ Set.univ)) k)))
/-- **The driver's data measured from the start of the grid is jointly independent of the
right-continuous filtration there.** -/
theorem indep_iSup_stepSigma_start {m : ℕ} (C : Fin m → Set (ℝ × E))
    (hCm : ∀ k, MeasurableSet (C k)) {g : ℕ → ℝ} (hg : StrictMono g) (hg0 : 0 ≤ g 0) (n : ℕ) :
    Indep (⨆ l, ⨆ _ : l < n,
        D.stepSigma (fun k => C k ∩ Set.Ioc (g 0) (g (l + 1)) ×ˢ Set.univ) (g 0) (g (l + 1)))
      (D.filtration.rightCont (g 0)) P :=
  indep_of_indep_of_le_left (D.indep_iSup_stepSigma C hCm hg hg0 n)
    (D.stepSigma_start_le C hCm hg.monotone n)
end LevyDriver

end LevyStochCalc.Driver


