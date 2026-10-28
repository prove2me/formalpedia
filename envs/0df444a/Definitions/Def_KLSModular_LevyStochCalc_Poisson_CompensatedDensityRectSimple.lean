-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityRectSimple
-- name    : KLSModular_LevyStochCalc_Poisson_CompensatedDensityRectSimple
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:07:42.345496+00:00
-- url     : https://prove2.me/theorems/3d1318b8-9b64-4ef2-92b7-cbf5b3e283ed
-- title:
--   Rectangle-simple functions and L² density
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `IsRectSimple g` means that $g:\Omega\times E\to\mathbb R$ is a finite linear combination of indicators of measurable rectangles $A\times B$; the class contains zero and is closed under addition, scalar multiplication, finite sums, and measurable representatives. `RectApprox μ f` means that every positive $\operatorname{ENNReal}$ tolerance admits a rectangle-simple $g$ with `eLpNorm (f-g) 2 μ` strictly below that tolerance. For every finite measure $\mu$ on $\Omega\times E$, `rectSimple_dense_L2` gives a rectangle-simple approximation with error at most any nonzero $\operatorname{ENNReal}$ tolerance; `lintegral_prod_trim_left` supplies the corresponding trimmed-product iterated-integral identity.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.CompensatedDensityShifted
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def IsRectSimple (g : Ω × E → ℝ) : Prop :=
--     ∃ L : List (ℝ × Set Ω × Set E),
--       (∀ t ∈ L, MeasurableSet t.2.1 ∧ MeasurableSet t.2.2) ∧
--       g = fun x => (L.map (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) x)).sum
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/CompensatedDensityShifted`](https://prove2.me/theorems/73d7f46e-5093-4665-887a-486735f73664).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedDensityRectSimple.lean) · `LevyStochCalc.Poisson.CompensatedDensityRectSimple` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedDensityRectSimple.lean#L37-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedDensityRectSimple`, definition bundle `KLSModular_LevyStochCalc_Poisson_CompensatedDensityRectSimple`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedDensityShifted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedDensityRectSimple.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- A finite `ℝ`-linear combination of indicators of measurable rectangles
`A ×ˢ B ⊆ Ω × E`. -/
def IsRectSimple (g : Ω × E → ℝ) : Prop :=
  ∃ L : List (ℝ × Set Ω × Set E),
    (∀ t ∈ L, MeasurableSet t.2.1 ∧ MeasurableSet t.2.2) ∧
    g = fun x => (L.map (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) x)).sum
/-- The zero function is rectangle-simple (empty combination). -/
lemma IsRectSimple.zero : IsRectSimple (fun _ : Ω × E => (0 : ℝ)) :=
  ⟨[], by simp, by funext x; simp⟩
/-- The indicator of a measurable rectangle is rectangle-simple. -/
lemma IsRectSimple.rect {A : Set Ω} {B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IsRectSimple (fun x : Ω × E => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x) := by
  refine ⟨[(1, A, B)], by simp [hA, hB], ?_⟩
  funext x; simp
/-- Rectangle-simple functions are closed under addition (list concatenation). -/
lemma IsRectSimple.add {g h : Ω × E → ℝ} (hg : IsRectSimple g) (hh : IsRectSimple h) :
    IsRectSimple (g + h) := by
  obtain ⟨L₁, hL₁, hgeq⟩ := hg
  obtain ⟨L₂, hL₂, hheq⟩ := hh
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro t ht; rcases List.mem_append.mp ht with h' | h'
    exacts [hL₁ t h', hL₂ t h']
  · funext x; simp only [Pi.add_apply, hgeq, hheq, List.map_append, List.sum_append]
/-- Rectangle-simple functions are closed under scalar multiplication. -/
lemma IsRectSimple.smul {g : Ω × E → ℝ} (hg : IsRectSimple g) (c : ℝ) :
    IsRectSimple (fun x => c * g x) := by
  obtain ⟨L, hL, hgeq⟩ := hg
  refine ⟨L.map (fun t => (c * t.1, t.2.1, t.2.2)), ?_, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hL t' ht'
  · funext x
    simp only [hgeq]
    clear hgeq hL
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]; ring
/-- A rectangle-simple function is measurable. -/
lemma IsRectSimple.measurable {g : Ω × E → ℝ} (hg : IsRectSimple g) : Measurable g := by
  obtain ⟨L, hL, rfl⟩ := hg
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht := hL t (List.mem_cons_self)
    refine Measurable.add ?_ (ih (fun s hs => hL s (List.mem_cons_of_mem t hs)))
    exact measurable_const.mul (measurable_const.indicator (ht.1.prod ht.2))
/-- Rectangle-simple functions are a.e.-strongly-measurable for any measure. -/
lemma IsRectSimple.aestronglyMeasurable {g : Ω × E → ℝ} (hg : IsRectSimple g)
    (μ : Measure (Ω × E)) : MeasureTheory.AEStronglyMeasurable g μ :=
  hg.measurable.aestronglyMeasurable
/-- Rectangle-simple functions are closed under finite sums. -/
lemma IsRectSimple.sum {ι : Type*} (s : Finset ι) (f : ι → Ω × E → ℝ)
    (h : ∀ i ∈ s, IsRectSimple (f i)) : IsRectSimple (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact IsRectSimple.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
/-- `f` is approximable in `L²(μ)` by rectangle-simple functions. -/
def RectApprox (μ : Measure (Ω × E)) (f : Ω × E → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ g, IsRectSimple g ∧ MeasureTheory.eLpNorm (f - g) 2 μ < ε
/-- **Indicators of measurable sets are rectangle-approximable in `L²`** (finite `μ`).
Monotone-class induction over the rectangle π-system (`isPiSystem_prod`): rectangles are
exact; the empty set and complements/countable disjoint unions follow from subspace
structure + `L²`-tail control. **General `E` — no countable generation needed.** -/
lemma rectApprox_indicator (μ : Measure (Ω × E)) [IsFiniteMeasure μ]
    {C : Set (Ω × E)} (hC : MeasurableSet C) :
    RectApprox μ (C.indicator (fun _ => (1 : ℝ))) := by
  induction C, hC using
      MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty =>
    intro ε hε
    refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
    rw [show ((∅ : Set (Ω × E)).indicator (fun _ => (1 : ℝ))) - (fun _ => 0) = 0 from by
      funext x; simp]
    rwa [MeasureTheory.eLpNorm_zero]
  | basic u hu =>
    obtain ⟨A, hA, B, hB, rfl⟩ := Set.mem_image2.mp hu
    intro ε hε
    refine ⟨fun x => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x, IsRectSimple.rect hA hB, ?_⟩
    rw [show ((A ×ˢ B).indicator (fun _ => (1 : ℝ)))
          - (fun x => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x) = 0 from by funext x; simp]
    rwa [MeasureTheory.eLpNorm_zero]
  | compl u hu ih =>
    intro ε hε
    obtain ⟨g, hg, hgerr⟩ := ih ε hε
    refine ⟨(fun x => (Set.univ ×ˢ Set.univ).indicator (fun _ => (1 : ℝ)) x)
        + (fun x => -1 * g x),
      (IsRectSimple.rect MeasurableSet.univ MeasurableSet.univ).add (hg.smul (-1)), ?_⟩
    have heq : (uᶜ.indicator (fun _ => (1 : ℝ)))
        - ((fun x => (Set.univ ×ˢ Set.univ).indicator (fun _ => (1 : ℝ)) x) + (fun x => -1 * g x))
        = -(u.indicator (fun _ => (1 : ℝ)) - g) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      by_cases hx : x ∈ u
      · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx),
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_univ _⟩)]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx),
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_univ _⟩)]; ring
    rw [heq, MeasureTheory.eLpNorm_neg]
    exact hgerr
  | iUnion F hFd hFm ih =>
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · -- `ε = ⊤`: the zero approximant already has finite `L²` norm (finite measure).
      refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
      rw [show ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - fun _ => (0 : ℝ))
            = (⋃ i, F i).indicator (fun _ => (1 : ℝ)) from by funext x; simp,
        MeasureTheory.eLpNorm_indicator_const (MeasurableSet.iUnion hFm)
          (by norm_num) (by norm_num)]
      simp only [enorm_one, one_mul]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top _ _)
    have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
    set S : ℕ → Set (Ω × E) := fun N => ⋃ i ∈ Finset.range N, F i with hSdef
    have hSmono : Monotone S := fun a b hab =>
      Set.biUnion_subset_biUnion_left (fun i hi =>
        Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hab))
    have hSunion : ⋃ N, S N = ⋃ i, F i := by
      ext x; simp only [hSdef, Set.mem_iUnion, Finset.mem_range]
      exact ⟨fun ⟨_, i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i + 1, i, Nat.lt_succ_self i, hx⟩⟩
    have hSmeas : ∀ N, MeasurableSet (S N) := fun N =>
      MeasurableSet.biUnion (Set.to_countable _) (fun i _ => hFm i)
    have hSsub : ∀ N, S N ⊆ ⋃ i, F i := fun N => hSunion ▸ Set.subset_iUnion S N
    -- the partial unions are disjoint sums of the `F i`.
    have hSsum : ∀ N, (S N).indicator (fun _ => (1 : ℝ))
        = ∑ i ∈ Finset.range N, (F i).indicator (fun _ => 1) := by
      intro N
      induction N with
      | zero => ext x; simp [hSdef]
      | succ n ih =>
        have hSsucc : S (n + 1) = S n ∪ F n := by
          simp only [hSdef, Finset.range_add_one, Finset.set_biUnion_insert]
          rw [Set.union_comm]
        have hdisj : Disjoint (S n) (F n) := by
          simp only [hSdef]
          rw [Set.disjoint_iUnion₂_left]
          exact fun i hi => hFd (Finset.mem_range.mp hi).ne
        rw [hSsucc, Set.indicator_union_of_disjoint hdisj, ih, Finset.sum_range_succ]
        rfl
    -- `μ((⋃F) \ Sₙ) → 0`, so the `L²` tail is eventually `< ε/2`.
    have hdiff_tend : Filter.Tendsto (fun N => μ ((⋃ i, F i) \ S N)) Filter.atTop (nhds 0) := by
      have hrw : ∀ N, μ ((⋃ i, F i) \ S N) = μ (⋃ i, F i) - μ (S N) := fun N =>
        measure_sdiff (hSsub N) (hSmeas N).nullMeasurableSet (measure_ne_top _ _)
      simp_rw [hrw]
      rw [show (0 : ℝ≥0∞) = μ (⋃ i, F i) - μ (⋃ i, F i) from (tsub_self _).symm]
      exact ENNReal.Tendsto.sub tendsto_const_nhds
        (hSunion ▸ tendsto_measure_iUnion_atTop hSmono) (Or.inl (measure_ne_top _ _))
    obtain ⟨N, hN⟩ := (hdiff_tend.eventually
      (gt_mem_nhds (show (0 : ℝ≥0∞) < (ε / 2) ^ 2 from by positivity))).exists
    -- approximate each `F i` (i < N) within `ε / (2·N)`.
    have hδ : (0 : ℝ≥0∞) < ε / 2 / N := ENNReal.div_pos hε2.ne' (by simp)
    choose g hg hgerr using fun i => ih i (ε / 2 / N) hδ
    refine ⟨∑ i ∈ Finset.range N, g i, IsRectSimple.sum _ _ (fun i _ => hg i), ?_⟩
    -- split: tail + finite-sum error.
    have htail : MeasureTheory.eLpNorm
        ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1)) 2 μ < ε / 2 := by
      rw [show ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1))
            = ((⋃ i, F i) \ S N).indicator (fun _ => 1) from
          (Set.indicator_sdiff (hSsub N) _).symm,
        MeasureTheory.eLpNorm_indicator_const
          (MeasurableSet.diff (MeasurableSet.iUnion hFm) (hSmeas N))
          (by norm_num) (by norm_num)]
      simp only [enorm_one, one_mul]
      calc (μ ((⋃ i, F i) \ S N)) ^ (1 / (2 : ℝ≥0∞).toReal)
          < ((ε / 2) ^ 2) ^ (1 / (2 : ℝ≥0∞).toReal) := by
            apply ENNReal.rpow_lt_rpow hN (by norm_num)
        _ = ε / 2 := by
            have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
            rw [h2, ← ENNReal.rpow_natCast (ε / 2) 2, ← ENNReal.rpow_mul,
              show ((2 : ℕ) : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
    -- the finite-sum error is `≤ ε/2` (with `0 ≤ ε/2` covering the `N = 0` corner).
    have hfin_le : MeasureTheory.eLpNorm
        ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) 2 μ ≤ ε / 2 := by
      rw [hSsum, ← Finset.sum_sub_distrib]
      refine le_trans (MeasureTheory.eLpNorm_sum_le
        (fun i _ => ((measurable_const.indicator (hFm i)).aestronglyMeasurable.sub
          ((hg i).aestronglyMeasurable μ))) (by norm_num)) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ => (hgerr i).le)) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos N with hN0 | hN0
      · simp [hN0]
      · exact le_of_eq (ENNReal.mul_div_cancel (by exact_mod_cast hN0.ne') (by simp))
    have hfin_ne : MeasureTheory.eLpNorm
        ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) 2 μ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.div_ne_top hεtop (by norm_num)) hfin_le
    calc MeasureTheory.eLpNorm ((⋃ i, F i).indicator (fun _ => (1 : ℝ))
            - ∑ i ∈ Finset.range N, g i) 2 μ
        ≤ MeasureTheory.eLpNorm
              ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1)) 2 μ
            + MeasureTheory.eLpNorm
              ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) 2 μ := by
          rw [show ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i)
                = ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1))
                  + ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) from by
              funext x
              simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply]
              ring]
          exact MeasureTheory.eLpNorm_add_le
            ((measurable_const.indicator (MeasurableSet.iUnion hFm)).aestronglyMeasurable.sub
              (measurable_const.indicator (hSmeas N)).aestronglyMeasurable)
            ((measurable_const.indicator (hSmeas N)).aestronglyMeasurable.sub
              ((IsRectSimple.sum _ _ (fun i _ => hg i)).aestronglyMeasurable μ)) (by norm_num)
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add_of_lt_of_le hfin_ne htail hfin_le
      _ = ε := ENNReal.add_halves ε
/-- Rectangle-approximability in `L²` is preserved under scalar multiplication. -/
lemma RectApprox.const_smul {μ : Measure (Ω × E)} {f : Ω × E → ℝ}
    (hf : RectApprox μ f) (c : ℝ) : RectApprox μ (c • f) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]
    intro ε hε
    refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
    rw [show (0 : Ω × E → ℝ) - (fun _ => 0) = 0 from by funext x; simp,
      MeasureTheory.eLpNorm_zero]
    exact hε
  · intro ε hε
    have hcn : ‖c‖ₑ ≠ 0 := by simp [hc]
    obtain ⟨g, hg, hgerr⟩ := hf (ε / ‖c‖ₑ) (ENNReal.div_pos hε.ne' enorm_ne_top)
    refine ⟨c • g, hg.smul c, ?_⟩
    rw [show c • f - c • g = c • (f - g) from (smul_sub c f g).symm,
      MeasureTheory.eLpNorm_const_smul]
    calc ‖c‖ₑ * MeasureTheory.eLpNorm (f - g) 2 μ
        < ‖c‖ₑ * (ε / ‖c‖ₑ) := ENNReal.mul_lt_mul_right hcn enorm_ne_top hgerr
      _ = ε := ENNReal.mul_div_cancel hcn enorm_ne_top
/-- The indicator of a measurable set scaled by a constant is `L²`-approximable by
rectangle-simple functions (finite measure, **general `E`**). -/
lemma rectApprox_indicator_const (μ : Measure (Ω × E)) [IsFiniteMeasure μ]
    {s : Set (Ω × E)} (hs : MeasurableSet s) (c : ℝ) :
    RectApprox μ (s.indicator (fun _ => c)) := by
  have h := (rectApprox_indicator μ hs).const_smul c
  rwa [show c • s.indicator (fun _ => (1 : ℝ)) = s.indicator (fun _ => c) from by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]] at h
/-- **Rectangle-simple functions are dense in `L²(μ)`** for any finite measure `μ` on
`Ω × E`, with **no countable-generation/standard-Borel hypothesis on the mark space `E`**.
Reduces (via `MemLp.induction_dense`) to the indicator case `rectApprox_indicator_const`,
using closure of `IsRectSimple` under addition. -/
lemma rectSimple_dense_L2 (μ : Measure (Ω × E)) [IsFiniteMeasure μ] {f : Ω × E → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, IsRectSimple g ∧ MeasureTheory.eLpNorm (f - g) 2 μ ≤ ε := by
  obtain ⟨g, hgerr, hg⟩ := MeasureTheory.MemLp.induction_dense (by norm_num) IsRectSimple
    (fun c s hs hμs ε' hε' => by
      obtain ⟨g, hg, hgerr⟩ := rectApprox_indicator_const μ hs c ε' (pos_iff_ne_zero.mpr hε')
      exact ⟨g, by rw [MeasureTheory.eLpNorm_sub_comm]; exact hgerr.le, hg⟩)
    (fun f g hf hg => hf.add hg) (fun f hf => hf.aestronglyMeasurable μ) hf hε
  exact ⟨g, hg, hgerr⟩
omit [MeasurableSpace Ω] in
/-- **Trim–product iterated-lintegral bridge.** For a sub-σ-algebra `m ≤ m₀` on `Ω`
and an `m ⊗ E`-measurable `F : Ω × E → ℝ≥0∞`, the integral against the product
`(P.trim hm) ⊗ ν` equals the iterated integral against `ν` then `P`. (Tonelli on the
trimmed space, then `lintegral_trim` on the `m`-measurable inner integral.) -/
lemma lintegral_prod_trim_left
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} {ν : Measure E} [SigmaFinite ν]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {F : Ω × E → ℝ≥0∞} (hF : @Measurable (Ω × E) ℝ≥0∞ (m.prod inferInstance) _ F) :
    ∫⁻ q, F q ∂((P.trim hm).prod ν) = ∫⁻ ω, ∫⁻ e, F (ω, e) ∂ν ∂P := by
  rw [MeasureTheory.lintegral_prod _ hF.aemeasurable]
  exact MeasureTheory.lintegral_trim hm
    (@Measurable.lintegral_prod_right' Ω E m _ ν _ F hF)
/-- A rectangle-simple function is a finite `Fin`-indexed sum of separable
indicator products `aₖ · 𝟙_{Aₖ}(ω) · 𝟙_{Bₖ}(e)`, with `Aₖ`, `Bₖ` measurable in the
ambient σ-algebras. (Repackages the defining `List` into a `Fin`-indexed family.) -/
lemma IsRectSimple.eq_finSum {g : Ω × E → ℝ} (hg : IsRectSimple g) :
    ∃ (K : ℕ) (a : Fin K → ℝ) (A : Fin K → Set Ω) (B : Fin K → Set E),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, MeasurableSet (B k)) ∧
      (∀ ω e, g (ω, e) = ∑ k : Fin K, a k * (A k).indicator (fun _ => (1 : ℝ)) ω
                              * (B k).indicator (fun _ => (1 : ℝ)) e) := by
  classical
  obtain ⟨L, hL, hgeq⟩ := hg
  refine ⟨L.length, fun k => (L.get k).1, fun k => (L.get k).2.1, fun k => (L.get k).2.2,
    fun k => (hL (L.get k) (List.get_mem L k)).1,
    fun k => (hL (L.get k) (List.get_mem L k)).2, ?_⟩
  intro ω e
  rw [hgeq]
  change (L.map (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) (ω, e))).sum = _
  rw [← List.ofFn_getElem_eq_map L
        (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) (ω, e)),
      Fin.sum_ofFn]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [List.get_eq_getElem]
  rw [show ((L[(k : ℕ)]).2.1 ×ˢ (L[(k : ℕ)]).2.2).indicator (fun _ => (1 : ℝ)) (ω, e)
        = ((L[(k : ℕ)]).2.1).indicator (fun _ => (1 : ℝ)) ω
          * ((L[(k : ℕ)]).2.2).indicator (fun _ => (1 : ℝ)) e from by
    by_cases hω : ω ∈ (L[(k : ℕ)]).2.1 <;> by_cases he : e ∈ (L[(k : ℕ)]).2.2 <;>
      simp [Set.mem_prod, hω, he]]
  ring
end Compensated
end Poisson
end LevyStochCalc


