-- Prove2me | Definitions.Def_OAIQ5T5000
-- name    : OAIQ5T5000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T11:57:23.347701+00:00
-- url     : https://prove2.me/theorems/93e9b782-7d71-45cc-86ad-7801dc28fec2
-- title:
--   Definitions bundle OAIQ5T5000 of the split of OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarL1.planar_graph_metrics_embed_L1`, carved from OpenAI's openai/math development (OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion*, OpenAI Math Release, September 23, 2026, result family 89, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1402 declarations of OpenAI's Lean: 630 definitions, 49 inductive types or structures, 24 instances and 699 theorems. The definitions and types are `OAI.PlanarL1.Clipping.clip`, `OAI.PlanarL1.Clipping.envelope`, `OAI.PlanarL1.Clipping.heightShield`, `OAI.PlanarL1.Clipping.orderedBranch`, `OAI.PlanarL1.ColumnOrder.BranchModel`, `OAI.PlanarL1.ColumnOrder.JumpsAcross`, `OAI.PlanarL1.ColumnOrder.Noncrossing`, `OAI.PlanarL1.ColumnOrder.componentAbove`, `OAI.PlanarL1.ColumnOrder.componentColumns`, `OAI.PlanarL1.Columns.Consecutive`, `OAI.PlanarL1.Columns.Model`, `OAI.PlanarL1.Columns.Model.Activity`, `OAI.PlanarL1.Columns.Model.Activity.component`, `OAI.PlanarL1.Columns.Model.Activity.cost`, `OAI.PlanarL1.Columns.Model.Activity.dilate`, `OAI.PlanarL1.Columns.Model.Activity.graph`, `OAI.PlanarL1.Columns.Model.Activity.indicator`, `OAI.PlanarL1.Columns.Model.Activity.movement`, `OAI.PlanarL1.Columns.Model.Activity.pathCost`, `OAI.PlanarL1.Columns.Model.Activity.vector`, `OAI.PlanarL1.Columns.Model.Ambient`, `OAI.PlanarL1.Columns.Model.Ambient.Common`, `OAI.PlanarL1.Columns.Model.Ambient.History`, `OAI.PlanarL1.Columns.Model.Ambient.History.append`, `OAI.PlanarL1.Columns.Model.Ambient.History.dilate`, `OAI.PlanarL1.Columns.Model.Ambient.History.empty`, `OAI.PlanarL1.Columns.Model.Ambient.History.field`, `OAI.PlanarL1.Columns.Model.Ambient.dilate`, `OAI.PlanarL1.Columns.Model.Ambient.historyField`, `OAI.PlanarL1.Columns.Model.Ambient.point`, `OAI.PlanarL1.Columns.Model.Ambient.scaleEquiv`, `OAI.PlanarL1.Columns.Model.BData`, `OAI.PlanarL1.Columns.Model.BData.Auxiliary`, `OAI.PlanarL1.Columns.Model.BData.Recorded`, `OAI.PlanarL1.Columns.Model.BData.Uses`, `OAI.PlanarL1.Columns.Model.BData.auxiliaryField`, `OAI.PlanarL1.Columns.Model.BData.band`, `OAI.PlanarL1.Columns.Model.BData.comparison`, `OAI.PlanarL1.Columns.Model.BData.dilate`, `OAI.PlanarL1.Columns.Model.BData.field` and 639 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/PlanarL1, in whole or in part: `PlanarL1_Ambient`, `PlanarL1_BandTrees`, `PlanarL1_Bands`, `PlanarL1_Clipping`, `PlanarL1_Columns`, `PlanarL1_CoupledState`, `PlanarL1_Crossings`, `PlanarL1_CutExtraction`, `PlanarL1_Cuts`, `PlanarL1_Dilation`, `PlanarL1_Distance`, `PlanarL1_Drawing`, `PlanarL1_Embedding`, `PlanarL1_Execution`, `PlanarL1_FamilyPersistence`, `PlanarL1_Fields`, `PlanarL1_FiniteL1`, `PlanarL1_Gluing`, `PlanarL1_Growth`, `PlanarL1_HeightTree`, `PlanarL1_Increments`, `PlanarL1_Interpolation`, `PlanarL1_Layout`, `PlanarL1_LocalPersistence`, `PlanarL1_MainCells`, `PlanarL1_MainFamily`, `PlanarL1_MainGain`, `PlanarL1_MainPersistence`, `PlanarL1_MainStep`, `PlanarL1_Movement`, `PlanarL1_Noncrossing`, `PlanarL1_Order`, `PlanarL1_OrderedState`, `PlanarL1_OrdinaryState`, `PlanarL1_PairGeometry`, `PlanarL1_PairSelection`, `PlanarL1_Parameters`, `PlanarL1_Persistence`, `PlanarL1_PlanarMetric`, `PlanarL1_Polygonal`, `PlanarL1_Probability`, `PlanarL1_RadialTree`, `PlanarL1_Retubing`, `PlanarL1_ScaleHistory`, `PlanarL1_Schedule`, `PlanarL1_SecondaryBatch`, `PlanarL1_SecondaryCells`, `PlanarL1_SecondaryFamily`, `PlanarL1_SecondaryGain`, `PlanarL1_SecondaryStep`, `PlanarL1_SeedPacking`, `PlanarL1_SelectedGain`, `PlanarL1_Separation`, `PlanarL1_Stem`, `PlanarL1_StepSuccess`, `PlanarL1_Surgery`, `PlanarL1_SurvivingSeeds`, `PlanarL1_Threshold`, `PlanarL1_Tiling`, `PlanarL1_TreeDisk`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5T5002`; the statement `OAI.PlanarL1.Columns.Model.World.run_success_probability`; the proof of `OAI.PlanarL1.Columns.Model.World.run_success_probability`.
-- source:
--   OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 89; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/PlanarL1 at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ5_T5.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Clipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Clipping

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

/-- The literal capped frontier extension; the empty frontier contributes
+infinity before taking the minimum, so the finite result is the cap. -/
noncomputable def envelope (S : Set X) (s : X → ℝ) (cap t : ℝ) (x : X) : ℝ := by
  classical
  exact if S.Nonempty then min cap (sInf ((fun z => s z+t*dist x z) '' S)) else cap

lemma envelope_le_cap (S : Set X) (s : X → ℝ) (cap t : ℝ) (x : X) :
    envelope S s cap t x ≤ cap := by
  classical
  unfold envelope
  split
  · exact min_le_left _ _
  · rfl

lemma cost_continuousOn {S : Set X} {s : X → ℝ} (hs : ContinuousOn s S) (t : ℝ) (x : X) :
    ContinuousOn (fun z => s z+t*dist x z) S :=
  hs.add (continuous_const.mul (continuous_const.dist continuous_id)).continuousOn

lemma inf_attained {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (hne : S.Nonempty) (t : ℝ) (x : X) :
    ∃ z ∈ S, sInf ((fun z => s z+t*dist x z) '' S) = s z+t*dist x z := by
  obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn hne (cost_continuousOn hs t x)
  refine ⟨z,hz,le_antisymm ?_ ?_⟩
  · exact csInf_le (hS.image_of_continuousOn (cost_continuousOn hs t x)).bddBelow
      ⟨z,hz,rfl⟩
  · apply le_csInf (hne.image _)
    rintro _ ⟨y,hy,rfl⟩
    exact hmin hy

lemma envelope_le_cost {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (cap t : ℝ) (x : X) {z : X} (hz : z ∈ S) :
    envelope S s cap t x ≤ s z+t*dist x z := by
  classical
  rw [envelope,ite_eq_left ⟨z,hz⟩]
  exact (min_le_right _ _).trans (csInf_le
    (hS.image_of_continuousOn (cost_continuousOn hs t x)).bddBelow ⟨z,hz,rfl⟩)

lemma envelope_frontier {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (cap t : ℝ) {x : X} (hx : x ∈ S) : envelope S s cap t x ≤ s x := by
  simpa only [dist_self,mul_zero,add_zero] using envelope_le_cost hS hs cap t x hx

lemma envelope_cases {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (cap t : ℝ) (x : X) :
    envelope S s cap t x = cap ∨
      ∃ z ∈ S, envelope S s cap t x = s z+t*dist x z := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨z,hz,he⟩ := inf_attained hS hs hn t x
    rw [envelope,ite_eq_left hn,he]
    rcases le_total cap (s z+t*dist x z) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr ⟨z,hz,min_eq_right h⟩
  · exact Or.inl (by rw [envelope,ite_eq_right hn])

lemma envelope_one_sided {S : Set X} {s : X → ℝ} (hS : IsCompact S)
    (hs : ContinuousOn s S) (cap : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    envelope S s cap t x ≤ envelope S s cap t y+t*dist x y := by
  obtain h | ⟨z,hz,h⟩ := envelope_cases hS hs cap t y
  · rw [h]
    exact (envelope_le_cap S s cap t x).trans (le_add_of_nonneg_right (mul_nonneg ht dist_nonneg))
  · rw [h]
    have hc := envelope_le_cost hS hs cap t x hz
    have hm := mul_le_mul_of_nonneg_left (dist_triangle x y z) ht
    linarith

lemma envelope_lipschitz {S : Set X} {s : X → ℝ} (hS : IsCompact S)
    (hs : ContinuousOn s S) (cap : ℝ) (t : ℝ≥0) : LipschitzWith t (envelope S s cap t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_le]
  have ha := envelope_one_sided hS hs cap t.coe_nonneg x y
  have hb := envelope_one_sided hS hs cap t.coe_nonneg y x
  rw [dist_comm y x] at hb
  constructor <;> linarith

/-- Single kept-cell clipping, before chart identifiers/rebasing. -/
noncomputable def clip (s F H : X → ℝ) (x : X) : ℝ := max (s x) (min (F x) (H x))

lemma clip_lipschitz {s F H : X → ℝ} {K : ℝ≥0}
    (hs : LipschitzWith K s) (hF : LipschitzWith K F) (hH : LipschitzWith K H) :
    LipschitzWith K (clip s F H) := by
  unfold clip
  simpa only [max_self] using hs.max (hF.min hH)

omit [PseudoMetricSpace X] in
lemma clip_unchanged {s F H : X → ℝ} {x : X} (h : F x ≤ s x ∨ H x ≤ s x) :
    clip s F H x = s x := by
  apply max_eq_left
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans h

end PlanarL1.Clipping


end

section

namespace PlanarL1.Clipping
open scoped NNReal

/-- Literal trapezoidal height branch, constant outside the closed band. -/
noncomputable def heightShield (lo a s α H : ℝ) : ℝ :=
  s-1+α + 3 * min 1 (max 0 (min (H-lo) (lo+a-H)) / (9*a/100))

lemma heightShield_left {lo a s α H : ℝ} (hH : H ≤ lo) :
    heightShield lo a s α H = s-1+α := by
  have hm : min (H-lo) (lo+a-H) ≤ 0 := (min_le_left _ _).trans (sub_nonpos.mpr hH)
  simp only [heightShield,max_eq_left hm,zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1),mul_zero,add_zero]

lemma heightShield_right {lo a s α H : ℝ} (hH : lo+a ≤ H) :
    heightShield lo a s α H = s-1+α := by
  have hm : min (H-lo) (lo+a-H) ≤ 0 := (min_le_right _ _).trans (sub_nonpos.mpr hH)
  simp only [heightShield,max_eq_left hm,zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1),mul_zero,add_zero]

lemma heightShield_lipschitz (lo s α : ℝ) {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨3/(9*a/100),by positivity⟩ (heightShield lo a s α) := by
  have hb : 0 < 9*a/100 := by positivity
  have hl : LipschitzWith 1 (fun H : ℝ => H-lo) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_right,NNReal.coe_one,one_mul,le_refl]
  have hr : LipschitzWith 1 (fun H : ℝ => lo+a-H) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_left,NNReal.coe_one,one_mul,le_refl]
  have hm : LipschitzWith 1 (fun H : ℝ => max 0 (min (H-lo) (lo+a-H))) := by
    simpa only [max_self, max_eq_right (show (0:ℝ≥0) ≤ 1 by norm_num)] using
      (LipschitzWith.const (0:ℝ)).max (hl.min hr)
  have hq : LipschitzWith ⟨1/(9*a/100),by positivity⟩
      (fun H : ℝ => max 0 (min (H-lo) (lo+a-H))/(9*a/100)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist _ _ ≤ (1/(9*a/100))*dist x y
    rw [Real.dist_eq,← sub_div,abs_div,abs_of_pos hb]
    have h := hm.dist_le_mul x y
    rw [Real.dist_eq,NNReal.coe_one,one_mul] at h
    calc
      _ ≤ dist x y/(9*a/100) := div_le_div_of_nonneg_right h hb.le
      _ = _ := by ring
  have hp : LipschitzWith ⟨1/(9*a/100),by positivity⟩
      (fun H : ℝ => min 1 (max 0 (min (H-lo) (lo+a-H))/(9*a/100))) := by
    exact hq.const_min 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hp.dist_le_mul x y
  change dist _ _ ≤ (1/(9*a/100))*dist x y at h
  rw [Real.dist_eq] at h
  change dist _ _ ≤ (3/(9*a/100))*dist x y
  rw [heightShield,heightShield,Real.dist_eq]
  let f (H : ℝ) := min 1 (max 0 (min (H-lo) (lo+a-H))/(9*a/100))
  change |(s-1+α+3*f x)-(s-1+α+3*f y)| ≤ (3/(9*a/100))*dist x y
  change |f x-f y| ≤ (1/(9*a/100))*dist x y at h
  calc
    _ = 3*|f x-f y| := by
      rw [show (s-1+α+3*f x)-(s-1+α+3*f y) = 3*(f x-f y) by ring,
        abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
    _ ≤ 3*((1/(9*a/100))*dist x y) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

end PlanarL1.Clipping


end

section

namespace PlanarL1.Clipping
variable {X : Type*}

noncomputable def orderedBranch (pc radius α : ℝ) (L : X → ℝ) (x : X) : ℝ :=
  pc+radius/20+4*(L x-pc)+α

lemma orderedBranch_boundary {pc radius α p : ℝ} {L : X → ℝ} {x : X}
    (hα : α ≤ radius/1000) (hL : L x ≤ p) (hp : p < pc-(65/100:ℝ)*radius) :
    orderedBranch pc radius α L x < p-(1899/1000:ℝ)*radius := by
  dsimp only [orderedBranch]
  linarith

lemma ordinary_boundary_margin {pc radius α p T : ℝ} {L : X → ℝ} {x : X} (hr : 0 ≤ radius)
    (hα : α ≤ radius/1000) (hL : L x ≤ p) (hT : T ≤ pc-(849/1000:ℝ)*radius) :
    min T (orderedBranch pc radius α L x) ≤ p-(199/1000:ℝ)*radius := by
  by_cases hp : pc-(65/100:ℝ)*radius ≤ p
  · exact (min_le_left _ _).trans (by linarith)
  · have ho := orderedBranch_boundary hα hL (lt_of_not_ge hp)
    exact (min_le_right _ _).trans (by linarith)

end PlanarL1.Clipping




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Order
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Ordered

/-- Running minimum toward a target in the circle cut at its root, index zero.
The exceptional root retains its global minimum. -/
noncomputable def running {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  if i = 0 then f 0 else (Finset.uIcc i b).inf' Finset.nonempty_uIcc f

lemma running_zero {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    running b f 0 = f 0 := by simp [running]

lemma running_le {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : running b f i ≤ f i := by
  by_cases hi : i = 0
  · simp [running, hi]
  · simp only [running, ite_eq_right hi]
    exact Finset.inf'_le f (Finset.left_mem_uIcc)

lemma le_running {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i) (i : Fin (n + 1)) : f 0 ≤ running b f i := by
  by_cases hi : i = 0
  · simp [running, hi]
  · simp only [running, ite_eq_right hi]
    exact Finset.le_inf' _ _ (fun j _ => hmin j)

lemma running_target {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    running b f b = f b := by
  by_cases hb : b = 0
  · simp [running, hb]
  · simp [running, hb]

lemma running_mono_left {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i) {i j : Fin (n + 1)} (hij : i ≤ j) (hjb : j ≤ b) :
    running b f i ≤ running b f j := by
  by_cases hi : i = 0
  · rw [hi, running_zero]
    exact le_running b f hmin j
  have hj : j ≠ 0 := by intro hj; subst j; exact hi (le_antisymm hij (Fin.zero_le i))
  simp only [running, ite_eq_right hi, ite_eq_right hj]
  apply Finset.inf'_mono f _ Finset.nonempty_uIcc
  intro z hz
  simp only [Finset.mem_uIcc, min_eq_left (hij.trans hjb), max_eq_right (hij.trans hjb), min_eq_left hjb, max_eq_right hjb] at hz ⊢
  exact ⟨hij.trans hz.1, hz.2⟩

lemma running_mono_right {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (hbi : b ≤ i) (hij : i ≤ j) :
    running b f j ≤ running b f i := by
  by_cases hi : i = 0
  · have hb : b = 0 := le_antisymm (hi ▸ hbi) (Fin.zero_le b)
    subst b
    have hj : running 0 f j ≤ f 0 := by
      by_cases hz : j = 0
      · simp [hz, running_zero]
      · simp only [running, ite_eq_right hz]
        exact Finset.inf'_le f Finset.right_mem_uIcc
    simpa only [hi, running_zero] using hj
  have hj : j ≠ 0 := by intro hj; subst j; exact hi (le_antisymm hij (Fin.zero_le i))
  simp only [running, ite_eq_right hi, ite_eq_right hj]
  apply Finset.inf'_mono f _ Finset.nonempty_uIcc
  intro z hz
  simp only [Finset.mem_uIcc, min_eq_right hbi, max_eq_left hbi, min_eq_right (hbi.trans hij), max_eq_left (hbi.trans hij)] at hz ⊢
  exact ⟨hz.1, hz.2.trans hij⟩

/-- Collision inequality for a chord is exactly what is needed to make running
minima respect its switch, including chords that straddle the target. -/
lemma running_switch {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i) {p q : Fin (n + 1)} (hpq : p < q) (he : f p = f q)
    (hcollision : p ≠ 0 → ∀ z, p ≤ z → z ≤ q → f p ≤ f z) :
    running b f p = running b f q := by
  by_cases hp : p = 0
  · rw [hp, running_zero]
    exact le_antisymm (le_running b f hmin q) ((running_le b f q).trans_eq (hp ▸ he).symm)
  have hq : q ≠ 0 := by intro hz; subst q; exact (not_lt_of_ge (Fin.zero_le p)) hpq
  simp only [running, ite_eq_right hp, ite_eq_right hq]
  by_cases hqb : q ≤ b
  · have hpb := hpq.le.trans hqb
    apply le_antisymm
    · apply Finset.inf'_mono f _ Finset.nonempty_uIcc
      intro z hz
      simp only [Finset.mem_uIcc, min_eq_left hqb, max_eq_right hqb, min_eq_left hpb, max_eq_right hpb] at hz ⊢
      exact ⟨hpq.le.trans hz.1, hz.2⟩
    · apply Finset.le_inf'
      intro z hz
      have hz' : p ≤ z ∧ z ≤ b := by
        simpa only [Finset.mem_uIcc, min_eq_left hpb, max_eq_right hpb] using hz
      by_cases hqz : q ≤ z
      · exact Finset.inf'_le f (by simpa only [Finset.mem_uIcc, min_eq_left hqb, max_eq_right hqb] using And.intro hqz hz'.2)
      · exact (Finset.inf'_le f Finset.left_mem_uIcc).trans
          (he ▸ hcollision hp z hz'.1 (lt_of_not_ge hqz).le)
  · by_cases hbp : b ≤ p
    · have hbq := hbp.trans hpq.le
      apply le_antisymm
      · apply Finset.le_inf'
        intro z hz
        have hz' : b ≤ z ∧ z ≤ q := by
          simpa only [Finset.mem_uIcc, min_eq_right hbq, max_eq_left hbq] using hz
        by_cases hzp : z ≤ p
        · exact Finset.inf'_le f (by simpa only [Finset.mem_uIcc, min_eq_right hbp, max_eq_left hbp] using And.intro hz'.1 hzp)
        · exact (Finset.inf'_le f Finset.left_mem_uIcc).trans
            (hcollision hp z (lt_of_not_ge hzp).le hz'.2)
      · apply Finset.inf'_mono f _ Finset.nonempty_uIcc
        intro z hz
        simp only [Finset.mem_uIcc, min_eq_right hbp, max_eq_left hbp, min_eq_right hbq, max_eq_left hbq] at hz ⊢
        exact ⟨hz.1, hz.2.trans hpq.le⟩
    · have hpb : p ≤ b := (lt_of_not_ge hbp).le
      have hbq : b ≤ q := (lt_of_not_ge hqb).le
      have hleft : (Finset.uIcc p b).inf' Finset.nonempty_uIcc f = f p := by
        apply le_antisymm (Finset.inf'_le f Finset.left_mem_uIcc)
        apply Finset.le_inf'
        intro z hz
        have hz' : p ≤ z ∧ z ≤ b := by
          simpa only [Finset.mem_uIcc, min_eq_left hpb, max_eq_right hpb] using hz
        exact hcollision hp z hz'.1 (hz'.2.trans hbq)
      have hright : (Finset.uIcc q b).inf' Finset.nonempty_uIcc f = f p := by
        apply le_antisymm ((Finset.inf'_le f Finset.left_mem_uIcc).trans_eq he.symm)
        apply Finset.le_inf'
        intro z hz
        have hz' : b ≤ z ∧ z ≤ q := by
          simpa only [Finset.mem_uIcc, min_eq_right hbq, max_eq_left hbq] using hz
        exact hcollision hp z (hpb.trans hz'.1) hz'.2
      exact hleft.trans hright.symm

lemma finite_inf_lipschitz {X ι : Type*} [PseudoMetricSpace X] (S : Finset ι)
    (hne : S.Nonempty) (f : ι → X → ℝ) (L : NNReal)
    (hf : ∀ i ∈ S, LipschitzWith L (f i)) :
    LipschitzWith L (fun x => S.inf' hne (fun i => f i x)) := by
  have hbound (x y : X) : S.inf' hne (fun i => f i x) - S.inf' hne (fun i => f i y) ≤
      L * dist x y := by
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hne (fun i => f i y)
    have hl := (hf i hi).dist_le_mul x y
    rw [Real.dist_eq] at hl
    have hle := Finset.inf'_le (fun i => f i x) hi
    rw [he]
    linarith [(abs_le.mp hl).2]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hbound y x
    rw [dist_comm y x] at h
    linarith
  · exact hbound x y

lemma running_lipschitz {n : ℕ} {X : Type*} [PseudoMetricSpace X] (b i : Fin (n + 1))
    (f : Fin (n + 1) → X → ℝ) (L : NNReal) (hf : ∀ j, LipschitzWith L (f j)) :
    LipschitzWith L (fun x => running b (fun j => f j x) i) := by
  by_cases hi : i = 0
  · simpa only [hi, running_zero] using hf 0
  · simp only [running, ite_eq_right hi]
    exact finite_inf_lipschitz _ _ f L (fun j _ => hf j)

end PlanarL1.Ordered

end

section

namespace PlanarL1.Ordered

lemma rotate_unimodal_neg {k : ℕ} (b : Fin (k+1)) (f : Fin (k+1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i)
    (hl : ∀ i j, i ≤ j → j ≤ b → f i ≤ f j)
    (hr : ∀ i j, b ≤ i → i ≤ j → f j ≤ f i) :
    (∀ i, -f b ≤ -f (i+b)) ∧
    (∀ i j : Fin (k+1), i ≤ j → j ≤ -b → -f (i+b) ≤ -f (j+b)) ∧
    (∀ i j : Fin (k+1), -b ≤ i → i ≤ j → -f (j+b) ≤ -f (i+b)) := by
  have hmax (i : Fin (k+1)) : f i ≤ f b := by
    rcases le_total i b with hi | hi
    · exact hl i b hi le_rfl
    · exact hr b i le_rfl hi
  by_cases hb : b=0
  · have he (i : Fin (k+1)) : f i=f 0 := le_antisymm (hb ▸ hmax i) (hmin i)
    simp only [he,le_refl,implies_true,and_self]
  have hbpos : 0 < b.val := by exact Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
  have hv : (-b).val=k+1-b.val := by
    simp only [Fin.val_neg,ite_eq_right hb]
  have add_before (i : Fin (k+1)) (hi : i < -b) : (i+b).val=i.val+b.val := by
    rw [Fin.val_add,Nat.mod_eq_of_lt]
    change i.val < (-b).val at hi
    rw [hv] at hi
    omega
  have add_after (i : Fin (k+1)) (hi : -b ≤ i) :
      (i+b).val=i.val+b.val-(k+1) := by
    rw [Fin.val_add,Nat.mod_eq_sub_mod (by change (-b).val ≤ i.val at hi; rw [hv] at hi; omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun i => neg_le_neg (hmax _),?_,?_⟩
  · intro i j hij hj
    by_cases he : j = -b
    · rw [he,neg_add_cancel]
      exact neg_le_neg (hmin _)
    · have hjs : j < -b := lt_of_le_of_ne hj he
      have his : i < -b := hij.trans_lt hjs
      apply neg_le_neg
      apply hr
      · change b.val ≤ (i+b).val
        rw [add_before i his]
        omega
      · change (i+b).val ≤ (j+b).val
        rw [add_before i his,add_before j hjs]
        exact Nat.add_le_add_right hij b.val
  · intro i j hi hij
    apply neg_le_neg
    apply hl
    · change (i+b).val ≤ (j+b).val
      rw [add_after i hi,add_after j (hi.trans hij)]
      exact Nat.sub_le_sub_right (Nat.add_le_add_right hij b.val) _
    · change (j+b).val ≤ b.val
      rw [add_after j (hi.trans hij)]
      omega
end PlanarL1.Ordered


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Noncrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
/-! ## Noncrossing column words 
These are the exact combinatorial separation tools used in the surviving-seed
packing argument. The circular set has been cut at index 0. -/

namespace ColumnOrder

/-- No two links have four alternating, distinct endpoints in cyclic order. -/
def Noncrossing {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    ¬ (G.Adj a c ∧ G.Adj b d)

lemma noncrossing_comap_rotate {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hG : Noncrossing G) : Noncrossing (G.comap (finRotate (n + 1))) := by
  intro a b c d hab hbc hcd h
  have ha : a ≠ Fin.last n := by intro he; subst a; exact (not_lt_of_ge b.le_last) hab
  have hb : b ≠ Fin.last n := by intro he; subst b; exact (not_lt_of_ge c.le_last) hbc
  have hc : c ≠ Fin.last n := by intro he; subst c; exact (not_lt_of_ge d.le_last) hcd
  have hab' : finRotate _ a < finRotate _ b := by
    rw [Fin.lt_def, coe_finRotate_of_ne_last ha, coe_finRotate_of_ne_last hb]
    exact Nat.add_lt_add_right hab 1
  have hbc' : finRotate _ b < finRotate _ c := by
    rw [Fin.lt_def, coe_finRotate_of_ne_last hb, coe_finRotate_of_ne_last hc]
    exact Nat.add_lt_add_right hbc 1
  change G.Adj (finRotate _ a) (finRotate _ c) ∧ G.Adj (finRotate _ b) (finRotate _ d) at h
  by_cases hd : d = Fin.last n
  · have hz : (0 : Fin (n + 1)) < finRotate _ a := by
      rw [Fin.lt_def, coe_finRotate_of_ne_last ha]
      exact Nat.zero_lt_succ _
    rw [hd, finRotate_last] at h
    exact hG 0 (finRotate _ a) (finRotate _ b) (finRotate _ c) hz hab' hbc' ⟨h.2.symm,h.1⟩
  · have hcd' : finRotate _ c < finRotate _ d := by
      rw [Fin.lt_def, coe_finRotate_of_ne_last hc, coe_finRotate_of_ne_last hd]
      exact Nat.add_lt_add_right hcd 1
    exact hG _ _ _ _ hab' hbc' hcd' h

lemma noncrossing_comap_iterate {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hG : Noncrossing G) (k : ℕ) : Noncrossing (G.comap ((finRotate (n + 1))^[k])) := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    have h := noncrossing_comap_rotate ih
    simpa only [Function.iterate_succ, SimpleGraph.comap_comap] using h

lemma noncrossing_comap_cycle {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hG : Noncrossing G) (a : Fin (n + 1)) : Noncrossing (G.comap (finCycle a)) := by
  rw [finCycle_eq_finRotate_iterate]
  exact noncrossing_comap_iterate hG a.val


/-- An edge cannot leave the strict interior of a chord without meeting one
of the chord endpoints. -/
theorem adj_stays_between {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b x y : Fin n} (hab : G.Adj a b)
    (hax : a < x) (hxb : x < b) (hxy : G.Adj x y)
    (hya : y ≠ a) (hyb : y ≠ b) : a < y ∧ y < b := by
  have hleft : ¬ y < a := by
    intro h
    exact hnc y a x b h hax hxb ⟨hxy.symm, hab⟩
  have hright : ¬ b < y := by
    intro h
    exact hnc a x b y hax hxb h ⟨hab, hxy⟩
  constructor <;> omega

/-- A column word avoiding the endpoints of a chord remains on its starting
strict side. This is the induction behind the chord-separation lemma. -/
theorem walk_stays_between {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b x y : Fin n} (hab : G.Adj a b)
    (p : G.Walk x y) (hx : a < x ∧ x < b)
    (ha : a ∉ p.support) (hb : b ∉ p.support) : a < y ∧ y < b := by
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    have haz : z ≠ a := by
      intro h
      apply ha
      exact List.mem_cons_of_mem x (h ▸ p.start_mem_support)
    have hbz : z ≠ b := by
      intro h
      apply hb
      exact List.mem_cons_of_mem x (h ▸ p.start_mem_support)
    have hz := adj_stays_between hnc hab hx.1 hx.2 hxz haz hbz
    exact ih hz (fun h => ha (by simp [h])) (fun h => hb (by simp [h]))

/-- Geometry, Lemma `geo:chord-separation`, with a cut in the circular order
outside the chosen strict interval. It applies to paths as well as walks. -/
theorem chord_separation {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b x y : Fin n} (hab : G.Adj a b)
    (p : G.Walk x y) (hx : a < x ∧ x < b)
    (hy : y < a ∨ b < y) : a ∈ p.support ∨ b ∈ p.support := by
  by_contra h
  push Not at h
  have hi := walk_stays_between hnc hab p hx h.1 h.2
  rcases hy with hy | hy <;> omega

/-- Occurrence of a step of the word that skips the specified index strictly. -/
def JumpsAcross {n : ℕ} {G : SimpleGraph (Fin n)} (i : Fin n)
    {x y : Fin n} (p : G.Walk x y) : Prop :=
  ∃ e ∈ p.darts, (e.fst < i ∧ i < e.snd) ∨ (e.snd < i ∧ i < e.fst)

/-- A connected set is a barrier between any two of its vertices in the
linear order. The edge and the set's connecting paths may belong to different
subgraphs; only noncrossing in the common ambient graph matters. -/
lemma adj_between_connected {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S : Set (Fin n)} (hS : (G.induce S).Preconnected)
    {a b x y : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (hx : a < x ∧ x < b) (hxy : G.Adj x y) (hxs : x ∉ S) (hys : y ∉ S) :
    a < y ∧ y < b := by
  have hya : y ≠ a := fun h => hys (h ▸ ha)
  have hyb : y ≠ b := fun h => hys (h ▸ hb)
  obtain ⟨q⟩ := hS ⟨a, ha⟩ ⟨b, hb⟩
  let p := q.map (SimpleGraph.Embedding.induce S).toHom
  have hmem : ∀ v ∈ p.support, v ∈ S := by
    intro v hv
    obtain ⟨w, _, hw⟩ := List.mem_map.mp (by simpa only [p, SimpleGraph.Walk.support_map] using hv)
    exact hw ▸ w.property
  have hpx : x ∉ p.support := fun h => hxs (hmem x h)
  have hpy : y ∉ p.support := fun h => hys (hmem y h)
  have hleft : ¬ y < a := by
    intro h
    have he := chord_separation hnc hxy.symm p ⟨h, hx.1⟩ (Or.inr hx.2)
    exact he.elim hpy hpx
  have hright : ¬ b < y := by
    intro h
    have he := chord_separation hnc hxy p.reverse ⟨hx.2, h⟩ (Or.inl hx.1)
    exact he.elim (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hpx)
      (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hpy)
  constructor <;> omega

/-- Paths avoiding a connected set have constant membership in every interval
whose endpoints belong to that set. This is the cut-independent content of
`geo:gap`: such a path stays in one open circular gap. -/
lemma walk_same_gap {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S : Set (Fin n)} (hS : (G.induce S).Preconnected)
    {x y : Fin n} (p : G.Walk x y) (hp : ∀ v ∈ p.support, v ∉ S)
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) :
    (a < x ∧ x < b) ↔ (a < y ∧ y < b) := by
  suffices ∀ {x y : Fin n} (p : G.Walk x y), (∀ v ∈ p.support, v ∉ S) →
      a < x ∧ x < b → a < y ∧ y < b by
    constructor
    · exact this p hp
    · apply this p.reverse
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hp
  intro x y p hp hx
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    have hz := adj_between_connected hnc hS ha hb hx hxz
      (hp x (by simp)) (hp z (List.mem_cons_of_mem _ p.start_mem_support))
    exact ih (fun v hv => hp v (by simp [hv])) hz

/-- Disjoint connected vertex sets cannot have representatives in alternating
circular order. This upgrades the individual-chord barrier to branch sets. -/
lemma connected_noninterleaving {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {S T : Set (Fin n)}
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hdis : Disjoint S T) {a b c d : Fin n}
    (ha : a ∈ S) (hb : b ∈ T) (hc : c ∈ S) (hd : d ∈ T)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : False := by
  obtain ⟨q⟩ := hT ⟨b, hb⟩ ⟨d, hd⟩
  let p := q.map (SimpleGraph.Embedding.induce T).toHom
  have hp : ∀ v ∈ p.support, v ∉ S := by
    intro v hv hvs
    obtain ⟨w, _, hw⟩ := List.mem_map.mp (by simpa only [p, SimpleGraph.Walk.support_map] using hv)
    have hvt : v ∈ T := hw ▸ w.property
    exact Set.disjoint_left.mp hdis hvs hvt
  have hi := (walk_same_gap hnc hS p hp ha hc).mp ⟨hab, hbc⟩
  exact (not_lt_of_ge hcd.le) hi.2

/-- A genuine finite branch-set model of a graph minor. Each branch is
nonempty and connected; branches are disjoint and edges are witnessed by
actual ambient edges. No topological or minor-exclusion axiom is hidden here. -/
structure BranchModel {n : ℕ} {W : Type*} (H : SimpleGraph W)
    (G : SimpleGraph (Fin n)) where
  branch : W → Set (Fin n)
  nonempty : ∀ w, (branch w).Nonempty
  connected : ∀ w, (G.induce (branch w)).Preconnected
  disjoint : Pairwise (fun i j => Disjoint (branch i) (branch j))
  edge : ∀ {i j}, H.Adj i j → ∃ a ∈ branch i, ∃ b ∈ branch j, G.Adj a b

namespace BranchModel

variable {n : ℕ} {W : Type*} {H : SimpleGraph W} {G : SimpleGraph (Fin n)}

lemma representative_injective (B : BranchModel H G) (r : W → Fin n)
    (hr : ∀ i, r i ∈ B.branch i) : Function.Injective r := by
  intro i j hij
  by_contra h
  exact Set.disjoint_left.mp (B.disjoint h) (hr i) (hij ▸ hr j)

lemma union_connected (B : BranchModel H G) {i j : W} (h : H.Adj i j) :
    (G.induce (B.branch i ∪ B.branch j)).Connected := by
  obtain ⟨a, ha, b, hb, hab⟩ := B.edge h
  exact SimpleGraph.connected_induce_union (B.connected i) (B.connected j) ha hb hab

/-- Noncrossing is inherited by every genuine branch-set minor, using any
chosen representative of each branch. This proves the needed minor closure
directly from walk separation, without a planar cone or a Jordan-curve axiom. -/
lemma noncrossing (B : BranchModel H G) (hnc : Noncrossing G)
    (r : W ↪ Fin n) (hr : ∀ i, r i ∈ B.branch i) : Noncrossing (H.map r) := by
  intro a b c d hab hbc hcd he
  obtain ⟨i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj r H a c).mp he.1
  obtain ⟨k, l, hkl, rfl, rfl⟩ := (SimpleGraph.map_adj r H b d).mp he.2
  apply connected_noninterleaving hnc (B.union_connected hij).preconnected
    (B.union_connected hkl).preconnected _ (Or.inl (hr i)) (Or.inl (hr k))
    (Or.inr (hr j)) (Or.inr (hr l)) hab hbc hcd
  apply Set.disjoint_union_left.mpr
  constructor <;> apply Set.disjoint_union_right.mpr
  · constructor
    · exact B.disjoint (fun h => (ne_of_lt hab) (congrArg r h))
    · exact B.disjoint (fun h => (ne_of_lt (hab.trans (hbc.trans hcd))) (congrArg r h))
  · constructor
    · exact B.disjoint (fun h => (ne_of_lt hbc) (congrArg r h).symm)
    · exact B.disjoint (fun h => (ne_of_lt hcd) (congrArg r h))

end BranchModel

/-- For two fixed hubs in a noncrossing graph, two distinct common neighbors
must lie on opposite open circular arcs of the hubs. -/
lemma common_neighbors_opposite {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b c d : Fin n} (hab : a < b) (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) :
    (a < c ∧ c < b) ↔ ¬ (a < d ∧ d < b) := by
  have hac' := hac.ne
  have had' := had.ne
  have hbc' := hbc.ne
  have hbd' := hbd.ne
  have h1 : ¬ (a < c ∧ c < d ∧ d < b) := fun h =>
    hnc a c d b h.1 h.2.1 h.2.2 ⟨had, hbc.symm⟩
  have h2 : ¬ (a < d ∧ d < c ∧ c < b) := fun h =>
    hnc a d c b h.1 h.2.1 h.2.2 ⟨hac, hbd.symm⟩
  have h3 : ¬ (c < d ∧ d < a) := fun h =>
    hnc c d a b h.1 h.2 hab ⟨hac.symm, hbd.symm⟩
  have h4 : ¬ (d < c ∧ c < a) := fun h =>
    hnc d c a b h.1 h.2 hab ⟨had.symm, hbc.symm⟩
  have h5 : ¬ (b < c ∧ c < d) := fun h =>
    hnc a b c d hab h.1 h.2 ⟨hac, hbd⟩
  have h6 : ¬ (b < d ∧ d < c) := fun h =>
    hnc a b d c hab h.1 h.2 ⟨had, hbc⟩
  have h7 : ¬ (c < a ∧ b < d) := fun h =>
    hnc c a b d h.1 hab h.2 ⟨hbc.symm, had⟩
  have h8 : ¬ (d < a ∧ b < c) := fun h =>
    hnc d a b c h.1 hab h.2 ⟨hbd.symm, hac⟩
  omega

lemma no_three_common_neighbors {n : ℕ} {G : SimpleGraph (Fin n)}
    (hnc : Noncrossing G) {a b c d e : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e) : False := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · have h1 := common_neighbors_opposite hnc hab hcd hac had hbc hbd
    have h2 := common_neighbors_opposite hnc hab hce hac hae hbc hbe
    have h3 := common_neighbors_opposite hnc hab hde had hae hbd hbe
    tauto
  · have h1 := common_neighbors_opposite hnc hab hcd hbc hbd hac had
    have h2 := common_neighbors_opposite hnc hab hce hbc hbe hac hae
    have h3 := common_neighbors_opposite hnc hab hde hbd hbe had hae
    tauto

/-- Geometry `geo:outerplanar`: no noncrossing circular graph has a
branch-set minor with two hubs and three distinct common neighbors. -/
lemma BranchModel.no_three_common_neighbors {n : ℕ} {W : Type*}
    {H : SimpleGraph W} {G : SimpleGraph (Fin n)} (B : BranchModel H G)
    (hnc : Noncrossing G) {a b c d e : W} (hab : a ≠ b)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hac : H.Adj a c) (had : H.Adj a d) (hae : H.Adj a e)
    (hbc : H.Adj b c) (hbd : H.Adj b d) (hbe : H.Adj b e) : False := by
  classical
  let r : W → Fin n := fun i => (B.nonempty i).choose
  have hr : ∀ i, r i ∈ B.branch i := fun i => (B.nonempty i).choose_spec
  let f : W ↪ Fin n := ⟨r, B.representative_injective r hr⟩
  have he {i j : W} (h : H.Adj i j) : (H.map f).Adj (f i) (f j) :=
    (SimpleGraph.map_adj f H (f i) (f j)).mpr ⟨i, j, h, rfl, rfl⟩
  exact PlanarL1.ColumnOrder.no_three_common_neighbors (B.noncrossing hnc f hr)
    (fun h => hab (f.injective h)) (fun h => hcd (f.injective h))
    (fun h => hce (f.injective h)) (fun h => hde (f.injective h))
    (he hac) (he had) (he hae) (he hbc) (he hbd) (he hbe)

/-- Trimming a connector after its last visit to one set and before its first
visit to the other. The nonadjacency assumption guarantees a nonempty core.
The proof minimizes the number of edges, not the metric length. -/
lemma connector_core {V : Type*} {G : SimpleGraph V} {C L T : Set V}
    (hCL : Disjoint C L) (hno : ∀ x ∈ C, ∀ y ∈ L, ¬ G.Adj x y)
    {x y : V} (hx : x ∈ C) (hy : y ∈ L) (p : G.Walk x y)
    (hp : ∀ v ∈ p.support, v ∈ T) :
    ∃ K : Set V, K.Nonempty ∧ (G.induce K).Preconnected ∧ K ⊆ T ∧
      Disjoint K C ∧ Disjoint K L ∧
      (∃ a ∈ C, ∃ b ∈ K, G.Adj a b) ∧
      (∃ a ∈ L, ∃ b ∈ K, G.Adj a b) := by
  classical
  let P : ℕ → Prop := fun m => ∃ a ∈ C, ∃ b ∈ L, ∃ q : G.Walk a b,
    q.length = m ∧ ∀ v ∈ q.support, v ∈ T
  have hex : ∃ m, P m := ⟨p.length, x, hx, y, hy, p, rfl, hp⟩
  obtain ⟨a, ha, b, hb, q, hlen, hmem⟩ := Nat.find_spec hex
  have hmin {c d : V} (hc : c ∈ C) (hd : d ∈ L) (r : G.Walk c d)
      (hr : ∀ v ∈ r.support, v ∈ T) : q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨c, hc, d, hd, r, rfl, hr⟩
  cases q with
  | nil => exact False.elim (Set.disjoint_left.mp hCL ha hb)
  | @cons a c b hac q =>
    have hq : ¬ q.Nil := by
      intro h
      have he := h.eq
      subst b
      exact hno a ha c hb hac
    let r := q.dropLast
    have hlast : G.Adj q.penultimate b := q.adj_penultimate hq
    have hrmem : ∀ v ∈ r.support, v ∈ T := by
      intro v hv
      apply hmem v
      apply List.mem_cons_of_mem
      exact List.mem_of_mem_dropLast (by simpa only [r, q.support_dropLast hq] using hv)
    have hshort : r.length + 1 = q.length := q.length_dropLast_add_one hq
    have hout : ∀ v ∈ r.support, v ∉ C ∧ v ∉ L := by
      intro v hv
      constructor
      · intro hvC
        have hh := hmin hvC hb ((r.dropUntil v hv).concat hlast) (by
          intro z hz
          rw [SimpleGraph.Walk.support_concat] at hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hrmem z (r.support_dropUntil_subset_support hv hz)
          · have hz' : z = b := List.mem_singleton.mp hz
            subst z
            exact hmem b (SimpleGraph.Walk.cons hac q).end_mem_support)
        have hd := r.length_dropUntil_le_length hv
        simp only [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons] at hh
        omega
      · intro hvL
        have hh := hmin ha hvL (SimpleGraph.Walk.cons hac (r.takeUntil v hv)) (by
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · subst z
            exact hmem a (SimpleGraph.Walk.cons hac q).start_mem_support
          · exact hrmem z (r.support_takeUntil_subset_support hv hz))
        have hd := r.length_takeUntil_le_length hv
        simp only [SimpleGraph.Walk.length_cons] at hh
        omega
    refine ⟨{v | v ∈ r.support}, ⟨c, r.start_mem_support⟩,
      r.connected_induce_support.preconnected, hrmem, ?_, ?_,
      ⟨a, ha, c, r.start_mem_support, hac⟩,
      ⟨b, hb, q.penultimate, r.end_mem_support, hlast.symm⟩⟩
    · exact Set.disjoint_left.mpr (fun v hv hvC => (hout v hv).1 hvC)
    · exact Set.disjoint_left.mpr (fun v hv hvL => (hout v hv).2 hvL)

/-- Three disjoint connected connector cores between two disjoint connected
sets would give the forbidden `K₂,₃` minor. -/
lemma no_three_cores {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {C L : Set (Fin n)} (hC : C.Nonempty) (hL : L.Nonempty)
    (hc : (G.induce C).Preconnected) (hl : (G.induce L).Preconnected)
    (hCL : Disjoint C L) (K : Fin 3 → Set (Fin n))
    (hne : ∀ i, (K i).Nonempty) (hconn : ∀ i, (G.induce (K i)).Preconnected)
    (hdis : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hdC : ∀ i, Disjoint (K i) C) (hdL : ∀ i, Disjoint (K i) L)
    (heC : ∀ i, ∃ a ∈ C, ∃ b ∈ K i, G.Adj a b)
    (heL : ∀ i, ∃ a ∈ L, ∃ b ∈ K i, G.Adj a b) : False := by
  let H := completeBipartiteGraph Bool (Fin 3)
  let B : BranchModel H G := {
    branch := Sum.elim (fun b : Bool => cond b C L) K
    nonempty := by
      intro i
      rcases i with i | i
      · cases i
        · exact hL
        · exact hC
      · exact hne i
    connected := by
      intro i
      rcases i with i | i
      · cases i
        · exact hl
        · exact hc
      · exact hconn i
    disjoint := by
      intro i j hij
      rcases i with i | i <;> rcases j with j | j
      · cases i <;> cases j
        · exact False.elim (hij rfl)
        · exact hCL.symm
        · exact hCL
        · exact False.elim (hij rfl)
      · cases i
        · exact (hdL j).symm
        · exact (hdC j).symm
      · cases j
        · exact hdL i
        · exact hdC i
      · exact hdis (fun h => hij (congrArg Sum.inr h))
    edge := by
      intro i j hij
      rcases i with i | i <;> rcases j with j | j
      · simp [H, completeBipartiteGraph] at hij
      · cases i
        · exact heL j
        · exact heC j
      · cases j
        · obtain ⟨a, ha, b, hb, hab⟩ := heL i
          exact ⟨b, hb, a, ha, hab.symm⟩
        · obtain ⟨a, ha, b, hb, hab⟩ := heC i
          exact ⟨b, hb, a, ha, hab.symm⟩
      · simp [H, completeBipartiteGraph] at hij }
  apply B.no_three_common_neighbors hnc
    (a := Sum.inl false) (b := Sum.inl true)
    (c := Sum.inr 0) (d := Sum.inr 1) (e := Sum.inr 2)
  all_goals simp [H, completeBipartiteGraph]

/-- The projected disjoint short portions used in the two-portals argument
cannot exist. This includes the trimming and nonempty-interior justifications. -/
lemma no_three_connectors {n : ℕ} {G : SimpleGraph (Fin n)} (hnc : Noncrossing G)
    {C L : Set (Fin n)} (hc : (G.induce C).Preconnected)
    (hl : (G.induce L).Preconnected) (hCL : Disjoint C L)
    (hno : ∀ x ∈ C, ∀ y ∈ L, ¬ G.Adj x y)
    (x y : Fin 3 → Fin n) (hx : ∀ i, x i ∈ C) (hy : ∀ i, y i ∈ L)
    (p : ∀ i, G.Walk (x i) (y i))
    (hdis : Pairwise (fun i j => Disjoint
      {v | v ∈ (p i).support} {v | v ∈ (p j).support})) : False := by
  classical
  have hcores := fun i => connector_core hCL hno (hx i) (hy i) (p i) (fun _ h => h)
  choose K hne hk hsub hdC hdL heC heL using hcores
  exact no_three_cores hnc ⟨x 0, hx 0⟩ ⟨y 0, hy 0⟩ hc hl hCL K hne hk
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j)) hdC hdL heC heL

/-- The vertices of an induced-graph component, as a set in the original
vertex type. Components here are Mathlib's actual reachability quotients. -/
def componentColumns {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) : Set V := Subtype.val '' C.supp

lemma componentColumns_subset {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) : componentColumns C ⊆ S := by
  rintro _ ⟨v, _, rfl⟩
  exact v.property

lemma componentColumns_connected {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) : (G.induce (componentColumns C)).Connected := by
  let f : C.toSimpleGraph →g G.induce (componentColumns C) :=
    ⟨fun v => ⟨v.val.val, ⟨v.val, v.property, rfl⟩⟩, fun h => h⟩
  have : Nonempty (componentColumns C) := by
    obtain ⟨v, hv⟩ := C.nonempty_supp
    exact ⟨⟨v.val, ⟨v, hv, rfl⟩⟩⟩
  refine ⟨?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (C.reachable_toSimpleGraph hu hv).map f

lemma componentColumns_adj {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) {x y : V}
    (hx : x ∈ componentColumns C) (hxy : G.Adj x y) (hy : y ∈ S) :
    y ∈ componentColumns C := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, C.mem_supp_of_adj_mem_supp hu hxy, rfl⟩

/-- Any walk inside the induced vertex set propagates membership in an
actual connected component. -/
lemma componentColumns_of_walk {V : Type*} {G : SimpleGraph V} {S : Set V}
    (C : (G.induce S).ConnectedComponent) {x y : V} (p : G.Walk x y)
    (hx : x ∈ componentColumns C) (hp : ∀ v ∈ p.support, v ∈ S) :
    y ∈ componentColumns C := by
  induction p with
  | nil => exact hx
  | @cons x z y hxz p ih =>
    exact ih (componentColumns_adj C hx hxz (hp z (by simp)))
      (fun v hv => hp v (by simp [hv]))

/-- A nonempty induced-connected subset lies in one actual component of
any larger induced subgraph. -/
lemma exists_component_containing {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hne : S.Nonempty) (hS : (G.induce S).Preconnected) (hST : S ⊆ T) :
    ∃ C : (G.induce T).ConnectedComponent, S ⊆ componentColumns C := by
  obtain ⟨x, hx⟩ := hne
  let C := (G.induce T).connectedComponentMk ⟨x, hST hx⟩
  refine ⟨C, ?_⟩
  intro y hy
  obtain ⟨w⟩ := hS ⟨x, hx⟩ ⟨y, hy⟩
  let p := w.map (SimpleGraph.Embedding.induce S).toHom
  apply componentColumns_of_walk C p
  · exact ⟨⟨x, hST hx⟩, rfl, rfl⟩
  · intro v hv
    obtain ⟨z, _, hz⟩ := List.mem_map.mp
      (by simpa only [p, SimpleGraph.Walk.support_map] using hv)
    exact hz ▸ hST z.property

/-- Components of one induced graph sharing an original vertex are equal. -/
lemma component_eq_of_column {V : Type*} {G : SimpleGraph V} {S : Set V}
    {C D : (G.induce S).ConnectedComponent} {i : V}
    (hC : i ∈ componentColumns C) (hD : i ∈ componentColumns D) : C = D := by
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, hyx⟩ := hD
  have he : y = x := Subtype.ext hyx
  subst y
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hx hy

/-- The parent component under inclusion of vertex sets. -/
def componentAbove {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hST : S ⊆ T) (C : (G.induce S).ConnectedComponent) :
    (G.induce T).ConnectedComponent :=
  C.map ⟨fun x => ⟨x.val, hST x.property⟩, fun h => h⟩

lemma componentColumns_above {V : Type*} {G : SimpleGraph V} {S T : Set V}
    (hST : S ⊆ T) (C : (G.induce S).ConnectedComponent) :
    componentColumns C ⊆ componentColumns (componentAbove hST C) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨x.val, hST x.property⟩, ?_, rfl⟩
  change (G.induce T).connectedComponentMk _ = componentAbove hST C
  change (G.induce S).connectedComponentMk x = C at hx
  rw [← hx]
  rfl

/-- A discrete connected union of two metric balls has controlled diameter.
The single edge allowance avoids assuming any continuous realization of the
column graph. It will be absorbed by the source's 10D constant. -/
lemma connected_two_balls {V X : Type*} [PseudoMetricSpace X] {G : SimpleGraph V}
    (hG : G.Preconnected) (f : V → X) (p q : X) {R a : ℝ} (hR : 0 ≤ R)
    (ha : 0 ≤ a) (hedge : ∀ i j, G.Adj i j → dist (f i) (f j) ≤ a)
    (hcover : ∀ i, dist (f i) p ≤ R ∨ dist (f i) q ≤ R) (x y : V) :
    dist (f x) (f y) ≤ 4 * R + a := by
  have near : ∀ i j, dist (f i) p ≤ R → dist (f j) q ≤ R →
      dist p q ≤ 2 * R + a → dist (f i) (f j) ≤ 4 * R + a := by
    intro i j hi hj hpq
    have h₁ := dist_triangle (f i) p (f j)
    have h₂ := dist_triangle p q (f j)
    rw [dist_comm q (f j)] at h₂
    linarith
  by_cases hpq : dist p q ≤ 2 * R + a
  · rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
    · have h := dist_triangle (f x) p (f y)
      rw [dist_comm p (f y)] at h
      linarith
    · exact near x y hx hy hpq
    · rw [dist_comm]
      exact near y x hy hx hpq
    · have h := dist_triangle (f x) q (f y)
      rw [dist_comm q (f y)] at h
      linarith
  · have stay : ∀ {i j} (w : G.Walk i j), dist (f i) p ≤ R → dist (f j) p ≤ R := by
      intro i j w
      induction w with
      | nil => exact id
      | @cons i z j hiz w ih =>
        intro hi
        apply ih
        rcases hcover z with hz | hz
        · exact hz
        · exfalso
          apply hpq
          have h₁ := dist_triangle p (f i) q
          have h₂ := dist_triangle (f i) (f z) q
          rw [dist_comm p (f i)] at h₁
          linarith [hedge i z hiz]
    rcases hcover x with hx | hx
    · obtain ⟨w⟩ := hG x y
      have hy := stay w hx
      have h := dist_triangle (f x) p (f y)
      rw [dist_comm p (f y)] at h
      linarith
    · rcases hcover y with hy | hy
      · obtain ⟨w⟩ := hG y x
        have hx' := stay w hy
        have h := dist_triangle (f x) p (f y)
        rw [dist_comm p (f y)] at h
        linarith
      · have h := dist_triangle (f x) q (f y)
        rw [dist_comm q (f y)] at h
        linarith

/-- Walks transport through a relabelling without introducing any new visited
columns. This is used to cut the circular order at a chosen root. -/
lemma walk_comap_equiv {n : ℕ} {G : SimpleGraph (Fin n)} (e : Fin n ≃ Fin n)
    {i j : Fin n} (w : G.Walk (e i) (e j)) :
    ∃ p : (G.comap e).Walk i j, ∀ z ∈ p.support, e z ∈ w.support := by
  let f := (SimpleGraph.Iso.comap e G).symm.toHom
  have hi : f (e i) = i := e.symm_apply_apply i
  have hj : f (e j) = j := e.symm_apply_apply j
  refine ⟨(w.map f).copy hi hj, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨v,hv,hvz⟩ := hz
  have he : e.symm v = z := hvz
  rw [← he, e.apply_symm_apply]
  exact hv

/-- Collision inequality for a profile whose strict sublevels connect back to
zero. The ceiling is kept explicit: only thresholds at or below it are used. -/
lemma collision {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hnc : Noncrossing G) (f : Fin (n + 1) → ℝ) (D : ℝ)
    (hbound : ∀ i, f i ≤ D)
    (hpath : ∀ t ≤ D, ∀ i, f i < t →
      ∃ w : G.Walk i 0, ∀ z ∈ w.support, f z < t)
    {p q : Fin (n + 1)} (_hpq : p < q) (hadj : G.Adj p q) (heq : f p = f q)
    (hp : p ≠ 0) (z : Fin (n + 1)) (hpz : p ≤ z) (hzq : z ≤ q) : f p ≤ f z := by
  by_contra hn
  have hz : f z < f p := lt_of_not_ge hn
  have hpz' : p < z := lt_of_le_of_ne hpz (by intro he; subst z; exact (lt_irrefl _) hz)
  have hzq' : z < q := lt_of_le_of_ne hzq (by intro he; subst z; exact (not_lt_of_ge heq.le) hz)
  obtain ⟨w,hw⟩ := hpath _ (hbound p) z hz
  have h0 : (0 : Fin (n + 1)) < p := lt_of_le_of_ne (Fin.zero_le p) (Ne.symm hp)
  rcases chord_separation hnc hadj w ⟨hpz',hzq'⟩ (Or.inl h0) with hpw | hqw
  · exact (lt_irrefl _) (hw p hpw)
  · exact (not_lt_of_ge heq.le) (hw q hqw)

end ColumnOrder

end PlanarL1

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Columns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
/-! ## Finite switching paths in the manuscript's column models
A switch retains height and has zero cost. Between switches a path travels
vertically; its length is the sum of all vertical variations. The band argument
below does not identify an ambient distance with a band distance. -/
namespace Columns

/-- Neighbors in the cyclic order, including the wrap-around edge. -/
def Consecutive {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)

/-- The data and standing hypotheses of a column model.
Only the actual prescribed switch heights identify columns. -/
structure Model (n : ℕ) where
  link : SimpleGraph (Fin n)
  heights : Fin n → Fin n → Set ℝ
  symm : ∀ i j, heights i j = heights j i
  permitted : ∀ i j H, H ∈ heights i j → link.Adj i j
  compact : ∀ i j, IsCompact (heights i j)
  noncrossing : ColumnOrder.Noncrossing link
  terminal : ∀ i j, link.Adj i j → ¬ Consecutive i j →
    ∃ H, heights i j = {H} ∧ ∀ k T,
      (T ∈ heights i k ∨ T ∈ heights j k) → T ≤ H

namespace Model

variable {n : ℕ} (M : Model n)

/-- A link is active in a band exactly when it has an allowed height there. -/
def activeGraph (J : Set ℝ) : SimpleGraph (Fin n) where
  Adj i j := ∃ H ∈ J, H ∈ M.heights i j
  symm := ⟨by
    intro i j
    rintro ⟨H, hH, h⟩
    exact ⟨H, hH, by rwa [M.symm i j] at h⟩⟩
  loopless := ⟨by
    intro i
    rintro ⟨H, _, h⟩
    exact M.link.loopless.irrefl i (M.permitted i i H h)⟩

lemma active_subgraph (J : Set ℝ) : M.activeGraph J ≤ M.link := by
  rintro i j ⟨H, _, h⟩
  exact M.permitted i j H h

lemma active_noncrossing (J : Set ℝ) : ColumnOrder.Noncrossing (M.activeGraph J) := by
  intro a b c d hab hbc hcd h
  exact M.noncrossing a b c d hab hbc hcd
    ⟨M.active_subgraph J h.1, M.active_subgraph J h.2⟩

/-- A finite column word with an allowed band-switch height at every step.
Endpoint heights are supplied separately; the nil word is a vertical segment. -/
inductive Path (J : Set ℝ) : Fin n → Fin n → Type
  | nil (i : Fin n) : Path J i i
  | cons {i j k : Fin n} (H : ℝ) (inBand : H ∈ J)
      (switch : H ∈ M.heights i j) (tail : Path J j k) : Path J i k

namespace Path

variable {M} {J : Set ℝ} {i j k : Fin n}

/-- Source length: sum of the lengths of vertical segments, with switches free. -/
def length : {i j : Fin n} → M.Path J i j → ℝ → ℝ → ℝ
  | _, _, .nil _, a, b => |a - b|
  | _, _, .cons H _ _ p, a, b => |a - H| + p.length H b

/-- The associated walk in the active column graph, used for planar separation. -/
def word : {i j : Fin n} → M.Path J i j → (M.activeGraph J).Walk i j
  | _, _, .nil _ => .nil
  | _, _, .cons H hH hs p => .cons ⟨H, hH, hs⟩ p.word

lemma length_nonneg (p : M.Path J i j) (a b : ℝ) : 0 ≤ p.length a b := by
  induction p generalizing a with
  | nil => exact abs_nonneg _
  | cons H _ _ p ih => exact add_nonneg (abs_nonneg _) (ih H)

lemma height_change_le (p : M.Path J i j) (a b : ℝ) : |a - b| ≤ p.length a b := by
  induction p generalizing a with
  | nil => exact le_rfl
  | cons H hH hs p ih =>
    dsimp only [length]
    linarith [abs_sub_le a H b, ih H]

/-- Moving just the final endpoint vertically changes a path length by at most
that vertical distance. The intermediate switch heights stay unchanged. -/
lemma length_end_le (p : M.Path J i j) (a b c : ℝ) :
    p.length a c ≤ p.length a b + |b - c| := by
  induction p generalizing a with
  | nil => exact abs_sub_le a b c
  | cons H hH hs p ih =>
    dsimp only [length]
    linarith [ih H]

lemma length_start_le (p : M.Path J i j) (a b c : ℝ) :
    p.length a c ≤ |a - b| + p.length b c := by
  cases p with
  | nil => exact abs_sub_le a b c
  | cons H hH hs p =>
    dsimp only [length]
    linarith [abs_sub_le a b H]

/-- Concatenate switching words. Any redundant final/initial vertical detour at
the common column is removed, so length can only decrease. -/
def append : {i j k : Fin n} → M.Path J i j → M.Path J j k → M.Path J i k
  | _, _, _, .nil _, q => q
  | _, _, _, .cons H hH hs p, q => .cons H hH hs (p.append q)

lemma length_append_le (p : M.Path J i j) (q : M.Path J j k) (a b c : ℝ) :
    (p.append q).length a c ≤ p.length a b + q.length b c := by
  induction p generalizing a with
  | nil => exact q.length_start_le a b c
  | cons H hH hs p ih =>
    dsimp only [length, append]
    linarith [ih q H]

/-- Adjoin one final switch at height `H`. -/
def snoc (p : M.Path J i j) (H : ℝ) (hH : H ∈ J) (hs : H ∈ M.heights j k) :
    M.Path J i k := p.append (.cons H hH hs (.nil k))

lemma length_snoc (p : M.Path J i j) (H : ℝ) (hH : H ∈ J)
    (hs : H ∈ M.heights j k) (a b : ℝ) :
    (p.snoc H hH hs).length a b = p.length a H + |H - b| := by
  induction p generalizing a with
  | nil => rfl
  | cons T hT ht p ih =>
    dsimp only [snoc, append, length] at *
    rw [ih]
    ring

/-- Reverse the column word and all its zero-cost switches. -/
def reverse : {i j : Fin n} → M.Path J i j → M.Path J j i
  | _, _, .nil _ => .nil _
  | _, _, .cons H hH hs p => p.reverse.snoc H hH (by rwa [M.symm] at hs)

lemma length_reverse (p : M.Path J i j) (a b : ℝ) :
    p.reverse.length b a = p.length a b := by
  induction p generalizing a with
  | nil => exact abs_sub_comm b a
  | cons H hH hs p ih =>
    dsimp only [reverse]
    rw [length_snoc, ih]
    dsimp only [length]
    rw [abs_sub_comm H a, add_comm]

/-- Every walk in the active graph really is a switching path: one chooses an
available height independently for each prescribed switch. -/
lemma exists_word (p : (M.activeGraph J).Walk i j) :
    ∃ q : M.Path J i j, q.word = p := by
  induction p with
  | nil => exact ⟨.nil _, rfl⟩
  | cons h p ih =>
    obtain ⟨H, hH, hs⟩ := h
    obtain ⟨q, hq⟩ := ih
    exact ⟨.cons H hH hs q, by simp only [word, hq]⟩

/-- A visit in a column word admits a genuine length-exact split at a height
in the band. This keeps paths that leave an individual radial cell available. -/
lemma split_at_column (p : M.Path J i j) {a b : ℝ} (ha : a ∈ J) (_hb : b ∈ J)
    {v : Fin n} (hv : v ∈ p.word.support) :
    ∃ H ∈ J, ∃ (q : M.Path J i v) (r : M.Path J v j),
      q.length a H + r.length H b = p.length a b := by
  induction p generalizing a with
  | nil i =>
    have hvi : v = i := by simpa only [word, SimpleGraph.Walk.support_nil,
      List.mem_singleton] using hv
    subst v
    exact ⟨a, ha, .nil _, .nil _, by simp only [length, sub_self, abs_zero, zero_add]⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hvi | hv
    · subst v
      exact ⟨a, ha, .nil _, .cons H hH hs p,
        by simp only [length, sub_self, abs_zero, zero_add]⟩
    · obtain ⟨T, hT, q, r, hqr⟩ := ih hH hv
      refine ⟨T, hT, .cons H hH hs q, r, ?_⟩
      dsimp only [length]
      linarith

/-- Split a vertical segment at a prescribed traveled length, remaining in
its closed interval. This is valid for every interval band in the paper. -/
lemma vertical_split (hJ : Set.OrdConnected J) {a b ℓ : ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hℓ : 0 ≤ ℓ) (hbound : ℓ ≤ |a - b|) :
    ∃ T ∈ J, |a - T| = ℓ ∧ |T - b| = |a - b| - ℓ := by
  by_cases hab : a ≤ b
  · have hlen : |a - b| = b - a := by rw [abs_of_nonpos (by linarith)]; ring
    refine ⟨a + ℓ, hJ.out ha hb ⟨by linarith, by rw [hlen] at hbound; linarith⟩, ?_, ?_⟩
    · rw [abs_of_nonpos (by linarith)]; ring
    · rw [abs_of_nonpos (by rw [hlen] at hbound; linarith), hlen]; ring
  · have hlen : |a - b| = a - b := abs_of_nonneg (by linarith)
    refine ⟨a - ℓ, hJ.out hb ha ⟨by rw [hlen] at hbound; linarith, by linarith⟩, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_nonneg (by rw [hlen] at hbound; linarith), hlen]; ring

/-- Every intermediate arclength is attained on a switching path in an
interval band, by actual finite prefix and suffix paths. No abstract length
space or geodesicity hypothesis is added. -/
lemma split_at_length (hJ : Set.OrdConnected J) (p : M.Path J i j)
    {a b ℓ : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hℓ : 0 ≤ ℓ)
    (hbound : ℓ ≤ p.length a b) :
    ∃ (k : Fin n) (T : ℝ), T ∈ J ∧
      ∃ (q : M.Path J i k) (r : M.Path J k j),
        q.length a T = ℓ ∧ r.length T b = p.length a b - ℓ := by
  induction p generalizing a ℓ with
  | nil i =>
    obtain ⟨T, hT, h₁, h₂⟩ := vertical_split hJ ha hb hℓ hbound
    exact ⟨i, T, hT, .nil _, .nil _, h₁, h₂⟩
  | @cons i k j H hH hs p ih =>
    by_cases hfirst : ℓ ≤ |a - H|
    · obtain ⟨T, hT, h₁, h₂⟩ := vertical_split hJ ha hH hℓ hfirst
      refine ⟨i, T, hT, .nil _, .cons H hH hs p, h₁, ?_⟩
      dsimp only [length]
      rw [h₂]
      ring
    · have htail : ℓ - |a - H| ≤ p.length H b := by
        change ℓ ≤ |a - H| + p.length H b at hbound
        linarith
      obtain ⟨v, T, hT, q, r, hq, hr⟩ := ih hH (by linarith) htail
      refine ⟨v, T, hT, .cons H hH hs q, r, ?_, ?_⟩
      · dsimp only [length]
        linarith
      · dsimp only [length]
        linarith

/-- A finite switching word from outside a column set to inside it has a
crossing switch. The decomposition retains the exact metric length, including
both endpoint vertical segments. -/
lemma crosses_set (p : M.Path J i j) (S : Set (Fin n)) (hi : i ∉ S) (hj : j ∈ S)
    (a b : ℝ) :
    ∃ (u v : Fin n) (H : ℝ) (_hH : H ∈ J) (_hs : H ∈ M.heights u v),
      u ∉ S ∧ v ∈ S ∧ ∃ (q : M.Path J i u) (r : M.Path J v j),
        q.length a H + r.length H b = p.length a b := by
  classical
  induction p generalizing a with
  | nil => exact False.elim (hi hj)
  | @cons i z j H hH hs p ih =>
    by_cases hz : z ∈ S
    · exact ⟨i, z, H, hH, hs, hi, hz, .nil _, p, rfl⟩
    · obtain ⟨u, v, T, hT, ht, hu, hv, q, r, he⟩ := ih hz hj H
      refine ⟨u, v, T, hT, ht, hu, hv, .cons H hH hs q, r, ?_⟩
      dsimp only [length] at *
      linarith

/-- Deleting a prefix up to a visited column cannot increase vertical
variation, even when the new initial height is the old initial height. -/
lemma suffix_at_column (p : M.Path J i j) (a b : ℝ) {v : Fin n}
    (hv : v ∈ p.word.support) :
    ∃ r : M.Path J v j, r.word.support.Sublist p.word.support ∧
      r.length a b ≤ p.length a b := by
  induction p generalizing a with
  | nil i =>
    have hvi : v = i := by simpa only [word, SimpleGraph.Walk.support_nil,
      List.mem_singleton] using hv
    subst v
    exact ⟨.nil _, List.Sublist.refl _, le_rfl⟩
  | @cons i z j H hH hs p ih =>
    rcases List.mem_cons.mp hv with hvi | hv
    · subst v
      exact ⟨.cons H hH hs p, List.Sublist.refl _, le_rfl⟩
    · obtain ⟨r, hr, hlen⟩ := ih H hv
      refine ⟨r, hr.trans (List.sublist_cons_self _ _), ?_⟩
      exact (r.length_start_le a H b).trans (add_le_add (le_refl _) hlen)

/-- Loop erasure with its essential metric estimate: replacing a detour by
vertical travel never increases length. The resulting word has no repeated
column, so the later minimization is over finitely many words. -/
lemma simple_replacement (p : M.Path J i j) (a b : ℝ) :
    ∃ q : M.Path J i j, q.word.IsPath ∧ q.length a b ≤ p.length a b := by
  classical
  induction p generalizing a with
  | nil i => exact ⟨.nil i, by simp [word], le_rfl⟩
  | @cons i z j H hH hs p ih =>
    obtain ⟨q, hq, hlen⟩ := ih H
    by_cases hi : i ∈ q.word.support
    · obtain ⟨r, hr, hlenr⟩ := q.suffix_at_column H b hi
      refine ⟨r, ?_, ?_⟩
      · exact SimpleGraph.Walk.IsPath.mk' (hq.support_nodup.sublist hr)
      · exact (r.length_start_le a H b).trans
          (add_le_add (le_refl _) (hlenr.trans hlen))
    · refine ⟨.cons H hH hs q, ?_, add_le_add (le_refl _) hlen⟩
      exact SimpleGraph.Walk.IsPath.mk' (List.nodup_cons.mpr ⟨hi, hq.support_nodup⟩)

end Path

/-- A schedule specifies one allowed height for each edge of a fixed word.
This recursive finite product carries its usual compact topology when the band
is closed. -/
def Schedule (J : Set ℝ) : {i j : Fin n} → (M.activeGraph J).Walk i j → Type
  | _, _, .nil => PUnit
  | _, _, @SimpleGraph.Walk.cons _ _ i k _ _ p =>
      ↥(M.heights i k ∩ J) × Schedule J p

namespace Schedule

variable {M} {J : Set ℝ} {i j : Fin n}

noncomputable instance topology (w : (M.activeGraph J).Walk i j) : TopologicalSpace (M.Schedule J w) := by
  induction w with
  | nil => exact inferInstanceAs (TopologicalSpace PUnit)
  | @cons i k j h p ih =>
    change TopologicalSpace (↥(M.heights i k ∩ J) × M.Schedule J p)
    letI := ih
    infer_instance

lemma compactSpace (hJ : IsClosed J) (w : (M.activeGraph J).Walk i j) :
    CompactSpace (M.Schedule J w) := by
  induction w with
  | nil => exact inferInstanceAs (CompactSpace PUnit)
  | @cons i k j h p ih =>
    have hc := (M.compact i k).inter_right hJ
    let : CompactSpace ↥(M.heights i k ∩ J) := isCompact_iff_compactSpace.mp hc
    let := ih
    exact inferInstanceAs (CompactSpace (↥(M.heights i k ∩ J) × M.Schedule J p))

/-- Realize a schedule as the literal switching path of the fixed word. -/
def toPath : {i j : Fin n} → {w : (M.activeGraph J).Walk i j} →
    M.Schedule J w → M.Path J i j
  | i, _, .nil, _ => .nil i
  | _, _, .cons _ _, s => .cons s.1.val s.1.property.2 s.1.property.1 (toPath s.2)

lemma word_toPath {w : (M.activeGraph J).Walk i j} (s : M.Schedule J w) :
    (toPath s).word = w := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    change SimpleGraph.Walk.cons _ (toPath s.2).word = .cons h p
    rw [ih]

def ofPath : {i j : Fin n} → (p : M.Path J i j) → M.Schedule J p.word
  | _, _, .nil _ => PUnit.unit
  | _, _, .cons H hH hs p => (⟨H, hs, hH⟩, ofPath p)

lemma toPath_ofPath (p : M.Path J i j) : toPath (ofPath p) = p := by
  induction p with
  | nil => rfl
  | cons H hH hs p ih =>
    change Path.cons H hH hs (toPath (ofPath p)) = _
    rw [ih]

/-- Length is a continuous function of all endpoint and switch heights. -/
lemma continuous_length {T : Type*} [TopologicalSpace T]
    (w : (M.activeGraph J).Walk i j) (a b : T → ℝ) (s : T → M.Schedule J w)
    (ha : Continuous a) (hb : Continuous b) (hs : Continuous s) :
    Continuous (fun t => (toPath (s t)).length (a t) (b t)) := by
  induction w generalizing a b with
  | nil => exact (ha.sub hb).abs
  | @cons i k j h p ih =>
    have hH : Continuous (fun t => ((s t).1 : ℝ)) := continuous_subtype_val.comp hs.fst
    exact ((ha.sub hH).abs).add (ih _ b (fun t => (s t).2) hH hb hs.snd)

end Schedule

/-- Points before quotienting, in one component of the intrinsic band. -/
structure Point (J : Set ℝ) (root : Fin n) where
  column : Fin n
  height : ℝ
  inBand : height ∈ J
  reachable : (M.activeGraph J).Reachable root column

end Model
end Columns
end PlanarL1

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Distance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)
namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

lemma paths_nonempty (x y : M.Point J root) : Nonempty (M.Path J x.column y.column) := by
  obtain ⟨p⟩ := x.reachable.symm.trans y.reachable
  obtain ⟨q, _⟩ := Path.exists_word p
  exact ⟨q⟩

noncomputable def distance (x y : M.Point J root) : ℝ :=
  ⨅ p : M.Path J x.column y.column, p.length x.height y.height

lemma lengths_bddBelow (x y : M.Point J root) :
    BddBelow (Set.range fun p : M.Path J x.column y.column => p.length x.height y.height) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact p.length_nonneg _ _⟩

lemma distance_le (x y : M.Point J root) (p : M.Path J x.column y.column) :
    x.distance y ≤ p.length x.height y.height :=
  ciInf_le (x.lengths_bddBelow y) p

lemma distance_nonneg (x y : M.Point J root) : 0 ≤ x.distance y := by
  have :=  x.paths_nonempty y
  exact le_ciInf (fun p => p.length_nonneg _ _)

lemma height_change_le (x y : M.Point J root) : |x.height - y.height| ≤ x.distance y := by
  have :=  x.paths_nonempty y
  exact le_ciInf (fun p => p.height_change_le _ _)

lemma distance_self (x : M.Point J root) : x.distance x = 0 := by
  apply le_antisymm _ (x.distance_nonneg x)
  simpa only [Path.length, sub_self, abs_zero] using x.distance_le x (.nil _)

lemma distance_triangle (x y z : M.Point J root) :
    x.distance z ≤ x.distance y + y.distance z := by
  have :=  x.paths_nonempty y
  have :=  y.paths_nonempty z
  apply le_ciInf_add
  intro p
  apply le_add_ciInf
  intro q
  exact (x.distance_le z (p.append q)).trans (p.length_append_le q _ _ _)

lemma distance_comm (x y : M.Point J root) : x.distance y = y.distance x := by
  have :=  x.paths_nonempty y
  have :=  y.paths_nonempty x
  suffices ∀ x y : M.Point J root, x.distance y ≤ y.distance x by
    exact le_antisymm (this x y) (this y x)
  intro x y
  have :=  y.paths_nonempty x
  apply le_ciInf
  intro p
  simpa only [Path.length_reverse] using x.distance_le y p.reverse

noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (M.Point J root) where
  dist := distance
  dist_self := distance_self
  dist_comm := distance_comm
  dist_triangle := distance_triangle

/-- The full vertical interval is isometric, before or after the quotient.
No path's vertical variation can improve upon direct travel. -/
lemma dist_same_column (x y : M.Point J root) (h : x.column = y.column) :
    dist x y = |x.height - y.height| := by
  rcases x with ⟨i, a, ha, hx⟩
  rcases y with ⟨j, b, hb, hy⟩
  change i = j at h
  subst j
  let x : M.Point J root := ⟨i, a, ha, hx⟩
  let y : M.Point J root := ⟨i, b, hb, hy⟩
  exact le_antisymm (x.distance_le y (.nil i)) (x.height_change_le y)

/-- Vertical motion on a chosen column representative. -/
def withHeight (x : M.Point J root) (H : ℝ) (hH : H ∈ J) : M.Point J root :=
  ⟨x.column, H, hH, x.reachable⟩

@[simp] lemma withHeight_self (x : M.Point J root) :
    x.withHeight x.height x.inBand = x := rfl

lemma dist_withHeight (x : M.Point J root) (H : ℝ) (hH : H ∈ J) :
    dist x (x.withHeight H hH) = |x.height - H| := x.dist_same_column _ rfl

lemma dist_le_switch (x y : M.Point J root) {H : ℝ} (hH : H ∈ J)
    (hs : H ∈ M.heights x.column y.column) :
    dist x y ≤ |x.height - H| + |H - y.height| :=
  x.distance_le y (.cons H hH hs (.nil _))

/-- The source's adjacent-midpoint estimate: one available switch costs at
most the width of the band. -/
lemma dist_midpoints_le (x y : M.Point J root) {H a : ℝ}
    (hx : x.height = H) (hy : y.height = H)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (h : (M.activeGraph J).Adj x.column y.column) : dist x y ≤ a := by
  obtain ⟨T, hT, hs⟩ := h
  have hd := x.dist_le_switch y hT hs
  rw [hx, hy, abs_sub_comm T H] at hd
  linarith [hhalf T hT]

/-- Lengths realized by words with no repeated column. -/
def simpleLengths (x y : M.Point J root) : Set ℝ :=
  ⋃ w : (M.activeGraph J).Path x.column y.column,
    Set.range (fun s : M.Schedule J w.val => s.toPath.length x.height y.height)

lemma mem_simpleLengths (x y : M.Point J root) (p : M.Path J x.column y.column)
    (hp : p.word.IsPath) : p.length x.height y.height ∈ x.simpleLengths y := by
  apply Set.mem_iUnion.mpr
  refine ⟨⟨p.word, hp⟩, ?_⟩
  exact ⟨Schedule.ofPath p, by simp only [Schedule.toPath_ofPath]⟩

lemma simpleLengths_nonempty (x y : M.Point J root) : (x.simpleLengths y).Nonempty := by
  obtain ⟨p⟩ := x.paths_nonempty y
  obtain ⟨q, hq, _⟩ := p.simple_replacement x.height y.height
  exact ⟨q.length x.height y.height, x.mem_simpleLengths y q hq⟩

lemma isCompact_simpleLengths (hJ : IsClosed J) (x y : M.Point J root) :
    IsCompact (x.simpleLengths y) := by
  classical
  apply isCompact_iUnion
  intro w
  let := Schedule.compactSpace hJ w.val
  exact isCompact_range (Schedule.continuous_length w.val _ _ id
    continuous_const continuous_const continuous_id)

/-- Geometry, `geo:geodesics`: finite intrinsic distances are attained by a
switching path with no repeated column. Compactness is required of the actual
switch-height sets, rather than of an artificial discretization. -/
lemma exists_shortest (hJ : IsClosed J) (x y : M.Point J root) :
    ∃ p : M.Path J x.column y.column,
      p.word.IsPath ∧ p.length x.height y.height = dist x y := by
  have hc := x.isCompact_simpleLengths hJ y
  have hm := hc.isLeast_sInf (x.simpleLengths_nonempty y)
  obtain ⟨w, s, hs⟩ := Set.mem_iUnion.mp hm.1
  change s.toPath.length x.height y.height = sInf (x.simpleLengths y) at hs
  refine ⟨s.toPath, ?_, ?_⟩
  · rw [Schedule.word_toPath]
    exact w.property
  · apply le_antisymm _ (x.distance_le y s.toPath)
    have := x.paths_nonempty y
    apply le_ciInf
    intro p
    obtain ⟨q, hq, hlen⟩ := p.simple_replacement x.height y.height
    rw [hs]
    exact (hm.2 (x.mem_simpleLengths y q hq)).trans hlen

/-- Two short paths whose projected words meet on a column give a short
connection, with only one band-width paid for the vertical transfer. -/
lemma dist_le_of_shared_column (x y : M.Point J root) {i j v : Fin n}
    (p : M.Path J x.column i) (q : M.Path J y.column j)
    {H T a : ℝ} (hH : H ∈ J) (hT : T ∈ J)
    (hwidth : ∀ r ∈ J, ∀ s ∈ J, |r - s| ≤ a)
    (hpv : v ∈ p.word.support) (hqv : v ∈ q.word.support) :
    dist x y ≤ p.length x.height H + q.length y.height T + a := by
  obtain ⟨A, hA, p₁, p₂, hp⟩ := p.split_at_column x.inBand hH hpv
  obtain ⟨B, hB, q₁, q₂, hq⟩ := q.split_at_column y.inBand hT hqv
  have hd := x.distance_le y (p₁.append q₁.reverse)
  have ha := p₁.length_append_le q₁.reverse x.height B y.height
  have he := p₁.length_end_le x.height A B
  rw [q₁.length_reverse] at ha
  have hw := hwidth A hA B hB
  have hn₁ := p₂.length_nonneg A H
  have hn₂ := q₂.length_nonneg B T
  change x.distance y ≤ _
  linarith

/-- Exact shortest paths to a fixed-height column stay in its distance
sublevel after projection to column indices. This is the metric assertion
underlying `geo:sublevel`, not merely a graph-connectivity assumption. -/
lemma shortest_sublevel (hJ : IsClosed J) (o y : M.Point J root) :
    ∃ p : M.Path J o.column y.column,
      p.length o.height y.height = dist o y ∧
      ∀ v ∈ p.word.support, ∃ hv : (M.activeGraph J).Reachable root v,
        dist o (⟨v, y.height, y.inBand, hv⟩ : M.Point J root) ≤ dist o y := by
  obtain ⟨p, _, hp⟩ := o.exists_shortest hJ y
  refine ⟨p, hp, ?_⟩
  intro v hv
  obtain ⟨H, _, q, r, hqr⟩ := p.split_at_column o.inBand y.inBand hv
  refine ⟨o.reachable.trans q.word.reachable, ?_⟩
  let z : M.Point J root := ⟨v, y.height, y.inBand, o.reachable.trans q.word.reachable⟩
  have h1 := o.distance_le z q
  have h2 := q.length_end_le o.height H y.height
  have h3 := r.height_change_le H y.height
  change o.distance z ≤ dist o y
  linarith

/-- The fixed-height radial sublevel in the active column graph. Columns
outside the chosen component are absent, as for the source's value `+∞`. -/
def sublevel (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) : Set (Fin n) :=
  {i | ∃ hi : (M.activeGraph J).Reachable root i,
    dist o (⟨i, H, hH, hi⟩ : M.Point J root) ≤ t}

lemma mem_sublevel_iff (o x : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) :
    x.column ∈ o.sublevel H hH t ↔ dist o (x.withHeight H hH) ≤ t := by
  constructor
  · rintro ⟨_, hd⟩
    exact hd
  · intro hd
    exact ⟨x.reachable, hd⟩

lemma sublevel_preconnected (hJ : IsClosed J) (o : M.Point J root)
    (H : ℝ) (hH : H ∈ J) (t : ℝ) :
    ((M.activeGraph J).induce (o.sublevel H hH t)).Preconnected := by
  intro x y
  obtain ⟨hx, hdx⟩ := x.property
  obtain ⟨hy, hdy⟩ := y.property
  obtain ⟨p, _, hp⟩ := o.shortest_sublevel hJ ⟨x.val, H, hH, hx⟩
  obtain ⟨q, _, hq⟩ := o.shortest_sublevel hJ ⟨y.val, H, hH, hy⟩
  have hmem : ∀ v ∈ (p.word.reverse.append q.word).support,
      v ∈ o.sublevel H hH t := by
    intro v hv
    rcases (p.word.reverse.mem_support_append_iff q.word).mp hv with hv | hv
    · have hv' : v ∈ p.word.support := by simpa using hv
      obtain ⟨hvr, hdv⟩ := hp v hv'
      exact ⟨hvr, hdv.trans hdx⟩
    · obtain ⟨hvr, hdv⟩ := hq v hv
      exact ⟨hvr, hdv.trans hdy⟩
  exact ⟨(p.word.reverse.append q.word).induce _ hmem⟩

/-- The short connector in the portal argument. We use the connected
fixed-height sublevel at `t - 12a`; this changes the source's intermediate
13a estimate to 14a, still strictly below the required 100a separation. -/
lemma short_connector (hJ : IsClosed J) (o x : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a) (ht : 30 * a ≤ t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (hx : t ≤ dist o (x.withHeight H hH)) (hnear : dist o x < t + a) :
    ∃ v ∈ o.sublevel H hH (t - 12 * a), ∃ T ∈ J,
      ∃ p : M.Path J x.column v, p.length x.height T ≤ 14 * a := by
  let S := o.sublevel H hH (t - 12 * a)
  have hxo : x.column ∉ S := by
    intro h
    have hd := (o.mem_sublevel_iff x H hH (t - 12 * a)).mp h
    linarith
  have hoo : o.column ∈ S := by
    apply (o.mem_sublevel_iff o H hH (t - 12 * a)).mpr
    rw [o.dist_withHeight, abs_sub_comm]
    linarith [hhalf o.height o.inBand]
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ o
  obtain ⟨u, v, T, hT, hs, hu, hv, q, r, hqr⟩ :=
    p.crosses_set S hxo hoo x.height o.height
  let z : M.Point J root := ⟨u, T, hT, x.reachable.trans q.word.reachable⟩
  have hout : t - 12 * a < dist o (z.withHeight H hH) := by
    apply lt_of_not_ge
    intro h
    exact hu ((o.mem_sublevel_iff z H hH _).mpr h)
  have hz : dist o z ≤ r.length T o.height := by
    have hh := z.distance_le o (.cons T hT hs r)
    rw [dist_comm o z]
    change z.distance o ≤ r.length T o.height
    simpa only [Path.length, z, sub_self, abs_zero, zero_add] using hh
  have hvshift : dist z (z.withHeight H hH) ≤ a / 2 := by
    rw [z.dist_withHeight]
    change |T - H| ≤ a / 2
    rw [abs_sub_comm]
    exact hhalf T hT
  have htri := dist_triangle o z (z.withHeight H hH)
  have hlen : q.length x.height T ≤ 14 * a := by
    rw [hp, dist_comm x o] at hqr
    linarith
  refine ⟨v, hv, T, hT, q.snoc T hT hs, ?_⟩
  simpa only [Path.length_snoc, sub_self, abs_zero, add_zero] using hlen

/-- Quantitative exclusion behind the two-portals lemma: three entrance-range
midpoints in a connected high set cannot be mutually more than 100 widths
apart. No minor-exclusion or short-connector hypothesis is assumed. -/
lemma no_three_far_entrances (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    {C : Set (Fin n)} (hC : ((M.activeGraph J).induce C).Preconnected)
    (hhigh : ∀ z : M.Point J root, z.column ∈ C → t ≤ dist o (z.withHeight H hH))
    (x : Fin 3 → M.Point J root) (hxc : ∀ i, (x i).column ∈ C)
    (hnear : ∀ i, dist o (x i) < t + a)
    (hfar : Pairwise (fun i j => 100 * a < dist (x i) (x j))) : False := by
  by_cases ht : 30 * a ≤ t
  · let L := o.sublevel H hH (t - 12 * a)
    have hCL : Disjoint C L := by
      apply Set.disjoint_left.mpr
      rintro v hv ⟨hr, hd⟩
      let z : M.Point J root := ⟨v, H, hH, hr⟩
      have hz := hhigh z hv
      change t ≤ dist o z at hz
      linarith
    have hno : ∀ u ∈ C, ∀ v ∈ L, ¬ (M.activeGraph J).Adj u v := by
      rintro u hu v ⟨hr, hd⟩ huv
      let y : M.Point J root := ⟨v, H, hH, hr⟩
      let z : M.Point J root := ⟨u, H, hH,
        hr.trans (SimpleGraph.Adj.reachable huv.symm)⟩
      have hz := hhigh z hu
      change t ≤ dist o z at hz
      have hzy := z.dist_midpoints_le y rfl rfl hhalf huv
      have hh := dist_triangle o y z
      rw [dist_comm y z] at hh
      change dist o y ≤ t - 12 * a at hd
      linarith
    have hcon := fun i => o.short_connector hJ (x i) hH ha ht hhalf
      (hhigh (x i) (hxc i)) (hnear i)
    choose v hv T hT p hp using hcon
    have hwidth : ∀ r ∈ J, ∀ s ∈ J, |r - s| ≤ a := by
      intro r hr s hs
      have hb := abs_sub_le r H s
      rw [abs_sub_comm r H] at hb
      linarith [hhalf r hr, hhalf s hs]
    have hdis : Pairwise (fun i j => Disjoint
        {w | w ∈ (p i).word.support} {w | w ∈ (p j).word.support}) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro w hwi hwj
      have hd := (x i).dist_le_of_shared_column (x j) (p i) (p j)
        (hT i) (hT j) hwidth hwi hwj
      have hf := hfar hij
      linarith [hp i, hp j]
    exact ColumnOrder.no_three_connectors (M.active_noncrossing J) hC
      (o.sublevel_preconnected hJ H hH (t - 12 * a)) hCL hno
      (fun i => (x i).column) v hxc hv (fun i => (p i).word) hdis
  · have hf := hfar (show (0 : Fin 3) ≠ 1 by decide)
    have hd := dist_triangle (x 0) o (x 1)
    rw [dist_comm (x 0) o] at hd
    linarith [hnear 0, hnear 1]

/-- Two entrances cover all entrance midpoints. The two chosen values may
coincide, representing the one-portal case; both are actual entrances. -/
lemma two_portal_midpoints (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    {C : Set (Fin n)} (hC : ((M.activeGraph J).induce C).Preconnected)
    (hhigh : ∀ z : M.Point J root, z.column ∈ C → t ≤ dist o (z.withHeight H hH))
    {E : Set (M.Point J root)} (hne : E.Nonempty)
    (heC : ∀ x ∈ E, x.column ∈ C) (hnear : ∀ x ∈ E, dist o x < t + a) :
    ∃ p ∈ E, ∃ q ∈ E, ∀ x ∈ E, dist x p ≤ 100 * a ∨ dist x q ≤ 100 * a := by
  classical
  obtain ⟨p, hp⟩ := hne
  by_cases hex : ∃ q ∈ E, 100 * a < dist p q
  · obtain ⟨q, hq, hpq⟩ := hex
    refine ⟨p, hp, q, hq, ?_⟩
    intro z hz
    by_contra h
    push Not at h
    apply o.no_three_far_entrances hJ hH ha hhalf hC hhigh ![p, q, z]
    · intro i
      fin_cases i
      · exact heC p hp
      · exact heC q hq
      · exact heC z hz
    · intro i
      fin_cases i
      · exact hnear p hp
      · exact hnear q hq
      · exact hnear z hz
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [dist_comm]
  · refine ⟨p, hp, p, hp, ?_⟩
    intro x hx
    left
    rw [dist_comm]
    exact le_of_not_gt (fun h => hex ⟨x, hx, h⟩)

/-- Geometry `geo:portals`, the full-column covering conclusion with the
stated 200a constant. The entrance-range hypothesis is derived from adjacency
by `dist_midpoints_le`; the two portal centers are selected from `E` itself. -/
lemma two_portals (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    {C : Set (Fin n)} (hC : ((M.activeGraph J).induce C).Preconnected)
    (hhigh : ∀ z : M.Point J root, z.column ∈ C → t ≤ dist o (z.withHeight H hH))
    {E : Set (M.Point J root)} (hne : E.Nonempty)
    (heC : ∀ x ∈ E, x.column ∈ C) (hnear : ∀ x ∈ E, dist o x < t + a) :
    ∃ p ∈ E, ∃ q ∈ E, ∀ x : M.Point J root, x.withHeight H hH ∈ E →
      dist x p ≤ 200 * a ∨ dist x q ≤ 200 * a := by
  obtain ⟨p, hp, q, hq, hcover⟩ := o.two_portal_midpoints hJ hH ha hhalf hC hhigh
    hne heC hnear
  refine ⟨p, hp, q, hq, ?_⟩
  intro x hx
  have hv : dist x (x.withHeight H hH) ≤ a / 2 := by
    rw [x.dist_withHeight, abs_sub_comm]
    exact hhalf x.height x.inBand
  rcases hcover _ hx with h | h
  · left
    linarith [dist_triangle x (x.withHeight H hH) p]
  · right
    linarith [dist_triangle x (x.withHeight H hH) q]

/-- Radial superlevels contain exactly the reachable columns whose midpoints
have radial value at least the threshold. -/
def superlevel (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) : Set (Fin n) :=
  {i | ∃ hi : (M.activeGraph J).Reachable root i,
    t ≤ dist o (⟨i, H, hH, hi⟩ : M.Point J root)}

lemma mem_superlevel_iff (o x : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) :
    x.column ∈ o.superlevel H hH t ↔ t ≤ dist o (x.withHeight H hH) := by
  constructor
  · rintro ⟨_, hd⟩
    exact hd
  · intro hd
    exact ⟨x.reachable, hd⟩

/-- The actual entrance midpoints of a radial high component. The adjacent
low column, rather than a separate entrance-range hypothesis, is part of the
definition. -/
def entrances (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    Set (M.Point J root) :=
  {x | x.height = H ∧ x.column ∈ ColumnOrder.componentColumns C ∧
    ∃ y : M.Point J root, y.height = H ∧
      (M.activeGraph J).Adj x.column y.column ∧ dist o y < t}

lemma entrance_radial (o : M.Point J root) {H a t : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    {x : M.Point J root} (hx : x ∈ o.entrances H hH t C) :
    t ≤ dist o x ∧ dist o x < t + a := by
  obtain ⟨hxH, hxC, y, hyH, hxy, hy⟩ := hx
  have hhigh := (o.mem_superlevel_iff x H hH t).mp
    (ColumnOrder.componentColumns_subset C hxC)
  have heq : x.withHeight H hH = x := by
    simpa only [← hxH] using x.withHeight_self
  rw [heq] at hhigh
  have hd := x.dist_midpoints_le y hxH hyH hhalf hxy
  have htri := dist_triangle o y x
  rw [dist_comm y x] at htri
  exact ⟨hhigh, by linarith⟩

/-- Exit a high component along an attained shortest path. The final high
column is an actual entrance. The estimate retains the distance to the radial
threshold, and is the geometric input for both cell diameters and portal levels. -/
lemma exit_superlevel (hJ : IsClosed J) (o x : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ht : a / 2 < t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C) :
    ∃ z : M.Point J root, z.withHeight H hH ∈ o.entrances H hH t C ∧
      dist x z ≤ dist o x - t + a / 2 := by
  let S := ColumnOrder.componentColumns C
  have hoo : o.column ∉ S := by
    intro ho
    have hh := (o.mem_superlevel_iff o H hH t).mp
      (ColumnOrder.componentColumns_subset C ho)
    rw [o.dist_withHeight, abs_sub_comm] at hh
    linarith [hhalf o.height o.inBand]
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ o
  obtain ⟨u, v, T, hT, hs, hu, hv, q, r, hqr⟩ :=
    p.crosses_set Sᶜ (by simpa only [Set.mem_compl_iff, not_not] using hx)
      hoo x.height o.height
  have huC : u ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hu
  have huv : (M.activeGraph J).Adj u v := ⟨T, hT, hs⟩
  let z : M.Point J root := ⟨u, T, hT, x.reachable.trans q.word.reachable⟩
  let y : M.Point J root := ⟨v, H, hH, z.reachable.trans huv.reachable⟩
  have hy : dist o y < t := by
    apply lt_of_not_ge
    intro h
    exact hv (ColumnOrder.componentColumns_adj C huC huv ⟨y.reachable, h⟩)
  have hentrance : z.withHeight H hH ∈ o.entrances H hH t C :=
    ⟨rfl, huC, y, rfl, huv, hy⟩
  refine ⟨z, hentrance, ?_⟩
  have hhigh := (o.mem_superlevel_iff z H hH t).mp
    (ColumnOrder.componentColumns_subset C huC)
  have hvshift : dist z (z.withHeight H hH) ≤ a / 2 := by
    rw [z.dist_withHeight, abs_sub_comm]
    exact hhalf T hT
  have hz : dist o z ≤ r.length T o.height := by
    have hh := z.distance_le o (.cons T hT hs r)
    rw [dist_comm o z]
    change z.distance o ≤ r.length T o.height
    simpa only [Path.length, z, sub_self, abs_zero, zero_add] using hh
  have htri := dist_triangle o z (z.withHeight H hH)
  have hdx := x.distance_le z q
  change dist x z ≤ q.length x.height T at hdx
  rw [hp, dist_comm x o] at hqr
  linarith

/-- Nonempty radial high components have entrances above the initial
half-width. This discharges the existence clause of `geo:portals`. -/
lemma entrances_nonempty (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ht : a / 2 < t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    (o.entrances H hH t C).Nonempty := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  obtain ⟨hr, _⟩ := i.property
  let x : M.Point J root := ⟨i.val, H, hH, hr⟩
  obtain ⟨z, hz, _⟩ := o.exit_superlevel hJ x hH ht hhalf C ⟨i, hi, rfl⟩
  exact ⟨z.withHeight H hH, hz⟩

/-- Geometry `geo:portals` with the actual radial component and actual
entrances. In particular no covering or radial-range conclusion is assumed. -/
lemma component_two_portals (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hne : (o.entrances H hH t C).Nonempty) :
    ∃ p ∈ o.entrances H hH t C, ∃ q ∈ o.entrances H hH t C,
      (t ≤ dist o p ∧ dist o p < t + a) ∧
      (t ≤ dist o q ∧ dist o q < t + a) ∧
      ∀ x : M.Point J root, x.withHeight H hH ∈ o.entrances H hH t C →
        dist x p ≤ 200 * a ∨ dist x q ≤ 200 * a := by
  obtain ⟨p, hp, q, hq, hcover⟩ := o.two_portals hJ hH ha hhalf
    (ColumnOrder.componentColumns_connected C).preconnected
    (fun z hz => (o.mem_superlevel_iff z H hH t).mp
      (ColumnOrder.componentColumns_subset C hz)) hne
    (fun _ hx => hx.2.1) (fun _ hx => (o.entrance_radial hH hhalf C hx).2)
  exact ⟨p, hp, q, hq, o.entrance_radial hH hhalf C hp,
    o.entrance_radial hH hhalf C hq, hcover⟩

/-- The geodesic-to-root estimate behind radial cells: every point of a
high component whose radial distance is bounded is close to a chosen portal. -/
lemma component_portal_cover (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a) (ht : a / 2 < t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    ∃ p ∈ o.entrances H hH t C, ∃ q ∈ o.entrances H hH t C,
      ∀ x : M.Point J root, x.column ∈ ColumnOrder.componentColumns C →
        dist x p ≤ dist o x - t + 201 * a ∨
        dist x q ≤ dist o x - t + 201 * a := by
  obtain ⟨p, hp, q, hq, _, _, hc⟩ := o.component_two_portals hJ hH ha hhalf C
    (o.entrances_nonempty hJ hH ht hhalf C)
  refine ⟨p, hp, q, hq, ?_⟩
  intro x hx
  obtain ⟨z, hz, hd⟩ := o.exit_superlevel hJ x hH ht hhalf C hx
  rcases hc z hz with hz | hz
  · left
    linarith [dist_triangle x z p]
  · right
    linarith [dist_triangle x z q]

/-- The half-open radial layer of the source. Its connected components,
not components of the ambient graph, are the cell column sets. -/
def layer (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (q D : ℝ) : Set (Fin n) :=
  {i | ∃ hi : (M.activeGraph J).Reachable root i,
    q ≤ dist o (⟨i, H, hH, hi⟩ : M.Point J root) ∧
    dist o (⟨i, H, hH, hi⟩ : M.Point J root) < q + D}

lemma layer_subset_superlevel (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (q D : ℝ) :
    o.layer H hH q D ⊆ o.superlevel H hH q := by
  rintro i ⟨hr, hlow, _⟩
  exact ⟨hr, hlow⟩

lemma mem_layer_iff (o x : M.Point J root) (H : ℝ) (hH : H ∈ J) (q D : ℝ) :
    x.column ∈ o.layer H hH q D ↔
      q ≤ dist o (x.withHeight H hH) ∧ dist o (x.withHeight H hH) < q + D := by
  constructor
  · rintro ⟨_, hd⟩
    exact hd
  · intro hd
    exact ⟨x.reachable, hd⟩

/-- The weak-diameter assertion of `geo:cells` for the literal full-column
cell. Paths measuring distance may leave the cell, exactly as in the source. -/
lemma radial_cell_diameter (hJ : IsClosed J) (o : M.Point J root)
    {H a q D : ℝ} (hH : H ∈ J) (ha : 0 < a) (hthin : a ≤ D / 1000)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (x y : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hy : y.column ∈ ColumnOrder.componentColumns C) : dist x y ≤ 10 * D := by
  classical
  have hD : 0 < D := by linarith
  have hup : ∀ z : M.Point J root, z.column ∈ ColumnOrder.componentColumns C →
      dist o z < q + D + a / 2 := by
    intro z hz
    have hr := (o.mem_layer_iff z H hH q D).mp
      (ColumnOrder.componentColumns_subset C hz)
    have hv := hhalf z.height z.inBand
    have hd := dist_triangle o (z.withHeight H hH) z
    rw [dist_comm (z.withHeight H hH) z, z.dist_withHeight, abs_sub_comm] at hd
    linarith [hr.2]
  by_cases hq : q ≤ 30 * a
  · have hd := dist_triangle x o y
    rw [dist_comm x o] at hd
    linarith [hup x hx, hup y hy]
  · let Cplus := ColumnOrder.componentAbove (o.layer_subset_superlevel H hH q D) C
    have hsub := ColumnOrder.componentColumns_above (o.layer_subset_superlevel H hH q D) C
    have ht : a / 2 < q := by linarith
    obtain ⟨p, _, r, _, hc⟩ := o.component_portal_cover hJ hH ha ht hhalf Cplus
    let f : ColumnOrder.componentColumns C → M.Point J root := fun i =>
      ⟨i.val, H, hH, (ColumnOrder.componentColumns_subset C i.property).choose⟩
    have hedge : ∀ i j, ((M.activeGraph J).induce (ColumnOrder.componentColumns C)).Adj i j →
        dist (f i) (f j) ≤ a := by
      intro i j hij
      exact (f i).dist_midpoints_le (f j) rfl rfl hhalf hij
    have hcover : ∀ i, dist (f i) p ≤ D + 210 * a ∨ dist (f i) r ≤ D + 210 * a := by
      intro i
      have hfi : (f i).column ∈ ColumnOrder.componentColumns C := i.property
      have hu := hup (f i) hfi
      rcases hc (f i) (hsub hfi) with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hd := ColumnOrder.connected_two_balls
      (ColumnOrder.componentColumns_connected C).preconnected f p r
      (show 0 ≤ D + 210 * a by positivity) ha.le hedge hcover ⟨x.column, hx⟩ ⟨y.column, hy⟩
    have hvx : dist x (f ⟨x.column, hx⟩) ≤ a / 2 := by
      change dist x (x.withHeight H hH) ≤ a / 2
      rw [x.dist_withHeight, abs_sub_comm]
      exact hhalf x.height x.inBand
    have hvy : dist (f ⟨y.column, hy⟩) y ≤ a / 2 := by
      change dist (y.withHeight H hH) y ≤ a / 2
      rw [dist_comm, y.dist_withHeight, abs_sub_comm]
      exact hhalf y.height y.inBand
    have ht₁ := dist_triangle x (f ⟨x.column, hx⟩) y
    have ht₂ := dist_triangle (f ⟨x.column, hx⟩) (f ⟨y.column, hy⟩) y
    linarith

/-- Changing to the fixed midheight costs at most one band width in any
radial comparison. This also controls all zero-distance representatives. -/
lemma radial_difference_le (o x y : M.Point J root) {H a : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) :
    |dist o (x.withHeight H hH) - dist o (y.withHeight H hH)| ≤ dist x y + a := by
  have hx : dist x (x.withHeight H hH) ≤ a / 2 := by
    rw [x.dist_withHeight, abs_sub_comm]
    exact hhalf x.height x.inBand
  have hy : dist y (y.withHeight H hH) ≤ a / 2 := by
    rw [y.dist_withHeight, abs_sub_comm]
    exact hhalf y.height y.inBand
  have h₁ := abs_dist_sub_le (x.withHeight H hH) (y.withHeight H hH) o
  rw [dist_comm (x.withHeight H hH) o, dist_comm (y.withHeight H hH) o] at h₁
  have h₂ := dist_triangle (x.withHeight H hH) x (y.withHeight H hH)
  have h₃ := dist_triangle x y (y.withHeight H hH)
  rw [dist_comm (x.withHeight H hH) x] at h₂
  linarith

/-- The literal full-column frontier of a column cell in the active graph. -/
def frontier (C : Set (Fin n)) : Set (Fin n) :=
  {i | i ∈ C ∧ ∃ j, (M.activeGraph J).Adj i j ∧ j ∉ C}


/-- Every fixed column is an isometric copy of its allowed height interval. -/
def columnMap (i : Fin n) (hi : (M.activeGraph J).Reachable root i) : J → M.Point J root :=
  fun H => ⟨i, H.val, H.property, hi⟩

lemma columnMap_isometry (i : Fin n) (hi : (M.activeGraph J).Reachable root i) :
    Isometry (columnMap i hi) := by
  apply Isometry.of_dist_eq
  intro H T
  exact (columnMap i hi H).dist_same_column (columnMap i hi T) rfl

/-- Compactness of any full-column subset in a compact band, including the
literal radial cells and their frontiers. This argument works before taking
the separation quotient and does not require a false Hausdorff assumption. -/
lemma fullColumns_compact (hJ : IsCompact J) (C : Set (Fin n)) :
    IsCompact {x : M.Point J root | x.column ∈ C} := by
  classical
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  let I := {i : Fin n // i ∈ C ∧ (M.activeGraph J).Reachable root i}
  have heq : {x : M.Point J root | x.column ∈ C} =
      ⋃ i : I, Set.range (columnMap i.val i.property.2) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.mpr ⟨⟨x.column, hx, x.reachable⟩, ?_⟩
      exact ⟨⟨x.height, x.inBand⟩, rfl⟩
    · intro hx
      obtain ⟨i, H, rfl⟩ := Set.mem_iUnion.mp hx
      exact i.property.1
  rw [heq]
  exact isCompact_iUnion (fun i => isCompact_range (columnMap_isometry i.val i.property.2).continuous)


/-- The metric interpolation property of an actual attained shortest path.
This is the geodesic fact used by the small-ball and descending-path arguments. -/
lemma exists_between (hJ : IsClosed J) (hconv : Set.OrdConnected J)
    (x y : M.Point J root) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hlen : ℓ ≤ dist x y) :
    ∃ z : M.Point J root, dist x z = ℓ ∧ dist z y = dist x y - ℓ := by
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  obtain ⟨k, T, hT, q, r, hq, hr⟩ := p.split_at_length hconv x.inBand y.inBand hℓ
    (hp ▸ hlen)
  let z : M.Point J root := ⟨k, T, hT, x.reachable.trans q.word.reachable⟩
  have h₁ : dist x z ≤ ℓ := by
    have h := x.distance_le z q
    exact h.trans_eq hq
  have h₂ : dist z y ≤ dist x y - ℓ := by
    have h := z.distance_le y r
    exact h.trans_eq (hr.trans (by rw [hp]))
  have ht := dist_triangle x z y
  exact ⟨z, by linarith, by linarith⟩


/-- All representatives of the intrinsic closed ball, projected to columns.
Using representatives includes columns identified by zero-length paths. -/
def ballColumns (x : M.Point J root) (ρ : ℝ) : Set (Fin n) :=
  {i | ∃ y : M.Point J root, y.column = i ∧ dist x y ≤ ρ}

lemma mem_ballColumns (x y : M.Point J root) {ρ : ℝ} (hy : dist x y ≤ ρ) :
    y.column ∈ x.ballColumns ρ := ⟨y, rfl, hy⟩

lemma path_ballColumns (x y : M.Point J root) (p : M.Path J x.column y.column)
    {ρ : ℝ} (hp : p.length x.height y.height ≤ ρ) :
    ∀ v ∈ p.word.support, v ∈ x.ballColumns ρ := by
  intro v hv
  obtain ⟨T, hT, q, r, hqr⟩ := p.split_at_column x.inBand y.inBand hv
  let z : M.Point J root := ⟨v, T, hT, x.reachable.trans q.word.reachable⟩
  refine ⟨z, rfl, ?_⟩
  have h := x.distance_le z q
  have hr := r.length_nonneg T y.height
  change dist x z ≤ q.length x.height T at h
  linarith

/-- The projection of an actual closed ball is induced-connected. This is
not an assumed graph property in the local interpolation argument. -/
lemma ballColumns_preconnected (hJ : IsClosed J) (x : M.Point J root) (ρ : ℝ) :
    ((M.activeGraph J).induce (x.ballColumns ρ)).Preconnected := by
  intro i j
  obtain ⟨y, hy, hxy⟩ := i.property
  obtain ⟨z, hz, hxz⟩ := j.property
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  obtain ⟨q, _, hq⟩ := x.exists_shortest hJ z
  have hm : ∀ v ∈ (p.word.reverse.append q.word).support,
      v ∈ x.ballColumns ρ := by
    intro v hv
    rcases (p.word.reverse.mem_support_append_iff q.word).mp hv with h | h
    · exact x.path_ballColumns y p (hp ▸ hxy) v (by simpa using h)
    · exact x.path_ballColumns z q (hq ▸ hxz) v h
  have hreach := (p.word.reverse.append q.word).induce _ hm
  exact ⟨hreach.copy (Subtype.ext hy) (Subtype.ext hz)⟩

lemma ballColumns_nonempty (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (x.ballColumns ρ).Nonempty :=
  ⟨x.column, x.mem_ballColumns x (by simpa using hρ)⟩

/-- The sharper `2ρ+a` version of the source's `2ρ+2a` radial spread. -/
lemma ball_radial_spread (o x y z : M.Point J root) {H a ρ : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (hy : dist x y ≤ ρ) (hz : dist x z ≤ ρ) :
    |dist o (y.withHeight H hH) - dist o (z.withHeight H hH)| ≤ 2 * ρ + a := by
  have h := o.radial_difference_le y z hH hhalf
  have ht := dist_triangle y x z
  rw [dist_comm y x] at ht
  linarith

/-- A shortest path to any point outside a high component reaches an actual
entrance within its total length. Unlike `exit_superlevel`, no radial decrease
to the root is needed. -/
lemma exit_superlevel_to (hJ : IsClosed J) (o x y : M.Point J root)
    {H t : ℝ} (hH : H ∈ J)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hy : y.column ∉ ColumnOrder.componentColumns C) :
    ∃ z : M.Point J root, z.withHeight H hH ∈ o.entrances H hH t C ∧
      dist x z ≤ dist x y := by
  let S := ColumnOrder.componentColumns C
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  obtain ⟨u, v, T, hT, hs, hu, hv, q, r, hqr⟩ :=
    p.crosses_set Sᶜ (by simpa only [Set.mem_compl_iff, not_not] using hx)
      hy x.height y.height
  have huC : u ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hu
  have huv : (M.activeGraph J).Adj u v := ⟨T, hT, hs⟩
  let z : M.Point J root := ⟨u, T, hT, x.reachable.trans q.word.reachable⟩
  let w : M.Point J root := ⟨v, H, hH, z.reachable.trans huv.reachable⟩
  have hw : dist o w < t := by
    apply lt_of_not_ge
    intro h
    exact hv (ColumnOrder.componentColumns_adj C huC huv ⟨w.reachable, h⟩)
  refine ⟨z, ⟨rfl, huC, w, rfl, huv, hw⟩, ?_⟩
  have hdx := x.distance_le z q
  change dist x z ≤ q.length x.height T at hdx
  have hr := r.length_nonneg T y.height
  linarith


/-- The fixed-height radial profile attains its minimum among the finite
set of columns represented in a nonempty closed ball. -/
lemma ball_radial_minimum (o x : M.Point J root) {H ρ : ℝ} (hH : H ∈ J)
    (hρ : 0 ≤ ρ) :
    ∃ y : M.Point J root, dist x y ≤ ρ ∧
      ∀ z : M.Point J root, dist x z ≤ ρ →
        dist o (y.withHeight H hH) ≤ dist o (z.withHeight H hH) := by
  let R := {i : Fin n // (M.activeGraph J).Reachable root i}
  let S : Set R := {i | i.val ∈ x.ballColumns ρ}
  let f : R → ℝ := fun i => dist o ⟨i.val, H, hH, i.property⟩
  have hne : S.Nonempty :=
    ⟨⟨x.column, x.reachable⟩, x.mem_ballColumns x (by simpa using hρ)⟩
  obtain ⟨i, hi, hmin⟩ := Set.exists_min_image S f (Set.toFinite _) hne
  obtain ⟨y, hy, hxy⟩ := hi
  refine ⟨y, hxy, ?_⟩
  intro z hz
  have heq : (⟨i.val, H, hH, i.property⟩ : M.Point J root) = y.withHeight H hH := by
    cases y
    simp_all only [withHeight]
  have h := hmin ⟨z.column, z.reachable⟩ (x.mem_ballColumns z hz)
  change dist o _ ≤ dist o (z.withHeight H hH) at h
  rwa [heq] at h

/-- The exact geometric content of the one-chain small-ball argument:
there are only two consecutive radial layer depths in a sufficiently small
ball, and all its representatives lie in one node at the lower depth. -/
lemma ball_two_layers (hJ : IsClosed J) (o x : M.Point J root)
    {H a ρ δ : ℝ} (hH : H ∈ J) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (hsmall : 2 * ρ + a < δ) :
    ∃ k : ℕ, ∃ y : M.Point J root,
      ∃ C : ((M.activeGraph J).induce (o.superlevel H hH (k * δ))).ConnectedComponent,
        dist x y ≤ ρ ∧ dist o (y.withHeight H hH) < (k + 1) * δ ∧
        (∀ z : M.Point J root, dist x z ≤ ρ →
          z.column ∈ ColumnOrder.componentColumns C ∧
          (k : ℝ) * δ ≤ dist o (z.withHeight H hH) ∧
          dist o (z.withHeight H hH) < (k + 2) * δ) := by
  obtain ⟨y, hy, hmin⟩ := o.ball_radial_minimum x hH hρ
  let b := dist o (y.withHeight H hH)
  let k := ⌊b / δ⌋₊
  have hb : 0 ≤ b / δ := div_nonneg dist_nonneg hδ.le
  have hlo : (k : ℝ) * δ ≤ b := (le_div_iff₀ hδ).mp (Nat.floor_le hb)
  have hhi : b < (k + 1) * δ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (b / δ))
  have hbound : ∀ z : M.Point J root, dist x z ≤ ρ →
      (k : ℝ) * δ ≤ dist o (z.withHeight H hH) ∧
        dist o (z.withHeight H hH) < (k + 2) * δ := by
    intro z hz
    have hminz := hmin z hz
    have hspread := o.ball_radial_spread x z y hH hhalf hz hy
    have hu := (abs_le.mp hspread).2
    constructor
    · exact hlo.trans hminz
    · dsimp [b] at hhi
      linarith
  have hsub : x.ballColumns ρ ⊆ o.superlevel H hH (k * δ) := by
    rintro _ ⟨z, rfl, hz⟩
    exact (o.mem_superlevel_iff z H hH (k * δ)).mpr (hbound z hz).1
  obtain ⟨C, hC⟩ := ColumnOrder.exists_component_containing
    (x.ballColumns_nonempty hρ) (x.ballColumns_preconnected hJ ρ) hsub
  exact ⟨k, y, C, hy, hhi, fun z hz => ⟨hC (x.mem_ballColumns z hz), hbound z hz⟩⟩


/-- At depth zero the single radial node contains every reachable column,
including the chosen basepoint column. -/
lemma mem_zero_component (o x : M.Point J root) {H : ℝ} (hH : H ∈ J)
    (C : ((M.activeGraph J).induce (o.superlevel H hH 0)).ConnectedComponent) :
    x.column ∈ ColumnOrder.componentColumns C := by
  classical
  obtain ⟨i, hi⟩ := C.nonempty_supp
  obtain ⟨hr, _⟩ := i.property
  obtain ⟨p⟩ := hr.symm.trans x.reachable
  apply ColumnOrder.componentColumns_of_walk C p ⟨i, hi, rfl⟩
  intro v hv
  exact ⟨hr.trans (p.takeUntil v hv).reachable, dist_nonneg⟩

/-- Two fixed geometric portals, with all bounds required by the actual
interpolation hierarchy. Repeated portals encode the one-portal case. -/
structure PortalData (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (a t : ℝ)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) where
  left : M.Point J root
  right : M.Point J root
  left_height : left.height = H
  right_height : right.height = H
  left_mem : left.column ∈ ColumnOrder.componentColumns C
  right_mem : right.column ∈ ColumnOrder.componentColumns C
  left_radial : t ≤ dist o left ∧ dist o left < t + a
  right_radial : t ≤ dist o right ∧ dist o right < t + a
  cover : ∀ x : M.Point J root, x.column ∈ ColumnOrder.componentColumns C →
    min (dist x left) (dist x right) ≤ dist o x - t + 201 * a
  entrance_cover : ∀ x : M.Point J root,
    x.withHeight H hH ∈ o.entrances H hH t C →
      min (dist x left) (dist x right) ≤ 200 * a

/-- The portal data are constructed from the proved geometry, including the
root convention; they are not assumptions on the interpolation input. -/
lemma portalData_nonempty (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ho : o.height = H) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (ht : t = 0 ∨ a / 2 < t)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    Nonempty (o.PortalData H hH a t C) := by
  rcases ht with rfl | ht
  · refine ⟨⟨o, o, ho, ho, o.mem_zero_component o hH C,
      o.mem_zero_component o hH C, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [dist_self, zero_add] using And.intro (le_refl (0 : ℝ)) ha
    · simpa only [dist_self, zero_add] using And.intro (le_refl (0 : ℝ)) ha
    · intro x _
      simp only [min_self, sub_zero, dist_comm x o]
      linarith
    · rintro x ⟨_, _, y, _, _, hy⟩
      exact (not_lt_of_ge dist_nonneg hy).elim
  · obtain ⟨p, hp, q, hq, hpr, hqr, hc⟩ := o.component_two_portals hJ hH ha hhalf C
      (o.entrances_nonempty hJ hH ht hhalf C)
    refine ⟨⟨p, q, hp.1, hq.1, hp.2.1, hq.2.1, hpr, hqr, ?_, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, hd⟩ := o.exit_superlevel hJ x hH ht hhalf C hx
      rcases hc z hz with hz | hz
      · exact (min_le_left _ _).trans (by linarith [dist_triangle x z p])
      · exact (min_le_right _ _).trans (by linarith [dist_triangle x z q])
    · intro x hx
      exact min_le_iff.mpr (hc x hx)

namespace PortalData

variable {o : M.Point J root} {H a t : ℝ} {hH : H ∈ J}
    {C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent}

/-- Layer points and points only slightly beyond its top are close to a
fixed portal. The radial allowance is kept explicit for child portals. -/
lemma near_of_radial (K : o.PortalData H hH a t C)
    {δ e : ℝ} (x : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hr : dist o x ≤ t + δ + e) :
    min (dist x K.left) (dist x K.right) ≤ δ + e + 201 * a := by
  linarith [K.cover x hx]

lemma near_layer (K : o.PortalData H hH a t C)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (ha : 0 ≤ a)
    {δ : ℝ} (x : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hr : dist o (x.withHeight H hH) < t + δ) :
    min (dist x K.left) (dist x K.right) ≤ δ + 220 * a := by
  have hv : dist (x.withHeight H hH) x ≤ a / 2 := by
    rw [dist_comm, x.dist_withHeight, abs_sub_comm]
    exact hhalf x.height x.inBand
  have htri := dist_triangle o (x.withHeight H hH) x
  linarith [K.cover x hx]

/-- A near-exit point is in the equality collar of these same portals;
there is no resampling or reselecting a different portal pair. -/
lemma near_exit (K : o.PortalData H hH a t C) (hJ : IsClosed J)
    (x y : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hy : y.column ∉ ColumnOrder.componentColumns C) :
    min (dist x K.left) (dist x K.right) ≤ dist x y + 200 * a := by
  obtain ⟨z, hz, hd⟩ := o.exit_superlevel_to hJ x y hH C hx hy
  rcases min_le_iff.mp (K.entrance_cover z hz) with h | h
  · exact (min_le_left _ _).trans (by linarith [dist_triangle x z K.left])
  · exact (min_le_right _ _).trans (by linarith [dist_triangle x z K.right])

end PortalData

end Point

end Model
end Columns
end PlanarL1

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Fields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)
/-- A scalar field on the whole band, including all its components. Its only
compatibility condition is equality at actual allowed switch heights. -/
structure Field (J : Set ℝ) (L : NNReal) where
  value : Fin n → J → ℝ
  vertical : ∀ i, LipschitzWith L (value i)
  switch : ∀ i j (H : J), H.val ∈ M.heights i j → value i H = value j H

namespace Field

variable {M} {J : Set ℝ} {L : NNReal}

lemma path_bound (F : M.Field J L) {i j : Fin n} (p : M.Path J i j)
    (a b : J) : |F.value i a - F.value j b| ≤ L * p.length a.val b.val := by
  induction p generalizing a b with
  | nil i =>
    simpa only [Path.length, Real.dist_eq, Subtype.dist_eq] using (F.vertical i).dist_le_mul a b
  | @cons i j k H hH hs p ih =>
    have ht := abs_sub_le (F.value i a) (F.value i ⟨H,hH⟩) (F.value k b)
    rw [F.switch i j ⟨H,hH⟩ hs] at ht
    have hv := (F.vertical i).dist_le_mul a ⟨H,hH⟩
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, F.switch i j ⟨H,hH⟩ hs] at hv
    have hi := ih ⟨H,hH⟩ b
    change _ ≤ L * (|a.val - H| + p.length H b.val)
    nlinarith

/-- Vertical Lipschitz bounds and switch equality imply the intrinsic bound,
by summing on an actual attaining shortest path. -/
lemma lipschitz (F : M.Field J L) (hJ : IsClosed J) (root : Fin n) :
    LipschitzWith L (fun x : M.Point J root => F.value x.column ⟨x.height,x.inBand⟩) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  rw [Real.dist_eq]
  simpa only [hp] using F.path_bound p ⟨x.height,x.inBand⟩ ⟨y.height,y.inBand⟩

end Field

namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

/-- Truncated point distance on EVERY column. Columns outside the metric
component have the constant ceiling. -/
noncomputable def truncated (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J) : ℝ := by
  classical
  exact if hi : (M.activeGraph J).Reachable root i then
    min (dist o (⟨i,H.val,H.property,hi⟩ : M.Point J root)) D else D

lemma truncated_of_reachable (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J)
    (hi : (M.activeGraph J).Reachable root i) :
    o.truncated D i H = min (dist o (⟨i,H.val,H.property,hi⟩ : M.Point J root)) D := by
  simp only [truncated, dite_eq_left hi]

lemma truncated_le (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J) :
    o.truncated D i H ≤ D := by
  unfold truncated
  split
  · exact min_le_right _ _
  · exact le_rfl

lemma truncated_vertical (o : M.Point J root) (D : ℝ) (i : Fin n) :
    LipschitzWith 1 (o.truncated D i) := by
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hp : LipschitzWith 1 (fun H : J => (⟨i,H.val,H.property,hi⟩ : M.Point J root)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Point.dist_same_column (⟨i,x.val,x.property,hi⟩ : M.Point J root)
        (⟨i,y.val,y.property,hi⟩ : M.Point J root) rfl]
      simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq]
      exact le_rfl
    have ho : LipschitzWith 1 (fun x : M.Point J root => dist o x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [NNReal.coe_one,one_mul] using dist_dist_dist_le_right o x y
    have hd := ho.comp hp
    have he : o.truncated D i = (fun H : J => min (dist o
        (⟨i,H.val,H.property,hi⟩ : M.Point J root)) D) :=
      funext (fun H => o.truncated_of_reachable D i H hi)
    rw [he]
    simpa only [mul_one,Function.comp_apply] using hd.min_const D
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [truncated,dite_eq_right hi,dist_self,NNReal.coe_one,one_mul]
    exact dist_nonneg

lemma truncated_switch (o : M.Point J root) (D : ℝ) (i j : Fin n) (H : J)
    (hs : H.val ∈ M.heights i j) : o.truncated D i H = o.truncated D j H := by
  have ha : (M.activeGraph J).Adj i j := ⟨H.val,H.property,hs⟩
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hj := hi.trans ha.reachable
    rw [truncated_of_reachable _ _ _ _ hi, truncated_of_reachable _ _ _ _ hj]
    congr 1
    let x : M.Point J root := ⟨i,H.val,H.property,hi⟩
    let y : M.Point J root := ⟨j,H.val,H.property,hj⟩
    have hz : dist x y = 0 := by
      apply le_antisymm _ dist_nonneg
      simpa only [x,y,sub_self,abs_zero,add_zero] using x.dist_le_switch y H.property hs
    exact PseudoMetricSpace.dist_eq_of_dist_zero o hz
  · have hj : ¬(M.activeGraph J).Reachable root j := by
      intro hj
      exact hi (hj.trans ha.symm.reachable)
    simp only [truncated,dite_eq_right hi,dite_eq_right hj]

lemma truncated_root (o : M.Point J root) (D : ℝ) (H : J) :
    o.truncated D o.column H = min |o.height - H.val| D := by
  rw [truncated_of_reachable _ _ _ _ o.reachable,
    Point.dist_same_column o (⟨o.column,H.val,H.property,o.reachable⟩ : M.Point J root) rfl]

lemma truncated_minimum (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J) :
    o.truncated D o.column H ≤ o.truncated D i H := by
  rw [truncated_root]
  by_cases hi : (M.activeGraph J).Reachable root i
  · rw [truncated_of_reachable _ _ _ _ hi]
    exact min_le_min_right D (o.height_change_le (⟨i,H.val,H.property,hi⟩ : M.Point J root))
  · simp only [truncated,dite_eq_right hi]
    exact min_le_right _ _

/-- The strict sublevel connects to the root by a real shortest switching
path; every visited column remains in the same strict sublevel. -/
lemma truncated_sublevel_path (hJ : IsClosed J) (o : M.Point J root) (D t : ℝ)
    (ht : t ≤ D) (i : Fin n) (H : J) (hi : o.truncated D i H < t) :
    ∃ w : (M.activeGraph J).Walk i o.column,
      ∀ z ∈ w.support, o.truncated D z H < t := by
  have hir : (M.activeGraph J).Reachable root i := by
    by_contra hn
    simp only [truncated,dite_eq_right hn] at hi
    exact (not_lt_of_ge ht) hi
  rw [truncated_of_reachable _ _ _ _ hir] at hi
  have hdist : dist o (⟨i,H.val,H.property,hir⟩ : M.Point J root) < t := by
    rcases (min_lt_iff).mp hi with hi | hi
    · exact hi
    · exact False.elim ((not_lt_of_ge ht) hi)
  obtain ⟨p, _, hp⟩ := o.shortest_sublevel hJ (⟨i,H.val,H.property,hir⟩ : M.Point J root)
  refine ⟨p.word.reverse, ?_⟩
  intro z hz
  obtain ⟨hzr, hdz⟩ := hp z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
  rw [truncated_of_reachable _ _ _ _ hzr]
  exact (min_le_left _ _).trans_lt (hdz.trans_lt hdist)

/-- The literal running-minimum projection of point distance, after cutting
at the chosen representative of the root. -/
noncomputable def supportValue {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (i : Fin (k + 1)) (H : J) : ℝ :=
  Ordered.running ((finCycle o.column).symm w.column)
    (fun j => o.truncated (dist o w) (finCycle o.column j) H)
    ((finCycle o.column).symm i)

lemma supportValue_vertical {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (i : Fin (k + 1)) : LipschitzWith 1 (o.supportValue w i) := by
  exact Ordered.running_lipschitz _ _ _ 1 (fun j => o.truncated_vertical _ _)

lemma supportValue_switch {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) (i j : Fin (k + 1)) (H : J)
    (hs : H.val ∈ M.heights i j) : o.supportValue w i H = o.supportValue w j H := by
  let e := finCycle o.column
  let f := fun z => o.truncated (dist o w) (e z) H
  have hzero : e 0 = o.column := by simp [e,finCycle_apply]
  have hmin : ∀ z, f 0 ≤ f z := by
    intro z
    simpa only [f,hzero] using o.truncated_minimum (dist o w) (e z) H
  have hpath : ∀ t ≤ dist o w, ∀ z, f z < t →
      ∃ p : ((M.activeGraph J).comap e).Walk z 0, ∀ v ∈ p.support, f v < t := by
    intro t ht z hz
    obtain ⟨p,hp⟩ := o.truncated_sublevel_path hJ (dist o w) t ht (e z) H hz
    obtain ⟨q,hq⟩ := ColumnOrder.walk_comap_equiv e (p.copy rfl hzero.symm)
    refine ⟨q,fun v hv => ?_⟩
    exact hp (e v) (by simpa only [SimpleGraph.Walk.support_copy] using hq v hv)
  have hnc := ColumnOrder.noncrossing_comap_cycle (M.active_noncrossing J) o.column
  have heq : f (e.symm i) = f (e.symm j) := by
    simpa only [f,Equiv.apply_symm_apply] using o.truncated_switch (dist o w) i j H hs
  have hadj : ((M.activeGraph J).comap e).Adj (e.symm i) (e.symm j) := by
    simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply] using
      (show (M.activeGraph J).Adj i j from ⟨H.val,H.property,hs⟩)
  change Ordered.running (e.symm w.column) f (e.symm i) =
    Ordered.running (e.symm w.column) f (e.symm j)
  rcases lt_trichotomy (e.symm i) (e.symm j) with hij | hij | hij
  · apply Ordered.running_switch _ _ hmin hij heq
    exact ColumnOrder.collision hnc f (dist o w) (fun z => o.truncated_le _ _ _) hpath hij hadj heq
  · rw [hij]
  · symm
    apply Ordered.running_switch _ _ hmin hij heq.symm
    exact ColumnOrder.collision hnc f (dist o w) (fun z => o.truncated_le _ _ _) hpath hij hadj.symm heq.symm

/-- Ordered support, with actual vertical and switch proofs. -/
noncomputable def supportField {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) : M.Field J 1 where
  value := o.supportValue w
  vertical := o.supportValue_vertical w
  switch := o.supportValue_switch hJ w

lemma supportValue_root {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (H : J) :
    o.supportValue w o.column H = min |o.height - H.val| (dist o w) := by
  simp only [supportValue,finCycle_symm_apply,sub_self,Ordered.running_zero,
    finCycle_apply,zero_add,truncated_root]

lemma supportValue_target {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) : o.supportValue w w.column ⟨w.height,w.inBand⟩ = dist o w := by
  rw [supportValue,Ordered.running_target,Equiv.apply_symm_apply,
    truncated_of_reachable _ _ _ _ w.reachable]
  exact min_self _

lemma supportValue_bounds {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (i : Fin (k + 1)) (H : J) :
    0 ≤ o.supportValue w i H ∧ o.supportValue w i H ≤ o.truncated (dist o w) i H := by
  let e := finCycle o.column
  let f := fun j => o.truncated (dist o w) (e j) H
  have hzero : e 0 = o.column := by simp [e,finCycle_apply]
  have hmin : ∀ z, f 0 ≤ f z := by
    intro z
    simpa only [f,hzero] using o.truncated_minimum (dist o w) (e z) H
  have hnonneg : 0 ≤ f 0 := by
    dsimp only [f]
    rw [hzero,truncated_root]
    exact le_min (abs_nonneg _) dist_nonneg
  exact ⟨hnonneg.trans (Ordered.le_running _ _ hmin _),
    by simpa only [supportValue,f,e,Equiv.apply_symm_apply] using
      Ordered.running_le (e.symm w.column) f (e.symm i)⟩

end Point

/-- Monotonicity on the two arcs, expressed in the circle cut at `a`.
The separate minimum condition records the wrap-around step to index zero. -/
def Field.OrderedFrom {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b : Fin (k + 1)) : Prop :=
  (∀ (H : J) i, F.value a H ≤ F.value i H) ∧
  (∀ (H : J) (i j : Fin (k + 1)), i ≤ j → j ≤ (finCycle a).symm b →
    F.value (finCycle a i) H ≤ F.value (finCycle a j) H) ∧
  (∀ (H : J) (i j : Fin (k + 1)), (finCycle a).symm b ≤ i → i ≤ j →
    F.value (finCycle a j) H ≤ F.value (finCycle a i) H)

namespace Point

lemma supportField_ordered {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) :
    (o.supportField hJ w).OrderedFrom o.column w.column := by
  have hmin (H : J) : ∀ z, o.truncated (dist o w) (finCycle o.column 0) H ≤
      o.truncated (dist o w) (finCycle o.column z) H := by
    simp only [finCycle_apply,zero_add]
    intro z
    exact o.truncated_minimum _ _ _
  refine ⟨?_,?_,?_⟩
  · intro H i
    change o.supportValue w o.column H ≤ o.supportValue w i H
    unfold supportValue
    simp only [finCycle_symm_apply,sub_self,Ordered.running_zero]
    simpa only [finCycle_symm_apply] using
      Ordered.le_running ((finCycle o.column).symm w.column)
        (fun z => o.truncated (dist o w) (finCycle o.column z) H) (hmin H)
        ((finCycle o.column).symm i)
  · intro H i j hij hjb
    change o.supportValue w (finCycle o.column i) H ≤ o.supportValue w (finCycle o.column j) H
    simp only [supportValue,Equiv.symm_apply_apply]
    exact Ordered.running_mono_left _ _ (hmin H) hij hjb
  · intro H i j hbi hij
    change o.supportValue w (finCycle o.column j) H ≤ o.supportValue w (finCycle o.column i) H
    simp only [supportValue,Equiv.symm_apply_apply]
    exact Ordered.running_mono_right _ _ hbi hij

/-- Lemma ord:support, on every representative of the whole band. No
connectivity of the whole band is assumed. The upper distance bound is on the
chosen finite-distance component, just as the source's infinite convention. -/
theorem exists_ordered_support {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) :
    ∃ F : M.Field J 1, F.OrderedFrom o.column w.column ∧
      (∀ i H, 0 ≤ F.value i H ∧ F.value i H ≤ dist o w) ∧
      F.value o.column ⟨o.height,o.inBand⟩ = 0 ∧
      F.value w.column ⟨w.height,w.inBand⟩ = dist o w ∧
      ∀ x : M.Point J r, F.value x.column ⟨x.height,x.inBand⟩ ≤ dist o x := by
  refine ⟨o.supportField hJ w, o.supportField_ordered hJ w, ?_, ?_, ?_, ?_⟩
  · intro i H
    exact ⟨(o.supportValue_bounds w i H).1,
      (o.supportValue_bounds w i H).2.trans (o.truncated_le _ _ _)⟩
  · change o.supportValue w o.column ⟨o.height,o.inBand⟩ = 0
    rw [supportValue_root,sub_self,abs_zero,min_eq_left dist_nonneg]
  · exact o.supportValue_target w
  · intro x
    have h := (o.supportValue_bounds w x.column ⟨x.height,x.inBand⟩).2
    rw [truncated_of_reachable _ _ _ _ x.reachable] at h
    exact h.trans (min_le_left _ _)

end Point

namespace Field

/-- Signed open-arc membership. Boundary columns have sign zero. -/
def arcSign {k : ℕ} (a b i : Fin (k + 1)) : ℝ :=
  if i = a ∨ i = b then 0 else if (finCycle a).symm i < (finCycle a).symm b then 1 else -1

lemma arcSign_cases {k : ℕ} (a b i : Fin (k + 1)) :
    arcSign a b i = 0 ∨ arcSign a b i = 1 ∨ arcSign a b i = -1 := by
  unfold arcSign
  split_ifs <;> simp

lemma arcSign_zero_iff {k : ℕ} (a b i : Fin (k + 1)) :
    arcSign a b i = 0 ↔ i = a ∨ i = b := by
  unfold arcSign
  split_ifs <;> simp_all

lemma abs_arcSign_le {k : ℕ} (a b i : Fin (k + 1)) : |arcSign a b i| ≤ 1 := by
  rcases arcSign_cases a b i with h | h | h <;> simp [h]

/-- Source Z_s in the max metric on R x R: the two boundary images and the
images of actual switches between opposite OPEN arcs. -/
def wall {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b : Fin (k + 1)) : Set (ℝ × ℝ) :=
  {z | (∃ H : J, z = (F.value a H,H.val)) ∨
    (∃ H : J, z = (F.value b H,H.val)) ∨
    ∃ (i j : Fin (k + 1)) (H : J), H.val ∈ M.heights i j ∧
      arcSign a b i = 1 ∧ arcSign a b j = -1 ∧ z = (F.value i H,H.val)}

lemma wall_of_boundary {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i : Fin (k + 1)) (H : J) (hi : arcSign a b i = 0) :
    (F.value i H,H.val) ∈ F.wall a b := by
  rcases (arcSign_zero_iff a b i).mp hi with hi | hi
  · exact Or.inl ⟨H,by rw [hi]⟩
  · exact Or.inr (Or.inl ⟨H,by rw [hi]⟩)

lemma wall_of_switch {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i j : Fin (k + 1)) (H : J) (hs : H.val ∈ M.heights i j)
    (hneq : arcSign a b i ≠ arcSign a b j) : (F.value i H,H.val) ∈ F.wall a b := by
  by_cases hi : arcSign a b i = 0
  · exact F.wall_of_boundary a b i H hi
  by_cases hj : arcSign a b j = 0
  · rw [F.switch i j H hs]
    exact F.wall_of_boundary a b j H hj
  rcases arcSign_cases a b i with hi' | hi' | hi'
  · exact False.elim (hi hi')
  · rcases arcSign_cases a b j with hj' | hj' | hj'
    · exact False.elim (hj hj')
    · exact False.elim (hneq (hi'.trans hj'.symm))
    · exact Or.inr (Or.inr ⟨i,j,H,hs,hi',hj',rfl⟩)
  · rcases arcSign_cases a b j with hj' | hj' | hj'
    · exact False.elim (hj hj')
    · exact Or.inr (Or.inr ⟨j,i,H,by rwa [M.symm j i],hj',hi',by rw [F.switch i j H hs]⟩)
    · exact False.elim (hneq (hi'.trans hj'.symm))

noncomputable def transverseValue {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i : Fin (k + 1)) (H : J) : ℝ :=
  arcSign a b i * Metric.infDist (F.value i H,H.val) (F.wall a b)

lemma coordinate_lipschitz {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (hL : 1 ≤ L) (i : Fin (k + 1)) :
    LipschitzWith L (fun H : J => (F.value i H,H.val)) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  rw [Prod.dist_eq]
  refine max_le ((F.vertical i).dist_le_mul H T) ?_
  change dist H T ≤ L * dist H T
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [dist_nonneg (x := H) (y := T)]

lemma transverse_vertical {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (hL : 1 ≤ L) (a b i : Fin (k + 1)) :
    LipschitzWith L (F.transverseValue a b i) := by
  have hd := (Metric.lipschitz_infDist_pt (F.wall a b)).comp (F.coordinate_lipschitz hL i)
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have hh := hd.dist_le_mul H T
  simp only [one_mul,Function.comp_apply,Real.dist_eq] at hh
  rw [Real.dist_eq,transverseValue,transverseValue,← mul_sub,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_arcSign_le a b i)).trans hh

lemma transverse_switch {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i j : Fin (k + 1)) (H : J) (hs : H.val ∈ M.heights i j) :
    F.transverseValue a b i H = F.transverseValue a b j H := by
  by_cases he : arcSign a b i = arcSign a b j
  · simp only [transverseValue,he,F.switch i j H hs]
  · have hz := Metric.infDist_zero_of_mem (F.wall_of_switch a b i j H hs he)
    unfold transverseValue
    rw [F.switch i j H hs] at hz ⊢
    rw [hz,mul_zero,mul_zero]

/-- The transverse field. Its slope bound is inherited
from the original field (and at least one), with the switch identity proved. -/
noncomputable def transverse {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (hL : 1 ≤ L) (a b : Fin (k + 1)) : M.Field J L where
  value := F.transverseValue a b
  vertical := F.transverse_vertical hL a b
  switch := F.transverse_switch a b

end Field

namespace Path

variable {M} {J : Set ℝ}

/-- The actual set of representatives visited by a finite switching path,
including every point of its vertical segments. -/
def trace : {i j : Fin n} → M.Path J i j → ℝ → ℝ → Set (Fin n × ℝ)
  | i, _, .nil _, a, b => {z | z.1 = i ∧ z.2 ∈ Set.uIcc a b}
  | i, _, .cons H _ _ p, a, b => {z | z.1 = i ∧ z.2 ∈ Set.uIcc a H} ∪ p.trace H b

end Path


end Model
end Columns

end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Point
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}

/-- A Lipschitz scalar on one intrinsic component, continued constantly on the
other components, is a genuine vertical/switch-compatible field. -/
noncomputable def extendValue (f : M.Point J root → ℝ) (i : Fin n) (H : J) : ℝ := by
  classical
  exact if h : (M.activeGraph J).Reachable root i then f ⟨i,H.val,H.property,h⟩ else 0

lemma extendValue_vertical {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f)
    (i : Fin n) : LipschitzWith K (extendValue f i) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  by_cases hi : (M.activeGraph J).Reachable root i
  · simp only [extendValue,dite_eq_left hi]
    have h := hf.dist_le_mul (⟨i,a.val,a.property,hi⟩ : M.Point J root)
      (⟨i,b.val,b.property,hi⟩ : M.Point J root)
    rw [Point.dist_same_column (⟨i,a.val,a.property,hi⟩ : M.Point J root)
      (⟨i,b.val,b.property,hi⟩ : M.Point J root) rfl] at h
    simpa only [Subtype.dist_eq,Real.dist_eq] using h
  · simp only [extendValue,dite_eq_right hi,dist_self]
    positivity

lemma extendValue_switch {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f)
    (i j : Fin n) (H : J) (hs : H.val ∈ M.heights i j) :
    extendValue f i H = extendValue f j H := by
  have ha : (M.activeGraph J).Adj i j := ⟨H.val,H.property,hs⟩
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hj := hi.trans ha.reachable
    simp only [extendValue,dite_eq_left hi,dite_eq_left hj]
    let x : M.Point J root := ⟨i,H.val,H.property,hi⟩
    let y : M.Point J root := ⟨j,H.val,H.property,hj⟩
    have hd : dist x y = 0 := by
      apply le_antisymm _ dist_nonneg
      simpa only [x,y,sub_self,abs_zero,add_zero] using x.dist_le_switch y H.property hs
    have h := hf.dist_le_mul x y
    rw [hd,mul_zero] at h
    exact dist_le_zero.mp h
  · have hj : ¬ (M.activeGraph J).Reachable root j := fun h => hi (h.trans ha.symm.reachable)
    simp only [extendValue,dite_eq_right hi,dite_eq_right hj]

noncomputable def extendField {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f) :
    M.Field J K where
  value := extendValue f
  vertical := extendValue_vertical f hf
  switch := extendValue_switch f hf

end PlanarL1.Columns.Model.Point


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Cuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model

/-- One label of a nested-set system. Nesting and exact switching are the
set invariants, not any embedding or separation assumption. -/
structure Activity {n : ℕ} (M : Model n) where
  active : Fin n → ℝ → Prop
  increasing : ∀ i s t, s ≤ t → active i s → active i t
  switch : ∀ i j H, H ∈ M.heights i j → (active i H ↔ active j H)

namespace Activity

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {M : Model n} (A : Activity M)

def graph : SimpleGraph (Fin n) where
  Adj i j := ∃ H, H ∈ M.heights i j ∧ A.active i H
  symm := ⟨by
    rintro i j ⟨H,hH,hA⟩
    exact ⟨H,by rwa [M.symm i j] at hH,(A.switch i j H hH).mp hA⟩⟩
  loopless := ⟨by
    rintro i ⟨H,hH,_⟩
    exact M.link.loopless.irrefl i (M.permitted i i H hH)⟩

def component (i : Fin n) : Set (Fin n) := {k | A.graph.Reachable i k}

lemma mem_component_self (i : Fin n) : i ∈ A.component i := .refl i

lemma component_eq_iff (i j : Fin n) : A.component i = A.component j ↔ A.graph.Reachable i j := by
  constructor
  · intro h
    change j ∈ A.component i
    rw [h]
    exact A.mem_component_self j
  · intro h
    ext k
    exact ⟨fun hik => h.symm.trans hik,fun hjk => h.trans hjk⟩

/-- Active points get a single component coordinate; inactive points get zero.
The finite coordinate set consists of all subsets of columns. -/
noncomputable def vector (i : Fin n) (H : ℝ) (S : Set (Fin n)) : ℝ :=
  if A.active i H ∧ S = A.component i then 1 else 0

noncomputable def indicator (i : Fin n) (H : ℝ) : ℝ := if A.active i H then 1 else 0

noncomputable def cost (i j : Fin n) (s t : ℝ) : ℝ :=
  ∑ S : Set (Fin n), |A.vector i s S - A.vector j t S|

lemma cost_nonneg (i j : Fin n) (s t : ℝ) : 0 ≤ A.cost i j s t := by
  unfold cost
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma vector_inactive {i : Fin n} {H : ℝ} (h : ¬ A.active i H) : A.vector i H = 0 := by
  funext S
  simp only [vector,h,false_and,ite_false,Pi.zero_apply]

lemma vector_active {i : Fin n} {H : ℝ} (h : A.active i H) (S : Set (Fin n)) :
    A.vector i H S = if S = A.component i then 1 else 0 := by
  simp only [vector,h,true_and]

lemma cost_comm (i j : Fin n) (s t : ℝ) : A.cost i j s t = A.cost j i t s := by
  unfold cost
  apply Finset.sum_congr rfl
  intro S _
  exact abs_sub_comm _ _

lemma cost_triangle (i j k : Fin n) (s t u : ℝ) :
    A.cost i k s u ≤ A.cost i j s t+A.cost j k t u := by
  unfold cost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun S _ => abs_sub_le _ _ _

lemma cost_vertical (i : Fin n) (s t : ℝ) :
    A.cost i i s t = |A.indicator i s-A.indicator i t| := by
  classical
  by_cases hs : A.active i s <;> by_cases ht : A.active i t
  · simp only [cost,A.vector_active hs,A.vector_active ht,sub_self,abs_zero,
      Finset.sum_const_zero,indicator,hs,ht,ite_true]
  · simp only [cost,A.vector_active hs,A.vector_inactive ht,Pi.zero_apply,sub_zero,
      indicator,hs,ht,ite_true,ite_false]
    simp only [apply_ite abs,abs_one,abs_zero]
    simp
  · rw [A.cost_comm]
    simp only [cost,A.vector_active ht,A.vector_inactive hs,Pi.zero_apply,sub_zero,
      indicator,hs,ht,ite_true,ite_false]
    simp only [apply_ite abs,abs_one,abs_zero]
    simp
  · simp only [cost,A.vector_inactive hs,A.vector_inactive ht,Pi.zero_apply,sub_self,
      abs_zero,Finset.sum_const_zero,indicator,hs,ht,ite_false]

lemma vector_switch {i j : Fin n} {H : ℝ} (hH : H ∈ M.heights i j) :
    A.vector i H = A.vector j H := by
  classical
  by_cases hi : A.active i H
  · have hj := (A.switch i j H hH).mp hi
    have he := (A.component_eq_iff i j).mpr (SimpleGraph.Adj.reachable ⟨H,hH,hi⟩)
    funext S
    simp only [A.vector_active hi,A.vector_active hj,he]
  · rw [A.vector_inactive hi,A.vector_inactive (fun h => hi ((A.switch i j H hH).mpr h))]

lemma cost_switch {i j : Fin n} {H : ℝ} (hH : H ∈ M.heights i j) : A.cost i j H H = 0 := by
  simp only [cost,A.vector_switch hH,sub_self,abs_zero,Finset.sum_const_zero]

/-- The unrefined costs of the vertical pieces of an ACTUAL permitted path. -/
noncomputable def pathCost {J : Set ℝ} : {i j : Fin n} → M.Path J i j → ℝ → ℝ → ℝ
  | _, _, .nil i, s, t => |A.indicator i s-A.indicator i t|
  | i, _, .cons H _ _ p, s, t => |A.indicator i s-A.indicator i H|+pathCost p H t

lemma cost_le_pathCost {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    A.cost i j s t ≤ A.pathCost p s t := by
  induction p generalizing s with
  | nil => exact le_of_eq (A.cost_vertical _ _ _)
  | @cons i k j H hH hs p ih =>
    have h₁ := A.cost_triangle i k j H H t
    rw [A.cost_switch hs,zero_add] at h₁
    have h₂ := A.cost_triangle i i j s H t
    rw [A.cost_vertical] at h₂
    change A.cost i j s t ≤ |A.indicator i s-A.indicator i H|+A.pathCost p H t
    linarith [ih H]

end Activity
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model
open MeasureTheory

/-- The exact hypotheses in the component-refinement lemma, put on an actual
measure space. The vertical bound is the invariant of the cut construction. -/
structure SetSystem {n : ℕ} (M : Model n) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  activity : Ω → Activity M
  measurable_active : ∀ i H, MeasurableSet {ω | (activity ω).active i H}
  vertical_integrable : ∀ i s t,
    Integrable (fun ω => |(activity ω).indicator i s-(activity ω).indicator i t|) μ
  vertical_bound : ∀ i s t,
    (∫ ω, |(activity ω).indicator i s-(activity ω).indicator i t| ∂μ) ≤ |s-t|

namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} (A : SetSystem M Ω μ)

lemma measurable_indicator (i : Fin n) (H : ℝ) :
    Measurable (fun ω => (A.activity ω).indicator i H) := by
  exact Measurable.ite (A.measurable_active i H) measurable_const measurable_const

/-- Compactness and monotonicity reduce active-link measurability to ONE fixed
height. There is no uncountable union of switching events. -/
lemma measurable_adj (i j : Fin n) :
    MeasurableSet {ω | (A.activity ω).graph.Adj i j} := by
  by_cases h : (M.heights i j).Nonempty
  · obtain ⟨H,hH,hmax⟩ := (M.compact i j).exists_isGreatest h
    have he : {ω | (A.activity ω).graph.Adj i j} =
        {ω | (A.activity ω).active i H} := by
      ext ω
      constructor
      · rintro ⟨T,hT,ha⟩
        exact (A.activity ω).increasing i T H (hmax hT) ha
      · intro ha
        exact ⟨H,hH,ha⟩
    rw [he]
    exact A.measurable_active i H
  · have he : {ω | (A.activity ω).graph.Adj i j} = ∅ := by
      ext ω
      constructor
      · rintro ⟨H,hH,_⟩
        exact h ⟨H,hH⟩
      · exact False.elim
    rw [he]
    exact MeasurableSet.empty

lemma measurable_graph_fiber (G : SimpleGraph (Fin n)) :
    MeasurableSet {ω | (A.activity ω).graph = G} := by
  have he : {ω | (A.activity ω).graph = G} =
      ⋂ i, ⋂ j, {ω | (A.activity ω).graph.Adj i j ↔ G.Adj i j} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    constructor
    · intro h; rw [h]; exact fun _ _ => Iff.rfl
    · intro h; exact SimpleGraph.ext (funext fun i => funext fun j => propext (h i j))
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : G.Adj i j
  · simpa only [h,iff_true] using A.measurable_adj i j
  · simpa only [h,iff_false,Set.compl_ofPred] using (A.measurable_adj i j).compl

lemma measurable_component (i : Fin n) (S : Set (Fin n)) :
    MeasurableSet {ω | (A.activity ω).component i = S} := by
  let : MeasurableSpace (SimpleGraph (Fin n)) := ⊤
  have hm : Measurable (fun ω => (A.activity ω).graph) :=
    measurable_to_countable' (A.measurable_graph_fiber)
  exact hm (t := {G | {k | G.Reachable i k} = S}) trivial

lemma measurable_vector (i : Fin n) (H : ℝ) (S : Set (Fin n)) :
    Measurable (fun ω => (A.activity ω).vector i H S) := by
  have hh : MeasurableSet {ω | S = (A.activity ω).component i} := by
    simpa only [eq_comm] using A.measurable_component i S
  exact Measurable.ite ((A.measurable_active i H).inter hh)
    measurable_const measurable_const

lemma measurable_cost (i j : Fin n) (s t : ℝ) :
    Measurable (fun ω => (A.activity ω).cost i j s t) := by
  classical
  exact Finset.measurable_sum _ fun S _ =>
    ((A.measurable_vector i s S).sub (A.measurable_vector j t S)).abs

lemma pathCost_integrable {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    Integrable (fun ω => (A.activity ω).pathCost p s t) μ := by
  induction p generalizing s with
  | nil => exact A.vertical_integrable _ _ _
  | cons H _ _ p ih => exact (A.vertical_integrable _ _ _).add (ih H)

lemma cost_integrable {J : Set ℝ} {i j : Fin n} (p : M.Path J i j) (s t : ℝ) :
    Integrable (fun ω => (A.activity ω).cost i j s t) μ := by
  apply (A.pathCost_integrable p s t).mono' (A.measurable_cost i j s t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg ((A.activity ω).cost_nonneg i j s t)]
    exact (A.activity ω).cost_le_pathCost p s t

/-- Finitely many coordinates, with the discrete sigma algebra. -/
local instance componentMeasurableSpace : MeasurableSpace (Set (Fin n)) := ⊤

noncomputable def coordinateDifference (i j : Fin n) (s t : ℝ)
    (z : Ω × Set (Fin n)) : ℝ :=
  (A.activity z.1).vector i s z.2-(A.activity z.1).vector j t z.2

lemma measurable_coordinateDifference (i j : Fin n) (s t : ℝ) :
    Measurable (A.coordinateDifference i j s t) := by
  apply measurable_from_prod_countable_left
  intro S
  exact (A.measurable_vector i s S).sub (A.measurable_vector j t S)

lemma integrable_coordinateDifference {J : Set ℝ} {i j : Fin n}
    (p : M.Path J i j) (s t : ℝ) :
    Integrable (A.coordinateDifference i j s t) (μ.prod Measure.count) := by
  classical
  apply (integrable_prod_iff (A.measurable_coordinateDifference i j s t).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun ω =>
      memLp_one_iff_integrable.mp MemLp.of_discrete
  · have he : (fun ω => ∫ S, ‖A.coordinateDifference i j s t (ω,S)‖ ∂Measure.count) =
        (fun ω => (A.activity ω).cost i j s t) := by
      funext ω
      rw [integral_count]
      simp only [coordinateDifference,Real.norm_eq_abs,Activity.cost]
    rw [he]
    exact A.cost_integrable p s t

variable [SFinite μ]

/-- Subtracting the actual reference point makes the component assignment
integrable, even when the original label measure is infinite. -/
noncomputable def refinedMap {J : Set ℝ} {root : Fin n} (o x : M.Point J root) :
    Lp ℝ 1 (μ.prod (Measure.count : Measure (Set (Fin n)))) :=
  (A.integrable_coordinateDifference (Classical.choice (x.paths_nonempty o)) x.height o.height).toL1
    (A.coordinateDifference x.column o.column x.height o.height)

end SetSystem
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace Activity
variable {n : ℕ} {M : Model n}

/-- Pointwise membership movement; component labels are deliberately not moved. -/
noncomputable def movement (A B : Activity M) (i : Fin n) (H : ℝ) : ℝ :=
  |B.indicator i H-A.indicator i H|

end Activity
namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A B : SetSystem M Ω μ)

noncomputable def movement (i : Fin n) (H : ℝ) : ℝ :=
  ∫ ω, (A.activity ω).movement (B.activity ω) i H ∂μ

end SetSystem
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Rebase
open scoped NNReal

variable {K : ℝ≥0} {ψ : ℝ → ℝ}

lemma shear_strictMono (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) :
    StrictMono (fun H => H+ψ H) := by
  intro s t hst
  have h := hψ.dist_le_mul s t
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst.le)] at h
  have hb := (abs_le.mp h).2
  have hm : (1-(K:ℝ))*(t-s) > 0 := mul_pos (by linarith) (by linarith)
  nlinarith

lemma shear_surjective (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) :
    Function.Surjective (fun H => H+ψ H) := by
  intro t
  let T := (|ψ 0|+|t|+1)/(1-(K:ℝ))
  have hden : 0 < 1-(K:ℝ) := by linarith
  have hT : 0 < T := div_pos (by positivity) hden
  have he : T*(1-(K:ℝ)) = |ψ 0|+|t|+1 := div_mul_cancel₀ _ (ne_of_gt hden)
  have hr := hψ.dist_le_mul T 0
  have hl := hψ.dist_le_mul (-T) 0
  rw [Real.dist_eq,Real.dist_eq,sub_zero,abs_of_pos hT] at hr
  rw [Real.dist_eq,Real.dist_eq,sub_zero,abs_neg,abs_of_pos hT] at hl
  have hp : t ≤ T+ψ T := by
    have := (abs_le.mp hr).1
    nlinarith [le_abs_self t,neg_abs_le (ψ 0)]
  have hm : -T+ψ (-T) ≤ t := by
    have := (abs_le.mp hl).2
    nlinarith [neg_abs_le t,le_abs_self (ψ 0)]
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc (by linarith : -T ≤ T)
    (continuous_id.add hψ.continuous).continuousOn ⟨hm,hp⟩
  exact ⟨x,hx⟩

/-- The branch change of variable H ↦ H+ψ(H) is a genuine increasing
bijection on the WHOLE real line, not just on the current chart heights. -/
noncomputable def shear (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) : ℝ ≃o ℝ :=
  (shear_strictMono hK hψ).orderIsoOfSurjective _ (shear_surjective hK hψ)

@[simp] lemma shear_apply (hK : (K:ℝ) < 1) (hψ : LipschitzWith K ψ) (H : ℝ) :
    shear hK hψ H = H+ψ H := rfl

end PlanarL1.Rebase


namespace PlanarL1.Threshold
open MeasureTheory
open scoped ENNReal

noncomputable def half (a z : ℝ) : ℝ := if z < a then 1 else 0

lemma measurable_half (a : ℝ) : Measurable (half a) := by
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

lemma abs_sub_half_of_le {a b : ℝ} (hab : a ≤ b) (z : ℝ) :
    |half a z-half b z| = (Set.Ico a b).indicator (fun _ => (1:ℝ)) z := by
  by_cases ha : z < a
  · have hb : z < b := ha.trans_le hab
    simp [half,ha,hb,Set.mem_Ico,not_le.mpr ha]
  · by_cases hb : z < b
    · simp [half,ha,hb,Set.mem_Ico,le_of_not_gt ha]
    · simp [half,ha,hb,Set.mem_Ico]

lemma abs_sub_half (a b z : ℝ) :
    |half a z-half b z| = (Set.Ico (min a b) (max a b)).indicator (fun _ => (1:ℝ)) z := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h,max_eq_right h] using abs_sub_half_of_le h z
  · rw [abs_sub_comm]
    simpa only [min_eq_right h,max_eq_left h] using abs_sub_half_of_le h z

lemma integrable_abs_sub_half (a b : ℝ) :
    Integrable (fun z => |half a z-half b z|) volume := by
  simp only [abs_sub_half]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (measure_Ico_lt_top.ne))

lemma integrable_sub_half (a b : ℝ) : Integrable (fun z => half a z-half b z) volume := by
  apply (integrable_norm_iff ((measurable_half a).sub (measurable_half b)).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using integrable_abs_sub_half a b

lemma integral_abs_sub_half (a b : ℝ) :
    (∫ z, |half a z-half b z|) = |a-b| := by
  simp only [abs_sub_half,integral_indicator_const (1:ℝ) measurableSet_Ico,smul_eq_mul,mul_one]
  rw [Real.volume_real_Ico]
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h),max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h,max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h),max_eq_left (sub_nonneg.mpr h)]

/-- The elementary two-sign identity behind exact vertical control. -/
lemma two_sign_abs (a b : ℝ) : (|a+b|+|a-b|)/2 = max |a| |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha,abs_of_nonneg hb,abs_of_nonneg (add_nonneg ha hb)]
    rcases le_total a b with h | h
    · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  · rw [abs_of_nonneg ha,abs_of_nonpos hb,abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))]
    rcases le_total a (-b) with h | h
    · rw [max_eq_right h,abs_of_nonpos (by linarith : a+b ≤ 0)]; ring
    · rw [max_eq_left h,abs_of_nonneg (by linarith : 0 ≤ a+b)]; ring
  · rw [abs_of_nonpos ha,abs_of_nonneg hb,abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))]
    rcases le_total (-a) b with h | h
    · rw [max_eq_right h,abs_of_nonneg (by linarith : 0 ≤ a+b)]; ring
    · rw [max_eq_left h,abs_of_nonpos (by linarith : a+b ≤ 0)]; ring
  · rw [abs_of_nonpos ha,abs_of_nonpos hb,abs_of_nonpos (add_nonpos ha hb)]
    rcases le_total (-a) (-b) with h | h
    · rw [max_eq_right h,abs_of_nonneg (by linarith : 0 ≤ a-b)]; ring
    · rw [max_eq_left h,abs_of_nonpos (by linarith : a-b ≤ 0)]; ring

local instance signMeasurableSpace : MeasurableSpace Bool := ⊤

/-- Lebesgue times a fair sign; its total mass is infinite, as in the source. -/
noncomputable def labelMeasure : Measure (Bool × ℝ) :=
  (1/2 : ℝ≥0∞) • (Measure.count.prod (volume : Measure ℝ))

noncomputable def chartValue (h p : ℝ) (z : Bool × ℝ) : ℝ :=
  half (if z.1 then h+p else h-p) z.2

lemma measurable_chartValue (h p : ℝ) : Measurable (chartValue h p) := by
  apply measurable_from_prod_countable_right
  intro b
  change Measurable (half (if b then h+p else h-p))
  exact measurable_half _

lemma integrable_chart_difference_count (h p k q : ℝ) :
    Integrable (fun z => chartValue h p z-chartValue k q z)
      (Measure.count.prod volume) := by
  apply (integrable_prod_iff ((measurable_chartValue h p).sub
    (measurable_chartValue k q)).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun b => by
      change Integrable (fun z => half (if b then h+p else h-p) z-
        half (if b then k+q else k-q) z) volume
      exact integrable_sub_half _ _
  · exact memLp_one_iff_integrable.mp MemLp.of_discrete

lemma integrable_chart_difference (h p k q : ℝ) :
    Integrable (fun z => chartValue h p z-chartValue k q z) labelMeasure := by
  change Integrable _ ((1/2 : ℝ≥0∞) • (Measure.count.prod volume))
  exact (integrable_chart_difference_count h p k q).smul_measure (by norm_num)

lemma chart_distance (h p k q : ℝ) :
    (∫ z, |chartValue h p z-chartValue k q z| ∂labelMeasure) = max |h-k| |p-q| := by
  rw [labelMeasure,integral_smul_measure]
  have he : (∫ z : Bool × ℝ, |chartValue h p z-chartValue k q z| ∂Measure.count.prod volume) =
      |(h+p)-(k+q)|+|(h-p)-(k-q)| := by
    rw [integral_prod _ ((integrable_chart_difference_count h p k q).norm.congr
      (Filter.Eventually.of_forall fun _ => Real.norm_eq_abs _))]
    simp only [chartValue,integral_count]
    rw [Fintype.sum_bool]
    simp only [ite_true,Bool.false_eq_true,ite_false,integral_abs_sub_half]
  rw [he]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  rw [show h+p-(k+q) = (h-k)+(p-q) by ring,
    show h-p-(k-q) = (h-k)-(p-q) by ring]
  nlinarith [two_sign_abs (h-k) (p-q)]

lemma chart_vertical (h p k q : ℝ) (hv : |p-q| ≤ |h-k|) :
    (∫ z, |chartValue h p z-chartValue k q z| ∂labelMeasure) = |h-k| := by
  rw [chart_distance,max_eq_left hv]

noncomputable def rebase (ep em : ℝ ≃o ℝ) (z : Bool × ℝ) : ℝ :=
  (if z.1 then ep else em).symm z.2

lemma measurable_rebase (ep em : ℝ ≃o ℝ) : Measurable (rebase ep em) := by
  apply measurable_from_prod_countable_right
  intro b
  exact (if b then ep else em).symm.continuous.measurable

lemma rebase_preimage_Ioc (ep em : ℝ ≃o ℝ) (a b : ℝ) (σ : Bool) :
    Prod.mk σ ⁻¹' (rebase ep em ⁻¹' Set.Ioc a b) =
      Set.Ioc ((if σ then ep else em) a) ((if σ then ep else em) b) := by
  change (if σ then ep else em).symm ⁻¹' Set.Ioc a b = _
  rw [OrderIso.preimage_Ioc]
  rfl

/-- Rebasing is measure preserving AFTER averaging the old sign. It does not
claim that either conditional change of variable preserves Lebesgue measure. -/
lemma rebase_preserving (ep em : ℝ ≃o ℝ) (hmean : ∀ H, ep H+em H = 2*H) :
    MeasurePreserving (rebase ep em) labelMeasure volume := by
  refine ⟨measurable_rebase ep em, ?_⟩
  symm
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [Measure.map_apply (measurable_rebase ep em) measurableSet_Ioc,
    labelMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.prod_apply ((measurable_rebase ep em) measurableSet_Ioc)]
  simp_rw [rebase_preimage_Ioc,Real.volume_Ioc]
  rw [lintegral_count,tsum_fintype,Fintype.sum_bool]
  simp only [ite_true,Bool.false_eq_true,ite_false]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  have hp : 0 ≤ ep b-ep a := sub_nonneg.mpr (ep.monotone hab.le)
  have hm : 0 ≤ em b-em a := sub_nonneg.mpr (em.monotone hab.le)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,
    ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal hm]
  linarith [hmean a,hmean b]

/-- Exact set equality, not merely equality in distribution. -/
lemma rebase_membership (ep em : ℝ ≃o ℝ) (H : ℝ) (z : Bool × ℝ) :
    z.2 < (if z.1 then ep else em) H ↔ rebase ep em z < H := by
  exact (if z.1 then ep else em).symm_apply_lt.symm

end PlanarL1.Threshold


end

section

namespace PlanarL1.Threshold
open MeasureTheory
open scoped NNReal

lemma threshold_mono {K : ℝ≥0} (hK : (K:ℝ) ≤ 1) {P : ℝ → ℝ}
    (hP : LipschitzWith K P) (b : Bool) :
    Monotone (fun H => if b then H+P H else H-P H) := by
  intro s t hst
  have h := hP.dist_le_mul s t
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst)] at h
  have hm := mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr hst)
  have hp := abs_le.mp h
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith

variable {n : ℕ} {M : Columns.Model n} {K : ℝ≥0}

noncomputable def chartActivity (F : M.Field Set.univ K) (hK : (K:ℝ) ≤ 1)
    (z : Bool × ℝ) : Columns.Model.Activity M where
  active i H := z.2 < if z.1 then H+F.value i ⟨H,Set.mem_univ H⟩
      else H-F.value i ⟨H,Set.mem_univ H⟩
  increasing i s t hst ha := by
    apply ha.trans_le
    apply threshold_mono hK _ z.1 hst
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (F.vertical i).dist_le_mul ⟨x,Set.mem_univ x⟩ ⟨y,Set.mem_univ y⟩
  switch i j H hH := by rw [F.switch i j ⟨H,Set.mem_univ H⟩ hH]

lemma chartIndicator (F : M.Field Set.univ K) (hK : (K:ℝ) ≤ 1)
    (z : Bool × ℝ) (i : Fin n) (H : ℝ) :
    (chartActivity F hK z).indicator i H = chartValue H (F.value i ⟨H,Set.mem_univ H⟩) z := rfl

noncomputable def chartSystem (F : M.Field Set.univ K) (hK : (K:ℝ) ≤ 1) :
    Columns.Model.SetSystem M (Bool × ℝ) labelMeasure where
  activity := chartActivity F hK
  measurable_active i H := by
    change MeasurableSet {z : Bool × ℝ | z.2 < if z.1 then
      H+F.value i ⟨H,Set.mem_univ H⟩ else H-F.value i ⟨H,Set.mem_univ H⟩}
    apply measurableSet_lt measurable_snd
    exact Measurable.ite (measurableSet_singleton true |>.preimage measurable_fst)
      measurable_const measurable_const
  vertical_integrable i s t := by
    simp only [chartIndicator]
    exact (integrable_chart_difference _ _ _ _).norm
  vertical_bound i s t := by
    simp only [chartIndicator]
    have h := (F.vertical i).dist_le_mul ⟨s,Set.mem_univ s⟩ ⟨t,Set.mem_univ t⟩
    rw [Real.dist_eq,Subtype.dist_eq,Real.dist_eq] at h
    have hb := h.trans (by simpa using mul_le_mul_of_nonneg_right hK (abs_nonneg (s-t)))
    exact (chart_vertical _ _ _ _ hb).le

/-- Rebasing a genuine strict Lipschitz height branch, with no differentiability
assumption. The old sign is averaged; its conditional laws are not asserted
Lebesgue preserving. -/
noncomputable def branchRebase {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) : Bool × ℝ → ℝ :=
  rebase (Rebase.shear hK hψ) (Rebase.shear hK hψ.neg)

lemma branchRebase_preserving {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) : MeasurePreserving (branchRebase hK hψ) labelMeasure volume := by
  apply rebase_preserving
  intro H
  simp only [Rebase.shear_apply,Pi.neg_apply]
  ring

lemma branchRebase_membership {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (H : ℝ) (z : Bool × ℝ) :
    chartValue H (ψ H) z = half H (branchRebase hK hψ z) := by
  unfold chartValue half
  congr 1
  apply propext
  unfold branchRebase
  have h := rebase_membership (Rebase.shear hK hψ) (Rebase.shear hK hψ.neg) H z
  cases hb : z.1 <;> simpa only [hb,Bool.false_eq_true,ite_false,ite_true,
    Rebase.shear_apply,Pi.neg_apply,sub_eq_add_neg] using h

end PlanarL1.Threshold


end

section

namespace PlanarL1.Threshold
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def fair : Measure Bool := (1/2 : ℝ≥0∞) • Measure.count

instance fair_probability : IsProbabilityMeasure fair := by
  constructor
  norm_num [fair,Measure.smul_apply,smul_eq_mul,Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

lemma labelMeasure_eq : labelMeasure = fair.prod (volume : Measure ℝ) := by
  simp only [fair,Measure.prod_smul_left,labelMeasure]

/-- A chart's actual label variables, not hypothetical independent coordinates.
The preservation proof is exactly the joint Lebesgue/fair-sign invariant. -/
structure Variables (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  value : Ω → Bool × ℝ
  preserving : MeasurePreserving value μ labelMeasure

namespace Variables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def initial : Variables (Bool × ℝ) labelMeasure :=
  ⟨id,MeasurePreserving.id labelMeasure⟩

noncomputable def lift (Z : Variables Ω μ) : Variables (Ω × Bool) (μ.prod fair) where
  value z := Z.value z.1
  preserving := Z.preserving.comp (measurePreserving_fst (μ := μ) (ν := fair))

noncomputable def rebase {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (Z : Variables Ω μ) [SFinite μ] :
    Variables (Ω × Bool) (μ.prod fair) where
  value z := (z.2,branchRebase hK hψ (Z.value z.1))
  preserving := by
    have hZ := (branchRebase_preserving hK hψ).comp Z.preserving
    have hp := hZ.prod (MeasurePreserving.id fair)
    have hs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := fair)).comp hp
    convert hs using 1
    · funext z
      rfl
    · exact labelMeasure_eq

lemma rebase_membership {K : ℝ≥0} (hK : (K:ℝ) < 1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (Z : Variables Ω μ) [SFinite μ] (H : ℝ) (z : Ω × Bool) :
    chartValue H (ψ H) ((Z.lift).value z) =
      chartValue H 0 ((Z.rebase hK hψ).value z) := by
  change chartValue H (ψ H) (Z.value z.1) = _
  rw [branchRebase_membership hK hψ H (Z.value z.1)]
  change half H (branchRebase hK hψ (Z.value z.1)) =
    half (if z.2 then H+0 else H-0) (branchRebase hK hψ (Z.value z.1))
  simp

lemma integrable_difference (Z : Variables Ω μ) (h p k q : ℝ) :
    Integrable (fun z => chartValue h p (Z.value z)-chartValue k q (Z.value z)) μ := by
  exact Z.preserving.integrable_comp_of_integrable
    (integrable_chart_difference h p k q)

lemma distance (Z : Variables Ω μ) (h p k q : ℝ) :
    (∫ z, |chartValue h p (Z.value z)-chartValue k q (Z.value z)| ∂μ) =
      max |h-k| |p-q| := by
  rw [← chart_distance h p k q]
  rw [← Z.preserving.map_eq]
  exact (integral_map_of_stronglyMeasurable Z.preserving.measurable
    (((measurable_chartValue h p).sub (measurable_chartValue k q)).norm.stronglyMeasurable)).symm

end Variables
end PlanarL1.Threshold



end

section

namespace PlanarL1.Threshold
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def active (Z : Variables Ω μ) (H P : ℝ) (ω : Ω) : Prop :=
  (Z.value ω).2 < if (Z.value ω).1 then H+P else H-P

lemma active_indicator (Z : Variables Ω μ) (H P : ℝ) (ω : Ω) :
    (if active Z H P ω then (1:ℝ) else 0) = chartValue H P (Z.value ω) := rfl

lemma measurable_active (Z : Variables Ω μ) (H P : ℝ) :
    MeasurableSet {ω | active Z H P ω} := by
  apply measurableSet_lt (measurable_snd.comp Z.preserving.measurable)
  exact Measurable.ite ((measurableSet_singleton true).preimage
    (measurable_fst.comp Z.preserving.measurable)) measurable_const measurable_const

lemma active_increasing (Z : Variables Ω μ) {S : Set ℝ} {P : ℝ → ℝ}
    (hP : LipschitzOnWith 1 P S) (ω : Ω) : MonotoneOn (fun H => active Z H (P H) ω) S := by
  intro s hs t ht hst ha
  have hb := hP.dist_le_mul s hs t ht
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst),NNReal.coe_one,one_mul] at hb
  have hp := abs_le.mp hb
  unfold active at ha ⊢
  apply ha.trans_le
  cases h : (Z.value ω).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith

end PlanarL1.Threshold

end

section

namespace PlanarL1.Threshold.Variables
open MeasureTheory
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma active_rebase [SFinite μ] {K : ℝ≥0} (hK : (K:ℝ)<1) {ψ : ℝ → ℝ}
    (hψ : LipschitzWith K ψ) (Z : Variables Ω μ) (H : ℝ) (ω : Ω × Bool) :
    active Z.lift H (ψ H) ω ↔ active (Z.rebase hK hψ) H 0 ω := by
  classical
  have he := Z.rebase_membership hK hψ H ω
  change (if active Z.lift H (ψ H) ω then (1:ℝ) else 0) =
    (if active (Z.rebase hK hψ) H 0 ω then 1 else 0) at he
  by_cases hp : active Z.lift H (ψ H) ω <;>
    by_cases hq : active (Z.rebase hK hψ) H 0 ω <;> simp_all
end PlanarL1.Threshold.Variables


end

section

namespace PlanarL1.Threshold
open MeasureTheory
attribute [local instance] Classical.propDecidable

lemma half_mono {a b : ℝ} (h : a ≤ b) (z : ℝ) : half a z ≤ half b z := by
  by_cases hz : z < a
  · simp [half,hz,hz.trans_le h]
  · simp only [half,ite_eq_right hz]
    split_ifs <;> norm_num

lemma integral_sub_half (a b : ℝ) : (∫ z, half a z-half b z) = a-b := by
  rcases le_total a b with h | h
  · have he : (fun z => half a z-half b z) = fun z => -|half a z-half b z| := by
      funext z
      rw [abs_of_nonpos (sub_nonpos.mpr (half_mono h z)),neg_neg]
    rw [he,integral_neg,integral_abs_sub_half,abs_of_nonpos (sub_nonpos.mpr h),neg_neg]
  · have he : (fun z => half a z-half b z) = fun z => |half a z-half b z| := by
      funext z
      rw [abs_of_nonneg (sub_nonneg.mpr (half_mono h z))]
    rw [he,integral_abs_sub_half,abs_of_nonneg (sub_nonneg.mpr h)]

lemma integral_chart_difference (h p k q : ℝ) :
    (∫ z, chartValue h p z-chartValue k q z ∂labelMeasure) = h-k := by
  rw [labelMeasure,integral_smul_measure]
  have he : (∫ z : Bool × ℝ, chartValue h p z-chartValue k q z ∂Measure.count.prod volume) =
      ((h+p)-(k+q))+((h-p)-(k-q)) := by
    rw [integral_prod _ (integrable_chart_difference_count h p k q)]
    simp only [chartValue,integral_count]
    rw [Fintype.sum_bool]
    simp only [ite_true,Bool.false_eq_true,ite_false,integral_sub_half]
  rw [he]
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  ring

namespace Variables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma integral_difference (Z : Variables Ω μ) (h p k q : ℝ) :
    (∫ z, chartValue h p (Z.value z)-chartValue k q (Z.value z) ∂μ) = h-k := by
  rw [← integral_chart_difference h p k q,← Z.preserving.map_eq]
  exact (integral_map_of_stronglyMeasurable Z.preserving.measurable
    (((measurable_chartValue h p).sub (measurable_chartValue k q)).stronglyMeasurable)).symm
end Variables
end PlanarL1.Threshold


end

section

namespace PlanarL1.Threshold
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma threshold_compare (Z : Variables Ω μ) {s t p q : ℝ}
    (h : |p-q| ≤ t-s) (ω : Ω) : active Z s p ω → active Z t q ω := by
  intro hs
  apply hs.trans_le
  have hd := abs_le.mp h
  cases (Z.value ω).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith

/-- A genuine gluing lemma for regions with arbitrarily complicated boundaries.
Small distance-tapered changes preserve nesting even though the identifiers
may have infinitely many changes along a column. All fields below already
include κ. No regularity of the name function is assumed. -/
lemma named_nested (name : ℝ → ι) (Z : ι → Variables Ω μ)
    (old newer : ℝ → ℝ) (A : ℝ → Ω → Prop)
    (hA : ∀ ω, Monotone (fun H => A H ω))
    (hrep : ∀ H ω, A H ω ↔ active (Z (name H)) H (old H) ω)
    (hold : ∀ s t, name s=name t → |old s-old t| ≤ |s-t|/2)
    (hnew : ∀ s t, name s=name t → |newer s-newer t| ≤ |s-t|)
    (hd : ∀ s t, name s≠name t → |newer s-old s| ≤ |s-t|/8)
    (ω : Ω) : Monotone (fun H => active (Z (name H)) H (newer H) ω) := by
  intro s t hst hs
  by_cases he : name s=name t
  · have hb := hnew s t he
    rw [abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] at hb
    rw [← he]
    exact threshold_compare (Z (name s)) hb ω hs
  let ds := |newer s-old s|
  let dt := |newer t-old t|
  have hds : 0 ≤ ds := abs_nonneg _
  have hdt : 0 ≤ dt := abs_nonneg _
  have hsbound : ds ≤ (t-s)/8 := by
    simpa only [ds,abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] using hd s t he
  have htbound : dt ≤ (t-s)/8 := by
    simpa only [dt,abs_of_nonneg (sub_nonneg.mpr hst)] using hd t s (Ne.symm he)
  let u := s+2*ds
  let v := t-2*dt
  have hsu : s ≤ u := by dsimp [u]; linarith
  have hvt : v ≤ t := by dsimp [v]; linarith
  have huv : u ≤ v := by dsimp [u,v]; linarith
  have hnameu : name s=name u := by
    by_contra hno
    have hb := hd s u hno
    rw [abs_of_nonpos (sub_nonpos.mpr hsu),neg_sub] at hb
    change ds ≤ (u-s)/8 at hb
    have hz : ds=0 := by dsimp [u] at hb; linarith
    have hu : u=s := by simp [u,hz]
    exact hno (congrArg name hu.symm)
  have hnamev : name v=name t := by
    by_contra hno
    have hb := hd t v (Ne.symm hno)
    rw [abs_of_nonneg (sub_nonneg.mpr hvt)] at hb
    change dt ≤ (t-v)/8 at hb
    have hz : dt=0 := by dsimp [v] at hb; linarith
    have hv : v=t := by simp [v,hz]
    exact hno (congrArg name hv)
  have hu : A u ω := by
    rw [hrep,← hnameu]
    apply threshold_compare (Z (name s)) (ω := ω) _ hs
    calc
      |newer s-old u| ≤ |newer s-old s|+|old s-old u| := abs_sub_le _ _ _
      _ ≤ ds+|s-u|/2 := add_le_add le_rfl (hold s u hnameu)
      _ = u-s := by rw [abs_of_nonpos (sub_nonpos.mpr hsu),neg_sub]; dsimp [u]; ring
  have hv : A v ω := hA ω huv hu
  rw [hrep,hnamev] at hv
  apply threshold_compare (Z (name t)) (ω := ω) _ hv
  calc
    |old v-newer t| ≤ |old v-old t|+|old t-newer t| := abs_sub_le _ _ _
    _ ≤ |v-t|/2+dt := by
      simpa only [dt,abs_sub_comm (old t)] using add_le_add (hold v t hnamev) (le_rfl : |old t-newer t| ≤ |old t-newer t|)
    _ = t-v := by rw [abs_of_nonpos (sub_nonpos.mpr hvt),neg_sub]; dsimp [v]; ring

end PlanarL1.Threshold



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Gluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Gluing
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

lemma frontier_between_right {S : Set ℝ} (hS : IsClosed S) {x y : ℝ}
    (hxy : x ≤ y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ z ∈ frontier S, x ≤ z ∧ z ≤ y := by
  have hc : IsCompact (Icc x y ∩ S) := isCompact_Icc.inter_right hS
  obtain ⟨z,hz,hmax⟩ := hc.exists_isGreatest ⟨x,⟨⟨le_rfl,hxy⟩,hx⟩⟩
  refine ⟨z,?_,hz.1⟩
  rw [frontier,mem_sdiff,hS.closure_eq]
  refine ⟨hz.2,?_⟩
  intro hzi
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzi
  have hzy : z < y := lt_of_le_of_ne hz.1.2 (fun h => hy (h ▸ hz.2))
  let t := z + min ε (y-z)/2
  have ht1 : z < t := by dsimp [t]; have := lt_min hε (sub_pos.mpr hzy); linarith
  have ht2 : t ≤ y := by dsimp [t]; have := min_le_right ε (y-z); linarith
  have htd : dist t z < ε := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr ht1)]
    dsimp [t]
    have := min_le_left ε (y-z)
    linarith
  have htS := interior_subset (hball htd)
  exact (not_le.mpr ht1) (hmax ⟨⟨hz.1.1.trans ht1.le,ht2⟩,htS⟩)

lemma frontier_between_left {S : Set ℝ} (hS : IsClosed S) {x y : ℝ}
    (hxy : x ≤ y) (hx : x ∉ S) (hy : y ∈ S) :
    ∃ z ∈ frontier S, x ≤ z ∧ z ≤ y := by
  have hc : IsCompact (Icc x y ∩ S) := isCompact_Icc.inter_right hS
  obtain ⟨z,hz,hmin⟩ := hc.exists_isLeast ⟨y,⟨⟨hxy,le_rfl⟩,hy⟩⟩
  refine ⟨z,?_,hz.1⟩
  rw [frontier,mem_sdiff,hS.closure_eq]
  refine ⟨hz.2,?_⟩
  intro hzi
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzi
  have hxz : x < z := lt_of_le_of_ne hz.1.1 (fun h => hx (h.symm ▸ hz.2))
  let t := z - min ε (z-x)/2
  have ht1 : t < z := by dsimp [t]; have := lt_min hε (sub_pos.mpr hxz); linarith
  have ht2 : x ≤ t := by dsimp [t]; have := min_le_right ε (z-x); linarith
  have htd : dist t z < ε := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr ht1)]
    dsimp [t]
    have := min_le_left ε (z-x)
    linarith
  have htS := interior_subset (hball htd)
  exact (not_le.mpr ht1) (hmin ⟨⟨ht2,ht1.le.trans hz.1.2⟩,htS⟩)

lemma monotone_piecewise {S : Set ℝ} (hS : IsClosed S)
    {β : Type*} [Preorder β] {f g : ℝ → β}
    (hf : Monotone f) (hg : MonotoneOn g S) (he : EqOn g f (frontier S)) :
    Monotone (S.piecewise g f) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy] using hg hx hy hxy
  · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_right hS hxy hx hy
    have hzS : z ∈ S := hS.frontier_subset hz
    have h : g x ≤ f y := (hg hx hzS hxz).trans (by rw [he hz]; exact hf hzy)
    simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy] using h
  · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_left hS hxy hx hy
    have hzS : z ∈ S := hS.frontier_subset hz
    have h : f x ≤ g y := (hf hxz).trans (by rw [← he hz]; exact hg hzS hy hzy)
    simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy] using h
  · simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy] using hf hxy

lemma lipschitz_piecewise {S : Set ℝ} (hS : IsClosed S)
    {β : Type*} [PseudoMetricSpace β] {f g : ℝ → β} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzOnWith K g S)
    (he : EqOn g f (frontier S)) : LipschitzWith K (S.piecewise g f) := by
  classical
  have hb (x y : ℝ) (hxy : x ≤ y) :
      dist (S.piecewise g f x) (S.piecewise g f y) ≤ K * (y-x) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy,
        Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hg.dist_le_mul x hx y hy
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_right hS hxy hx hy
      have hzS : z ∈ S := hS.frontier_subset hz
      have h1 := hg.dist_le_mul x hx z hzS
      have h2 := hf.dist_le_mul z y
      rw [he hz] at h1
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      have h3 := dist_triangle (g x) (f z) (f y)
      simp only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy]
      nlinarith
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_left hS hxy hx hy
      have hzS : z ∈ S := hS.frontier_subset hz
      have h1 := hf.dist_le_mul x z
      have h2 := hg.dist_le_mul z hzS y hy
      rw [he hz] at h2
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      have h3 := dist_triangle (f x) (f z) (g y)
      simp only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy]
      nlinarith
    · simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy,
        Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hf.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain hxy | hyx := le_total x y
  · simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hb x y hxy
  · simpa only [dist_comm (S.piecewise g f y),Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx)] using hb y x hyx

end PlanarL1.Gluing



end

section

namespace PlanarL1.Gluing
open MeasureTheory Set
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The upper-bound invariant on a set of heights, stated on differences
because individual half-line indicators need not be integrable. -/
def VerticalBound (μ : Measure Ω) (f : ℝ → Ω → ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, Integrable (fun ω => f s ω-f t ω) μ ∧
    (∫ ω, |f s ω-f t ω| ∂μ) ≤ |s-t|

lemma difference_triangle {f g h : Ω → ℝ}
    (hf : Integrable (fun ω => f ω-g ω) μ)
    (hg : Integrable (fun ω => g ω-h ω) μ) :
    Integrable (fun ω => f ω-h ω) μ ∧
      (∫ ω, |f ω-h ω| ∂μ) ≤ (∫ ω, |f ω-g ω| ∂μ)+(∫ ω, |g ω-h ω| ∂μ) := by
  have hadd : Integrable (fun ω => (f ω-g ω)+(g ω-h ω)) μ := hf.add hg
  have hi : Integrable (fun ω => f ω-h ω) μ := by
    simpa only [sub_add_sub_cancel] using hadd
  have hfn : Integrable (fun ω => |f ω-g ω|) μ := hf.norm
  have hgn : Integrable (fun ω => |g ω-h ω|) μ := hg.norm
  have hin : Integrable (fun ω => |f ω-h ω|) μ := hi.norm
  have hsum : Integrable (fun ω => |f ω-g ω|+|g ω-h ω|) μ := hfn.add hgn
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, |f ω-g ω|+|g ω-h ω| ∂μ := by
      exact integral_mono hin hsum (fun ω => abs_sub_le _ _ _)
    _ = _ := integral_add hfn hgn

lemma verticalBound_piecewise {S : Set ℝ} (hS : IsClosed S)
    {f g : ℝ → Ω → ℝ} (hf : VerticalBound μ f univ)
    (hg : VerticalBound μ g S) (he : EqOn g f (frontier S)) :
    VerticalBound μ (S.piecewise g f) univ := by
  classical
  have hb (x y : ℝ) (hxy : x ≤ y) :
      Integrable (fun ω => S.piecewise g f x ω-S.piecewise g f y ω) μ ∧
      (∫ ω, |S.piecewise g f x ω-S.piecewise g f y ω| ∂μ) ≤ y-x := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy,
        abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hg x hx y hy
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_right hS hxy hx hy
      have hgz := hg x hx z (hS.frontier_subset hz)
      have hfz := hf z (mem_univ z) y (mem_univ y)
      rw [he hz] at hgz
      obtain ⟨hi,hb⟩ := difference_triangle hgz.1 hfz.1
      simp only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy]
      refine ⟨hi,?_⟩
      have h1 := hgz.2
      have h2 := hfz.2
      rw [abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      linarith
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_left hS hxy hx hy
      have hfz := hf x (mem_univ x) z (mem_univ z)
      have hgz := hg z (hS.frontier_subset hz) y hy
      rw [he hz] at hgz
      obtain ⟨hi,hb⟩ := difference_triangle hfz.1 hgz.1
      simp only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy]
      refine ⟨hi,?_⟩
      have h1 := hfz.2
      have h2 := hgz.2
      rw [abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      linarith
    · simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy,
        abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hf x (mem_univ x) y (mem_univ y)
  intro x _ y _
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hb x y hxy
  · obtain ⟨hi,hb⟩ := hb y x hyx
    constructor
    · have hn : Integrable (fun ω => -(S.piecewise g f y ω-S.piecewise g f x ω)) μ := hi.neg
      simpa only [neg_sub] using hn
    · simpa only [abs_sub_comm (S.piecewise g f x _),abs_of_nonneg (sub_nonneg.mpr hyx)] using hb

end PlanarL1.Gluing

namespace PlanarL1.Columns.Model
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Local update data on closed full-column pieces. Cross-domain switches
must be unchanged, as ensured by the strict frontier margins in the source. -/
structure SetPatch (A : SetSystem M Ω μ) where
  domain : Fin n → Set ℝ
  closed : ∀ i, IsClosed (domain i)
  active : Ω → Fin n → ℝ → Prop
  measurable_active : ∀ i H, MeasurableSet {ω | active ω i H}
  increasing : ∀ ω i, MonotoneOn (active ω i) (domain i)
  boundary : ∀ ω i H, H ∈ frontier (domain i) →
    (active ω i H ↔ (A.activity ω).active i H)
  switch_inside : ∀ ω i j H, H ∈ M.heights i j → H ∈ domain i → H ∈ domain j →
    (active ω i H ↔ active ω j H)
  switch_outside : ∀ ω i j H, H ∈ M.heights i j → H ∈ domain i → H ∉ domain j →
    (active ω i H ↔ (A.activity ω).active i H)
  vertical : ∀ i, Gluing.VerticalBound μ (fun H ω => if active ω i H then 1 else 0) (domain i)

namespace SetPatch
variable {A : SetSystem M Ω μ} (P : SetPatch A)

noncomputable def patchedActivity (ω : Ω) : Activity M where
  active i H := if H ∈ P.domain i then P.active ω i H else (A.activity ω).active i H
  increasing i s t hst := by
    have hf : Monotone ((A.activity ω).active i) := by
      intro s t hst
      exact (A.activity ω).increasing i s t hst
    have hm := Gluing.monotone_piecewise (P.closed i)
      hf (P.increasing ω i)
      (fun H hH => propext (P.boundary ω i H hH))
    exact hm hst
  switch i j H hs := by
    by_cases hi : H ∈ P.domain i <;> by_cases hj : H ∈ P.domain j
    · simpa only [ite_eq_left hi,ite_eq_left hj] using P.switch_inside ω i j H hs hi hj
    · simpa only [ite_eq_left hi,ite_eq_right hj] using
        (P.switch_outside ω i j H hs hi hj).trans ((A.activity ω).switch i j H hs)
    · have hs' : H ∈ M.heights j i := by rwa [M.symm]
      simpa only [ite_eq_right hi,ite_eq_left hj] using
        ((A.activity ω).switch i j H hs).trans (P.switch_outside ω j i H hs' hj hi).symm
    · simpa only [ite_eq_right hi,ite_eq_right hj] using (A.activity ω).switch i j H hs

lemma indicator_eq (ω : Ω) (i : Fin n) (H : ℝ) :
    (P.patchedActivity ω).indicator i H =
      (P.domain i).piecewise (fun H ω => if P.active ω i H then (1:ℝ) else 0)
        (fun H ω => (A.activity ω).indicator i H) H ω := by
  unfold patchedActivity Activity.indicator
  by_cases h : H ∈ P.domain i <;> simp [h,Set.piecewise]

lemma verticalBound (i : Fin n) : Gluing.VerticalBound μ
    (fun H ω => (P.patchedActivity ω).indicator i H) univ := by
  have hf : Gluing.VerticalBound μ (fun H ω => (A.activity ω).indicator i H) univ := by
    intro s _ t _
    constructor
    · apply (integrable_norm_iff ((A.measurable_indicator i s).sub
        (A.measurable_indicator i t)).aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using A.vertical_integrable i s t
    · exact A.vertical_bound i s t
  have he : EqOn (fun H ω => if P.active ω i H then (1:ℝ) else 0)
      (fun H ω => (A.activity ω).indicator i H) (frontier (P.domain i)) := by
    intro H hH
    ext ω
    simp only [Activity.indicator,P.boundary ω i H hH]
  have hb := Gluing.verticalBound_piecewise (P.closed i) hf (P.vertical i) he
  simpa only [indicator_eq] using hb

noncomputable def apply : SetSystem M Ω μ where
  activity := P.patchedActivity
  measurable_active i H := by
    by_cases h : H ∈ P.domain i
    · simpa only [patchedActivity,ite_eq_left h] using P.measurable_active i H
    · simpa only [patchedActivity,ite_eq_right h] using A.measurable_active i H
  vertical_integrable i s t := by
    exact (P.verticalBound i s (mem_univ s) t (mem_univ t)).1.norm
  vertical_bound i s t := (P.verticalBound i s (mem_univ s) t (mem_univ t)).2

lemma unchanged {i : Fin n} {H : ℝ} (h : H ∉ P.domain i) (ω : Ω) :
    (P.apply.activity ω).active i H ↔ (A.activity ω).active i H := by
  simp only [apply,patchedActivity,ite_eq_right h]

lemma inside {i : Fin n} {H : ℝ} (h : H ∈ P.domain i) (ω : Ω) :
    (P.apply.activity ω).active i H ↔ P.active ω i H := by
  simp only [apply,patchedActivity,ite_eq_left h]

end SetPatch
end PlanarL1.Columns.Model

namespace PlanarL1.Threshold
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma active_verticalBound (Z : Variables Ω μ) {S : Set ℝ} {P : ℝ → ℝ}
    (hP : LipschitzOnWith 1 P S) : Gluing.VerticalBound μ
      (fun H ω => if active Z H (P H) ω then (1:ℝ) else 0) S := by
  intro s hs t ht
  simp only [active_indicator]
  refine ⟨Z.integrable_difference s (P s) t (P t),?_⟩
  rw [Z.distance]
  have h := hP.dist_le_mul s hs t ht
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul] at h
  exact max_le le_rfl h

/-- A literal common-label scalar chart replacement yields local patch data.
P already contains the source κ and comparison-orientation factors. -/
noncomputable def chartPatch {n : ℕ} {M : Columns.Model n}
    (A : M.SetSystem Ω μ) (Z : Variables Ω μ) (D : Fin n → Set ℝ)
    (hD : ∀ i, IsClosed (D i)) (P : Fin n → ℝ → ℝ)
    (hP : ∀ i, LipschitzOnWith 1 (P i) (D i))
    (hb : ∀ ω i H, H ∈ frontier (D i) →
      (active Z H (P i H) ω ↔ (A.activity ω).active i H))
    (hs : ∀ i j H, H ∈ M.heights i j → H ∈ D i → H ∈ D j → P i H = P j H)
    (hc : ∀ ω i j H, H ∈ M.heights i j → H ∈ D i → H ∉ D j →
      (active Z H (P i H) ω ↔ (A.activity ω).active i H)) : Columns.Model.SetPatch A where
  domain := D
  closed := hD
  active ω i H := active Z H (P i H) ω
  measurable_active i H := measurable_active Z H (P i H)
  increasing ω i := active_increasing Z (hP i) ω
  boundary := hb
  switch_inside ω i j H hij hi hj := by rw [hs i j H hij hi hj]
  switch_outside := hc
  vertical i := active_verticalBound Z (hP i)

end PlanarL1.Threshold


end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma Activity.indicator_mono (A : Activity M) (i : Fin n) : Monotone (A.indicator i) := by
  intro s t hst
  by_cases hs : A.active i s
  · simp only [Activity.indicator,ite_eq_left hs,ite_eq_left (A.increasing i s t hst hs),le_refl]
  · simp only [Activity.indicator,ite_eq_right hs]
    split_ifs <;> norm_num

/-- Balanced changes of one-point marginals preserve the exact vertical bound
once genuine nestedness has been established. This avoids an unjustified
finite-boundary assumption on chart regions. -/
noncomputable def SetSystem.balancedUpdate (S : SetSystem M Ω μ) (A : Ω → Activity M)
    (hm : ∀ i H, MeasurableSet {ω | (A ω).active i H})
    (hi : ∀ i H, Integrable (fun ω => (A ω).indicator i H-(S.activity ω).indicator i H) μ)
    (hz : ∀ i H, (∫ ω, (A ω).indicator i H-(S.activity ω).indicator i H ∂μ)=0) :
    SetSystem M Ω μ := by
  have hoi (i : Fin n) (s t : ℝ) :
      Integrable (fun ω => (S.activity ω).indicator i s-(S.activity ω).indicator i t) μ := by
    apply (integrable_norm_iff ((S.measurable_indicator i s).sub
      (S.measurable_indicator i t)).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using S.vertical_integrable i s t
  have hnew (i : Fin n) (s t : ℝ) :
      Integrable (fun ω => (A ω).indicator i s-(A ω).indicator i t) μ ∧
      (∫ ω, (A ω).indicator i s-(A ω).indicator i t ∂μ)=
        ∫ ω, (S.activity ω).indicator i s-(S.activity ω).indicator i t ∂μ := by
    have he : (fun ω => (A ω).indicator i s-(A ω).indicator i t) = fun ω =>
        ((A ω).indicator i s-(S.activity ω).indicator i s)+
        ((S.activity ω).indicator i s-(S.activity ω).indicator i t)-
        ((A ω).indicator i t-(S.activity ω).indicator i t) := by funext ω; ring
    rw [he]
    constructor
    · exact ((hi i s).add (hoi i s t)).sub (hi i t)
    · have hsum : Integrable (fun ω =>
          ((A ω).indicator i s-(S.activity ω).indicator i s)+
          ((S.activity ω).indicator i s-(S.activity ω).indicator i t)) μ :=
        (hi i s).add (hoi i s t)
      rw [integral_sub hsum (hi i t),
        integral_add (hi i s) (hoi i s t),hz i s,hz i t,zero_add,sub_zero]
  have habs (i : Fin n) (s t : ℝ) :
      (∫ ω, |(A ω).indicator i s-(A ω).indicator i t| ∂μ)=
        ∫ ω, |(S.activity ω).indicator i s-(S.activity ω).indicator i t| ∂μ := by
    rcases le_total t s with h | h
    · simp only [abs_of_nonneg (sub_nonneg.mpr ((A _).indicator_mono i h)),
        abs_of_nonneg (sub_nonneg.mpr ((S.activity _).indicator_mono i h))]
      exact (hnew i s t).2
    · simp only [abs_of_nonpos (sub_nonpos.mpr ((A _).indicator_mono i h)),
        abs_of_nonpos (sub_nonpos.mpr ((S.activity _).indicator_mono i h)),integral_neg]
      rw [(hnew i s t).2]
  exact {
    activity := A
    measurable_active := hm
    vertical_integrable := fun i s t => (hnew i s t).1.norm
    vertical_bound := fun i s t => (habs i s t).trans_le (S.vertical_bound i s t)
  }
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model.SetPatch
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {A : SetSystem M Ω μ}

/-- A patch can be installed after other patches which have not changed its
closed domain. Its actual activity and all clipping data are retained. -/
def rebase (P : SetPatch A) (B : SetSystem M Ω μ)
    (hB : ∀ ω i H, H ∈ P.domain i → ((B.activity ω).active i H ↔ (A.activity ω).active i H)) :
    SetPatch B where
  domain := P.domain
  closed := P.closed
  active := P.active
  measurable_active := P.measurable_active
  increasing := P.increasing
  boundary ω i H hH := (P.boundary ω i H hH).trans
    (hB ω i H ((P.closed i).frontier_subset hH)).symm
  switch_inside := P.switch_inside
  switch_outside ω i j H hs hi hj := (P.switch_outside ω i j H hs hi hj).trans (hB ω i H hi).symm
  vertical := P.vertical

def UnchangedOverlap (P Q : SetPatch A) : Prop :=
  ∀ ω i H, H ∈ P.domain i → H ∈ Q.domain i →
    (P.active ω i H ↔ (A.activity ω).active i H) ∧
      (Q.active ω i H ↔ (A.activity ω).active i H)

/-- The deterministic tie rule chooses the first closed cell containing a
point. On all main-cell overlaps every proposal is the original activity. -/
noncomputable def selectActive : List (SetPatch A) → Ω → Fin n → ℝ → Prop
  | [],ω,i,H => (A.activity ω).active i H
  | P::L,ω,i,H => if H ∈ P.domain i then P.active ω i H else selectActive L ω i H

lemma selectActive_old (L : List (SetPatch A)) (ω : Ω) (i : Fin n) (H : ℝ)
    (h : ∀ P ∈ L, H ∈ P.domain i → (P.active ω i H ↔ (A.activity ω).active i H)) :
    selectActive L ω i H ↔ (A.activity ω).active i H := by
  induction L with
  | nil => rfl
  | cons P L ih =>
    dsimp only [selectActive]
    split_ifs with hi
    · exact h P (List.mem_cons_self) hi
    · exact ih (fun Q hQ => h Q (List.mem_cons_of_mem P hQ))

lemma exists_batch (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap) :
    ∃ B : SetSystem M Ω μ, ∀ ω i H, (B.activity ω).active i H ↔ selectActive L ω i H := by
  induction L with
  | nil => exact ⟨A,fun _ _ _ => Iff.rfl⟩
  | cons P L ih =>
    obtain ⟨hPL,hL⟩ := List.pairwise_cons.mp hL
    obtain ⟨B,hB⟩ := ih hL
    have hB0 (ω i H) (hi : H ∈ P.domain i) :
        (B.activity ω).active i H ↔ (A.activity ω).active i H := by
      rw [hB]
      exact selectActive_old L ω i H (fun Q hQ hj => (hPL Q hQ ω i H hi hj).2)
    refine ⟨(P.rebase B hB0).apply,?_⟩
    intro ω i H
    by_cases hi : H ∈ P.domain i
    · exact ((P.rebase B hB0).inside hi ω).trans (by simp only [selectActive,ite_eq_left hi,rebase])
    · exact ((P.rebase B hB0).unchanged hi ω).trans (by simpa only [selectActive,ite_eq_right hi] using hB ω i H)

noncomputable def batch (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap) : SetSystem M Ω μ :=
  (exists_batch L hL).choose

lemma batch_active (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap) (ω i H) :
    ((batch L hL).activity ω).active i H ↔ selectActive L ω i H :=
  (exists_batch L hL).choose_spec ω i H

end PlanarL1.Columns.Model.SetPatch


namespace PlanarL1.Columns.Model.SetPatch
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {A : SetSystem M Ω μ}

lemma selectActive_inside (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    {P : SetPatch A} (hP : P ∈ L) (ω i H) (hi : H ∈ P.domain i) :
    selectActive L ω i H ↔ P.active ω i H := by
  induction L with
  | nil => simp only [List.not_mem_nil] at hP
  | cons Q L ih =>
    obtain ⟨hQL,hL⟩ := List.pairwise_cons.mp hL
    rcases List.mem_cons.mp hP with hP | hP
    · subst P
      simp only [selectActive,ite_eq_left hi]
    · by_cases hj : H ∈ Q.domain i
      · simp only [selectActive,ite_eq_left hj]
        exact (hQL P hP ω i H hj hi).1.trans (hQL P hP ω i H hj hi).2.symm
      · simpa only [selectActive,ite_eq_right hj] using ih hL hP

lemma batch_inside (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    {P : SetPatch A} (hP : P ∈ L) (ω i H) (hi : H ∈ P.domain i) :
    ((batch L hL).activity ω).active i H ↔ (P.apply.activity ω).active i H :=
  (batch_active L hL ω i H).trans ((selectActive_inside L hL hP ω i H hi).trans
    (P.inside hi ω).symm)

lemma batch_old (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    (ω i H) (hp : ∀ P ∈ L, (P.apply.activity ω).active i H ↔ (A.activity ω).active i H) :
    ((batch L hL).activity ω).active i H ↔ (A.activity ω).active i H := by
  apply (batch_active L hL ω i H).trans
  exact selectActive_old L ω i H (fun P hP hi => (P.inside hi ω).symm.trans (hp P hP))
end PlanarL1.Columns.Model.SetPatch


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Increments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Increment
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

noncomputable def clamp (a b t : ℝ) : ℝ := min b (max a t)

lemma clamp_bounds {a b t : ℝ} (hab : a ≤ b) : a ≤ clamp a b t ∧ clamp a b t ≤ b :=
  ⟨le_min hab (le_max_left _ _),min_le_left _ _⟩

lemma clamp_lipschitz (a b : ℝ) : LipschitzWith 1 (clamp a b) :=
  (LipschitzWith.id.const_max a).const_min b

lemma clamp_eq {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) : clamp a b t = t := by
  rw [clamp,max_eq_right hat,min_eq_right htb]

lemma clamp_left {a b t : ℝ} (hab : a ≤ b) (ht : t ≤ a) : clamp a b t = a := by
  rw [clamp,max_eq_left ht,min_eq_right hab]

lemma clamp_right {a b t : ℝ} (ht : b ≤ t) : clamp a b t = b := by
  exact min_eq_left (ht.trans (le_max_right _ _))

noncomputable def quadratic (a b c d t : ℝ) : ℝ :=
  clamp a b t * (c-clamp a b t)/d

lemma quadratic_lipschitz {a b c d : ℝ} {K : ℝ≥0} (hab : a ≤ b) (hd : 0 < d)
    (hlo : -(K:ℝ)*d ≤ c-2*b) (hhi : c-2*a ≤ (K:ℝ)*d) :
    LipschitzWith K (quadratic a b c d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨hxa,hxb⟩ := clamp_bounds (t := x) hab
  obtain ⟨hya,hyb⟩ := clamp_bounds (t := y) hab
  have hf : |c-clamp a b x-clamp a b y| ≤ (K:ℝ)*d := by
    rw [abs_le]
    constructor <;> linarith
  have hc := (clamp_lipschitz a b).dist_le_mul x y
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at hc
  rw [Real.dist_eq]
  have he : quadratic a b c d x-quadratic a b c d y =
      (clamp a b x-clamp a b y)*(c-clamp a b x-clamp a b y)/d := by
    unfold quadratic
    ring
  rw [he,abs_div,abs_mul,abs_of_pos hd]
  calc
    _ ≤ (|clamp a b x-clamp a b y| *((K:ℝ)*d))/d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf (abs_nonneg _)) hd.le
    _ = (K:ℝ)*|clamp a b x-clamp a b y| := by field_simp
    _ ≤ (K:ℝ)*dist x y := mul_le_mul_of_nonneg_left hc K.coe_nonneg

noncomputable def splice (c : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ c then f t else g t

lemma splice_lipschitz {K : ℝ≥0} {c : ℝ} {f g : ℝ → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (he : f c = g c) :
    LipschitzWith K (splice c f g) := by
  have h : LipschitzWith K ((Iic c).piecewise f g) := Gluing.lipschitz_piecewise isClosed_Iic
    hg hf.lipschitzOnWith (by simpa only [frontier_Iic,eqOn_singleton] using he)
  exact h

noncomputable def low (a t : ℝ) : ℝ := -quadratic a (2*a) a a t
noncomputable def high (r t : ℝ) : ℝ := splice (8*r) id (quadratic (8*r) (10*r) (10*r) (2*r)) t
noncomputable def positivePart (a r t : ℝ) : ℝ := splice (2*a) (low a) (high r) t
noncomputable def scalar (a r t : ℝ) : ℝ := splice 0 (fun t => -positivePart a r (-t)) (positivePart a r) t

lemma low_lipschitz {a : ℝ} (ha : 0 < a) : LipschitzWith 6 (low a) := by
  have h : LipschitzWith 6 (quadratic a (2*a) a a) :=
    quadratic_lipschitz (by linarith) ha (by norm_num; linarith) (by norm_num; linarith)
  exact h.neg

lemma high_lipschitz {r : ℝ} (hr : 0 < r) : LipschitzWith 6 (high r) := by
  apply splice_lipschitz (LipschitzWith.id.weaken (by norm_num))
  · exact quadratic_lipschitz (by linarith) (by linarith) (by norm_num; linarith) (by norm_num; linarith)
  · dsimp only [id,quadratic]
    rw [clamp_eq (by rfl) (by linarith)]
    field_simp
    ring

lemma positive_zero {a r t : ℝ} (ha : 0 < a) (ht : t ≤ a) : positivePart a r t = 0 := by
  rw [positivePart,splice,ite_eq_left (by linarith),low,quadratic,clamp_left (by linarith) ht]
  ring

lemma positive_lipschitz {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    LipschitzWith 6 (positivePart a r) := by
  apply splice_lipschitz (low_lipschitz ha) (high_lipschitz hr)
  rw [low,quadratic,clamp_right (le_refl _),high,splice,ite_eq_left har]
  dsimp only [id]
  field_simp
  ring

lemma scalar_lipschitz {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    LipschitzWith 6 (scalar a r) := by
  have hp := positive_lipschitz ha hr har
  have hn : LipschitzWith 6 (fun t => -positivePart a r (-t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_neg_neg] using hp.dist_le_mul (-x) (-y)
  apply splice_lipschitz hn hp
  simp only [neg_zero,positive_zero ha (by linarith : (0:ℝ) ≤ a)]

lemma positive_far_zero {a r t : ℝ} (hr : 0 < r) (har : 2*a ≤ 8*r)
    (ht : 10*r ≤ t) : positivePart a r t = 0 := by
  rw [positivePart,splice,ite_eq_right (by linarith),high,splice,ite_eq_right (by linarith),
    quadratic,clamp_right ht]
  ring

lemma positive_nonneg {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : 0 ≤ t) : 0 ≤ positivePart a r t := by
  unfold positivePart splice
  split_ifs with h
  · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show a ≤ 2*a by linarith)
    unfold low quadratic
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) ha.le)
  · unfold high splice
    split_ifs with h'
    · exact ht
    · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show 8*r ≤ 10*r by linarith)
      unfold quadratic
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

lemma positive_le {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    positivePart a r t ≤ 10*r := by
  unfold positivePart splice
  split_ifs with h
  · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show a ≤ 2*a by linarith)
    have hc : clamp a (2*a) t * (clamp a (2*a) t-a) ≤ 2*a*a := by
      nlinarith [sq_nonneg (clamp a (2*a) t-2*a)]
    unfold low quadratic
    calc
      _ = (clamp a (2*a) t * (clamp a (2*a) t-a))/a := by ring
      _ ≤ (2*a*a)/a := div_le_div_of_nonneg_right hc ha.le
      _ = 2*a := by field_simp
      _ ≤ 10*r := by linarith
  · unfold high splice
    split_ifs with h'
    · dsimp
      linarith
    · obtain ⟨hl,hu⟩ := clamp_bounds (t := t) (show 8*r ≤ 10*r by linarith)
      unfold quadratic
      rw [div_le_iff₀ (by linarith : 0 < 2*r)]
      nlinarith [sq_nonneg (clamp (8*r) (10*r) t-8*r)]

lemma scalar_support {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r)
    (hne : scalar a r t ≠ 0) : a < |t| ∧ |t| < 10*r := by
  by_cases ht : t ≤ 0
  · have he : |t| = -t := abs_of_nonpos ht
    rw [scalar,splice,ite_eq_left ht,neg_ne_zero] at hne
    rw [he]
    constructor
    · exact lt_of_not_ge (fun h => hne (positive_zero ha h))
    · exact lt_of_not_ge (fun h => hne (positive_far_zero hr har h))
  · have he : |t| = t := abs_of_pos (lt_of_not_ge ht)
    rw [scalar,splice,ite_eq_right ht] at hne
    rw [he]
    constructor
    · exact lt_of_not_ge (fun h => hne (positive_zero ha h))
    · exact lt_of_not_ge (fun h => hne (positive_far_zero hr har h))

lemma scalar_magnitude {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) :
    |scalar a r t| ≤ 10*r := by
  unfold scalar splice
  split_ifs with ht
  · rw [abs_neg,abs_of_nonneg (positive_nonneg ha hr (by linarith))]
    exact positive_le ha hr har
  · rw [abs_of_nonneg (positive_nonneg ha hr (by linarith))]
    exact positive_le ha hr har

section Taper
variable {X : Type*} [PseudoMetricSpace X]
open Metric

noncomputable def taper (S : Set X) (r : ℝ) (x : X) : ℝ :=
  if S.Nonempty then min 1 (infDist x S/r) else 1

lemma taper_bounds {S : Set X} {r : ℝ} (hr : 0 < r) (x : X) :
    0 ≤ taper S r x ∧ taper S r x ≤ 1 := by
  unfold taper
  split_ifs
  · exact ⟨le_min (by norm_num) (div_nonneg infDist_nonneg hr.le),min_le_left _ _⟩
  · norm_num

lemma taper_difference {S : Set X} {r : ℝ} (hr : 0 < r) (x y : X) :
    |taper S r x-taper S r y| ≤ dist x y/r := by
  by_cases hS : S.Nonempty
  · simp only [taper,hS,ite_true]
    have h := (LipschitzWith.id.const_min (1:ℝ)).dist_le_mul (infDist x S/r) (infDist y S/r)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq] at h
    have hd := (lipschitz_infDist_pt S).dist_le_mul x y
    rw [Real.dist_eq,NNReal.coe_one,one_mul] at hd
    calc
      _ ≤ |infDist x S/r-infDist y S/r| := h
      _ = |infDist x S-infDist y S|/r := by rw [← sub_div,abs_div,abs_of_pos hr]
      _ ≤ dist x y/r := div_le_div_of_nonneg_right hd hr.le
  · simp only [taper,hS,ite_false,sub_self,abs_zero]
    exact div_nonneg dist_nonneg hr.le

lemma sum_lipschitz_sparse {I : Type*} (A : Finset I) {f : I → X → ℝ} {K : ℝ≥0}
    (hf : ∀ i ∈ A, LipschitzWith K (f i))
    (hs : ∀ x, (A.filter (fun i => f i x ≠ 0)).card ≤ 1) :
    LipschitzWith (2*K) (fun x => ∑ i ∈ A, f i x) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let T := (A.filter (fun i => f i x ≠ 0)) ∪ (A.filter (fun i => f i y ≠ 0))
  have hTA : T ⊆ A := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc : T.card ≤ 2 := (Finset.card_union_le _ _).trans (by linarith [hs x,hs y])
  have he : ∑ i ∈ A, (f i x-f i y) = ∑ i ∈ T, (f i x-f i y) := by
    symm
    apply Finset.sum_subset hTA
    intro i hi hnot
    have hix : f i x = 0 := by
      by_contra h
      exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,h⟩))
    have hiy : f i y = 0 := by
      by_contra h
      exact hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,h⟩))
    rw [hix,hiy,sub_self]
  rw [Real.dist_eq,← Finset.sum_sub_distrib,he]
  calc
    _ ≤ ∑ i ∈ T, |f i x-f i y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ T, (K:ℝ)*dist x y := Finset.sum_le_sum (fun i hi =>
      by simpa only [Real.dist_eq] using (hf i (hTA hi)).dist_le_mul x y)
    _ = (T.card:ℝ)*((K:ℝ)*dist x y) := by simp
    _ ≤ 2*((K:ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = ((2*K:ℝ≥0):ℝ)*dist x y := by simp; ring

end Taper


end PlanarL1.Increment



end

section

namespace PlanarL1.Increment
open scoped NNReal
variable {X : Type*} [PseudoMetricSpace X]

/-- The actual increment with an ambient-metric taper. The scalar transverse
field is measured intrinsically, while this weight may use the unrestricted
metric. -/
noncomputable def damped (a r : ℝ) (t w : X → ℝ) (x : X) : ℝ :=
  scalar a r (t x)*w x

lemma damped_lipschitz {a r : ℝ} {t w : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (ht : LipschitzWith 4 t)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (hd : ∀ x y, |w x-w y| ≤ dist x y/r) :
    LipschitzWith 34 (damped a r t w) := by
  have hs : LipschitzWith 24 (fun x => scalar a r (t x)) := by
    simpa only [Function.comp_def,show (6:ℝ≥0)*4=24 by norm_num] using
      (scalar_lipschitz ha hr har).comp ht
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := hs.dist_le_mul x y
  rw [Real.dist_eq] at hxy
  norm_num at hxy ⊢
  have he : damped a r t w x-damped a r t w y =
      (scalar a r (t x)-scalar a r (t y))*w x+
      scalar a r (t y)*(w x-w y) := by unfold damped; ring
  rw [Real.dist_eq,he]
  calc
    _ ≤ |(scalar a r (t x)-scalar a r (t y))*w x|+
        |scalar a r (t y)*(w x-w y)| := abs_add_le _ _
    _ = |scalar a r (t x)-scalar a r (t y)| *w x+
        |scalar a r (t y)| *|w x-w y| := by rw [abs_mul,abs_mul,abs_of_nonneg (hw x).1]
    _ ≤ (24*dist x y)*1+(10*r)*(dist x y/r) := by
      exact add_le_add (mul_le_mul hxy (hw x).2 (hw x).1 (by positivity))
        (mul_le_mul (scalar_magnitude ha hr har) (hd x y)
          (abs_nonneg _) (by positivity))
    _ = 34*dist x y := by field_simp; ring

noncomputable def signedDamped (e : Bool) (a r : ℝ) (t w : X → ℝ) (x : X) : ℝ :=
  if e then damped a r t w x else -damped a r t w x

omit [PseudoMetricSpace X] in
lemma signedDamped_support {e : Bool} {a r : ℝ} {t w : X → ℝ}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) {x : X}
    (hx : signedDamped e a r t w x ≠ 0) : a < |t x| ∧ |t x| < 10*r := by
  have hn : damped a r t w x ≠ 0 := by
    cases e <;> simpa only [signedDamped,Bool.false_eq_true,ite_false,ite_true,neg_ne_zero] using hx
  exact scalar_support ha hr har (left_ne_zero_of_mul hn)

lemma damped_lifetime {I : Type*} (A : Finset I) {c : ℝ} {r : I → ℝ} {t : X → ℝ}
    {w : I → X → ℝ} (e : I → Bool) (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ i ∈ A, 0 < r i) (ht : LipschitzWith 4 t)
    (hw : ∀ i ∈ A, ∀ x, 0 ≤ w i x ∧ w i x ≤ 1)
    (hd : ∀ i ∈ A, ∀ x y, |w i x-w i y| ≤ dist x y/r i)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i) :
    LipschitzWith 68 (fun x => ∑ i ∈ A, signedDamped (e i) (c*r i) (r i) t (w i) x) := by
  have hf (i) (hi : i ∈ A) :
      LipschitzWith 34 (signedDamped (e i) (c*r i) (r i) t (w i)) := by
    have h := damped_lipschitz (mul_pos hc (hr i hi)) (hr i hi)
      (by nlinarith [hr i hi]) ht (hw i hi) (hd i hi)
    cases e i
    · exact h.neg
    · exact h
  have hs (x : X) : (A.filter (fun i => signedDamped (e i) (c*r i) (r i) t (w i) x ≠ 0)).card ≤ 1 := by
    classical
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hiA,hi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjA,hj⟩ := Finset.mem_filter.mp hj
    by_contra hij
    obtain ⟨hil,hiu⟩ := signedDamped_support (mul_pos hc (hr i hiA)) (hr i hiA)
      (by nlinarith [hr i hiA]) hi
    obtain ⟨hjl,hju⟩ := signedDamped_support (mul_pos hc (hr j hjA)) (hr j hjA)
      (by nlinarith [hr j hjA]) hj
    rcases hsep i hiA j hjA hij with h | h <;> linarith
  simpa only [show (2:ℝ≥0)*34=68 by norm_num] using sum_lipschitz_sparse A hf hs
end PlanarL1.Increment


end

section

namespace PlanarL1.Increment
open scoped NNReal
variable {X : Type*} [PseudoMetricSpace X]

lemma tapered_magnitude {a r q : ℝ} {S : Set X} {x y : X}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (hy : y ∈ S) :
    |scalar a r q*taper S r x| ≤ 10*dist x y := by
  have hb : taper S r x ≤ dist x y/r := by
    unfold taper
    rw [ite_eq_left (show S.Nonempty from ⟨y,hy⟩)]
    exact (min_le_right _ _).trans
      (div_le_div_of_nonneg_right (Metric.infDist_le_dist_of_mem hy) hr.le)
  rw [abs_mul,abs_of_nonneg (taper_bounds hr x).1]
  calc
    _ ≤ (10*r)*(dist x y/r) := mul_le_mul (scalar_magnitude ha hr har) hb
      (taper_bounds hr x).1 (by positivity)
    _ = 10*dist x y := by field_simp

lemma signed_tapered_magnitude (e : Bool) {a r q : ℝ} {S : Set X} {x y : X}
    (ha : 0 < a) (hr : 0 < r) (har : 2*a ≤ 8*r) (hy : y ∈ S) :
    |if e then scalar a r q*taper S r x else -(scalar a r q*taper S r x)| ≤
      10*dist x y := by
  cases e <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using
    tapered_magnitude ha hr har hy

end PlanarL1.Increment


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Crossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model

namespace Path

variable {n : ℕ} {M : Model n} {I J : Set ℝ}

/-- The same finite path is permitted in a larger band. -/
def widen (hJI : J ⊆ I) {i j : Fin n} : M.Path J i j → M.Path I i j
  | .nil i => .nil i
  | .cons H hH hs p => .cons H (hJI hH) hs (widen hJI p)

lemma length_widen (hJI : J ⊆ I) {i j : Fin n} (p : M.Path J i j) (a b : ℝ) :
    (p.widen hJI).length a b = p.length a b := by
  induction p generalizing a with
  | nil => rfl
  | cons H hH hs p ih => simp only [widen,length,ih]

end Path

namespace Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Geometric control of visits to a set of columns. The witnesses are actual
points at heights in J and actual ambient-band distances from the center. -/
def NearColumns (x : M.Point I root) (J : Set ℝ) (A : ℝ) (S : Set (Fin n)) : Prop :=
  ∀ v ∈ S, ∃ z : M.Point I root, z.column = v ∧ z.height ∈ J ∧ dist x z ≤ A

end Point
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k + 1)} {I J : Set ℝ} {L : NNReal}

lemma ordered_maximum (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (H : I) (i : Fin (k+1)) : F.value i H ≤ F.value b H := by
  let e := finCycle a
  rcases le_total (e.symm i) (e.symm b) with hi | hi
  · simpa only [e,Equiv.apply_symm_apply] using ho.2.1 H (e.symm i) (e.symm b) hi le_rfl
  · simpa only [e,Equiv.apply_symm_apply] using ho.2.2 H (e.symm b) (e.symm i) le_rfl hi

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Field

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {L : NNReal} {root : Fin n}

abbrev eval (F : M.Field I L) (z : M.Point I root) : ℝ :=
  F.value z.column ⟨z.height,z.inBand⟩

/-- The genuine pair of short low/high paths in : no scalar
separation or arc conclusion is included as an assumption. -/
structure Excursions (F : M.Field I L) (hJI : J ⊆ I) (z : M.Point I root) (A ε : ℝ) where
  inBand : z.height ∈ J
  lowColumn : Fin n
  highColumn : Fin n
  lowHeight : J
  highHeight : J
  lowPath : M.Path J z.column lowColumn
  highPath : M.Path J z.column highColumn
  lowLength : lowPath.length z.height lowHeight.val ≤ A
  highLength : highPath.length z.height highHeight.val ≤ A
  lowValue : F.value lowColumn ⟨lowHeight.val,hJI lowHeight.property⟩ < F.eval z - ε
  highValue : F.eval z + ε < F.value highColumn ⟨highHeight.val,hJI highHeight.property⟩

namespace Excursions

variable {F : M.Field I L} {hJI : J ⊆ I} {z : M.Point I root} {A ε : ℝ}

def traversal (E : F.Excursions hJI z A ε) :
    (M.activeGraph J).Walk E.lowColumn E.highColumn :=
  E.lowPath.word.reverse.append E.highPath.word

end Excursions

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model.Field

variable {k : ℕ} {M : Model (k+1)} {I J : Set ℝ} {L : NNReal}

def restrict (F : M.Field I L) (hJI : J ⊆ I) : M.Field J L where
  value i H := F.value i ⟨H.val,hJI H.property⟩
  vertical i := by
    apply LipschitzWith.of_dist_le_mul
    intro H T
    exact (F.vertical i).dist_le_mul ⟨H.val,hJI H.property⟩ ⟨T.val,hJI T.property⟩
  switch i j H hs := F.switch i j ⟨H.val,hJI H.property⟩ hs

end PlanarL1.Columns.Model.Field


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SeedPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.Path

variable {n : ℕ} {M : Model n} {J I : Set ℝ}

/-- A specified visit of a finite switching path, retaining its traveled
arclength. Multiple visits of the same representative are not identified. -/
def AtTime : {i j : Fin n} → M.Path J i j → ℝ → ℝ → (Fin n × ℝ) → ℝ → Prop
  | i, _, .nil _, a, b, z, t => z.1 = i ∧ z.2 ∈ Set.uIcc a b ∧ t = |a-z.2|
  | i, _, .cons H _ _ p, a, b, z, t =>
      (z.1 = i ∧ z.2 ∈ Set.uIcc a H ∧ t = |a-z.2|) ∨ p.AtTime H b z (t-|a-H|)

end PlanarL1.Columns.Model.Path

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

namespace Field

/-- Strict separation of representatives by the chord, with an arbitrary
linear cut outside its first open arc. -/
def TipSeparates (a b x y : Fin n) : Prop :=
  (a < x ∧ x < b ∧ (y < a ∨ b < y)) ∨ (a < y ∧ y < b ∧ (x < a ∨ b < x))

/-- Complement of the main procedure's barrier-drop exclusion. Both endpoint
thresholds are tested, exactly as in pack:barrier and pack:retained-data. -/
def NoLowTip (F : M.Field I 1) (x y : M.Point I root) (J : Set ℝ) (j : ℝ) : Prop :=
  ∀ (e : M.Point I root) (b : Fin n), e.height ∈ J →
    e.height ∈ M.heights e.column b → ¬ Consecutive e.column b →
    TipSeparates e.column b x.column y.column →
    (dist x e ≤ 1 ∨ dist y e ≤ 1) →
    F.eval x-j ≤ F.eval e ∧ F.eval y-j ≤ F.eval e

end Field

end PlanarL1.Columns.Model


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Bands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns

namespace Model

/-- Relabelling columns does not change geometry. The two order conditions
are explicit, so the construction never assumes invariance under an arbitrary
permutation of the circular order. -/
def relabel {n : ℕ} (M : Model n) (e : Equiv.Perm (Fin n))
    (hnc : ColumnOrder.Noncrossing (M.link.comap e))
    (hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j) : Model n where
  link := M.link.comap e
  heights i j := M.heights (e i) (e j)
  symm i j := M.symm (e i) (e j)
  permitted i j H h := M.permitted (e i) (e j) H h
  compact i j := M.compact (e i) (e j)
  noncrossing := hnc
  terminal i j h hn := by
    obtain ⟨H,hH,ht⟩ := M.terminal (e i) (e j) h (fun hc => hn ((hcon i j).mp hc))
    exact ⟨H,hH,fun k T h => ht (e k) T h⟩

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J : Set ℝ} {root i j : Fin n}

/-- Undo a column relabelling on actual finite switching paths. -/
def Path.unlabel : {i j : Fin n} → (M.relabel e hnc hcon).Path J i j →
    M.Path J (e i) (e j)
  | _, _, .nil _ => .nil _
  | _, _, .cons H hH hs p => .cons H hH hs p.unlabel

@[simp] lemma Path.length_unlabel (p : (M.relabel e hnc hcon).Path J i j) (s t : ℝ) :
    p.unlabel.length s t = p.length s t := by
  induction p generalizing s with
  | nil => rfl
  | cons H hH hs p ih => simp only [Path.unlabel, Path.length, ih]

def Path.label : {i j : Fin n} → M.Path J i j →
    (M.relabel e hnc hcon).Path J (e.symm i) (e.symm j)
  | _, _, .nil _ => .nil _
  | _, _, .cons H hH hs p => .cons H hH (by simpa only [relabel, e.apply_symm_apply] using hs)
      p.label

@[simp] lemma Path.length_label (p : M.Path J i j) (s t : ℝ) :
    (p.label (hnc := hnc) (hcon := hcon)).length s t = p.length s t := by
  induction p generalizing s with
  | nil => rfl
  | cons H hH hs p ih => simp only [Path.label, Path.length, ih]

/-- The point map keeps the height and moves only the column name. -/
def Point.unlabel (x : (M.relabel e hnc hcon).Point J root) : M.Point J (e root) where
  column := e x.column
  height := x.height
  inBand := x.inBand
  reachable := by
    obtain ⟨p⟩ := x.reachable
    obtain ⟨q,hq⟩ := Path.exists_word p
    exact ⟨q.unlabel.word⟩

def Path.cast {i j k l : Fin n} (p : M.Path J i j) (h : i = k) (g : j = l) :
    M.Path J k l := h ▸ g ▸ p

@[simp] lemma Path.length_cast {i j k l : Fin n} (p : M.Path J i j)
    (h : i = k) (g : j = l) (s t : ℝ) : (p.cast h g).length s t = p.length s t := by
  subst k; subst l; rfl

end Model
end PlanarL1.Columns

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Inclusion of intrinsic components into a larger band. No equality of the
intrinsic metrics is asserted. -/
def Point.widen (x : M.Point J root) (hJI : J ⊆ I) : M.Point I root where
  column := x.column
  height := x.height
  inBand := hJI x.inBand
  reachable := by
    obtain ⟨p⟩ := x.reachable
    obtain ⟨q,_⟩ := Path.exists_word p
    exact ⟨(q.widen hJI).word⟩

lemma Point.dist_widen_le (x y : M.Point J root) (hJI : J ⊆ I) :
    dist (x.widen hJI) (y.widen hJI) ≤ dist x y := by
  change (x.widen hJI).distance (y.widen hJI) ≤ x.distance y
  have := x.paths_nonempty y
  apply le_ciInf
  intro p
  exact ((x.widen hJI).distance_le (y.widen hJI) (p.widen hJI)).trans_eq (p.length_widen _ _ _)

namespace Field

/-- The source descent lives in the BROAD CURRENT band J, whereas the old
comparison field and witnesses live in the OLD chart I, possibly in different
J-components. The attaining condition refers to J, not to the larger band. -/
structure BandDescent (F : M.Field I 1) (J : Set ℝ) (x : M.Point I root) (ε : ℝ) where
  start_in : x.height ∈ J
  target : M.Point I root
  target_in : target.height ∈ J
  path : M.Path J x.column target.column
  shortest : ∀ p : M.Path J x.column target.column,
    path.length x.height target.height ≤ p.length x.height target.height
  lower : (1:ℝ)/100000 ≤ path.length x.height target.height
  upper : path.length x.height target.height ≤ (1:ℝ)/50
  drop : F.eval target ≤ F.eval x-path.length x.height target.height+ε

end Field
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Point

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

/-- Actual distance field of an old chart. Outside its component we choose
zero only to make a whole-band scalar function; radial sublevels retain the
source's +infinity convention and never include those columns. -/
noncomputable def radialValue (o : M.Point I root) (i : Fin n) (H : I) : ℝ := by
  classical
  exact if hi : (M.activeGraph I).Reachable root i then
    dist o (⟨i,H.val,H.property,hi⟩ : M.Point I root) else 0

lemma radialValue_vertical (o : M.Point I root) (i : Fin n) :
    LipschitzWith 1 (o.radialValue i) := by
  by_cases hi : (M.activeGraph I).Reachable root i
  · apply LipschitzWith.of_dist_le_mul
    intro H T
    simp only [radialValue,dite_eq_left hi,NNReal.coe_one,one_mul]
    exact (dist_dist_dist_le_right o
      (⟨i,H.val,H.property,hi⟩ : M.Point I root)
      (⟨i,T.val,T.property,hi⟩ : M.Point I root)).trans_eq
      (Point.dist_same_column _ _ rfl)
  · apply LipschitzWith.of_dist_le_mul
    intro H T
    simp only [radialValue,dite_eq_right hi,dist_self,NNReal.coe_one,one_mul]
    exact dist_nonneg

lemma radialValue_switch (o : M.Point I root) (i j : Fin n) (H : I)
    (hs : H.val ∈ M.heights i j) : o.radialValue i H = o.radialValue j H := by
  have ha : (M.activeGraph I).Adj i j := ⟨H.val,H.property,hs⟩
  by_cases hi : (M.activeGraph I).Reachable root i
  · have hj := hi.trans ha.reachable
    simp only [radialValue,dite_eq_left hi,dite_eq_left hj]
    let x : M.Point I root := ⟨i,H.val,H.property,hi⟩
    let y : M.Point I root := ⟨j,H.val,H.property,hj⟩
    have hz : dist x y = 0 := by
      apply le_antisymm _ dist_nonneg
      simpa only [x,y,sub_self,abs_zero,add_zero] using x.dist_le_switch y H.property hs
    exact PseudoMetricSpace.dist_eq_of_dist_zero o hz
  · have hj : ¬(M.activeGraph I).Reachable root j := by
      intro hj
      exact hi (hj.trans ha.symm.reachable)
    simp only [radialValue,dite_eq_right hi,dite_eq_right hj]

noncomputable def radialField (o : M.Point I root) : M.Field I 1 where
  value := o.radialValue
  vertical := o.radialValue_vertical
  switch := o.radialValue_switch

@[simp] lemma radialField_eval (o x : M.Point I root) : o.radialField.eval x = dist o x := by
  simp only [Field.eval,radialField,radialValue,dite_eq_left x.reachable]

end PlanarL1.Columns.Model.Point


namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J I : Set ℝ} {root : Fin n}

def Point.label (x : M.Point J (e root)) : (M.relabel e hnc hcon).Point J root where
  column := e.symm x.column
  height := x.height
  inBand := x.inBand
  reachable := by
    obtain ⟨p⟩ := x.reachable
    obtain ⟨q,_⟩ := Path.exists_word p
    simpa only [e.symm_apply_apply] using
      (q.label (hnc := hnc) (hcon := hcon)).word.reachable

@[simp] lemma Point.unlabel_label (x : M.Point J (e root)) :
    (x.label (hnc := hnc) (hcon := hcon)).unlabel = x := by
  cases x
  simp only [Point.label,Point.unlabel,e.apply_symm_apply]

@[simp] lemma Point.label_unlabel (x : (M.relabel e hnc hcon).Point J root) :
    x.unlabel.label = x := by
  cases x
  simp only [Point.label,Point.unlabel,e.symm_apply_apply]

def Field.label {L : NNReal} (F : M.Field I L) : (M.relabel e hnc hcon).Field I L where
  value := fun i => F.value (e i)
  vertical := fun i => F.vertical (e i)
  switch := fun i j H h => F.switch (e i) (e j) H h

@[simp] lemma Field.eval_label {L : NNReal} (F : M.Field I L) (x : M.Point I (e root)) :
    (F.label (hnc := hnc) (hcon := hcon)).eval x.label = F.eval x := by
  simp only [Field.eval,Field.label,Point.label,e.apply_symm_apply]

@[simp] lemma Field.eval_unlabel {L : NNReal} (F : M.Field I L)
    (x : (M.relabel e hnc hcon).Point I root) :
    (F.label (hnc := hnc) (hcon := hcon)).eval x = F.eval x.unlabel := rfl

noncomputable def Field.BandDescent.label {F : M.Field I 1} {x : M.Point I (e root)} {ε : ℝ}
    (D : F.BandDescent J x ε) :
    (F.label (hnc := hnc) (hcon := hcon)).BandDescent J x.label ε where
  start_in := D.start_in
  target := D.target.label
  target_in := D.target_in
  path := D.path.label
  shortest := by
    intro p
    let q := p.unlabel
    have he₁ : e (x.label (hnc := hnc) (hcon := hcon)).column = x.column := e.apply_symm_apply _
    have he₂ : e (D.target.label (hnc := hnc) (hcon := hcon)).column = D.target.column := e.apply_symm_apply _
    have hd := D.shortest (q.cast he₁ he₂)
    rw [Path.length_cast] at hd
    dsimp only [q] at hd
    rw [Path.length_unlabel] at hd
    simpa only [Path.length_label,Point.label] using hd
  lower := by simpa only [Path.length_label,Point.label] using D.lower
  upper := by simpa only [Path.length_label,Point.label] using D.upper
  drop := by
    simpa only [Path.length_label,Field.eval,Field.label,Point.label,e.apply_symm_apply] using D.drop

end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field

/-- Strictly opposite sides of an unoriented circular chord. -/
def CircularTipSeparates {n : ℕ} (a b x y : Fin n) : Prop :=
  TipSeparates a b x y ∨ TipSeparates b a x y

end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model

variable {n : ℕ} {M : Model n} {e : Equiv.Perm (Fin n)}
  {hnc : ColumnOrder.Noncrossing (M.link.comap e)}
  {hcon : ∀ i j, Consecutive (e i) (e j) ↔ Consecutive i j}
  {J I : Set ℝ} {root : Fin n}

@[simp] lemma Point.widen_label (x : M.Point J (e root)) (hJI : J ⊆ I) :
    (x.label (hnc := hnc) (hcon := hcon)).widen hJI = (x.widen hJI).label := rfl

namespace Field

/-- Absence of a low separating tip is intrinsically circular: reversing
the listed chord endpoints does not change the exclusion test. -/
def NoLowCircular (F : M.Field I 1) (x y : M.Point I root) (J : Set ℝ) (j : ℝ) : Prop :=
  ∀ (v : M.Point I root) (b : Fin n), v.height ∈ J →
    v.height ∈ M.heights v.column b → ¬ Consecutive v.column b →
    CircularTipSeparates v.column b x.column y.column →
    (dist x v ≤ 1 ∨ dist y v ≤ 1) →
    F.eval x-j ≤ F.eval v ∧ F.eval y-j ≤ F.eval v

end Field
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.FiniteRandom

attribute [local instance] Classical.propDecidable

noncomputable def event {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : Finset Ω := by
  classical
  exact Finset.univ.filter P

noncomputable def prob {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact ((event P).card : ℝ) / Fintype.card Ω

end PlanarL1.FiniteRandom

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Interpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
/-! ## The deterministic clamping core of thin-band interpolation
No probabilistic or geometric claim is assumed by
these lemmas; they establish the scalar inequalities used at each actual node. -/

namespace Interpolation

/-- The exact parent/tentative clamp in the source: `U=max parent A`,
`L=min parent B`, and `F=min U (max L T)`. -/
def nodeValue (parent upper lower tentative : ℝ) : ℝ :=
  min (max parent upper) (max (min parent lower) tentative)

/-- Clamping into an interval whose upper end is not too small and whose lower
end is not too large preserves the claimed accuracy window. -/
theorem nodeValue_bounds {parent upper lower tentative lo hi : ℝ}
    (hlo : lo ≤ upper) (hhi : lower ≤ hi)
    (htlo : lo ≤ tentative) (hthi : tentative ≤ hi) :
    lo ≤ nodeValue parent upper lower tentative ∧
      nodeValue parent upper lower tentative ≤ hi := by
  constructor
  · exact le_min (hlo.trans (le_max_right _ _)) (htlo.trans (le_max_right _ _))
  · exact (min_le_right _ _).trans (max_le ((min_le_right _ _).trans hhi) hthi)

/-- An atom evaluation together with its deterministic priority/inheritance
name. Its value may depend on all the already sampled ancestor noises. -/
structure NamedValue where
  name : ℕ
  value : ℝ

/-- Minima and maxima both resolve ties toward the earliest atom name. -/
noncomputable def minNamed (a b : NamedValue) : NamedValue :=
  if a.value < b.value ∨ (a.value = b.value ∧ a.name ≤ b.name) then a else b

noncomputable def maxNamed (a b : NamedValue) : NamedValue :=
  if b.value < a.value ∨ (a.value = b.value ∧ a.name ≤ b.name) then a else b

lemma minNamed_mem (a b : NamedValue) : minNamed a b = a ∨ minNamed a b = b := by
  unfold minNamed
  split_ifs <;> simp

lemma maxNamed_mem (a b : NamedValue) : maxNamed a b = a ∨ maxNamed a b = b := by
  unfold maxNamed
  split_ifs <;> simp

@[simp]
lemma minNamed_value (a b : NamedValue) : (minNamed a b).value = min a.value b.value := by
  unfold minNamed
  split_ifs with h
  · rcases h with h | ⟨h, _⟩
    · exact (min_eq_left h.le).symm
    · exact (min_eq_left h.le).symm
  · have hh : b.value ≤ a.value := le_of_not_gt (fun hh => h (Or.inl hh))
    exact (min_eq_right hh).symm

@[simp]
lemma maxNamed_value (a b : NamedValue) : (maxNamed a b).value = max a.value b.value := by
  unfold maxNamed
  split_ifs with h
  · rcases h with h | ⟨h, _⟩
    · exact (max_eq_left h.le).symm
    · exact (max_eq_left h.ge).symm
  · have hh : a.value ≤ b.value := le_of_not_gt (fun hh => h (Or.inl hh))
    exact (max_eq_right hh).symm

/-- The clamp with the manuscript's consistent atom-name tie rule. -/
noncomputable def nodeNamed (parent upper lower tentative : NamedValue) : NamedValue :=
  minNamed (maxNamed parent upper) (maxNamed (minNamed parent lower) tentative)

@[simp]
lemma nodeNamed_value (parent upper lower tentative : NamedValue) :
    (nodeNamed parent upper lower tentative).value =
      nodeValue parent.value upper.value lower.value tentative.value := by
  simp [nodeNamed, nodeValue]

lemma nodeNamed_mem (parent upper lower tentative : NamedValue) :
    nodeNamed parent upper lower tentative = parent ∨
    nodeNamed parent upper lower tentative = upper ∨
    nodeNamed parent upper lower tentative = lower ∨
    nodeNamed parent upper lower tentative = tentative := by
  rcases minNamed_mem (maxNamed parent upper)
      (maxNamed (minNamed parent lower) tentative) with h | h
  · rcases maxNamed_mem parent upper with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl (h.trans h'))
  · rcases maxNamed_mem (minNamed parent lower) tentative with h' | h'
    · rcases minNamed_mem parent lower with h'' | h''
      · exact Or.inl ((h.trans h').trans h'')
      · exact Or.inr (Or.inr (Or.inl ((h.trans h').trans h'')))
    · exact Or.inr (Or.inr (Or.inr (h.trans h')))

/-- The complete equality collar, including exact retention of the parent
atom's name . -/
lemma nodeNamed_collar {parent upper lower tentative : NamedValue}
    (hu : upper.value < parent.value) (hl : parent.value < lower.value)
    (ht : parent.name ≤ tentative.name) :
    nodeNamed parent upper lower tentative = parent := by
  have hU : maxNamed parent upper = parent := by
    simp only [maxNamed, ite_eq_left (Or.inl hu)]
  have hL : minNamed parent lower = parent := by
    simp only [minNamed, ite_eq_left (Or.inl hl)]
  simp only [nodeNamed, hU, hL]
  rcases lt_trichotomy parent.value tentative.value with h | h | h
  · have hm : maxNamed parent tentative = tentative := by
      apply ite_eq_right
      push Not
      exact ⟨h.le, fun hh => (h.ne hh).elim⟩
    rw [hm]
    exact ite_eq_left (Or.inl h)
  · have hm : maxNamed parent tentative = parent := ite_eq_left (Or.inr ⟨h, ht⟩)
    rw [hm]
    exact ite_eq_left (Or.inr ⟨rfl, le_rfl⟩)
  · have hm : maxNamed parent tentative = parent := ite_eq_left (Or.inl h)
    rw [hm]
    exact ite_eq_left (Or.inr ⟨rfl, le_rfl⟩)

/-- Both signed distance cones have their exact unit Lipschitz constant. -/
lemma distance_cone_lipschitz {X : Type*} [PseudoMetricSpace X] (x : X) (c : ℝ) :
    LipschitzWith 1 (fun v => c + dist x v) ∧
      LipschitzWith 1 (fun v => c - dist x v) := by
  constructor <;> apply LipschitzWith.of_dist_le_mul <;> intro u v
  · simpa only [Real.dist_eq, add_sub_add_left_eq_sub, NNReal.coe_one, one_mul, dist_comm x] using
      abs_dist_sub_le u v x
  · rw [Real.dist_eq]
    have he : c - dist x u - (c - dist x v) = dist x v - dist x u := by ring
    rw [he, abs_sub_comm]
    simpa only [NNReal.coe_one, one_mul, dist_comm x] using abs_dist_sub_le u v x

lemma nodeValue_lipschitz {X : Type*} [PseudoMetricSpace X]
    {P A B T : X → ℝ} (hP : LipschitzWith 1 P) (hA : LipschitzWith 1 A)
    (hB : LipschitzWith 1 B) (hT : LipschitzWith 1 T) :
    LipschitzWith 1 (fun x => nodeValue (P x) (A x) (B x) (T x)) := by
  simpa only [nodeValue, max_self] using (hP.max hA).min ((hP.min hB).max hT)


end Interpolation



end PlanarL1

end

section

namespace PlanarL1.Interpolation
open scoped NNReal

noncomputable def clippedNamed (o p h : NamedValue) : NamedValue :=
  maxNamed o (minNamed p h)

lemma clippedNamed_mem (o p h : NamedValue) :
    clippedNamed o p h = o ∨ clippedNamed o p h = p ∨ clippedNamed o p h = h := by
  rcases maxNamed_mem o (minNamed p h) with he | he
  · exact Or.inl he
  · rcases minNamed_mem p h with he' | he'
    · exact Or.inr (Or.inl (he.trans he'))
    · exact Or.inr (Or.inr (he.trans he'))

lemma clippedNamed_value (o p h : NamedValue) :
    (clippedNamed o p h).value = max o.value (min p.value h.value) := by
  simp only [clippedNamed,maxNamed_value,minNamed_value]

noncomputable def clipNames (S : Finset ℕ) : Finset ℕ :=
  insert 0 (insert 1 (S.image (fun i => i+2)))

/-- The old field has priority zero; the shield has priority one, and actual
inherited atom identities are shifted by two. Thus a retaining tie keeps the
old identifier, just as required by the source chart update. -/
noncomputable def namedClip {X : Type*} (F : X → NamedValue) (old shield : X → ℝ)
    (x : X) : NamedValue :=
  clippedNamed ⟨0,old x⟩ ⟨(F x).name+2,(F x).value⟩ ⟨1,shield x⟩

noncomputable def clipAtom {X : Type*} (atom : ℕ → X → ℝ) (old shield : X → ℝ)
    (i : ℕ) (x : X) : ℝ := if i = 0 then old x else if i = 1 then shield x else atom (i-2) x

end PlanarL1.Interpolation


namespace PlanarL1.Interpolation
lemma clippedNamed_retains {o p h : NamedValue} (hp : p.value < o.value) :
    clippedNamed o p h = o := by
  have ht : (minNamed p h).value < o.value := by
    rw [minNamed_value]
    exact (min_le_left _ _).trans_lt hp
  exact ite_eq_left (Or.inl ht)
end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

noncomputable def secondaryNames (S : Finset ℕ) : Finset ℕ :=
  insert 0 (insert 1 (insert 2 (S.image (fun i => i+3))))

noncomputable def secondaryNamed {X : Type*} (F : X → NamedValue)
    (old ordered shield : X → ℝ) (ordinary : Bool) (x : X) : NamedValue :=
  clippedNamed ⟨0,old x⟩
    (if ordinary then minNamed ⟨(F x).name+3,(F x).value⟩ ⟨2,ordered x⟩
      else ⟨(F x).name+3,(F x).value⟩) ⟨1,shield x⟩

noncomputable def secondaryAtom {X : Type*} (atom : ℕ → X → ℝ)
    (old ordered shield : X → ℝ) (i : ℕ) (x : X) : ℝ :=
  if i=0 then old x else if i=1 then shield x else if i=2 then ordered x else atom (i-3) x

lemma secondaryNamed_value {X : Type*} (F : X → NamedValue)
    (old ordered shield : X → ℝ) (ordinary : Bool) (x : X) :
    (secondaryNamed F old ordered shield ordinary x).value =
      max (old x) (min (if ordinary then min (F x).value (ordered x) else (F x).value) (shield x)) := by
  cases ordinary <;> simp only [secondaryNamed,clippedNamed_value,Bool.false_eq_true,
    ite_false,ite_true,minNamed_value]

lemma secondaryNamed_mem {X : Type*} (F : X → NamedValue)
    (old ordered shield : X → ℝ) (ordinary : Bool) (x : X) :
    secondaryNamed F old ordered shield ordinary x = ⟨0,old x⟩ ∨
    secondaryNamed F old ordered shield ordinary x = ⟨1,shield x⟩ ∨
    secondaryNamed F old ordered shield ordinary x = ⟨2,ordered x⟩ ∨
    secondaryNamed F old ordered shield ordinary x = ⟨(F x).name+3,(F x).value⟩ := by
  rcases clippedNamed_mem ⟨0,old x⟩
    (if ordinary then minNamed ⟨(F x).name+3,(F x).value⟩ ⟨2,ordered x⟩
      else ⟨(F x).name+3,(F x).value⟩) ⟨1,shield x⟩ with h | h | h
  · exact Or.inl h
  · change secondaryNamed F old ordered shield ordinary x = _ at h
    cases ordinary with
    | false => exact Or.inr (Or.inr (Or.inr h))
    | true =>
      rcases minNamed_mem ⟨(F x).name+3,(F x).value⟩ ⟨2,ordered x⟩ with ha | ha
      · exact Or.inr (Or.inr (Or.inr (h.trans ha)))
      · exact Or.inr (Or.inr (Or.inl (h.trans ha)))
  · exact Or.inr (Or.inl h)

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

/-- Retained old branches are shared (name zero). Every genuinely new group
branch receives a distinct name including its group, not merely its formula. -/
def familyName {k : ℕ} (g : Fin k) (i : ℕ) : ℕ :=
  if i=0 then 0 else Nat.pair g.val (i-1)+1

lemma familyName_zero {k : ℕ} (g : Fin k) : familyName g 0 = 0 := by
  simp [familyName]

lemma familyName_ne_zero {k : ℕ} (g : Fin k) {i : ℕ} (hi : i ≠ 0) :
    familyName g i ≠ 0 := by simp [familyName,hi]

noncomputable def familyNames {k : ℕ} (S : Fin k → Finset ℕ) : Finset ℕ :=
  insert 0 (Finset.univ.biUnion (fun g => (S g).image (familyName g)))

noncomputable def familyAtom {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (i : ℕ) (x : X) : ℝ :=
  if i=0 then old x else if h : (Nat.unpair (i-1)).1 < k then
    A ⟨(Nat.unpair (i-1)).1,h⟩ ((Nat.unpair (i-1)).2+1) x else old x


noncomputable def maxSelection {X : Type*} (old : X → NamedValue) :
    List (X → NamedValue) → X → NamedValue
  | [], x => old x
  | F::Fs, x => maxNamed (F x) (maxSelection old Fs x)

lemma maxSelection_mem {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (x : X) :
    maxSelection old Fs x = old x ∨ ∃ F ∈ Fs, maxSelection old Fs x = F x := by
  induction Fs with
  | nil => exact Or.inl rfl
  | cons F Fs ih =>
    rcases maxNamed_mem (F x) (maxSelection old Fs x) with h | h
    · exact Or.inr ⟨F,by simp,h⟩
    · change maxSelection old (F::Fs) x = _ at h
      rcases ih with ih | ⟨G,hG,he⟩
      · exact Or.inl (h.trans ih)
      · exact Or.inr ⟨G,List.mem_cons_of_mem _ hG,h.trans he⟩

lemma maxSelection_lipschitz {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0}
    (old : X → NamedValue) (Fs : List (X → NamedValue))
    (ho : LipschitzWith K (fun x => (old x).value))
    (hF : ∀ F ∈ Fs, LipschitzWith K (fun x => (F x).value)) :
    LipschitzWith K (fun x => (maxSelection old Fs x).value) := by
  induction Fs with
  | nil => exact ho
  | cons F Fs ih =>
    simp only [maxSelection,maxNamed_value]
    simpa only [max_self] using (hF F (by simp)).max (ih (fun G hG => hF G (List.mem_cons_of_mem _ hG)))

noncomputable def familySelection {X : Type*} {k : ℕ} (old : X → ℝ)
    (F : Fin k → X → NamedValue) : X → NamedValue :=
  maxSelection (fun x => ⟨0,old x⟩)
    (List.ofFn (fun g => fun x => ⟨familyName g (F g x).name,(F g x).value⟩))

lemma familySelection_lipschitz {X : Type*} [PseudoMetricSpace X] {k : ℕ} {K : ℝ≥0}
    (old : X → ℝ) (F : Fin k → X → NamedValue) (ho : LipschitzWith K old)
    (hF : ∀ g, LipschitzWith K (fun x => (F g x).value)) :
    LipschitzWith K (fun x => (familySelection old F x).value) := by
  apply maxSelection_lipschitz _ _ ho
  intro G hG
  obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
  exact hF g

end PlanarL1.Interpolation


end

section

namespace PlanarL1.Interpolation
open scoped NNReal

lemma clippedNamed_eq_old_of_value {o p h : NamedValue}
    (hname : o.name = 0) (he : (clippedNamed o p h).value = o.value) :
    clippedNamed o p h = o := by
  have hle : (minNamed p h).value ≤ o.value := by
    rw [clippedNamed_value] at he
    rw [minNamed_value]
    exact max_eq_left_iff.mp he
  apply ite_eq_left
  rcases lt_or_eq_of_le hle with hh | hh
  · exact Or.inl hh
  · exact Or.inr ⟨hh.symm,by omega⟩

lemma namedClip_eq_old_iff {X : Type*} (F : X → NamedValue) (old shield : X → ℝ)
    (x : X) : (namedClip F old shield x).name = 0 ↔
      (namedClip F old shield x).value = old x := by
  constructor
  · intro hn
    rcases clippedNamed_mem ⟨0,old x⟩ ⟨(F x).name+2,(F x).value⟩ ⟨1,shield x⟩ with h | h | h
    · exact congrArg NamedValue.value h
    · change namedClip F old shield x = _ at h
      rw [h] at hn
      simp only at hn
      omega
    · change namedClip F old shield x = _ at h
      rw [h] at hn
      contradiction
  · intro he
    exact congrArg NamedValue.name (clippedNamed_eq_old_of_value rfl he)

end PlanarL1.Interpolation



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_RadialTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)

namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

/-! ### The actual radial-node tree and its interpolation formulas
The geometric data below use precisely the thin-band constants. Nodes and their
parent maps are induced-graph components, not an assumed abstract hierarchy. -/

structure RadialTree where
  base : M.Point J root
  δ : ℝ
  a : ℝ
  ζ : ℝ
  delta_pos : 0 < δ
  width_pos : 0 < a
  zeta_pos : 0 < ζ
  zeta_lt_one : ζ < 1
  width_bound : a ≤ ζ * δ / 1000000
  half_width : ∀ T ∈ J, |base.height - T| ≤ a / 2
  closed_band : IsClosed J
  interval_band : Set.OrdConnected J

namespace RadialTree

variable (R : RadialTree (M := M) (J := J) (root := root))

def Node (k : ℕ) :=
  ((M.activeGraph J).induce
    (R.base.superlevel R.base.height R.base.inBand (k * R.δ))).ConnectedComponent

lemma width_small : R.a < R.δ / 1000 := by
  have h := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
  nlinarith [R.width_bound, R.delta_pos]

lemma superlevel_antitone {k m : ℕ} (hkm : k ≤ m) :
    R.base.superlevel R.base.height R.base.inBand (m * R.δ) ⊆
      R.base.superlevel R.base.height R.base.inBand (k * R.δ) := by
  rintro i ⟨hr, hi⟩
  refine ⟨hr, le_trans ?_ hi⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) R.delta_pos.le

def parent {k : ℕ} (C : R.Node (k + 1)) : R.Node k :=
  ColumnOrder.componentAbove (R.superlevel_antitone (Nat.le_succ k)) C

lemma mem_parent {k : ℕ} (C : R.Node (k + 1)) :
    ColumnOrder.componentColumns C ⊆ ColumnOrder.componentColumns (R.parent C) :=
  ColumnOrder.componentColumns_above _ C

noncomputable def portals {k : ℕ} (C : R.Node k) :
    R.base.PortalData R.base.height R.base.inBand R.a (k * R.δ) C :=
  Classical.choice (R.base.portalData_nonempty R.closed_band R.base.inBand rfl
    R.width_pos R.half_width (by
      by_cases hk : k = 0
      · left; simp [hk]
      · right
        have hk' : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
        have hw := R.width_small
        nlinarith [mul_le_mul_of_nonneg_right hk' R.delta_pos.le, R.delta_pos]) C)

lemma parent_near {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root)
    (hv : v = (R.portals C).left ∨ v = (R.portals C).right) :
    min (dist v (R.portals (R.parent C)).left)
      (dist v (R.portals (R.parent C)).right) ≤ R.δ + 220 * R.a := by
  have hm : v.column ∈ ColumnOrder.componentColumns (R.parent C) := by
    apply R.mem_parent C
    rcases hv with rfl | rfl
    · exact (R.portals C).left_mem
    · exact (R.portals C).right_mem
  have hr : dist R.base v < (k : ℝ) * R.δ + R.δ + R.a := by
    rcases hv with rfl | rfl
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).left_radial.2
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).right_radial.2
  linarith [(R.portals (R.parent C)).near_of_radial v hm hr.le, R.width_pos]

lemma parent_separated {k : ℕ} (C : R.Node (k + 1)) (u v : M.Point J root)
    (hu : u = (R.portals (R.parent C)).left ∨ u = (R.portals (R.parent C)).right)
    (hv : v = (R.portals C).left ∨ v = (R.portals C).right) :
    R.δ - 10 * R.a ≤ dist u v := by
  have hr : dist R.base u < (k : ℝ) * R.δ + R.a := by
    rcases hu with rfl | rfl
    · exact (R.portals (R.parent C)).left_radial.2
    · exact (R.portals (R.parent C)).right_radial.2
  have hs : (k : ℝ) * R.δ + R.δ ≤ dist R.base v := by
    rcases hv with rfl | rfl
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).left_radial.1
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).right_radial.1
  linarith [dist_triangle R.base u v, R.width_pos]

/-- Atom names use depth, portal column and type. Equal portals therefore have
one name and one noise, including the root's single tentative atom. -/
def atomName (k : ℕ) (v : M.Point J root) (j : Fin 3) : ℕ :=
  3 * (n * k + v.column.val) + j.val

lemma atomName_bounds (k : ℕ) (v : M.Point J root) (j : Fin 3) :
    3 * n * k ≤ atomName k v j ∧ atomName k v j < 3 * n * (k + 1) := by
  simp only [atomName, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have := v.column.isLt
  have := j.isLt
  constructor <;> omega

/-- A complete noise assignment. Bounds and independence are imposed on the
actual probability space later, not assumed properties of the output. -/
abbrev Noise := ℕ → Fin n → Fin 3 → ℝ

open Interpolation

noncomputable def tentative (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) : NamedValue :=
  minNamed
    ⟨atomName k (R.portals C).left 0,
      p (R.portals C).left + dist (R.portals C).left v + α k (R.portals C).left.column 0⟩
    ⟨atomName k (R.portals C).right 0,
      p (R.portals C).right + dist (R.portals C).right v + α k (R.portals C).right.column 0⟩

noncomputable def upperCone (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) : NamedValue :=
  minNamed
    ⟨atomName k (R.portals C).left 1,
      (F (R.portals C).left).value + dist (R.portals C).left v - α k (R.portals C).left.column 1⟩
    ⟨atomName k (R.portals C).right 1,
      (F (R.portals C).right).value + dist (R.portals C).right v - α k (R.portals C).right.column 1⟩

noncomputable def lowerCone (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) : NamedValue :=
  maxNamed
    ⟨atomName k (R.portals C).left 2,
      (F (R.portals C).left).value - dist (R.portals C).left v + α k (R.portals C).left.column 2⟩
    ⟨atomName k (R.portals C).right 2,
      (F (R.portals C).right).value - dist (R.portals C).right v + α k (R.portals C).right.column 2⟩

/-- The manuscript's recursive named formulas, on the whole metric component. -/
noncomputable def formula (p : M.Point J root → ℝ) (α : Noise (n := n)) :
    (k : ℕ) → R.Node k → M.Point J root → NamedValue
  | 0, C, v => R.tentative p α C v
  | k + 1, C, v =>
    let F := formula p α k (R.parent C)
    nodeNamed (F v) (R.upperCone F α C v) (R.lowerCone F α C v) (R.tentative p α C v)

lemma tentative_names (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    3 * n * k ≤ (R.tentative p α C v).name ∧
      (R.tentative p α C v).name < 3 * n * (k + 1) := by
  rcases minNamed_mem _ _ with h | h
  · rw [tentative, h]
    exact atomName_bounds k (R.portals C).left 0
  · rw [tentative, h]
    exact atomName_bounds k (R.portals C).right 0

lemma upperCone_names (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    3 * n * k ≤ (R.upperCone F α C v).name ∧
      (R.upperCone F α C v).name < 3 * n * (k + 1) := by
  rcases minNamed_mem _ _ with h | h
  · rw [upperCone, h]
    exact atomName_bounds k (R.portals C).left 1
  · rw [upperCone, h]
    exact atomName_bounds k (R.portals C).right 1

lemma lowerCone_names (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    3 * n * k ≤ (R.lowerCone F α C v).name ∧
      (R.lowerCone F α C v).name < 3 * n * (k + 1) := by
  rcases maxNamed_mem _ _ with h | h
  · rw [lowerCone, h]
    exact atomName_bounds k (R.portals C).left 2
  · rw [lowerCone, h]
    exact atomName_bounds k (R.portals C).right 2

lemma formula_name_bound (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (v : M.Point J root) :
    (R.formula p α k C v).name < 3 * n * (k + 1) := by
  induction k with
  | zero => exact (R.tentative_names p α C v).2
  | succ k ih =>
    rw [formula]
    rcases nodeNamed_mem _ _ _ _ with h | h | h | h
    · rw [h]
      exact (ih (R.parent C)).trans_le (Nat.mul_le_mul_left (3 * n) (Nat.le_succ (k + 1)))
    · rw [h]
      exact (R.upperCone_names _ _ _ _).2
    · rw [h]
      exact (R.lowerCone_names _ _ _ _).2
    · rw [h]
      exact (R.tentative_names _ _ _ _).2

lemma tentative_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) : LipschitzWith 1 (fun v => (R.tentative p α C v).value) := by
  let l := (R.portals C).left
  let r := (R.portals C).right
  have hl := (distance_cone_lipschitz l (p l + α k l.column 0)).1
  have hr := (distance_cone_lipschitz r (p r + α k r.column 0)).1
  simpa only [tentative, minNamed_value, max_self, add_right_comm] using hl.min hr

lemma upperCone_lipschitz (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) : LipschitzWith 1 (fun v => (R.upperCone F α C v).value) := by
  let l := (R.portals C).left
  let r := (R.portals C).right
  have hl := (distance_cone_lipschitz l ((F l).value - α k l.column 1)).1
  have hr := (distance_cone_lipschitz r ((F r).value - α k r.column 1)).1
  simpa only [upperCone, minNamed_value, max_self, sub_add_eq_add_sub] using hl.min hr

lemma lowerCone_lipschitz (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) : LipschitzWith 1 (fun v => (R.lowerCone F α C v).value) := by
  let l := (R.portals C).left
  let r := (R.portals C).right
  have hl := (distance_cone_lipschitz l ((F l).value + α k l.column 2)).2
  have hr := (distance_cone_lipschitz r ((F r).value + α k r.column 2)).2
  simpa only [lowerCone, maxNamed_value, max_self, sub_add_eq_add_sub] using hl.max hr

lemma formula_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) : LipschitzWith 1 (fun v => (R.formula p α k C v).value) := by
  induction k with
  | zero => exact R.tentative_lipschitz p α C
  | succ k ih =>
    simpa only [formula, nodeNamed_value] using
      nodeValue_lipschitz (ih (R.parent C)) (R.upperCone_lipschitz _ _ _)
        (R.lowerCone_lipschitz _ _ _) (R.tentative_lipschitz _ _ _)

noncomputable def q : ℝ := R.ζ * R.δ / 20

lemma q_pos : 0 < R.q := div_pos (mul_pos R.zeta_pos R.delta_pos) (by norm_num)

lemma q_small : 2 * R.q ≤ R.δ / 10 := by
  have h := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
  dsimp [q]
  linarith

def NoiseBounds (α : Noise (n := n)) : Prop :=
  ∀ k i j, R.q ≤ α k i j ∧ α k i j ≤ 2 * R.q

def InputLip (p : M.Point J root → ℝ) : Prop :=
  ∀ x y, |p x - p y| ≤ (1 - R.ζ) * dist x y

noncomputable def portalDistance {k : ℕ} (C : R.Node k) (v : M.Point J root) : ℝ :=
  min (dist (R.portals C).left v) (dist (R.portals C).right v)

lemma portalDistance_nonneg {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    0 ≤ R.portalDistance C v := le_min dist_nonneg dist_nonneg

lemma tentative_bounds {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    p v + R.ζ * R.portalDistance C v + R.q ≤ (R.tentative p α C v).value ∧
    (R.tentative p α C v).value ≤ p v + (2 - R.ζ) * R.portalDistance C v + 2 * R.q := by
  have atom (w : M.Point J root) :
      p v + R.ζ * dist w v + R.q ≤ p w + dist w v + α k w.column 0 ∧
      p w + dist w v + α k w.column 0 ≤ p v + (2 - R.ζ) * dist w v + 2 * R.q := by
    have hlip := abs_le.mp (hp w v)
    have hn := hα k w.column 0
    constructor <;> nlinarith
  have hleft := atom (R.portals C).left
  have hright := atom (R.portals C).right
  simp only [tentative, minNamed_value]
  constructor
  · apply le_min
    · have hd := mul_le_mul_of_nonneg_left
        (min_le_left (dist (R.portals C).left v) (dist (R.portals C).right v)) R.zeta_pos.le
      dsimp [portalDistance]
      linarith
    · have hd := mul_le_mul_of_nonneg_left
        (min_le_right (dist (R.portals C).left v) (dist (R.portals C).right v)) R.zeta_pos.le
      dsimp [portalDistance]
      linarith
  · rcases le_total (dist (R.portals C).left v) (dist (R.portals C).right v) with h | h
    · rw [portalDistance, min_eq_left h]
      exact (min_le_left _ _).trans hleft.2
    · rw [portalDistance, min_eq_right h]
      exact (min_le_right _ _).trans hright.2

lemma cone_bounds {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k)
    (F : M.Point J root → NamedValue)
    (hF : ∀ w, w = (R.portals C).left ∨ w = (R.portals C).right →
      |(F w).value - p w| ≤ 5 * R.δ) (v : M.Point J root) :
    p v - 5 * R.δ + R.ζ * R.portalDistance C v - 2 * R.q ≤ (R.upperCone F α C v).value ∧
    (R.lowerCone F α C v).value ≤ p v + 5 * R.δ - R.ζ * R.portalDistance C v + 2 * R.q := by
  have atom (w : M.Point J root) (hw : w = (R.portals C).left ∨ w = (R.portals C).right)
      (hd : R.portalDistance C v ≤ dist w v) :
      p v - 5 * R.δ + R.ζ * R.portalDistance C v - 2 * R.q ≤
        (F w).value + dist w v - α k w.column 1 ∧
      (F w).value - dist w v + α k w.column 2 ≤
        p v + 5 * R.δ - R.ζ * R.portalDistance C v + 2 * R.q := by
    have hlip := abs_le.mp (hp w v)
    have ha := abs_le.mp (hF w hw)
    have hn₁ := hα k w.column 1
    have hn₂ := hα k w.column 2
    have hz := mul_le_mul_of_nonneg_left hd R.zeta_pos.le
    constructor <;> nlinarith
  have hl := atom (R.portals C).left (Or.inl rfl) (min_le_left _ _)
  have hr := atom (R.portals C).right (Or.inr rfl) (min_le_right _ _)
  exact ⟨by simpa only [upperCone, minNamed_value, le_min_iff] using And.intro hl.1 hr.1,
    by simpa only [lowerCone, maxNamed_value, max_le_iff] using And.intro hl.2 hr.2⟩

/-- With the thin-band constants, every nearby tentative value lies in the
same three-delta window used in the manuscript's induction. -/
lemma tentative_near {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k) (v : M.Point J root)
    (hn : R.portalDistance C v ≤ R.δ + 220 * R.a) :
    p v ≤ (R.tentative p α C v).value ∧ (R.tentative p α C v).value ≤ p v + 3 * R.δ := by
  obtain ⟨hl, hu⟩ := R.tentative_bounds hp hα C v
  have hd := R.portalDistance_nonneg C v
  have hz := R.zeta_pos
  have hδ := R.delta_pos
  constructor
  · nlinarith [R.q_pos]
  · have h := mul_le_mul_of_nonneg_left hn (by linarith [R.zeta_lt_one] : 0 ≤ 2 - R.ζ)
    have hw := R.width_small
    have hq := R.q_small
    nlinarith [R.width_pos, mul_nonneg hz.le hd]

/-- Exact named inheritance on the genuine entrance collar. -/
lemma formula_collar (p : M.Point J root → ℝ) {α : Noise (n := n)}
    (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root)
    (hc : R.portalDistance C v ≤ R.ζ * R.δ / 50) :
    R.formula p α (k + 1) C v = R.formula p α k (R.parent C) v := by
  let F := R.formula p α k (R.parent C)
  have hF := R.formula_lipschitz p α k (R.parent C)
  have hcq : 2 * (R.ζ * R.δ / 50) < R.q := by
    dsimp [q]
    nlinarith [mul_pos R.zeta_pos R.delta_pos]
  have single (w : M.Point J root) (hw : dist w v ≤ R.ζ * R.δ / 50) :
      (F w).value + dist w v - α (k + 1) w.column 1 < (F v).value ∧
      (F v).value < (F w).value - dist w v + α (k + 1) w.column 2 := by
    have hlip := hF.dist_le_mul w v
    change |(F w).value - (F v).value| ≤ (1 : ℝ) * dist w v at hlip
    simp only [one_mul, abs_le] at hlip
    have hn₁ := hα (k + 1) w.column 1
    have hn₂ := hα (k + 1) w.column 2
    constructor <;> linarith
  have hcones : (R.upperCone F α C v).value < (F v).value ∧
      (F v).value < (R.lowerCone F α C v).value := by
    simp only [upperCone, lowerCone, minNamed_value, maxNamed_value]
    rcases min_le_iff.mp hc with h | h
    · have hs := single (R.portals C).left h
      exact ⟨lt_of_le_of_lt (min_le_left _ _) hs.1,
        lt_of_lt_of_le hs.2 (le_max_left _ _)⟩
    · have hs := single (R.portals C).right h
      exact ⟨lt_of_le_of_lt (min_le_right _ _) hs.1,
        lt_of_lt_of_le hs.2 (le_max_right _ _)⟩
  change nodeNamed (F v) _ _ _ = F v
  apply nodeNamed_collar hcones.1 hcones.2
  exact (R.formula_name_bound p α k (R.parent C) v).le.trans
    (R.tentative_names p α C v).1


lemma portal_spacing : 2 * R.q ≤ R.ζ * (R.δ - 10 * R.a) := by
  have hw : R.δ / 10 ≤ R.δ - 10 * R.a := by linarith [R.width_small, R.delta_pos]
  have hh := mul_le_mul_of_nonneg_left hw R.zeta_pos.le
  dsimp [q]
  nlinarith

/-- The complete quantitative induction on the ACTUAL component hierarchy.
The second bound applies to child portals; the first applies on the own layer. -/
lemma formula_near_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hn : R.portalDistance C v ≤ R.δ + 220 * R.a) :
    |(R.formula p α k C v).value - p v| ≤ 5 * R.δ + 2 * R.q ∧
    (2 * R.q ≤ R.ζ * R.portalDistance C v →
      |(R.formula p α k C v).value - p v| ≤ 5 * R.δ) := by
  induction k generalizing v with
  | zero =>
    have hT := R.tentative_near hp hα C v hn
    simp only [formula, abs_le]
    constructor
    · constructor <;> linarith [R.delta_pos, R.q_pos]
    · intro _
      constructor <;> linarith [R.delta_pos]
  | succ k ih =>
    let F := R.formula p α k (R.parent C)
    have hF : ∀ w, w = (R.portals C).left ∨ w = (R.portals C).right →
        |(F w).value - p w| ≤ 5 * R.δ := by
      intro w hw
      have hn' : R.portalDistance (R.parent C) w ≤ R.δ + 220 * R.a := by
        simpa only [portalDistance, dist_comm w] using R.parent_near C w hw
      have hd : R.δ - 10 * R.a ≤ R.portalDistance (R.parent C) w :=
        le_min (R.parent_separated C _ w (Or.inl rfl) hw)
          (R.parent_separated C _ w (Or.inr rfl) hw)
      have hs := R.portal_spacing.trans (mul_le_mul_of_nonneg_left hd R.zeta_pos.le)
      exact (ih (R.parent C) w hn').2 hs
    obtain ⟨hA, hB⟩ := R.cone_bounds hp hα C F hF v
    obtain ⟨hTlo, hThi⟩ := R.tentative_near hp hα C v hn
    have hval : (R.formula p α (k + 1) C v).value =
        nodeValue (F v).value (R.upperCone F α C v).value
          (R.lowerCone F α C v).value (R.tentative p α C v).value := by
      simp only [formula, nodeNamed_value, F]
    have bound (e : ℝ) (he : 3 * R.δ ≤ e)
        (hu : 5 * R.δ - R.ζ * R.portalDistance C v + 2 * R.q ≤ e) :
        |(R.formula p α (k + 1) C v).value - p v| ≤ e := by
      have hb := nodeValue_bounds (parent := (F v).value)
        (lo := p v - e) (hi := p v + e)
        (show p v - e ≤ (R.upperCone F α C v).value by linarith)
        (show (R.lowerCone F α C v).value ≤ p v + e by linarith)
        (show p v - e ≤ (R.tentative p α C v).value by linarith [R.delta_pos])
        (show (R.tentative p α C v).value ≤ p v + e by linarith)
      rw [hval, abs_le]
      constructor <;> linarith
    constructor
    · apply bound (5 * R.δ + 2 * R.q)
      · linarith [R.delta_pos, R.q_pos]
      · nlinarith [mul_nonneg R.zeta_pos.le (R.portalDistance_nonneg C v)]
    · intro hs
      exact bound (5 * R.δ) (by linarith [R.delta_pos]) (by linarith)

lemma formula_layer_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k) (v : M.Point J root)
    (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hr : dist R.base (v.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ) :
    |(R.formula p α k C v).value - p v| ≤ 6 * R.δ := by
  have hn : R.portalDistance C v ≤ R.δ + 220 * R.a := by
    have hh : dist R.base (v.withHeight R.base.height R.base.inBand) < (k : ℝ) * R.δ + R.δ := by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hr
    simpa only [portalDistance, dist_comm v] using
      (R.portals C).near_layer R.half_width R.width_pos.le v hv hh
  have ha := (R.formula_near_accuracy hp hα k C v hn).1
  linarith [R.q_small, R.delta_pos]


/-- The unique depth of the layer assigned to a column. -/
noncomputable def layerDepth (v : M.Point J root) : ℕ :=
  ⌊dist R.base (v.withHeight R.base.height R.base.inBand) / R.δ⌋₊

lemma layerDepth_bounds (v : M.Point J root) :
    (R.layerDepth v : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand) ∧
    dist R.base (v.withHeight R.base.height R.base.inBand) < (R.layerDepth v + 1 : ℕ) * R.δ := by
  have hl := Nat.floor_le (div_nonneg (dist_nonneg (x := R.base)
    (y := v.withHeight R.base.height R.base.inBand)) R.delta_pos.le)
  have hu := Nat.lt_floor_add_one
    (dist R.base (v.withHeight R.base.height R.base.inBand) / R.δ)
  constructor
  · exact (le_div_iff₀ R.delta_pos).mp hl
  · simpa only [layerDepth, Nat.cast_add, Nat.cast_one] using (div_lt_iff₀ R.delta_pos).mp hu

lemma layerDepth_eq {k : ℕ} (v : M.Point J root)
    (hl : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (hu : dist R.base (v.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ) :
    R.layerDepth v = k := by
  apply (Nat.floor_eq_iff (div_nonneg dist_nonneg R.delta_pos.le)).mpr
  refine ⟨(le_div_iff₀ R.delta_pos).mpr hl, ?_⟩
  apply (div_lt_iff₀ R.delta_pos).mpr
  simpa only [Nat.cast_add, Nat.cast_one] using hu

noncomputable def nodeOf (k : ℕ) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) : R.Node k :=
  ((M.activeGraph J).induce _).connectedComponentMk
    ⟨v.column, (R.base.mem_superlevel_iff v R.base.height R.base.inBand (k * R.δ)).mpr hv⟩

lemma mem_nodeOf (k : ℕ) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) :
    v.column ∈ ColumnOrder.componentColumns (R.nodeOf k v hv) :=
  ⟨⟨v.column, (R.base.mem_superlevel_iff v R.base.height R.base.inBand (k * R.δ)).mpr hv⟩, rfl, rfl⟩

noncomputable def layerNode (v : M.Point J root) : R.Node (R.layerDepth v) :=
  R.nodeOf (R.layerDepth v) v (R.layerDepth_bounds v).1

lemma mem_layerNode (v : M.Point J root) :
    v.column ∈ ColumnOrder.componentColumns (R.layerNode v) :=
  R.mem_nodeOf (R.layerDepth v) v (R.layerDepth_bounds v).1

/-- The actual pasted named output on representatives. -/
noncomputable def pasted (p : M.Point J root → ℝ) (α : Noise (n := n)) (v : M.Point J root) : NamedValue :=
  R.formula p α (R.layerDepth v) (R.layerNode v) v

lemma pasted_eq_of_layer (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root)
    (hm : v.column ∈ ColumnOrder.componentColumns C)
    (hl : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (hu : dist R.base (v.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ) :
    R.pasted p α v = R.formula p α k C v := by
  have hd := R.layerDepth_eq v hl hu
  subst k
  have he : R.layerNode v = C := ColumnOrder.component_eq_of_column (R.mem_layerNode v) hm
  simp only [pasted, he]

lemma pasted_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (v : M.Point J root) :
    |(R.pasted p α v).value - p v| ≤ 6 * R.δ :=
  R.formula_layer_accuracy hp hα (R.layerNode v) v (R.mem_layerNode v) (R.layerDepth_bounds v).2

noncomputable def radius : ℝ := R.ζ * R.δ / 1000

lemma radius_pos : 0 < R.radius := div_pos (mul_pos R.zeta_pos R.delta_pos) (by norm_num)

lemma radius_bounds {ρ : ℝ} (hρ : ρ ≤ R.radius) :
    2 * ρ + R.a < R.δ ∧ 2 * ρ + 200 * R.a ≤ R.ζ * R.δ / 50 := by
  have hw := R.width_bound
  have hd := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
  have hz := mul_pos R.zeta_pos R.delta_pos
  dsimp [radius] at hρ
  constructor <;> nlinarith

/-- One deterministic node formula, with identical atom names, represents the
pasted output on the whole small ball (including every zero-distance copy).
The node exists independently of the noises and the input. -/
lemma common_formula (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius) :
    ∃ k : ℕ, ∃ C : R.Node k,
      (∀ z : M.Point J root, dist x z ≤ ρ →
        (k : ℝ) * R.δ ≤ dist R.base (z.withHeight R.base.height R.base.inBand)) ∧
      (∀ (p : M.Point J root → ℝ) (α : Noise (n := n)), R.NoiseBounds α →
        ∀ z : M.Point J root, dist x z ≤ ρ → R.pasted p α z = R.formula p α k C z) := by
  obtain ⟨k, y, C, hy, hylo, hC⟩ := R.base.ball_two_layers R.closed_band x R.base.inBand
    hρ R.delta_pos R.half_width (R.radius_bounds hs).1
  refine ⟨k, C, fun z hz => (hC z hz).2.1, ?_⟩
  intro p α hα z hz
  obtain ⟨hzm, hzl, hzu⟩ := hC z hz
  by_cases hlo : dist R.base (z.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ
  · exact R.pasted_eq_of_layer p α C z hzm hzl hlo
  · have hzl' := le_of_not_gt hlo
    let D := R.nodeOf (k + 1) z hzl'
    have hD := R.mem_nodeOf (k + 1) z hzl'
    have hparent : R.parent D = C :=
      ColumnOrder.component_eq_of_column (R.mem_parent D hD) hzm
    have hyout : y.column ∉ ColumnOrder.componentColumns D := by
      intro hym
      have hry := (R.base.mem_superlevel_iff y R.base.height R.base.inBand (((k + 1 : ℕ) : ℝ) * R.δ)).mp
        (ColumnOrder.componentColumns_subset D hym)
      have hyp : dist R.base (y.withHeight R.base.height R.base.inBand) < ((k + 1 : ℕ) : ℝ) * R.δ := by
        simpa only [Nat.cast_add, Nat.cast_one] using hylo
      exact hyp.not_ge hry
    have hexit := (R.portals D).near_exit R.closed_band z y hD hyout
    have hzy : dist z y ≤ 2 * ρ := by
      have ht := dist_triangle z x y
      rw [dist_comm z x] at ht
      linarith
    have hcollar : R.portalDistance D z ≤ R.ζ * R.δ / 50 := by
      dsimp only [portalDistance]
      simp only [dist_comm z] at hexit
      rw [dist_comm y z] at hexit
      linarith [(R.radius_bounds hs).2]
    have hupper : dist R.base (z.withHeight R.base.height R.base.inBand) < ((k + 1 + 1 : ℕ) : ℝ) * R.δ := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hzu
    rw [R.pasted_eq_of_layer p α D z hD hzl' hupper,
      R.formula_collar p hα D z hcollar, hparent]

lemma formula_congr_zero (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (x y : M.Point J root) (hxy : dist x y = 0) :
    R.formula p α k C x = R.formula p α k C y := by
  have hd (w : M.Point J root) : dist w x = dist w y := by
    apply le_antisymm
    · have ht := dist_triangle w y x
      rw [dist_comm y x, hxy, add_zero] at ht
      exact ht
    · have ht := dist_triangle w x y
      rw [hxy, add_zero] at ht
      exact ht
  induction k with
  | zero => simp only [formula, tentative, hd]
  | succ k ih => simp only [formula, tentative, upperCone, lowerCone, hd, ih]

lemma pasted_congr_zero (p : M.Point J root → ℝ) {α : Noise (n := n)}
    (hα : R.NoiseBounds α) (x y : M.Point J root) (hxy : dist x y = 0) :
    R.pasted p α x = R.pasted p α y := by
  obtain ⟨k, C, _, hC⟩ := R.common_formula x R.radius_pos.le le_rfl
  rw [hC p α hα x (by simpa using R.radius_pos.le), hC p α hα y (by simpa [hxy] using R.radius_pos.le)]
  exact R.formula_congr_zero p α k C x y hxy

lemma pasted_local_lipschitz (p : M.Point J root → ℝ) {α : Noise (n := n)}
    (hα : R.NoiseBounds α) (x y : M.Point J root) (hxy : dist x y ≤ R.radius) :
    |(R.pasted p α x).value - (R.pasted p α y).value| ≤ dist x y := by
  obtain ⟨k, C, _, hC⟩ := R.common_formula x R.radius_pos.le le_rfl
  rw [hC p α hα x (by simpa using R.radius_pos.le), hC p α hα y hxy]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using (R.formula_lipschitz p α k C).dist_le_mul x y

/-- Uniform local unit bounds extend globally by genuine shortest-path
interpolation. No length-space axiom has been added. -/
lemma pasted_lipschitz (p : M.Point J root → ℝ) {α : Noise (n := n)} (hα : R.NoiseBounds α) :
    LipschitzWith 1 (fun v => (R.pasted p α v).value) := by
  have bound (m : ℕ) : ∀ x y : M.Point J root, dist x y ≤ m * R.radius →
      |(R.pasted p α x).value - (R.pasted p α y).value| ≤ dist x y := by
    induction m with
    | zero =>
      intro x y hxy
      have hzero : dist x y ≤ 0 := by simpa only [Nat.cast_zero, zero_mul] using hxy
      exact R.pasted_local_lipschitz p hα x y (hzero.trans R.radius_pos.le)
    | succ m ih =>
      intro x y hxy
      by_cases hsmall : dist x y ≤ R.radius
      · exact R.pasted_local_lipschitz p hα x y hsmall
      · obtain ⟨z, hxz, hzy⟩ := x.exists_between R.closed_band R.interval_band y
          R.radius_pos.le (le_of_not_ge hsmall)
        have hzsmall : dist z y ≤ m * R.radius := by
          simp only [Nat.cast_succ, add_mul, one_mul] at hxy
          linarith
        have h₁ := R.pasted_local_lipschitz p hα x z hxz.le
        have h₂ := ih z y hzsmall
        have htri := abs_sub_le (R.pasted p α x).value (R.pasted p α z).value (R.pasted p α y).value
        linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨m, hm⟩ := exists_nat_ge (dist x y / R.radius)
  have hdist := bound m x y ((div_le_iff₀ R.radius_pos).mp hm)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hdist


/-- Ancestors are constructed by inclusion of actual superlevel components. -/
def ancestor {k : ℕ} (C : R.Node k) (j : ℕ) (hj : j ≤ k) : R.Node j :=
  ColumnOrder.componentAbove (R.superlevel_antitone hj) C

lemma mem_ancestor {k : ℕ} (C : R.Node k) (j : ℕ) (hj : j ≤ k) :
    ColumnOrder.componentColumns C ⊆ ColumnOrder.componentColumns (R.ancestor C j hj) :=
  ColumnOrder.componentColumns_above _ C

lemma ancestor_self {k : ℕ} (C : R.Node k) (h : k ≤ k) : R.ancestor C k h = C := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  exact ColumnOrder.component_eq_of_column (R.mem_ancestor C k h ⟨i, hi, rfl⟩) ⟨i, hi, rfl⟩

lemma ancestor_parent {k j : ℕ} (C : R.Node (k + 1)) (hj : j ≤ k) :
    R.ancestor (R.parent C) j hj = R.ancestor C j (hj.trans (Nat.le_succ k)) := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  have hm : i.val ∈ ColumnOrder.componentColumns C := ⟨i, hi, rfl⟩
  exact ColumnOrder.component_eq_of_column
    (R.mem_ancestor (R.parent C) j hj (R.mem_parent C hm)) (R.mem_ancestor C j _ hm)

/-- The source's lookback constant, independent of diameter and tree depth. -/
noncomputable def lookback : ℕ := ⌈15 / R.ζ⌉₊ + 3


/-- The fixed enumeration remembers whichever portal occurrence generated a
name. Duplicated portals still produce the same name. -/
noncomputable def portalAt {k : ℕ} (C : R.Node k) (i : Fin 2) : M.Point J root :=
  if i = 0 then (R.portals C).left else (R.portals C).right

noncomputable def nodeNames {k : ℕ} (C : R.Node k) : Finset ℕ :=
  Finset.univ.image (fun ij : Fin 2 × Fin 3 => atomName k (R.portalAt C ij.1) ij.2)

/-- The deterministic, diameter-independent list at a node. -/
noncomputable def recentNames {k : ℕ} (C : R.Node k) (L : ℕ) : Finset ℕ :=
  (Finset.Icc (k - L) k).attach.biUnion
    (fun j => R.nodeNames (R.ancestor C j (Finset.mem_Icc.mp j.property).2))

lemma portalAt_height {k : ℕ} (C : R.Node k) (i : Fin 2) :
    (R.portalAt C i).height = R.base.height := by
  dsimp only [portalAt]
  split
  · exact (R.portals C).left_height
  · exact (R.portals C).right_height

lemma portalAt_eq_of_column {k : ℕ} (C : R.Node k) (i i' : Fin 2)
    (h : (R.portalAt C i).column = (R.portalAt C i').column) :
    R.portalAt C i = R.portalAt C i' := by
  have hh := (R.portalAt_height C i).trans (R.portalAt_height C i').symm
  have hext : ∀ x y : M.Point J root, x.column = y.column → x.height = y.height → x = y := by
    rintro ⟨xc, xh, xb, xr⟩ ⟨yc, yh, yb, yr⟩ hc hh
    cases hc
    cases hh
    rfl
  exact hext _ _ h hh

lemma atomName_same_depth {k : ℕ} (u v : M.Point J root) (t t' : Fin 3)
    (h : atomName k u t = atomName k v t') : u.column = v.column ∧ t = t' := by
  have ht := t.isLt
  have ht' := t'.isLt
  simp only [atomName] at h
  constructor <;> apply Fin.ext <;> omega

/-- A node's parent intercept uses no noise from the current depth. The
root convention below merely fills unused clamping slots with the fixed input. -/
noncomputable def parentValue (p : M.Point J root → ℝ) (α : Noise (n := n)) :
    (k : ℕ) → R.Node k → M.Point J root → ℝ
  | 0, _, v => p v
  | k + 1, C, v => (R.formula p α k (R.parent C) v).value

noncomputable def atomIntercept (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) : ℝ :=
  (if t = 0 then p (R.portalAt C i) else R.parentValue p α k C (R.portalAt C i)) +
    (if t = 2 then -dist (R.portalAt C i) v else dist (R.portalAt C i) v)

noncomputable def nodeAtom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) : NamedValue :=
  ⟨atomName k (R.portalAt C i) t,
    R.atomIntercept p α C i t v +
      (if t = 1 then -α k (R.portalAt C i).column t else α k (R.portalAt C i).column t)⟩

lemma tentative_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    ∃ i : Fin 2, R.tentative p α C v = R.nodeAtom p α C i 0 v := by
  rcases minNamed_mem _ _ with h | h
  · refine ⟨0, ?_⟩
    rw [tentative, h]
    simp [nodeAtom, atomIntercept, portalAt]
  · refine ⟨1, ?_⟩
    rw [tentative, h]
    simp [nodeAtom, atomIntercept, portalAt]

lemma upperCone_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root) :
    ∃ i : Fin 2, R.upperCone (R.formula p α k (R.parent C)) α C v = R.nodeAtom p α C i 1 v := by
  rcases minNamed_mem _ _ with h | h
  · refine ⟨0, ?_⟩
    rw [upperCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]
  · refine ⟨1, ?_⟩
    rw [upperCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]

lemma lowerCone_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root) :
    ∃ i : Fin 2, R.lowerCone (R.formula p α k (R.parent C)) α C v = R.nodeAtom p α C i 2 v := by
  rcases maxNamed_mem _ _ with h | h
  · refine ⟨0, ?_⟩
    rw [lowerCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]
  · refine ⟨1, ?_⟩
    rw [lowerCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]

/-- Selection is of literal named functions, not just numerical atom names. -/
lemma formula_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (v : M.Point J root) :
    ∃ j : ℕ, ∃ hj : j ≤ k, ∃ i : Fin 2, ∃ t : Fin 3,
      R.formula p α k C v = R.nodeAtom p α (R.ancestor C j hj) i t v := by
  induction k with
  | zero =>
    obtain ⟨i, hi⟩ := R.tentative_eq_atom p α C v
    exact ⟨0, le_rfl, i, 0, by simpa only [formula, R.ancestor_self] using hi⟩
  | succ k ih =>
    rw [formula]
    rcases nodeNamed_mem _ _ _ _ with h | h | h | h
    · obtain ⟨j, hj, i, t, heq⟩ := ih (R.parent C)
      refine ⟨j, hj.trans (Nat.le_succ k), i, t, ?_⟩
      rw [h, ← R.ancestor_parent C hj]
      exact heq
    · obtain ⟨i, hi⟩ := R.upperCone_eq_atom p α C v
      exact ⟨k + 1, le_rfl, i, 1, by simpa only [h, R.ancestor_self] using hi⟩
    · obtain ⟨i, hi⟩ := R.lowerCone_eq_atom p α C v
      exact ⟨k + 1, le_rfl, i, 2, by simpa only [h, R.ancestor_self] using hi⟩
    · obtain ⟨i, hi⟩ := R.tentative_eq_atom p α C v
      exact ⟨k + 1, le_rfl, i, 0, by simpa only [h, R.ancestor_self] using hi⟩

lemma nodeAtom_eq_of_name (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i i' : Fin 2) (t t' : Fin 3)
    (h : atomName k (R.portalAt C i) t = atomName k (R.portalAt C i') t') :
    R.nodeAtom p α C i t = R.nodeAtom p α C i' t' := by
  obtain ⟨hc, rfl⟩ := atomName_same_depth _ _ _ _ h
  have he := R.portalAt_eq_of_column C i i' hc
  funext v
  simp only [nodeAtom, atomIntercept, he]

/-- Explicit positions in the ancestor chain. The name, not this occurrence,
is the randomized identity; opposite portal occurrences may coincide. -/
abbrev ChainIndex (k : ℕ) := Fin (k + 1) × Fin 2 × Fin 3

noncomputable def chainName {k : ℕ} (C : R.Node k) (u : ChainIndex k) : ℕ :=
  atomName u.1 (R.portalAt (R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)) u.2.1) u.2.2

noncomputable def chainAtom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (u : ChainIndex k) : M.Point J root → NamedValue :=
  R.nodeAtom p α (R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)) u.2.1 u.2.2

lemma recentNames_representation {k : ℕ} (C : R.Node k) (L m : ℕ)
    (hm : m ∈ R.recentNames C L) : ∃ u : ChainIndex k, R.chainName C u = m := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨⟨i,t⟩, _, he⟩ := Finset.mem_image.mp hj
  exact ⟨(⟨j.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp j.property).2⟩, i, t), he⟩

noncomputable def representative {k : ℕ} (C : R.Node k) (L m : ℕ)
    (hm : m ∈ R.recentNames C L) : ChainIndex k :=
  (R.recentNames_representation C L m hm).choose

/-- A fixed representation for each name, chosen from geometry before noises.
Off the list the harmless zero branch makes this a total function. -/
noncomputable def listedAtom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (L m : ℕ) (v : M.Point J root) : NamedValue :=
  if hm : m ∈ R.recentNames C L then R.chainAtom p α C (R.representative C L m hm) v
  else ⟨m, 0⟩

/-- Replacement of exactly one current interpolation noise. -/
noncomputable def replaceNoise (α : Noise (n := n)) (d : ℕ) (c : Fin n) (t : Fin 3) (r : ℝ) :
    Noise (n := n) := fun j i s => if j = d ∧ i = c ∧ s = t then r else α j i s

/-- The finite noise sample space used by the construction. -/
abbrev GridSample (cap m : ℕ) := (Fin cap × Fin n × Fin 3) → Fin (m + 1)

noncomputable def gridNoise (cap m : ℕ) (ω : GridSample (n := n) cap m) : Noise (n := n) :=
  fun j i t => if hj : j < cap then R.q + R.q / m * (ω (⟨j,hj⟩,i,t)).val else R.q

lemma gridNoise_bounds (cap m : ℕ) (hm : 0 < m) (ω : GridSample (n := n) cap m) :
    R.NoiseBounds (R.gridNoise cap m ω) := by
  intro j i t
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hstep : 0 < R.q / m := div_pos R.q_pos hm'
  have hmul : R.q / (m : ℝ) * m = R.q := div_mul_cancel₀ R.q (ne_of_gt hm')
  simp only [gridNoise]
  split_ifs with hj
  · have hval : ((ω (⟨j,hj⟩,i,t)).val : ℝ) ≤ m := by
      exact_mod_cast Nat.le_of_lt_succ (ω (⟨j,hj⟩,i,t)).isLt
    have hhi := mul_le_mul_of_nonneg_left hval hstep.le
    rw [hmul] at hhi
    have hlo := mul_nonneg hstep.le (Nat.cast_nonneg (ω (⟨j,hj⟩,i,t)).val)
    constructor <;> linarith
  · constructor <;> linarith [R.q_pos]

/-- The radial profile has only finitely many values, one per reachable column.
This explicit cap bounds every node ever used by the pasted field. -/
noncomputable def depthCap : ℕ := by
  classical
  exact 1 + ∑ i : Fin n,
    if hi : (M.activeGraph J).Reachable root i then
      ⌊dist R.base (⟨i, R.base.height, R.base.inBand, hi⟩ : M.Point J root) / R.δ⌋₊ else 0

lemma layerDepth_lt_cap (v : M.Point J root) : R.layerDepth v < R.depthCap := by
  classical
  let g : Fin n → ℕ := fun i => if hi : (M.activeGraph J).Reachable root i then
    ⌊dist R.base (⟨i, R.base.height, R.base.inBand, hi⟩ : M.Point J root) / R.δ⌋₊ else 0
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := g) (fun i _ => Nat.zero_le (g i))
    (Finset.mem_univ v.column)
  have he : R.layerDepth v = g v.column := by
    simp only [g, dite_eq_left v.reachable, layerDepth, withHeight]
  dsimp only [depthCap]
  change R.layerDepth v < 1 + ∑ i, g i
  omega

end RadialTree


end Point

end Model
end Columns
end PlanarL1

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model

open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

lemma Field.widen_lipschitz (F : M.Field I 1) (hJI : J ⊆ I) (hJ : IsClosed J) :
    LipschitzWith 1 (fun x : M.Point J root => F.eval (x.widen hJI)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  have hf := F.path_bound (p.widen hJI) ⟨x.height,hJI x.inBand⟩ ⟨y.height,hJI y.inBand⟩
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, Path.length_widen,hp,Field.eval,Point.widen] using hf

namespace MainCell
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
abbrev Cell := ((M.activeGraph J).induce (R.base.layer R.base.height R.base.inBand q (1/1000))).ConnectedComponent
variable (C : Cell R q)

noncomputable def old (x : M.Point J root) : ℝ := F.eval (x.widen hJI)

def boundary : Set (M.Point J root) :=
  {x | x.column ∈ Point.frontier (M := M) (J := J) (ColumnOrder.componentColumns C)}

noncomputable def input (v : M.Point J root) : M.Point J root → ℝ :=
  Clipping.envelope (boundary R q C) (old F hJI) (old F hJI v+1) (1-R.ζ)

noncomputable def proposal (v : M.Point J root) (α : Point.RadialTree.Noise (n := n))
    (E : ℝ) (x : M.Point J root) : ℝ :=
  (R.pasted (input F hJI R q C v) α x).value-4*E

lemma boundary_compact (hJ : IsCompact J) : IsCompact (boundary R q C) :=
  Point.fullColumns_compact hJ _

include R in
lemma old_lipschitz : LipschitzWith 1 (old F hJI : M.Point J root → ℝ) :=
  F.widen_lipschitz hJI R.closed_band

lemma input_lipschitz (hJ : IsCompact J) (v : M.Point J root) :
    R.InputLip (input F hJI R q C v) := by
  let t : ℝ≥0 := ⟨1-R.ζ,by linarith [R.zeta_lt_one]⟩
  have h := Clipping.envelope_lipschitz (boundary_compact R q C hJ)
    (old_lipschitz F hJI R).continuous.continuousOn (old F hJI v+1) t
  intro x y
  exact h.dist_le_mul x y

lemma proposal_accuracy (hJ : IsCompact J) (v x : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E)
    (hδ : R.δ = E/8) :
    input F hJI R q C v x-5*E ≤ proposal F hJI R q C v α E x ∧
    proposal F hJI R q C v α E x ≤ input F hJI R q C v x-3*E := by
  have ha := abs_le.mp (R.pasted_accuracy (input_lipschitz F hJI R q C hJ v) hα x)
  dsimp only [proposal]
  rw [hδ] at ha
  constructor <;> linarith

lemma proposal_lipschitz (v : M.Point J root) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) (E : ℝ) : LipschitzWith 1 (proposal F hJI R q C v α E) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [proposal,dist_sub_right] using (R.pasted_lipschitz (input F hJI R q C v) hα).dist_le_mul x y

lemma frontier_margin (hJ : IsCompact J) (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {E : ℝ} (hE : 0 ≤ E)
    (hδ : R.δ = E/8) {z : M.Point J root} (hz : z ∈ boundary R q C) :
    proposal F hJI R q C v α E z ≤ old F hJI z-3*E := by
  have hf := Clipping.envelope_frontier (boundary_compact R q C hJ)
    (old_lipschitz F hJI R).continuous.continuousOn (old F hJI v+1) (1-R.ζ) hz
  have hp := (proposal_accuracy F hJI R q C hJ v z hα hE hδ).2
  change input F hJI R q C v z ≤ old F hJI z at hf
  linarith

lemma variation (hthin : R.a ≤ (1/1000:ℝ)/1000) (v x : M.Point J root)
    (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hx : x.column ∈ ColumnOrder.componentColumns C) :
    |old F hJI v-old F hJI x| ≤ (1:ℝ)/100 := by
  have hd := R.base.radial_cell_diameter R.closed_band R.base.inBand
    R.width_pos hthin R.half_width C v x hv hx
  have hf := (old_lipschitz F hJI R).dist_le_mul v x
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at hf
  exact hf.trans (by linarith)

end MainCell
end PlanarL1.Columns.Model


end

section

namespace PlanarL1.Columns.Model.MainCell
open scoped NNReal
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

noncomputable def replacement (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) : ℝ :=
  Clipping.clip (old F hJI) (proposal F hJI R q C v α E)
    (fun x => Clipping.heightShield lo R.a (old F hJI v) β x.height) x

noncomputable def replacementConstant : ℝ≥0 :=
  max 1 ⟨3/(9*R.a/100), by positivity [R.width_pos]⟩

lemma replacement_lipschitz (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo : ℝ) :
    LipschitzWith (replacementConstant R) (replacement F hJI R q C v α E β lo) := by
  apply Clipping.clip_lipschitz
  · exact (old_lipschitz F hJI R).weaken (le_max_left _ _)
  · exact (proposal_lipschitz F hJI R q C v hα E).weaken (le_max_left _ _)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (Clipping.heightShield_lipschitz lo (old F hJI v) β R.width_pos).dist_le_mul
      x.height y.height
    have hheight := x.height_change_le y
    change |x.height-y.height| ≤ dist x y at hheight
    change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
    change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at h
    rw [Real.dist_eq x.height y.height] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hheight (by positivity [R.width_pos])).trans
      (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma replacement_switch (v x y : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo : ℝ)
    (he : x.height = y.height) (hs : x.height ∈ M.heights x.column y.column) :
    replacement F hJI R q C v α E β lo x = replacement F hJI R q C v α E β lo y := by
  have hd := x.dist_le_switch y x.inBand hs
  rw [he,sub_self,abs_zero,add_zero] at hd
  have hh := (replacement_lipschitz F hJI R q C v hα E β lo).dist_le_mul x y
  rw [le_antisymm hd dist_nonneg,mul_zero] at hh
  exact dist_le_zero.mp hh

lemma replacement_frontier (hJ : IsCompact J) (v x : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8) (β lo : ℝ)
    (hx : x ∈ boundary R q C) :
    replacement F hJI R q C v α E β lo x = old F hJI x := by
  apply Clipping.clip_unchanged
  left
  have h := frontier_margin F hJI R q C hJ v hα hE hδ hx
  linarith

lemma replacement_endpoint (hthin : R.a ≤ (1/1000:ℝ)/1000)
    (v x : M.Point J root) (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (hβ : β ≤ (1:ℝ)/100)
    (he : x.height = lo ∨ x.height = lo+R.a) :
    replacement F hJI R q C v α E β lo x = old F hJI x := by
  apply Clipping.clip_unchanged
  right
  have h := (abs_le.mp (variation F hJI R q C hthin v x hv hx)).2
  have hh : Clipping.heightShield lo R.a (old F hJI v) β x.height = old F hJI v-1+β := by
    rcases he with he | he
    · exact Clipping.heightShield_left (by rw [he])
    · exact Clipping.heightShield_right (by rw [he])
  rw [hh]
  linarith


/-- Actual closed full-column update domain. -/
def domain (i : Fin n) : Set ℝ :=
  if i ∈ ColumnOrder.componentColumns C then J else ∅

lemma mem_domain {i : Fin n} {H : ℝ} :
    H ∈ domain R q C i ↔ i ∈ ColumnOrder.componentColumns C ∧ H ∈ J := by
  by_cases hi : i ∈ ColumnOrder.componentColumns C <;> simp [domain,hi]

lemma closed_domain (i : Fin n) : IsClosed (domain R q C i) := by
  by_cases hi : i ∈ ColumnOrder.componentColumns C <;>
    simp only [domain,hi,ite_true,ite_false]
  · exact R.closed_band
  · exact isClosed_empty

/-- The actual point in the broad component underlying a cell-domain point. -/
def cellPoint (i : Fin n) (H : ℝ) (h : H ∈ domain R q C i) : M.Point J root :=
  ⟨i,H,((mem_domain R q C).mp h).2,
    (ColumnOrder.componentColumns_subset C ((mem_domain R q C).mp h).1).choose⟩

noncomputable def converted (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo c η κ : ℝ) (i : Fin n) (H : ℝ) : ℝ :=
  if h : H ∈ domain R q C i then
    κ * (c + η * replacement F hJI R q C v α E β lo (cellPoint R q C i H h)) else 0

lemma converted_on (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo c η κ : ℝ) {i : Fin n} {H : ℝ}
    (h : H ∈ domain R q C i) :
    converted F hJI R q C v α E β lo c η κ i H =
    κ * (c + η * replacement F hJI R q C v α E β lo (cellPoint R q C i H h)) := by
  simp only [converted,dite_eq_left h]

lemma converted_lipschitz (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo c η κ : ℝ)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1) (i : Fin n) :
    LipschitzOnWith 1 (converted F hJI R q C v α E β lo c η κ i) (domain R q C i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro H hH T hT
  rw [converted_on F hJI R q C v α E β lo c η κ hH,
    converted_on F hJI R q C v α E β lo c η κ hT]
  let x := cellPoint R q C i H hH
  let y := cellPoint R q C i T hT
  have h := (replacement_lipschitz F hJI R q C v hα E β lo).dist_le_mul x y
  rw [x.dist_same_column y rfl] at h
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  change |κ*(c+η*replacement F hJI R q C v α E β lo x)-
    κ*(c+η*replacement F hJI R q C v α E β lo y)| ≤ |H-T|
  rw [show κ*(c+η*replacement F hJI R q C v α E β lo x)-
    κ*(c+η*replacement F hJI R q C v α E β lo y) =
    κ*η*(replacement F hJI R q C v α E β lo x-replacement F hJI R q C v α E β lo y) by ring,
      abs_mul,abs_mul,abs_of_nonneg hκ,hη,mul_one]
  rw [Real.dist_eq] at h
  change |_ - _| ≤ (replacementConstant R : ℝ) * |H-T| at h
  calc
    _ ≤ κ*((replacementConstant R : ℝ)*|H-T|) := mul_le_mul_of_nonneg_left h hκ
    _ = (κ*(replacementConstant R : ℝ))*|H-T| := by ring
    _ ≤ 1*|H-T| := mul_le_mul_of_nonneg_right hκK (abs_nonneg _)
    _ = _ := one_mul _


/-- A kept main cell, with the literal interpolated proposal and trapezoidal
shield, is an actual invariant-preserving measurable set update. The old
chart agreement is used only on its real update domain. -/
noncomputable def patch {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : SetSystem M Ω μ) (Z : Threshold.Variables Ω μ)
    (hJ : IsCompact J) (lo : ℝ) (hband : J = Icc lo (lo+R.a))
    (hthin : R.a ≤ (1/1000:ℝ)/1000)
    (v : M.Point J root) (hv : v.column ∈ ColumnOrder.componentColumns C)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (E β c η κ : ℝ) (hE : 0 ≤ E) (hδ : R.δ = E/8) (hβ : β ≤ (1:ℝ)/100)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1)
    (hchart : ∀ ω i H (h : H ∈ domain R q C i),
      Threshold.active Z H (κ*(c+η*old F hJI (cellPoint R q C i H h))) ω ↔
        (A.activity ω).active i H) : SetPatch A := by
  apply Threshold.chartPatch A Z (domain R q C) (closed_domain R q C)
    (converted F hJI R q C v α E β lo c η κ)
    (converted_lipschitz F hJI R q C v hα E β lo c η κ hη hκ hκK)
  · intro ω i H hH
    have hd : H ∈ domain R q C i := (closed_domain R q C i).frontier_subset hH
    have hi := ((mem_domain R q C).mp hd).1
    rw [converted_on F hJI R q C v α E β lo c η κ hd]
    have he : H = lo ∨ H = lo+R.a := by
      simpa only [domain,ite_eq_left hi,hband,frontier_Icc (a := lo) (b := lo+R.a) (by linarith [R.width_pos]),
        mem_insert_iff,mem_singleton_iff] using hH
    rw [replacement_endpoint F hJI R q C hthin v (cellPoint R q C i H hd)
      hv hi α E β lo hβ he]
    exact hchart ω i H hd
  · intro i j H hs hi hj
    rw [converted_on F hJI R q C v α E β lo c η κ hi,
      converted_on F hJI R q C v α E β lo c η κ hj,
      replacement_switch F hJI R q C v (cellPoint R q C i H hi)
        (cellPoint R q C j H hj) hα E β lo rfl hs]
  · intro ω i j H hs hi hj
    have hmem := (mem_domain R q C).mp hi
    have hnj : j ∉ ColumnOrder.componentColumns C := by
      intro h
      exact hj ((mem_domain R q C).mpr ⟨h,hmem.2⟩)
    have hf : cellPoint R q C i H hi ∈ boundary R q C :=
      ⟨hmem.1,j,⟨H,hmem.2,hs⟩,hnj⟩
    rw [converted_on F hJI R q C v α E β lo c η κ hi,
      replacement_frontier F hJI R q C hJ v (cellPoint R q C i H hi) hα hE hδ β lo hf]
    exact hchart ω i H hi

end PlanarL1.Columns.Model.MainCell


end

section

namespace PlanarL1.Columns.Model.MainCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

noncomputable def namedReplacement (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) : NamedValue :=
  namedClip (fun z => let A := R.pasted (input F hJI R q C v) α z; ⟨A.name,A.value-4*E⟩)
    (old F hJI) (fun z => Clipping.heightShield lo R.a (old F hJI v) β z.height) x

lemma namedReplacement_value (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) :
    (namedReplacement F hJI R q C v α E β lo x).value =
      replacement F hJI R q C v α E β lo x := by
  exact clippedNamed_value _ _ _

noncomputable def localClipAtom {k : ℕ} (A : R.Node k) (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) : ℕ → M.Point J root → ℝ :=
  clipAtom (fun i z => (R.listedAtom (input F hJI R q C v) α A R.lookback i z).value-4*E)
    (old F hJI) (fun z => Clipping.heightShield lo R.a (old F hJI v) β z.height)

end PlanarL1.Columns.Model.MainCell



end

section

namespace PlanarL1.Columns.Model.MainCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}
variable (F : M.Field I 1) (hJI : J ⊆ I)
variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)
variable (C : Cell R q)

lemma namedReplacement_cases (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) :
    (namedReplacement F hJI R q C v α E β lo x = ⟨0,old F hJI x⟩) ∨
    (namedReplacement F hJI R q C v α E β lo x =
      ⟨1,Clipping.heightShield lo R.a (old F hJI v) β x.height⟩) ∨
    (namedReplacement F hJI R q C v α E β lo x =
      ⟨(R.pasted (input F hJI R q C v) α x).name+2,
        (R.pasted (input F hJI R q C v) α x).value-4*E⟩) := by
  rcases clippedNamed_mem ⟨0,old F hJI x⟩
    ⟨(R.pasted (input F hJI R q C v) α x).name+2,
        (R.pasted (input F hJI R q C v) α x).value-4*E⟩
    ⟨1,Clipping.heightShield lo R.a (old F hJI v) β x.height⟩ with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

lemma namedReplacement_bound (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (x : M.Point J root) :
    (namedReplacement F hJI R q C v α E β lo x).name < 3*n*R.depthCap+2 := by
  rcases namedReplacement_cases F hJI R q C v α E β lo x with h | h | h
  · rw [h]; simp only; omega
  · rw [h]; simp only; omega
  · rw [h]
    exact Nat.add_lt_add_right
      ((R.formula_name_bound (input F hJI R q C v) α
        (R.layerDepth x) (R.layerNode x) x).trans_le
        (Nat.mul_le_mul_left (3*n) (R.layerDepth_lt_cap x))) 2

lemma namedReplacement_congr_zero (v x y : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (E β lo : ℝ)
    (hxy : dist x y=0) :
    namedReplacement F hJI R q C v α E β lo x =
      namedReplacement F hJI R q C v α E β lo y := by
  have hp := R.pasted_congr_zero (input F hJI R q C v) hα x y hxy
  have ho : old F hJI x=old F hJI y := by
    apply dist_le_zero.mp
    have ht := (old_lipschitz F hJI R).dist_le_mul x y
    simpa only [hxy,mul_zero] using ht
  have hh : x.height=y.height := by
    have ht : |x.height-y.height| ≤ dist x y := x.height_change_le y
    rw [hxy] at ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ht (abs_nonneg _)))
  simp only [namedReplacement,namedClip,hp,ho,hh]


/-- A local winner other than the old field receives exactly one new name.
The height-only branch is zero in the fresh block, and spatial atom a is a+1. -/
noncomputable def choose (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ) :
    Option (Fin (3*n*R.depthCap+1)) := by
  classical
  exact if hd : H ∈ domain R q C i then
    let t := namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd)
    if ht : t.name=0 then none else some ⟨t.name-1,by
      have hb := namedReplacement_bound F hJI R q C v α E β lo (cellPoint R q C i H hd)
      dsimp only [t] at ht ⊢
      omega⟩
    else none

lemma choose_spec (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ)
    (a : Fin (3*n*R.depthCap+1)) (ha : choose F hJI R q C v α E β lo i H=some a) :
    ∃ hd : H ∈ domain R q C i,
      (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd)).name=a.val+1 := by
  classical
  by_cases hd : H ∈ domain R q C i
  · simp only [choose,dite_eq_left hd] at ha
    split_ifs at ha with ht
    refine ⟨hd,?_⟩
    have he := congrArg Fin.val (Option.some.inj ha)
    dsimp only at he ht
    omega
  · simp only [choose,dite_eq_right hd] at ha
    cases ha

lemma choose_none_inside (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ)
    (hd : H ∈ domain R q C i) (hc : choose F hJI R q C v α E β lo i H=none) :
    (namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd)).name=0 := by
  classical
  by_contra hn
  simp only [choose,dite_eq_left hd,dite_eq_right hn] at hc
  cases hc

lemma choose_none_outside (v : M.Point J root)
    (α : Point.RadialTree.Noise (n := n)) (E β lo : ℝ) (i : Fin n) (H : ℝ)
    (hd : H ∉ domain R q C i) : choose F hJI R q C v α E β lo i H=none := by
  simp only [choose,dite_eq_right hd]

lemma choose_none_frontier (hJ : IsCompact J) (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0<E) (hδ : R.δ=E/8) (β lo : ℝ) (i : Fin n) (H : ℝ)
    (hd : H ∈ domain R q C i) (hf : cellPoint R q C i H hd ∈ boundary R q C) :
    choose F hJI R q C v α E β lo i H=none := by
  have hm := frontier_margin F hJI R q C hJ v hα hE.le hδ hf
  have hn : namedReplacement F hJI R q C v α E β lo (cellPoint R q C i H hd) =
      ⟨0,old F hJI (cellPoint R q C i H hd)⟩ := by
    apply clippedNamed_retains
    change proposal F hJI R q C v α E _ < old F hJI _
    linarith
  simp [choose,hd,hn]

lemma choose_switch (hJ : IsCompact J) (v : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0<E) (hδ : R.δ=E/8) (β lo : ℝ) (i j : Fin n) (H : ℝ)
    (hs : H ∈ M.heights i j) :
    choose F hJI R q C v α E β lo i H=choose F hJI R q C v α E β lo j H := by
  classical
  by_cases hi : H ∈ domain R q C i <;> by_cases hj : H ∈ domain R q C j
  · have hd : dist (cellPoint R q C i H hi) (cellPoint R q C j H hj)=0 := by
      apply le_antisymm _ dist_nonneg
      have ht := (cellPoint R q C i H hi).dist_le_switch (cellPoint R q C j H hj)
        ((mem_domain R q C).mp hi).2 hs
      simpa only [cellPoint,sub_self,abs_zero,add_zero] using ht
    have hn := namedReplacement_congr_zero F hJI R q C v
      (cellPoint R q C i H hi) (cellPoint R q C j H hj) hα E β lo hd
    simp only [choose,dite_eq_left hi,dite_eq_left hj]
    simp only [hn]
  · have hx := (mem_domain R q C).mp hi
    have hn : j ∉ ColumnOrder.componentColumns C := by
      intro h
      exact hj ((mem_domain R q C).mpr ⟨h,hx.2⟩)
    rw [choose_none_frontier F hJI R q C hJ v hα hE hδ β lo i H hi
      ⟨hx.1,j,⟨H,hx.2,hs⟩,hn⟩,choose_none_outside F hJI R q C v α E β lo j H hj]
  · have hx := (mem_domain R q C).mp hj
    have hn : i ∉ ColumnOrder.componentColumns C := by
      intro h
      exact hi ((mem_domain R q C).mpr ⟨h,hx.2⟩)
    have hs' : H ∈ M.heights j i := by rwa [M.symm]
    rw [choose_none_outside F hJI R q C v α E β lo i H hi,
      choose_none_frontier F hJI R q C hJ v hα hE hδ β lo j H hj
        ⟨hx.1,i,⟨H,hx.2,hs'⟩,hn⟩]
  · rw [choose_none_outside F hJI R q C v α E β lo i H hi,
      choose_none_outside F hJI R q C v α E β lo j H hj]

end PlanarL1.Columns.Model.MainCell



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_OrdinaryState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal

namespace SetSystem
variable {n : ℕ} {M : Model n} {Ω Ω' : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'}

/-- Change label coordinates only: every individual set and component graph is
pulled back, and the upper invariant is transported by the actual measure. -/
noncomputable def pullback (A : SetSystem M Ω μ) {g : Ω' → Ω}
    (hg : MeasurePreserving g μ' μ) : SetSystem M Ω' μ' where
  activity ω := A.activity (g ω)
  measurable_active i H := (A.measurable_active i H).preimage hg.measurable
  vertical_integrable i s t := hg.integrable_comp_of_integrable (A.vertical_integrable i s t)
  vertical_bound i s t := by
    have he : (∫ ω, |(A.activity (g ω)).indicator i s-(A.activity (g ω)).indicator i t| ∂μ') =
        ∫ ω, |(A.activity ω).indicator i s-(A.activity ω).indicator i t| ∂μ := by
      calc
        _ = ∫ ω, |(A.activity ω).indicator i s-(A.activity ω).indicator i t|
            ∂Measure.map g μ' :=
          (integral_map_of_stronglyMeasurable hg.measurable
            (((A.measurable_indicator i s).sub
              (A.measurable_indicator i t)).abs.stronglyMeasurable)).symm
        _ = _ := congrArg (fun ν => ∫ ω,
          |(A.activity ω).indicator i s-(A.activity ω).indicator i t| ∂ν) hg.map_eq
    exact he.trans_le (A.vertical_bound i s t)

noncomputable def lift (A : SetSystem M Ω μ) : SetSystem M (Ω × Bool) (μ.prod Threshold.fair) :=
  A.pullback (measurePreserving_fst (μ := μ) (ν := Threshold.fair))

@[simp] lemma lift_active (A : SetSystem M Ω μ) (z : Ω × Bool) (i : Fin n) (H : ℝ) :
    (A.lift.activity z).active i H ↔ (A.activity z.1).active i H := Iff.rfl

end SetSystem

namespace Field
variable {n : ℕ} (M : Model n) (I : Set ℝ)
noncomputable def constant (c : ℝ) : M.Field I 1 where
  value _ _ := c
  vertical _ := (LipschitzWith.const c).weaken (by norm_num)
  switch _ _ _ _ := rfl
end Field

/-- The literal ordinary-chart scalar data. A nonconstant chart remembers its
old band component and its one point source, rather than just a Lipschitz bound.
The zero extension outside that component is never used on the chart's region. -/
structure OrdinaryData {n : ℕ} (M : Model n) where
  band : Set ℝ
  closed : IsClosed band
  convex : band.OrdConnected
  origin : Option (Σ r : Fin n, M.Point band r)
  constant : ℝ
  orientation : ℝ
  unit_orientation : |orientation| = 1

namespace OrdinaryData
variable {n : ℕ} {M : Model n}

noncomputable def comparison (D : OrdinaryData M) : M.Field D.band 1 :=
  match D.origin with
  | none => Field.constant M D.band 0
  | some o => o.2.radialField

noncomputable def value (D : OrdinaryData M) (i : Fin n) (H : D.band) : ℝ :=
  D.constant + D.orientation * D.comparison.value i H

lemma vertical (D : OrdinaryData M) (i : Fin n) : LipschitzWith 1 (D.value i) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq]
  change |D.constant+D.orientation*D.comparison.value i s-
    (D.constant+D.orientation*D.comparison.value i t)| ≤ _
  rw [show D.constant+D.orientation*D.comparison.value i s-
    (D.constant+D.orientation*D.comparison.value i t) =
    D.orientation*(D.comparison.value i s-D.comparison.value i t) by ring,
    abs_mul,D.unit_orientation,one_mul]
  exact (D.comparison.vertical i).dist_le_mul s t

lemma switch (D : OrdinaryData M) (i j : Fin n) (H : D.band)
    (h : H.val ∈ M.heights i j) : D.value i H = D.value j H := by
  simp only [value,D.comparison.switch i j H h]

noncomputable def field (D : OrdinaryData M) : M.Field D.band 1 :=
  ⟨D.value,D.vertical,D.switch⟩

noncomputable def initial (M : Model n) : OrdinaryData M where
  band := Set.univ
  closed := isClosed_univ
  convex := Set.ordConnected_univ
  origin := none
  constant := 0
  orientation := 1
  unit_orientation := by norm_num

@[simp] lemma initial_value (M : Model n) (i : Fin n) (H : ℝ) :
    (initial M).value i ⟨H,Set.mem_univ H⟩ = 0 := by
  simp [initial,value,comparison,Field.constant]

/-- Conversion of an actual signed atom back to the old ordinary orientation. -/
noncomputable def atom (D : OrdinaryData M) (J : Set ℝ) (hJ : IsClosed J)
    (hc : J.OrdConnected) {r : Fin n} (o : M.Point J r) (c η : ℝ) (hη : |η| = 1) :
    OrdinaryData M where
  band := J
  closed := hJ
  convex := hc
  origin := some ⟨r,o⟩
  constant := D.constant+D.orientation*c
  orientation := D.orientation*η
  unit_orientation := by rw [abs_mul,D.unit_orientation,hη,mul_one]

lemma atom_value (D : OrdinaryData M) (J : Set ℝ) (hJ : IsClosed J)
    (hc : J.OrdConnected) {r : Fin n} (o x : M.Point J r) (c η : ℝ) (hη : |η| = 1) :
    (D.atom J hJ hc o c η hη).value x.column ⟨x.height,x.inBand⟩ =
      D.constant+D.orientation*(c+η*dist o x) := by
  have he : o.radialField.value x.column ⟨x.height,x.inBand⟩=dist o x := o.radialField_eval x
  simp only [value,atom,comparison,he]
  ring

end OrdinaryData

/-- A finite ordinary chart partition for system A, with the actual globally
nested sets and actual jointly distributed label variables. Chart regions may
be disconnected; no artificial connected-component identifiers are introduced. -/
structure OrdinaryState {n : ℕ} (M : Model n) (κ : ℝ) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  sets : SetSystem M Ω μ
  count : ℕ
  chart : Fin (count+1) → OrdinaryData M
  labels : Fin (count+1) → Threshold.Variables Ω μ
  name : Fin n → ℝ → Fin (count+1)
  height_in : ∀ i H, H ∈ (chart (name i H)).band
  component_in : ∀ i H r o, (chart (name i H)).origin = some ⟨r,o⟩ →
    (M.activeGraph (chart (name i H)).band).Reachable r i
  switch_name : ∀ i j H, H ∈ M.heights i j → name i H = name j H
  represents : ∀ ω i H,
    (sets.activity ω).active i H ↔ Threshold.active (labels (name i H)) H
      (κ*(chart (name i H)).value i ⟨H,height_in i H⟩) ω

namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def initial (M : Model n) (κ : ℝ) :
    OrdinaryState M κ (Bool × ℝ) Threshold.labelMeasure where
  sets := Threshold.chartSystem (Field.constant M Set.univ 0) (by norm_num)
  count := 0
  chart _ := OrdinaryData.initial M
  labels _ := Threshold.Variables.initial
  name _ _ := 0
  height_in _ _ := Set.mem_univ _
  component_in _ _ r o h := by cases h
  switch_name _ _ _ _ := rfl
  represents ω i H := by
    simp only [Threshold.chartSystem,Threshold.chartActivity,OrdinaryData.initial_value,
      mul_zero,Field.constant,Threshold.active,Threshold.Variables.initial]
    rfl

noncomputable def lift (S : OrdinaryState M κ Ω μ) :
    OrdinaryState M κ (Ω × Bool) (μ.prod Threshold.fair) where
  sets := S.sets.lift
  count := S.count
  chart := S.chart
  labels j := (S.labels j).lift
  name := S.name
  height_in := S.height_in
  component_in := S.component_in
  switch_name := S.switch_name
  represents ω i H := S.represents ω.1 i H

end OrdinaryState
end PlanarL1.Columns.Model


namespace PlanarL1.Columns.Model.Point.RadialTree
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : RadialTree (M := M) (J := J) (root := root))

lemma atomName_depth_eq {k l : ℕ} (u v : M.Point J root) (t t' : Fin 3)
    (he : atomName k u t = atomName l v t') : k = l := by
  have hu := atomName_bounds k u t
  have hv := atomName_bounds l v t'
  rcases lt_trichotomy k l with h | h | h
  · have hm := Nat.mul_le_mul_left (3*n) (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hm
    omega
  · exact h
  · have hm := Nat.mul_le_mul_left (3*n) (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hm
    omega

lemma portalAt_mem {k : ℕ} (C : R.Node k) (i : Fin 2) :
    (R.portalAt C i).column ∈ ColumnOrder.componentColumns C := by
  by_cases hi : i = 0
  · simpa only [portalAt,ite_eq_left hi] using (R.portals C).left_mem
  · simpa only [portalAt,ite_eq_right hi] using (R.portals C).right_mem

lemma node_eq_of_portal_column {k : ℕ} (C D : R.Node k) (i j : Fin 2)
    (he : (R.portalAt C i).column=(R.portalAt D j).column) : C = D := by
  apply ColumnOrder.component_eq_of_column (R.portalAt_mem C i)
  rw [he]
  exact R.portalAt_mem D j

/-- A name is global to the whole interpolation tree, not only a chosen chain.
Different node occurrences cannot silently give one identifier two fields. -/
lemma nodeAtom_eq_global (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k l : ℕ} (C : R.Node k) (D : R.Node l) (i j : Fin 2) (t t' : Fin 3)
    (he : atomName k (R.portalAt C i) t = atomName l (R.portalAt D j) t') :
    R.nodeAtom p α C i t = R.nodeAtom p α D j t' := by
  have hk := atomName_depth_eq (R.portalAt C i) (R.portalAt D j) t t' he
  subst l
  obtain ⟨hc,ht⟩ := atomName_same_depth _ _ _ _ he
  have hC := R.node_eq_of_portal_column C D i j hc
  subst D
  exact R.nodeAtom_eq_of_name p α C i j t t' he

/-- The exact portal occurrence from which an atom identifier originates. -/
structure AtomSource (a : ℕ) where
  depth : ℕ
  node : R.Node depth
  portal : Fin 2
  kind : Fin 3
  name_eq : atomName depth (R.portalAt node portal) kind = a

lemma pasted_has_source (p : M.Point J root → ℝ) (α : Noise (n := n))
    (x : M.Point J root) : Nonempty (R.AtomSource (R.pasted p α x).name) := by
  obtain ⟨k,hk,i,t,he⟩ := R.formula_eq_atom p α (R.layerDepth x) (R.layerNode x) x
  refine ⟨⟨k,R.ancestor (R.layerNode x) k hk,i,t,?_⟩⟩
  exact (congrArg NamedValue.name he).symm

lemma pasted_name_lt (p : M.Point J root → ℝ) (α : Noise (n := n))
    (x : M.Point J root) : (R.pasted p α x).name < 3*n*R.depthCap := by
  exact (R.formula_name_bound p α (R.layerDepth x) (R.layerNode x) x).trans_le
    (Nat.mul_le_mul_left (3*n) (R.layerDepth_lt_cap x))

namespace AtomSource
variable {R} {a : ℕ}

noncomputable def eval (S : R.AtomSource a) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) : M.Point J root → NamedValue :=
  R.nodeAtom p α S.node S.portal S.kind

noncomputable def center (S : R.AtomSource a) : M.Point J root := R.portalAt S.node S.portal

noncomputable def intercept (S : R.AtomSource a) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) : ℝ :=
  (if S.kind = 0 then p S.center else R.parentValue p α S.depth S.node S.center) +
    (if S.kind = 1 then -α S.depth S.center.column S.kind else α S.depth S.center.column S.kind)

noncomputable def sign (S : R.AtomSource a) : ℝ := if S.kind = 2 then -1 else 1

lemma sign_unit (S : R.AtomSource a) : |S.sign| = 1 := by
  unfold sign
  split_ifs <;> norm_num

lemma eval_formula (S : R.AtomSource a) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (x : M.Point J root) :
    (S.eval p α x).value = S.intercept p α+S.sign*dist S.center x := by
  simp only [eval,nodeAtom,atomIntercept,intercept,sign,center]
  split_ifs <;> ring

/-- Convert back to the old ordinary orientation, as in /main-packing.
The -4E proposal shift is part of the literal atom constant. -/
noncomputable def chart (S : R.AtomSource a) (D : OrdinaryData M)
    (p : M.Point J root → ℝ) (α : Noise (n := n)) (E : ℝ) : OrdinaryData M :=
  D.atom J R.closed_band R.interval_band S.center (S.intercept p α-4*E) S.sign S.sign_unit

lemma chart_value (S : R.AtomSource a) (D : OrdinaryData M)
    (p : M.Point J root → ℝ) (α : Noise (n := n)) (E : ℝ) (x : M.Point J root) :
    (S.chart D p α E).value x.column ⟨x.height,x.inBand⟩ =
      D.constant+D.orientation*((S.eval p α x).value-4*E) := by
  calc _ = D.constant+D.orientation*((S.intercept p α-4*E)+S.sign*dist S.center x) :=
         OrdinaryData.atom_value D J R.closed_band R.interval_band S.center x _ _ _
       _ = _ := by rw [S.eval_formula]; ring

end AtomSource

/-- A finite globally consistent chart table for every possible spatial atom.
Unused identifiers get a constant chart and can never be selected by pasted. -/
noncomputable def atomChart (D : OrdinaryData M) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (E : ℝ) (a : ℕ) : OrdinaryData M := by
  classical
  exact if h : Nonempty (R.AtomSource a) then h.some.chart D p α E else OrdinaryData.initial M

lemma source_eval_pasted (p : M.Point J root → ℝ) (α : Noise (n := n))
    (x : M.Point J root) (S : R.AtomSource (R.pasted p α x).name) :
    S.eval p α x = R.pasted p α x := by
  obtain ⟨k,hk,i,t,he⟩ := R.formula_eq_atom p α (R.layerDepth x) (R.layerNode x) x
  have hn : atomName k (R.portalAt (R.ancestor (R.layerNode x) k hk) i) t =
      (R.pasted p α x).name := (congrArg NamedValue.name he).symm
  have hsame := R.nodeAtom_eq_global p α S.node (R.ancestor (R.layerNode x) k hk)
    S.portal i S.kind t (S.name_eq.trans hn.symm)
  exact (congrFun hsame x).trans he.symm

lemma atomChart_value (D : OrdinaryData M) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (E : ℝ) (x : M.Point J root) :
    ∃ h : x.height ∈ (R.atomChart D p α E (R.pasted p α x).name).band,
      (R.atomChart D p α E (R.pasted p α x).name).value x.column ⟨x.height,h⟩ =
        D.constant+D.orientation*((R.pasted p α x).value-4*E) := by
  have h := R.pasted_has_source p α x
  let Q : OrdinaryData M → Prop := fun T => ∃ hi : x.height ∈ T.band,
    T.value x.column ⟨x.height,hi⟩ =
      D.constant+D.orientation*((R.pasted p α x).value-4*E)
  change Q (R.atomChart D p α E (R.pasted p α x).name)
  have he : R.atomChart D p α E (R.pasted p α x).name = h.some.chart D p α E := dite_eq_left h
  rw [he]
  exact ⟨x.inBand,(AtomSource.chart_value h.some D p α E x).trans
    (by rw [R.source_eval_pasted])⟩

end PlanarL1.Columns.Model.Point.RadialTree


namespace PlanarL1.Columns.Model
open MeasureTheory
namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Finite chart-table extension. Old identifiers are literally retained in the
right summand; installing a fresh chart never refines the old regions. -/
noncomputable def append (S : OrdinaryState M κ Ω μ) (B : SetSystem M Ω μ)
    (k : ℕ) (D : Fin k → OrdinaryData M) (Z : Fin k → Threshold.Variables Ω μ)
    (choose : Fin n → ℝ → Option (Fin k))
    (hin : ∀ i H a, choose i H = some a → H ∈ (D a).band)
    (hcomp : ∀ i H a (_hc : choose i H = some a) r o,
      (D a).origin = some ⟨r,o⟩ → (M.activeGraph (D a).band).Reachable r i)
    (hswitch : ∀ i j H, H ∈ M.heights i j → choose i H = choose j H)
    (hold : ∀ ω i H, choose i H = none →
      ((B.activity ω).active i H ↔ (S.sets.activity ω).active i H))
    (hnew : ∀ ω i H a (hc : choose i H = some a),
      ((B.activity ω).active i H ↔ Threshold.active (Z a) H
        (κ*(D a).value i ⟨H,hin i H a hc⟩) ω)) : OrdinaryState M κ Ω μ where
  sets := B
  count := k+S.count
  chart := Fin.addCases (m := k) (n := S.count+1) D S.chart
  labels := Fin.addCases (m := k) (n := S.count+1) Z S.labels
  name i H := match choose i H with
    | none => Fin.natAdd k (S.name i H)
    | some a => Fin.castAdd (S.count+1) a
  height_in i H := by
    cases hc : choose i H with
    | none => simpa only [hc,Fin.addCases_right] using S.height_in i H
    | some a => simpa only [hc,Fin.addCases_left] using hin i H a hc
  component_in i H := by
    let Uses (D : OrdinaryData M) : Prop := ∀ r o,
      D.origin = some ⟨r,o⟩ → (M.activeGraph D.band).Reachable r i
    change Uses (Fin.addCases (m := k) (n := S.count+1) D S.chart
      (match choose i H with
      | none => Fin.natAdd k (S.name i H)
      | some a => Fin.castAdd (S.count+1) a))
    cases hc : choose i H with
    | none =>
      simp only [Fin.addCases_right]
      exact S.component_in i H
    | some a =>
      simp only [Fin.addCases_left]
      exact hcomp i H a hc
  switch_name i j H hh := by
    have hc := hswitch i j H hh
    rw [hc]
    cases choose j H with
    | none => exact congrArg (Fin.natAdd k) (S.switch_name i j H hh)
    | some a => rfl
  represents ω i H := by
    let Rep (D : OrdinaryData M) (Z : Threshold.Variables Ω μ) : Prop :=
      ∀ hi : H ∈ D.band, (B.activity ω).active i H ↔
        Threshold.active Z H (κ*D.value i ⟨H,hi⟩) ω
    have hr : Rep
        (Fin.addCases (m := k) (n := S.count+1) D S.chart
          (match choose i H with
          | none => Fin.natAdd k (S.name i H)
          | some a => Fin.castAdd (S.count+1) a))
        (Fin.addCases (m := k) (n := S.count+1) Z S.labels
          (match choose i H with
          | none => Fin.natAdd k (S.name i H)
          | some a => Fin.castAdd (S.count+1) a)) := by
      cases hc : choose i H with
      | none =>
        simp only [Fin.addCases_right]
        intro hi
        exact (hold ω i H hc).trans (S.represents ω i H)
      | some a =>
        simp only [Fin.addCases_left]
        intro hi
        exact hnew ω i H a hc
    exact hr _

end OrdinaryState
end PlanarL1.Columns.Model


end

section

namespace PlanarL1.Columns.Model.OrdinaryData
variable {n : ℕ} {M : Model n}

/-- The actual chart domain, with the connected-component requirement made
explicit. Different copies of a quotient point satisfy the same condition. -/
def Contains (D : OrdinaryData M) (i : Fin n) (H : ℝ) : Prop :=
  H ∈ D.band ∧ ∀ r o, D.origin = some ⟨r,o⟩ → (M.activeGraph D.band).Reachable r i

lemma initial_contains (i : Fin n) (H : ℝ) : (initial M).Contains i H := by
  refine ⟨Set.mem_univ _,?_⟩
  intro r o he
  cases he

lemma atom_contains (D : OrdinaryData M) (J : Set ℝ) (hJ : IsClosed J)
    (hc : J.OrdConnected) {r : Fin n} (o x : M.Point J r) (c η : ℝ) (hη : |η|=1) :
    (D.atom J hJ hc o c η hη).Contains x.column x.height := by
  refine ⟨x.inBand,?_⟩
  intro r' o' he
  have hr : r=r' := congrArg (fun z : Option (Σ r : Fin n, M.Point J r) =>
    z.map Sigma.fst) he |> Option.some.inj
  subst r'
  exact x.reachable

end PlanarL1.Columns.Model.OrdinaryData

namespace PlanarL1.Columns.Model.Point.RadialTree
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : RadialTree (M := M) (J := J) (root := root))

lemma atomChart_contains (D : OrdinaryData M) (p : M.Point J root → ℝ)
    (α : Noise (n := n)) (E : ℝ) (x : M.Point J root) :
    (R.atomChart D p α E (R.pasted p α x).name).Contains x.column x.height := by
  have h := R.pasted_has_source p α x
  have he : R.atomChart D p α E (R.pasted p α x).name = h.some.chart D p α E := dite_eq_left h
  rw [he]
  exact OrdinaryData.atom_contains D J R.closed_band R.interval_band h.some.center x _ _ _

end PlanarL1.Columns.Model.Point.RadialTree


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_OrderedState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.Field
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {I : Set ℝ} {L : ℝ≥0}

noncomputable def negate (F : M.Field I L) : M.Field I L where
  value i H := -F.value i H
  vertical i := (F.vertical i).neg
  switch i j H hs := congrArg Neg.neg (F.switch i j H hs)

lemma ordered_negate (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b) :
    F.negate.OrderedFrom b a := by
  have hrot (H : I) := Ordered.rotate_unimodal_neg (b-a)
    (fun i => F.value (finCycle a i) H)
    (by simpa only [finCycle_apply,zero_add] using fun i => ho.1 H (finCycle a i))
    (by simpa only [finCycle_symm_apply] using ho.2.1 H)
    (by simpa only [finCycle_symm_apply] using ho.2.2 H)
  have had (i : Fin (k+1)) : (i+(b-a))+a=i+b := by abel
  have hbal : -(b-a)=a-b := by abel
  refine ⟨?_,?_,?_⟩
  · intro H i
    exact neg_le_neg (F.ordered_maximum ho H i)
  · intro H i j hij hj
    have hh := (hrot H).2.1 i j hij (by simpa only [hbal,finCycle_symm_apply] using hj)
    simpa only [finCycle_apply,had,negate] using hh
  · intro H i j hi hij
    have hh := (hrot H).2.2 i j (by simpa only [hbal,finCycle_symm_apply] using hi) hij
    simpa only [finCycle_apply,had,negate] using hh

noncomputable def affine (F : M.Field I L) (c : ℝ) (q : ℝ≥0) : M.Field I (q*L) where
  value i H := c+q*F.value i H
  vertical i := by
    apply LipschitzWith.of_dist_le_mul
    intro H T
    have hh := (F.vertical i).dist_le_mul H T
    simp only [Real.dist_eq] at hh ⊢
    rw [show c+(q:ℝ)*F.value i H-(c+(q:ℝ)*F.value i T) =
      (q:ℝ)*(F.value i H-F.value i T) by ring, abs_mul,abs_of_nonneg q.coe_nonneg]
    simpa only [NNReal.coe_mul,mul_assoc] using mul_le_mul_of_nonneg_left hh q.coe_nonneg
  switch i j H hs := by rw [F.switch i j H hs]

lemma ordered_affine (F : M.Field I L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b)
    (c : ℝ) (q : ℝ≥0) : (F.affine c q).OrderedFrom a b := by
  refine ⟨?_,?_,?_⟩
  · intro H i
    simpa only [affine,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (ho.1 H i) q.coe_nonneg) c
  · intro H i j hij hj
    simpa only [affine,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (ho.2.1 H i j hij hj) q.coe_nonneg) c
  · intro H i j hi hij
    simpa only [affine,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (ho.2.2 H i j hi hij) q.coe_nonneg) c

end PlanarL1.Columns.Model.Field


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal

namespace Field
variable {n : ℕ} {M : Model n} {I : Set ℝ} {L K : ℝ≥0}

def weaken (F : M.Field I L) (h : L ≤ K) : M.Field I K where
  value := F.value
  vertical i := (F.vertical i).weaken h
  switch := F.switch

noncomputable def add (F : M.Field I L) (G : M.Field I K) : M.Field I (L+K) where
  value i H := F.value i H+G.value i H
  vertical i := (F.vertical i).add (G.vertical i)
  switch i j H h := by rw [F.switch i j H h,G.switch i j H h]
end Field

/-- The ordered-chart data. The base ordered field never
changes during this identifier's lifetime. The auxiliary field is replaced by
its actual signed increment history; its bound is 100, not an unbounded sum
of the individual increments. -/
structure OrderedData {k : ℕ} (M : Model (k+1)) where
  band : Set ℝ
  closed : IsClosed band
  convex : band.OrdConnected
  base : M.Field band 4
  lower : Fin (k+1)
  upper : Fin (k+1)
  ordered : base.OrderedFrom lower upper
  auxiliary : M.Field band 100

namespace OrderedData
variable {k : ℕ} {M : Model (k+1)}

noncomputable def value (D : OrderedData M) (lam : ℝ≥0) (i : Fin (k+1)) (H : D.band) : ℝ :=
  D.base.value i H+lam*D.auxiliary.value i H

noncomputable def field (D : OrderedData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) :
    M.Field D.band 5 :=
  (D.base.add (D.auxiliary.affine 0 lam)).weaken (by nlinarith)

lemma field_value (D : OrderedData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (H : D.band) : (D.field lam hlam).value i H=D.value lam i H := by
  simp only [field,Field.weaken,Field.add,Field.affine,zero_add,value]

/-- Install the spatial ordered branch O_F, with zero auxiliary history.
The boolean is the conversion back to the old chart orientation. Negation
exchanges, rather than discards, the two circular boundary columns. -/
noncomputable def install {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c : ℝ) (positive : Bool) : OrderedData M where
  band := I
  closed := hI
  convex := hc
  base := if positive then
    (L.affine c 4).weaken (by norm_num) else
    ((L.affine c 4).negate).weaken (by norm_num)
  lower := if positive then a else b
  upper := if positive then b else a
  ordered := by
    cases positive
    · exact (L.affine c 4).ordered_negate (L.ordered_affine ho c 4)
    · exact L.ordered_affine ho c 4
  auxiliary := (Field.constant M I 0).weaken (by norm_num)

lemma install_value {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c : ℝ) (positive : Bool) (lam : ℝ≥0) (i : Fin (k+1)) (H : I) :
    (install hI hc L a b ho c positive).value lam i H =
      if positive then c+4*L.value i H else -(c+4*L.value i H) := by
  cases positive <;> simp [install,value,Field.weaken,Field.affine,Field.negate,Field.constant]
end OrderedData

/-- System B has precisely the ordinary and ordered chart alternatives. -/
inductive BData {k : ℕ} (M : Model (k+1))
  | ordinary : OrdinaryData M → BData M
  | ordered : OrderedData M → BData M

namespace BData
variable {k : ℕ} {M : Model (k+1)}

def band : BData M → Set ℝ
  | .ordinary D => D.band
  | .ordered D => D.band

lemma closed (D : BData M) : IsClosed D.band := by
  cases D with
  | ordinary D => exact D.closed
  | ordered D => exact D.closed

lemma convex (D : BData M) : D.band.OrdConnected := by
  cases D with
  | ordinary D => exact D.convex
  | ordered D => exact D.convex

noncomputable def value (lam : ℝ≥0) : (D : BData M) → Fin (k+1) → D.band → ℝ
  | .ordinary D => D.value
  | .ordered D => D.value lam

noncomputable def field (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) :
    (D : BData M) → M.Field D.band 5
  | .ordinary D => D.field.weaken (by norm_num)
  | .ordered D => D.field lam hlam

lemma field_value (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) (D : BData M)
    (i : Fin (k+1)) (H : D.band) : (D.field lam hlam).value i H=D.value lam i H := by
  cases D with
  | ordinary D => rfl
  | ordered D => exact D.field_value lam hlam i H

/-- Component restriction is attached only to a genuine point-source chart;
the ordered formula is defined on every component of its recorded band. -/
def Uses (D : BData M) (i : Fin (k+1)) : Prop :=
  match D with
  | .ordinary C => ∀ r o, C.origin=some ⟨r,o⟩ → (M.activeGraph C.band).Reachable r i
  | .ordered _ => True
end BData

structure BState {k : ℕ} (M : Model (k+1)) (κ : ℝ) (lam : ℝ≥0) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  sets : SetSystem M Ω μ
  count : ℕ
  chart : Fin (count+1) → BData M
  labels : Fin (count+1) → Threshold.Variables Ω μ
  name : Fin (k+1) → ℝ → Fin (count+1)
  height_in : ∀ i H, H ∈ (chart (name i H)).band
  component_in : ∀ i H, (chart (name i H)).Uses i
  switch_name : ∀ i j H, H ∈ M.heights i j → name i H = name j H
  represents : ∀ ω i H,
    (sets.activity ω).active i H ↔ Threshold.active (labels (name i H)) H
      (κ*(chart (name i H)).value lam i ⟨H,height_in i H⟩) ω

namespace BState
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def ofOrdinary (S : OrdinaryState M κ Ω μ) : BState M κ lam Ω μ where
  sets := S.sets
  count := S.count
  chart a := .ordinary (S.chart a)
  labels := S.labels
  name := S.name
  height_in := S.height_in
  component_in := S.component_in
  switch_name := S.switch_name
  represents := S.represents

noncomputable def initial (M : Model (k+1)) (κ : ℝ) (lam : ℝ≥0) :
    BState M κ lam (Bool × ℝ) Threshold.labelMeasure :=
  ofOrdinary (OrdinaryState.initial M κ)

noncomputable def lift (S : BState M κ lam Ω μ) :
    BState M κ lam (Ω × Bool) (μ.prod Threshold.fair) where
  sets := S.sets.lift
  count := S.count
  chart := S.chart
  labels a := (S.labels a).lift
  name := S.name
  height_in := S.height_in
  component_in := S.component_in
  switch_name := S.switch_name
  represents ω i H := S.represents ω.1 i H

/-- Finite chart-table extension. Old identifiers are literally retained in the
right summand; installing a fresh chart never refines the old regions. -/
noncomputable def append (S : BState M κ lam Ω μ) (B : SetSystem M Ω μ)
    (m : ℕ) (D : Fin m → BData M) (Z : Fin m → Threshold.Variables Ω μ)
    (choose : Fin (k+1) → ℝ → Option (Fin m))
    (hin : ∀ i H a, choose i H = some a → H ∈ (D a).band)
    (hcomp : ∀ i H a, choose i H = some a → (D a).Uses i)
    (hswitch : ∀ i j H, H ∈ M.heights i j → choose i H = choose j H)
    (hold : ∀ ω i H, choose i H = none →
      ((B.activity ω).active i H ↔ (S.sets.activity ω).active i H))
    (hnew : ∀ ω i H a (hc : choose i H = some a),
      ((B.activity ω).active i H ↔ Threshold.active (Z a) H
        (κ*(D a).value lam i ⟨H,hin i H a hc⟩) ω)) : BState M κ lam Ω μ where
  sets := B
  count := m+S.count
  chart := Fin.addCases (m := m) (n := S.count+1) D S.chart
  labels := Fin.addCases (m := m) (n := S.count+1) Z S.labels
  name i H := match choose i H with
    | none => Fin.natAdd m (S.name i H)
    | some a => Fin.castAdd (S.count+1) a
  height_in i H := by
    cases hc : choose i H with
    | none => simpa only [hc,Fin.addCases_right] using S.height_in i H
    | some a => simpa only [hc,Fin.addCases_left] using hin i H a hc
  component_in i H := by
    let Uses (D : BData M) : Prop := D.Uses i
    change Uses (Fin.addCases (m := m) (n := S.count+1) D S.chart
      (match choose i H with
      | none => Fin.natAdd m (S.name i H)
      | some a => Fin.castAdd (S.count+1) a))
    cases hc : choose i H with
    | none =>
      simp only [Fin.addCases_right]
      exact S.component_in i H
    | some a =>
      simp only [Fin.addCases_left]
      exact hcomp i H a hc
  switch_name i j H hh := by
    have hc := hswitch i j H hh
    rw [hc]
    cases choose j H with
    | none => exact congrArg (Fin.natAdd m) (S.switch_name i j H hh)
    | some a => rfl
  represents ω i H := by
    let Rep (D : BData M) (Z : Threshold.Variables Ω μ) : Prop :=
      ∀ hi : H ∈ D.band, (B.activity ω).active i H ↔
        Threshold.active Z H (κ*D.value lam i ⟨H,hi⟩) ω
    have hr : Rep
        (Fin.addCases (m := m) (n := S.count+1) D S.chart
          (match choose i H with
          | none => Fin.natAdd m (S.name i H)
          | some a => Fin.castAdd (S.count+1) a))
        (Fin.addCases (m := m) (n := S.count+1) Z S.labels
          (match choose i H with
          | none => Fin.natAdd m (S.name i H)
          | some a => Fin.castAdd (S.count+1) a)) := by
      cases hc : choose i H with
      | none =>
        simp only [Fin.addCases_right]
        intro hi
        exact (hold ω i H hc).trans (S.represents ω i H)
      | some a =>
        simp only [Fin.addCases_left]
        intro hi
        exact hnew ω i H a hc
    exact hr _

end BState
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BState
variable (S : BState M κ lam Ω μ)

noncomputable def oldValue (i : Fin (k+1)) (H : ℝ) : ℝ :=
  κ*(S.chart (S.name i H)).value lam i ⟨H,S.height_in i H⟩

noncomputable def newValue (F : ∀ a, M.Field (S.chart a).band 5)
    (i : Fin (k+1)) (H : ℝ) : ℝ :=
  κ*(F (S.name i H)).value i ⟨H,S.height_in i H⟩

lemma newValue_eq (F : ∀ a, M.Field (S.chart a).band 5)
    (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1)) (h : S.name i H=a) :
    S.newValue F i H = κ*(F a).value i ⟨H,by simpa only [h] using S.height_in i H⟩ := by
  subst a
  rfl

lemma newValue_lipschitz (F : ∀ a, M.Field (S.chart a).band 5) (hk : 0 ≤ κ)
    (i : Fin (k+1)) (H T : ℝ) (he : S.name i H=S.name i T) :
    |S.newValue F i H-S.newValue F i T| ≤ (κ*5)*|H-T| := by
  rw [S.newValue_eq F i H (S.name i H) rfl,S.newValue_eq F i T (S.name i H) he.symm]
  rw [← mul_sub,abs_mul,abs_of_nonneg hk]
  have hb := ((F (S.name i H)).vertical i).dist_le_mul
    ⟨H,S.height_in i H⟩ ⟨T,by simpa only [he] using S.height_in i T⟩
  simp only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat] at hb
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hk

lemma oldValue_lipschitz (hk : 0 ≤ κ) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (H T : ℝ) (he : S.name i H=S.name i T) :
    |S.oldValue i H-S.oldValue i T| ≤ (κ*5)*|H-T| := by
  have hf (i H) : S.newValue (fun a => (S.chart a).field lam hlam) i H=S.oldValue i H := by
    simp only [newValue,oldValue,BData.field_value]
  simpa only [hf] using S.newValue_lipschitz (fun a => (S.chart a).field lam hlam) hk i H T he

/-- A simultaneous same-identifier update, defined by the actual new fields.
The boundary estimate is exactly what the ambient complement taper provides.
The name map is retained literally; it is not refined to a partition with
better-behaved boundaries. -/
noncomputable def fieldActivity (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue F i H-S.oldValue i H| ≤ |H-T|/8)
    (ω : Ω) : Activity M where
  active i H := Threshold.active (S.labels (S.name i H)) H (S.newValue F i H) ω
  increasing i H T hHT := by
    apply Threshold.named_nested (S.name i) S.labels (S.oldValue i) (S.newValue F i)
      (fun H ω => (S.sets.activity ω).active i H)
      (fun ω s t hst => (S.sets.activity ω).increasing i s t hst)
      (fun H ω => S.represents ω i H)
      (fun s t he => (S.oldValue_lipschitz hk hlam i s t he).trans (by
        nlinarith [abs_nonneg (s-t)]))
      (fun s t he => (S.newValue_lipschitz F hk i s t he).trans (by
        nlinarith [abs_nonneg (s-t)]))
      (hd i) ω hHT
  switch i j H hh := by
    have he := S.switch_name i j H hh
    have hv : S.newValue F i H=S.newValue F j H := by
      rw [S.newValue_eq F i H (S.name i H) rfl,
        S.newValue_eq F j H (S.name i H) he.symm]
      rw [(F (S.name i H)).switch i j ⟨H,S.height_in i H⟩ hh]
    simp only [he,hv]

lemma field_indicator (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue F i H-S.oldValue i H| ≤ |H-T|/8)
    (ω : Ω) (i : Fin (k+1)) (H : ℝ) :
    (S.fieldActivity F hk hsmall hlam hd ω).indicator i H =
      Threshold.chartValue H (S.newValue F i H) ((S.labels (S.name i H)).value ω) := rfl

lemma old_indicator (ω : Ω) (i : Fin (k+1)) (H : ℝ) :
    (S.sets.activity ω).indicator i H =
      Threshold.chartValue H (S.oldValue i H) ((S.labels (S.name i H)).value ω) := by
  simp only [Activity.indicator,S.represents,oldValue,
    Threshold.chartValue,Threshold.half,Threshold.active]
  rfl

noncomputable def fieldUpdate (F : ∀ a, M.Field (S.chart a).band 5)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue F i H-S.oldValue i H| ≤ |H-T|/8) : SetSystem M Ω μ :=
  S.sets.balancedUpdate (S.fieldActivity F hk hsmall hlam hd)
    (fun i H => Threshold.measurable_active _ _ _)
    (fun i H => by
      simp only [S.field_indicator,S.old_indicator]
      exact (S.labels (S.name i H)).integrable_difference _ _ _ _)
    (fun i H => by
      simp only [S.field_indicator,S.old_indicator]
      rw [(S.labels (S.name i H)).integral_difference,sub_self])

end BState
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model
open scoped NNReal
namespace OrderedData
variable {k : ℕ} {M : Model (k+1)}

/-- Replace only the auxiliary history; all data determining t_s stay fixed. -/
def withAuxiliary (D : OrderedData M) (u : M.Field D.band 100) : OrderedData M :=
  { D with auxiliary := u }

lemma withAuxiliary_value (D : OrderedData M) (u : M.Field D.band 100)
    (lam : ℝ≥0) (i : Fin (k+1)) (H : D.band) :
    (D.withAuxiliary u).value lam i H-D.value lam i H =
      lam*(u.value i H-D.auxiliary.value i H) := by
  unfold withAuxiliary value
  ring

end OrderedData
end PlanarL1.Columns.Model




end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData

def Auxiliary : BData M → Type
  | .ordinary _ => Unit
  | .ordered D => M.Field D.band 100

def withAuxiliary (D : BData M) (u : D.Auxiliary) : BData M :=
  match D with
  | .ordinary C => .ordinary C
  | .ordered C => .ordered (C.withAuxiliary u)

@[simp] lemma withAuxiliary_band (D : BData M) (u : D.Auxiliary) :
    (D.withAuxiliary u).band=D.band := by cases D <;> rfl

lemma withAuxiliary_uses (D : BData M) (u : D.Auxiliary) (i : Fin (k+1)) :
    (D.withAuxiliary u).Uses i ↔ D.Uses i := by cases D <;> rfl

noncomputable def auxiliaryField (D : BData M) (u : D.Auxiliary)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) : M.Field D.band 5 :=
  match D with
  | .ordinary C => C.field.weaken (by norm_num)
  | .ordered C => (C.withAuxiliary u).field lam hlam

lemma auxiliaryField_value (D : BData M) (u : D.Auxiliary)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100) (i : Fin (k+1)) (H : D.band) :
    (D.auxiliaryField u lam hlam).value i H =
      (D.withAuxiliary u).value lam i ⟨H.val,by simp⟩ := by
  cases D with
  | ordinary C => rfl
  | ordered C => exact (C.withAuxiliary u).field_value lam hlam i H

end BData

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  (S : BState M κ lam Ω μ)

/-- Simultaneously replace every ordered history, while retaining literally all
old chart names and all label variables. Ordinary charts are unaltered. -/
noncomputable def withAuxiliary (U : ∀ a, (S.chart a).Auxiliary)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hd : ∀ i H T, S.name i H≠S.name i T →
      |S.newValue (fun a => (S.chart a).auxiliaryField (U a) lam hlam) i H-S.oldValue i H| ≤
        |H-T|/8) : BState M κ lam Ω μ where
  sets := S.fieldUpdate (fun a => (S.chart a).auxiliaryField (U a) lam hlam) hk hsmall hlam hd
  count := S.count
  chart a := (S.chart a).withAuxiliary (U a)
  labels := S.labels
  name := S.name
  height_in i H := by simpa only [BData.withAuxiliary_band] using S.height_in i H
  component_in i H := (BData.withAuxiliary_uses _ _ _).mpr (S.component_in i H)
  switch_name := S.switch_name
  represents ω i H := by
    change Threshold.active (S.labels (S.name i H)) H
      (S.newValue (fun a => (S.chart a).auxiliaryField (U a) lam hlam) i H) ω ↔ _
    unfold newValue
    rw [BData.auxiliaryField_value]

end BState
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Ambient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)}

/-- Full columns regarded in the unrestricted path pseudometric. Connectedness
here is supplied by the connected graph realization, not an extra condition on
the embedding theorem. -/
structure Ambient (M : Model (k+1)) where
  root : Fin (k+1)
  connected : ∀ i, (M.activeGraph Set.univ).Reachable root i

namespace Ambient
variable (A : Ambient M)

def point (i : Fin (k+1)) (H : ℝ) : M.Point Set.univ A.root :=
  ⟨i,H,Set.mem_univ H,A.connected i⟩

lemma point_dist (i : Fin (k+1)) (H T : ℝ) :
    dist (A.point i H) (A.point i T)=|H-T| := (A.point i H).dist_same_column _ rfl

lemma point_switch (i j : Fin (k+1)) (H : ℝ) (hh : H ∈ M.heights i j) :
    dist (A.point i H) (A.point j H)=0 := by
  apply le_antisymm _ dist_nonneg
  simpa only [point,sub_self,abs_zero,add_zero] using
    (A.point i H).dist_le_switch (A.point j H) (Set.mem_univ H) hh

lemma taper_switch {r : ℝ} (hr : 0 < r) (S : Set (M.Point Set.univ A.root))
    (i j : Fin (k+1)) (H : ℝ) (hh : H ∈ M.heights i j) :
    Increment.taper S r (A.point i H)=Increment.taper S r (A.point j H) := by
  have h := Increment.taper_difference (S := S) hr (A.point i H) (A.point j H)
  rw [A.point_switch i j H hh,zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- Every signed increment from the recorded lifetime is retained. Regions are
those at their creation times and are not re-tapered after subsequent changes. -/
noncomputable def historyField {I : Set ℝ} (s : M.Field I 4) (a b : Fin (k+1))
    {m : ℕ} (r : Fin m → ℝ) (regions : Fin m → Set (M.Point Set.univ A.root))
    (sign : Fin m → Bool) (c : ℝ) (hc : 0 < c) (hcr : c ≤ 4)
    (hr : ∀ j, 0 < r j)
    (hsep : ∀ i j, i ≠ j → 10*r i ≤ c*r j ∨ 10*r j ≤ c*r i) : M.Field I 100 where
  value i H := ∑ j, Increment.signedDamped (sign j) (c*r j) (r j)
    ((s.transverse (by norm_num) a b).value i)
    (fun T : I => Increment.taper (regions j)ᶜ (r j) (A.point i T.val)) H
  vertical i := by
    have h := Increment.damped_lifetime Finset.univ (r := r)
      (t := (s.transverse (by norm_num) a b).value i)
      (w := fun j (H : I) => Increment.taper (regions j)ᶜ (r j) (A.point i H.val))
      sign hc hcr (fun j _ => hr j) ((s.transverse (by norm_num) a b).vertical i)
      (fun j _ H => Increment.taper_bounds (hr j) (A.point i H.val))
      (fun j _ H T => by
        have h := Increment.taper_difference (S := (regions j)ᶜ) (hr j) (A.point i H.val) (A.point i T.val)
        simpa only [A.point_dist,Subtype.dist_eq,Real.dist_eq] using h)
      (fun i _ j _ hij => hsep i j hij)
    simpa only [Finset.mem_univ,Finset.sum_const_zero,ite_true] using h.weaken (by norm_num : (68:ℝ≥0) ≤ 100)
  switch i j H hh := by
    apply Finset.sum_congr rfl
    intro q _
    have ht := (s.transverse (by norm_num) a b).switch i j H hh
    have hw := A.taper_switch (hr q) (regions q)ᶜ i j H.val hh
    simp only [Increment.signedDamped,Increment.damped,ht,hw]

end Ambient
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model.Ambient
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)}

/-- The literal finite list of increments already recorded for an identifier.
Regions are recorded at creation time, as required by . -/
structure History (A : Ambient M) (c : ℝ) where
  count : ℕ
  radius : Fin count → ℝ
  region : Fin count → Set (M.Point Set.univ A.root)
  sign : Fin count → Bool
  positive : ∀ i, 0 < radius i
  separated : ∀ i j, i≠j → 10*radius i ≤ c*radius j ∨ 10*radius j ≤ c*radius i

namespace History
variable {A : Ambient M} {c : ℝ}

def empty (A : Ambient M) (c : ℝ) : History A c where
  count := 0
  radius := Fin.elim0
  region := Fin.elim0
  sign := Fin.elim0
  positive := fun i => Fin.elim0 i
  separated := fun i => Fin.elim0 i

noncomputable def field (H : History A c) {I : Set ℝ} (s : M.Field I 4)
    (a b : Fin (k+1)) (hc : 0 < c) (hcr : c ≤ 4) : M.Field I 100 :=
  A.historyField s a b H.radius H.region H.sign c hc hcr H.positive H.separated

lemma field_empty {I : Set ℝ} (s : M.Field I 4) (a b : Fin (k+1))
    (hc : 0 < c) (hcr : c ≤ 4) (i : Fin (k+1)) (T : I) :
    ((empty A c).field s a b hc hcr).value i T=0 := by
  simp only [field,empty,historyField]
  exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)

def append (H : History A c) (r : ℝ) (S : Set (M.Point Set.univ A.root)) (e : Bool)
    (hr : 0 < r) (hcross : ∀ j, 10*r ≤ c*H.radius j) : History A c where
  count := H.count+1
  radius := Fin.snoc H.radius r
  region := Fin.snoc H.region S
  sign := Fin.snoc H.sign e
  positive i := by
    cases i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hr
    | cast i => simpa only [Fin.snoc_castSucc] using H.positive i
  separated i j hij := by
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j => exact Or.inl (by simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j)
    | cast i =>
      cases j using Fin.lastCases with
      | last => exact Or.inr (by simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross i)
      | cast j =>
        simpa only [Fin.snoc_castSucc] using H.separated i j (fun h => hij (congrArg Fin.castSucc h))

/-- No earlier summand is re-tapered or otherwise modified by appending a step. -/
lemma field_append_value (H : History A c) (r : ℝ) (S : Set (M.Point Set.univ A.root))
    (e : Bool) (hr : 0 < r) (hcross : ∀ j, 10*r ≤ c*H.radius j)
    {I : Set ℝ} (s : M.Field I 4) (a b : Fin (k+1)) (hc : 0 < c) (hcr : c ≤ 4)
    (i : Fin (k+1)) (T : I) :
    ((H.append r S e hr hcross).field s a b hc hcr).value i T =
      (H.field s a b hc hcr).value i T+
      Increment.signedDamped e (c*r) r ((s.transverse (by norm_num) a b).value i)
        (fun U : I => Increment.taper Sᶜ r (A.point i U.val)) T := by
  change (∑ j : Fin (H.count+1), _) = (∑ j : Fin H.count, _)+_
  rw [Fin.sum_univ_castSucc]
  simp only [append,Fin.snoc_castSucc,Fin.snoc_last]

end History
end PlanarL1.Columns.Model.Ambient



end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData
variable {A : Ambient M} {c : ℝ}

def Recorded (D : BData M) (H : A.History c) (hc : 0 < c) (hcr : c ≤ 4) : Prop :=
  match D with
  | .ordinary _ => True
  | .ordered D => ∀ i T, D.auxiliary.value i T=(H.field D.base D.lower D.upper hc hcr).value i T

noncomputable def incrementAuxiliary (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) : D.Auxiliary :=
  match D with
  | .ordinary _ => ()
  | .ordered D => (H.append r region e hr hcross).field D.base D.lower D.upper hc hcr

/-- The actual recorded increment, not a replacement of the old history. -/
lemma increment_difference (D : OrderedData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j)
    (hrec : (BData.ordered D).Recorded H hc hcr)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (T : D.band) :
    ((BData.ordered D).auxiliaryField
      ((BData.ordered D).incrementAuxiliary H r region e hc hcr hr hcross) lam hlam).value i T -
      D.value lam i T =
      lam*Increment.signedDamped e (c*r) r ((D.base.transverse (by norm_num) D.lower D.upper).value i)
        (fun U : D.band => Increment.taper regionᶜ r (A.point i U.val)) T := by
  change ((D.withAuxiliary ((H.append r region e hr hcross).field D.base D.lower D.upper hc hcr)).field lam hlam).value i T - D.value lam i T = _
  erw [OrderedData.field_value,OrderedData.withAuxiliary_value]
  rw [hrec i T,Ambient.History.field_append_value]
  ring

lemma increment_boundary (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) (hrec : D.Recorded H hc hcr)
    (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (i : Fin (k+1)) (T : D.band) (U : ℝ) (hU : A.point i U ∉ region) :
    |(D.auxiliaryField (D.incrementAuxiliary H r region e hc hcr hr hcross) lam hlam).value i T -
      D.value lam i T| ≤ (lam:ℝ)*10*|T.val-U| := by
  cases D with
  | ordinary D =>
    change |D.value i T-D.value i T| ≤ _
    rw [sub_self,abs_zero]
    positivity
  | ordered D =>
    dsimp only [BData.value]
    erw [increment_difference D H r region e hc hcr hr hcross hrec lam hlam]
    rw [abs_mul,abs_of_nonneg lam.coe_nonneg]
    have hb := Increment.signed_tapered_magnitude e (mul_pos hc hr) hr
      (by nlinarith : 2*(c*r) ≤ 8*r) (show A.point i U ∈ regionᶜ from hU)
      (x := A.point i T.val) (q := (D.base.transverse (by norm_num) D.lower D.upper).value i T)
    rw [A.point_dist] at hb
    simpa only [Increment.signedDamped,Increment.damped,mul_assoc] using
      mul_le_mul_of_nonneg_left hb lam.coe_nonneg

/-- Ordinary identifiers record no increments. Ordered identifiers keep the
entire old list and append precisely the new signed region-tapered term. -/
def incrementHistory (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hr : 0 < r) (hcross : ∀ j, 10*r ≤ c*H.radius j) : A.History c :=
  match D with
  | .ordinary _ => H
  | .ordered _ => H.append r region e hr hcross

lemma increment_recorded (D : BData M) (H : A.History c)
    (r : ℝ) (region : Set (M.Point Set.univ A.root)) (e : Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ j, 10*r ≤ c*H.radius j) :
    (D.withAuxiliary (D.incrementAuxiliary H r region e hc hcr hr hcross)).Recorded
      (D.incrementHistory H r region e hr hcross) hc hcr := by
  cases D with
  | ordinary D => trivial
  | ordered D => exact fun _ _ => rfl

end BData

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  (S : BState M κ lam Ω μ) (A : Ambient M)

/-- A region is exactly the old identifier's inverse image in the full-column
ambient model. No approximation of its boundary is used. -/
def region (a : Fin (S.count+1)) : Set (M.Point Set.univ A.root) :=
  {p | S.name p.column p.height=a}

lemma other_height_not_region (i : Fin (k+1)) (H T : ℝ)
    (hne : S.name i H≠S.name i T) : A.point i T ∉ S.region A (S.name i H) := by
  exact fun h => hne h.symm

noncomputable def incrementFields {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hlam : lam ≤ (1:ℝ≥0)/100) : ∀ a, M.Field (S.chart a).band 5 :=
  fun a => (S.chart a).auxiliaryField
    ((S.chart a).incrementAuxiliary (hist a) r (S.region A a) (sign a) hc hcr hr (hcross a)) lam hlam

lemma increment_boundary {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hlam : lam ≤ (1:ℝ≥0)/100) (hsmall : κ*(lam:ℝ)*10 ≤ 1/8)
    (i : Fin (k+1)) (H T : ℝ) (hne : S.name i H≠S.name i T) :
    |S.newValue (S.incrementFields A hist sign hc hcr hr hcross hlam) i H-S.oldValue i H| ≤
      |H-T|/8 := by
  unfold newValue oldValue
  rw [← mul_sub,abs_mul,abs_of_nonneg hk]
  have hb := (S.chart (S.name i H)).increment_boundary (hist (S.name i H)) r
    (S.region A (S.name i H)) (sign (S.name i H)) hc hcr hr (hcross (S.name i H))
    (hrec (S.name i H)) lam hlam i ⟨H,S.height_in i H⟩ T
    (S.other_height_not_region A i H T hne)
  calc
    _ ≤ κ*((lam:ℝ)*10*|H-T|) := mul_le_mul_of_nonneg_left hb hk
    _ ≤ |H-T|/8 := by nlinarith [mul_le_mul_of_nonneg_right hsmall (abs_nonneg (H-T))]

noncomputable def increment {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) : BState M κ lam Ω μ :=
  S.withAuxiliary
    (fun a => (S.chart a).incrementAuxiliary (hist a) r (S.region A a) (sign a) hc hcr hr (hcross a))
    hk hsmall hlam (S.increment_boundary A hist sign hc hcr hr hcross hrec hk hlam hboundary)

lemma increment_recorded {c r : ℝ}
    (hist : Fin (S.count+1) → A.History c) (sign : Fin (S.count+1) → Bool)
    (hc : 0 < c) (hcr : c ≤ 4) (hr : 0 < r)
    (hcross : ∀ a j, 10*r ≤ c*(hist a).radius j)
    (hrec : ∀ a, (S.chart a).Recorded (hist a) hc hcr)
    (hk : 0 ≤ κ) (hsmall : κ*5 ≤ 1/2) (hlam : lam ≤ (1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10 ≤ 1/8) (a : Fin (S.count+1)) :
    ((S.increment A hist sign hc hcr hr hcross hrec hk hsmall hlam hboundary).chart a).Recorded
      ((S.chart a).incrementHistory (hist a) r (S.region A a) (sign a) hr (hcross a)) hc hcr :=
  (S.chart a).increment_recorded (hist a) r (S.region A a) (sign a) hc hcr hr (hcross a)

end BState
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Execution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1

/-- Finite adaptive execution trees. Every node makes an actual uniform finite
choice; its continuation, including the number of later choices, may depend on
that choice. This is the finite probability law used by the manuscript. -/
inductive Execution (α : Type*) where
  | pure : α → Execution α
  | choose (n : ℕ) : (Fin (n+1) → Execution α) → Execution α

namespace Execution
attribute [local instance] Classical.propDecidable
variable {α β : Type*}

noncomputable def mean : Execution α → (α → ℝ) → ℝ
  | .pure x, f => f x
  | .choose n E, f => (∑ i, mean (E i) f)/(n+1)

noncomputable def prob (E : Execution α) (P : α → Prop) : ℝ := by
  classical
  exact E.mean (fun x => if P x then 1 else 0)

def bind : Execution α → (α → Execution β) → Execution β
  | .pure x, f => f x
  | .choose n E, f => .choose n (fun i => bind (E i) f)

lemma mean_const (E : Execution α) (c : ℝ) : E.mean (fun _ => c) = c := by
  induction E with
  | pure x => rfl
  | choose n E ih => simp [mean,ih]; field_simp

lemma mean_mono (E : Execution α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    E.mean f ≤ E.mean g := by
  induction E with
  | pure x => exact h x
  | choose n E ih => exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => ih i)) (by positivity)

lemma mean_nonneg (E : Execution α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ E.mean f := by
  simpa only [mean_const] using E.mean_mono h

end Execution
end PlanarL1

namespace PlanarL1.Execution
variable {α β ι : Type*}

noncomputable def uniform [Fintype α] [Nonempty α] : Execution α := by
  classical
  let e : Fin (Fintype.card α-1+1) ≃ α :=
    (finCongr (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance))).trans
      (Fintype.equivFin α).symm
  exact .choose (Fintype.card α-1) (fun i => .pure (e i))

end PlanarL1.Execution


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Parameters
noncomputable section
/-- Universal ordered parameter choices. The two free widths are chosen
strictly smaller than every displayed upper bound, not adapted to a graph. -/
def R : ℝ := 1/10^8
def D : ℝ := 1/10^3
def g : ℝ := 1/10^14
def j : ℝ := 1/10^20
def epsilon : ℝ := 1/10^24
def EA : ℝ := epsilon/1000
def EB : ℝ := R/1000
def zetaA : ℝ := epsilon/100
def zetaB : ℝ := 1/10
def a₁ : ℝ := 1/10^100
def a₂ : ℝ := 1/10^160
def kappaA : ℝ := a₁/10^6
def kappaB : ℝ := a₂/10^6
def lambda : ℝ := R/(10^12*100)

lemma interpolationA : 0<EA ∧ 0<a₁ ∧ 0<zetaA ∧ zetaA<1 ∧
    a₁ ≤ zetaA*(EA/8)/1000000 := by
  norm_num [EA,epsilon,a₁,zetaA]
lemma interpolationB : 0<EB ∧ 0<a₂ ∧ 0<zetaB ∧ zetaB<1 ∧
    a₂ ≤ zetaB*(EB/8)/1000000 := by
  norm_num [EB,R,a₂,zetaB]
lemma thinA : a₁≤(1/1000:ℝ)/1000 := by norm_num [a₁]
lemma verticalA : 0≤kappaA ∧ kappaA*max 1 (3/(9*a₁/100))≤1 ∧
    kappaA*(3/(9*a₁/100))<1 := by
  norm_num [kappaA,a₁]
lemma verticalB : 0≤kappaB ∧ kappaB*max 5 (3/(9*a₂/100))≤1 ∧
    kappaB*(3/(9*a₂/100))<1 ∧ kappaB*5≤1 := by
  norm_num [kappaB,a₂]

/-- Numeric input to the literal interpolation hierarchy. -/
structure Interpolation where
  error : ℝ
  width : ℝ
  zeta : ℝ
  error_pos : 0 < error
  width_pos : 0 < width
  zeta_pos : 0 < zeta
  zeta_lt : zeta < 1
  width_bound : width ≤ zeta*(error/8)/1000000

def broad : Interpolation := ⟨EA,a₁,zetaA,interpolationA.1,
  interpolationA.2.1,interpolationA.2.2.1,interpolationA.2.2.2.1,
  interpolationA.2.2.2.2⟩
def narrow : Interpolation := ⟨EB,a₂,zetaB,interpolationB.1,
  interpolationB.2.1,interpolationB.2.2.1,interpolationB.2.2.2.1,
  interpolationB.2.2.2.2⟩

end
end PlanarL1.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Tiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1
namespace Tiling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal closed height bands. Adjacent bands share only their endpoint,
where every clipping proposal retains the old field. -/
def band (a q : ℝ) (k : ℤ) : Set ℝ := Set.Icc (q+k*a) (q+(k+1)*a)

noncomputable def index (a q h : ℝ) : ℤ := ⌊(h-q)/a⌋

lemma mem_band_index {a : ℝ} (ha : 0<a) (q h : ℝ) : h ∈ band a q (index a q h) := by
  have hl := Int.floor_le ((h-q)/a)
  have hu := Int.lt_floor_add_one ((h-q)/a)
  have hl' := (le_div_iff₀ ha).mp hl
  have hu' := (div_lt_iff₀ ha).mp hu
  change q+↑⌊(h-q)/a⌋*a≤h ∧ h≤q+(↑⌊(h-q)/a⌋+1)*a
  exact ⟨by linarith,by linarith⟩

lemma overlap {a : ℝ} (ha : 0<a) {q h : ℝ} {j k : ℤ} (hjk : j<k)
    (hj : h ∈ band a q j) (hk : h ∈ band a q k) :
    h=q+((j:ℝ)+1)*a ∧ h=q+(k:ℝ)*a := by
  have hcast : (j:ℝ)+1≤k := by exact_mod_cast hjk
  have hm := mul_le_mul_of_nonneg_right hcast ha.le
  dsimp [band] at hj hk
  constructor <;> linarith [hj.2,hk.1]

/-- The finite list is precisely the closed bands meeting the prescribed
closed height window, not a truncation at individual points of a band. -/
noncomputable def processed (a q L U : ℝ) : Finset ℤ :=
  (Finset.Icc (index a q L-1) (index a q U)).filter
    (fun k => (band a q k ∩ Set.Icc L U).Nonempty)

lemma mem_processed {a : ℝ} (ha : 0<a) (q L U : ℝ) (k : ℤ) :
    k ∈ processed a q L U ↔ (band a q k ∩ Set.Icc L U).Nonempty := by
  rw [processed,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_,he⟩
    obtain ⟨h,hb,hL,hU⟩ := he
    dsimp [band] at hb
    rw [Finset.mem_Icc]
    constructor
    · have htt : (L-q)/a ≤ (k:ℝ)+1 := (div_le_iff₀ ha).mpr (by linarith [hb.2])
      have hf : index a q L ≤ k+1 := by
        simpa only [index,Int.floor_intCast_add,Int.floor_intCast,Int.floor_one] using
          Int.floor_le_floor htt
      omega
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ ha).mpr
      linarith [hb.1]

/-- Small-ball height loss is proximity to a genuine band boundary. -/
def NearBoundary (a q h t : ℝ) : Prop := ∃ k : ℤ, |h-(q+k*a)|≤t

end Tiling
end PlanarL1

end


section

namespace PlanarL1.Tiling

/-- Strict padding in the actual floor-indexed band. -/
def Padded (a q h t : ℝ) : Prop :=
  q+(index a q h:ℝ)*a+t<h ∧ h<q+((index a q h:ℝ)+1)*a-t

lemma padded_of_avoid {a q h t : ℝ} (ha : 0<a) (hn : ¬NearBoundary a q h t) :
    Padded a q h t := by
  have hm := mem_band_index ha q h
  constructor
  · by_contra he
    apply hn
    refine ⟨index a q h,?_⟩
    rw [abs_of_nonneg (by linarith [hm.1])]
    linarith
  · by_contra he
    apply hn
    refine ⟨index a q h+1,?_⟩
    rw [Int.cast_add,Int.cast_one,abs_of_nonpos (by linarith [hm.2])]
    linarith

lemma index_eq_of_mem_lt {a q h : ℝ} (ha : 0<a) (k : ℤ)
    (hl : q+(k:ℝ)*a≤h) (hu : h<q+((k:ℝ)+1)*a) : index a q h=k := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ ha).mpr (by linarith),(div_lt_iff₀ ha).mpr (by linarith)⟩

lemma band_subset_of_padding {a b q p h t : ℝ} (_ha : 0<a) (hb : 0<b)
    (hp : Padded a q h t) (hbt : b≤t) :
    band b p (index b p h) ⊆ band a q (index a q h) := by
  have hh := mem_band_index hb p h
  intro x hx
  change q+(index a q h:ℝ)*a≤x ∧ x≤q+((index a q h:ℝ)+1)*a
  change p+(index b p h:ℝ)*b≤x ∧ x≤p+((index b p h:ℝ)+1)*b at hx
  change p+(index b p h:ℝ)*b≤h ∧ h≤p+((index b p h:ℝ)+1)*b at hh
  exact ⟨by linarith [hp.1,hh.2,hx.1],by linarith [hp.2,hh.1,hx.2]⟩

end PlanarL1.Tiling

namespace PlanarL1.Tiling
open Parameters FiniteRandom

lemma narrow_contained {q p h : ℝ} (hp : Padded a₁ q h (a₁/10)) :
    band a₂ p (index a₂ p h) ⊆ band a₁ q (index a₁ q h) :=
  band_subset_of_padding interpolationA.2.1 interpolationB.2.1 hp (by norm_num [a₁,a₂])

end PlanarL1.Tiling

end


section

namespace PlanarL1.Tiling
lemma unique_band_of_padded {a q h t : ℝ} (ha : 0<a) (ht : 0≤t)
    (hp : Padded a q h t) {n : ℤ} (hn : h ∈ band a q n) : n=index a q h := by
  rcases lt_trichotomy n (index a q h) with hl | he | hu
  · have hnl : (n:ℝ)+1≤(index a q h:ℝ) := by exact_mod_cast (show n+1 ≤ index a q h by omega)
    have hb := mul_le_mul_of_nonneg_right hnl ha.le
    have hx := hn.2
    change h≤q+((n:ℝ)+1)*a at hx
    have hh := hp.1
    change q+(index a q h:ℝ)*a+t<h at hh
    linarith
  · exact he
  · have hnl : (index a q h:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show index a q h+1≤n by omega)
    have hb := mul_le_mul_of_nonneg_right hnl ha.le
    have hx := hn.1
    change q+(n:ℝ)*a≤h at hx
    have hh := hp.2
    change h<q+((index a q h:ℝ)+1)*a-t at hh
    linarith
end PlanarL1.Tiling

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_BandTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n)

namespace BandTrees
variable (P : Parameters.Interpolation) (lo : ℝ)

def band : Set ℝ := Set.Icc lo (lo+P.width)
abbrev Component := (M.activeGraph (band P lo)).ConnectedComponent
noncomputable def root (C : Component M P lo) : Fin n := C.nonempty_supp.choose
lemma root_mem (C : Component M P lo) : root M P lo C ∈ C.supp := C.nonempty_supp.choose_spec

noncomputable def middle : ℝ := lo+P.width/2
lemma middle_mem : middle P lo ∈ band P lo := by
  constructor <;> dsimp [middle] <;> linarith [P.width_pos]

noncomputable def point (C : Component M P lo) (i : C.supp) :
    M.Point (band P lo) (root M P lo C) :=
  ⟨i.val,middle P lo,middle_mem P lo,C.reachable_of_mem_supp (root_mem M P lo C) i.property⟩
noncomputable def base (C : Component M P lo) : M.Point (band P lo) (root M P lo C) :=
  point M P lo C ⟨root M P lo C,root_mem M P lo C⟩
noncomputable def tree (C : Component M P lo) :
    Point.RadialTree (M := M) (J := band P lo) (root := root M P lo C) where
  base := base M P lo C
  δ := P.error/8
  a := P.width
  ζ := P.zeta
  delta_pos := div_pos P.error_pos (by norm_num)
  width_pos := P.width_pos
  zeta_pos := P.zeta_pos
  zeta_lt_one := P.zeta_lt
  width_bound := P.width_bound
  half_width := by
    intro T hT
    change |lo+P.width/2-T|≤P.width/2
    obtain ⟨h1,h2⟩ := hT
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  closed_band := isClosed_Icc
  interval_band := Set.ordConnected_Icc

lemma reachable_mem (C : Component M P lo) {i : Fin n}
    (hi : (M.activeGraph (band P lo)).Reachable (root M P lo C) i) : i ∈ C.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact (SimpleGraph.ConnectedComponent.sound hi).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp (root_mem M P lo C))

/-- Only the radial layers meeting a column occur. No infinite layer family
or arbitrary cut-off is added to the finite random step. -/
noncomputable def levels (C : Component M P lo) (phase width : ℝ) : Finset ℤ :=
  Finset.univ.image (fun i : C.supp => Tiling.index width phase (dist (base M P lo C) (point M P lo C i)))

lemma same_level (C : Component M P lo) {phase width : ℝ} (hw : 0 < width)
    {k l : ℤ} {i : Fin n}
    (hi : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo) (phase+k*width) width)
    (hj : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo) (phase+l*width) width) : k=l := by
  obtain ⟨hr,hl,hu⟩ := hi
  obtain ⟨hr',hl',hu'⟩ := hj
  by_contra hn
  rcases lt_or_gt_of_ne hn with hk | hk
  · have hh : (k:ℝ)+1≤l := by exact_mod_cast hk
    have hmul := mul_le_mul_of_nonneg_right hh hw.le
    linarith
  · have hh : (l:ℝ)+1≤k := by exact_mod_cast hk
    have hmul := mul_le_mul_of_nonneg_right hh hw.le
    linarith

abbrev MainIndex (C : Component M P lo) (phase : ℝ) :=
  Σ k : levels M P lo C phase (1/1000), MainCell.Cell (tree M P lo C) (phase+k.val*(1/1000))

noncomputable instance instFintypeMainIndex (C : Component M P lo) (phase : ℝ) :
    Fintype (MainIndex M P lo C phase) := Fintype.ofFinite _

noncomputable def anchor (C : Component M P lo) (phase : ℝ) (K : MainIndex M P lo C phase) :
    M.Point (band P lo) (root M P lo C) :=
  let i := K.2.nonempty_supp.choose
  ⟨i.val,middle P lo,middle_mem P lo,i.property.choose⟩

lemma anchor_mem (C : Component M P lo) (phase : ℝ) (K : MainIndex M P lo C phase) :
    (anchor M P lo C phase K).column ∈ ColumnOrder.componentColumns K.2 :=
  ⟨K.2.nonempty_supp.choose,K.2.nonempty_supp.choose_spec,rfl⟩

lemma same_component {V : Type*} {G : SimpleGraph V} {S : Set V}
    {C D : (G.induce S).ConnectedComponent} {i : V}
    (hi : i ∈ ColumnOrder.componentColumns C) (hj : i ∈ ColumnOrder.componentColumns D) : C=D := by
  obtain ⟨u,hu,rfl⟩ := hi
  obtain ⟨v,hv,he⟩ := hj
  have hvu : v=u := Subtype.ext he
  subst v
  exact ((SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff D u).mp hv)

lemma main_disjoint (C : Component M P lo) (phase : ℝ) {K L : MainIndex M P lo C phase}
    (hne : K≠L) : Disjoint (ColumnOrder.componentColumns K.2) (ColumnOrder.componentColumns L.2) := by
  apply Set.disjoint_left.mpr
  intro i hi hj
  have hk := ColumnOrder.componentColumns_subset K.2 hi
  have hl := ColumnOrder.componentColumns_subset L.2 hj
  have he : K.1=L.1 := Subtype.ext (same_level M P lo C (by norm_num) hk hl)
  obtain ⟨K,Ck⟩ := K
  obtain ⟨L,Cl⟩ := L
  dsimp only at he
  subst L
  have he' : Ck=Cl := same_component hi hj
  subst Cl
  exact hne rfl

end BandTrees
end PlanarL1.Columns.Model

end


section

namespace PlanarL1.Columns.Model
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {i j r s : Fin n}

namespace Path
/-- A short path stays in a height interval containing its entire permitted
height deviation. This restricts the actual switching path, not a metric model. -/
lemma restrict_of_length (p : M.Path I i j) (a b c t : ℝ)
    (hJ : ∀ H, |H-c|≤t → H ∈ J) (hp : |a-c|+p.length a b≤t) :
    ∃ q : M.Path J i j, q.length a b=p.length a b := by
  induction p generalizing a with
  | nil i => exact ⟨.nil i,rfl⟩
  | @cons i u j H hH hs p ih =>
    have htri := abs_sub_le H a c
    rw [abs_sub_comm H a] at htri
    have htail : |H-c|+p.length H b≤t := by
      change |a-c|+(|a-H|+p.length H b)≤t at hp
      linarith
    have hh : H ∈ J := hJ H (by linarith [p.length_nonneg H b])
    obtain ⟨q,hq⟩ := ih H htail
    exact ⟨.cons H hh hs q,by simp only [length,hq]⟩
end Path

namespace Point
lemma dist_coordinates (x y : M.Point J r) (x' y' : M.Point J s)
    (hx : x.column=x'.column) (hX : x.height=x'.height)
    (hy : y.column=y'.column) (hY : y.height=y'.height) : dist x y=dist x' y' := by
  change (⨅ p : M.Path J x.column y.column, p.length x.height y.height)=
    (⨅ p : M.Path J x'.column y'.column, p.length x'.height y'.height)
  rw [hx,hX,hy,hY]

/-- On a ball farther from the band ends than its radius, unrestricted shortest
paths give exact intrinsic distances from its center. -/
lemma local_point (x y : M.Point I r) (x' : M.Point J s)
    (hx : x'.column=x.column) (hX : x'.height=x.height)
    (hI : IsClosed I) (hJI : J ⊆ I) {t : ℝ}
    (hJ : ∀ H, |H-x.height|≤t → H ∈ J) (hxy : dist x y≤t) :
    ∃ y' : M.Point J s, y'.column=y.column ∧ y'.height=y.height ∧ dist x' y'=dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hI y
  obtain ⟨q,hq⟩ := p.restrict_of_length x.height y.height x.height t hJ (by simpa [hp] using hxy)
  have hyJ : y.height ∈ J := hJ _ (by
    rw [abs_sub_comm]
    exact (x.height_change_le y).trans hxy)
  let yy : M.Point J s := ⟨y.column,y.height,hyJ,x'.reachable.trans (hx ▸ q.word.reachable)⟩
  refine ⟨yy,rfl,rfl,le_antisymm ?_ ?_⟩
  · have hh := x'.distance_le yy (hx ▸ q)
    change dist x' yy ≤ (hx ▸ q).length x'.height yy.height at hh
    have he : (hx ▸ q).length x'.height yy.height=q.length x.height y.height := by
      obtain ⟨xc,xh,xi,xr⟩ := x'
      dsimp only at hx hX
      subst xc
      subst xh
      rfl
    rw [he,hq,hp] at hh
    exact hh
  · have h := x'.dist_widen_le yy hJI
    have he := dist_coordinates (x'.widen hJI) (yy.widen hJI) x y hx hX rfl rfl
    exact he ▸ h
end Point
end PlanarL1.Columns.Model

end


section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace Field
lemma constant_ordered {I : Set ℝ} (c : ℝ) (a b : Fin (k+1)) :
    (constant M I c).OrderedFrom a b := by
  exact ⟨fun _ _ => le_rfl,fun _ _ _ _ _ => le_rfl,fun _ _ _ _ _ => le_rfl⟩
end Field

namespace OrdinaryData
/-- The support required by a secondary group is constructed from the actual
old point source. The comparison outside that source's component is never used. -/
lemma support_at (D : OrdinaryData M) (i : Fin (k+1)) (H : ℝ) (hi : D.Contains i H) :
    ∃ (F : M.Field D.band 1) (a b : Fin (k+1)), F.OrderedFrom a b ∧
      F.value i ⟨H,hi.1⟩=D.comparison.value i ⟨H,hi.1⟩ ∧
      ∀ (j : Fin (k+1)) (T : ℝ) (hj : D.Contains j T),
        F.value j ⟨T,hj.1⟩≤D.comparison.value j ⟨T,hj.1⟩ := by
  by_cases ho : D.origin=none
  ·
    refine ⟨Field.constant M D.band 0,0,0,Field.constant_ordered 0 0 0,?_,?_⟩
    · simp only [comparison,ho]
    · intro j T hj
      simp only [comparison,ho,Field.constant,le_refl]
  · obtain ⟨o,ho⟩ := Option.ne_none_iff_exists'.mp ho
    let w : M.Point D.band o.1 := ⟨i,H,hi.1,hi.2 o.1 o.2 ho⟩
    obtain ⟨F,hord,_,_,hw,hF⟩ := Point.exists_ordered_support D.closed o.2 w
    have hv (j : Fin (k+1)) (T : ℝ) (hj : D.Contains j T) :
        D.comparison.value j ⟨T,hj.1⟩=
          dist o.2 (⟨j,T,hj.1,hj.2 o.1 o.2 ho⟩ : M.Point D.band o.1) := by
      simp only [comparison,ho]
      exact o.2.radialField_eval (⟨j,T,hj.1,hj.2 o.1 o.2 ho⟩ : M.Point D.band o.1)
    refine ⟨F,o.2.column,w.column,hord,?_,?_⟩
    · rw [hv i H hi]
      exact hw
    · intro j T hj
      rw [hv j T hj]
      exact hF (⟨j,T,hj.1,hj.2 o.1 o.2 ho⟩ : M.Point D.band o.1)
end OrdinaryData

namespace Ambient
variable (A : Ambient M)

lemma coordinate_point (x : M.Point Set.univ A.root) : A.point x.column x.height=x := by
  cases x
  rfl

/-- A chart identifier is common on the actual unrestricted closed ball.
The test includes every representative, not merely the original vertices. -/
def Common {ι : Type*} (name : Fin (k+1) → ℝ → ι)
    (x : M.Point Set.univ A.root) (r : ℝ) (a : ι) : Prop :=
  ∀ y : M.Point Set.univ A.root, dist x y ≤ r → name y.column y.height=a

lemma Common.center {ι : Type*} {name : Fin (k+1) → ℝ → ι}
    {x : M.Point Set.univ A.root} {r : ℝ} {a : ι}
    (h : A.Common name x r a) (hr : 0 ≤ r) : name x.column x.height=a := by
  exact h x (by simpa using hr)

end Ambient

namespace OrdinaryState
variable {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M κ Ω μ)

/-- Band containment follows from a common geometric ball and ordinary
vertical segments, rather than being assumed in a secondary update. -/
lemma ball_band {x : M.Point Set.univ A.root} {a : Fin (S.count+1)} {r : ℝ}
    (h : A.Common S.name x r a) {J : Set ℝ}
    (hJ : ∀ H ∈ J, |x.height-H| ≤ r) : J ⊆ (S.chart a).band := by
  intro H hH
  have hh := h (A.point x.column H) (by
    conv_lhs => lhs; rw [← A.coordinate_point x]
    rw [A.point_dist]
    exact hJ H hH)
  change S.name x.column H = a at hh
  simpa only [hh] using S.height_in x.column H
end OrdinaryState

namespace BState
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : BState M κ lam Ω μ)

lemma height_named (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1))
    (ha : S.name i H=a) : H ∈ (S.chart a).band := by
  subst a
  exact S.height_in i H

lemma uses_named (i : Fin (k+1)) (H : ℝ) (a : Fin (S.count+1))
    (ha : S.name i H=a) : (S.chart a).Uses i := by
  subst a
  exact S.component_in i H

lemma ball_band {x : M.Point Set.univ A.root} {a : Fin (S.count+1)} {r : ℝ}
    (h : A.Common S.name x r a) {J : Set ℝ}
    (hJ : ∀ H ∈ J, |x.height-H| ≤ r) : J ⊆ (S.chart a).band := by
  intro H hH
  have hh := h (A.point x.column H) (by
    conv_lhs => lhs; rw [← A.coordinate_point x]
    rw [A.point_dist]
    exact hJ H hH)
  exact S.height_named x.column H a hh
end BState
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_FiniteL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.FiniteL1

open MeasureTheory

variable {I : Type*} [Fintype I] [MeasurableSpace I] [DiscreteMeasurableSpace I]

noncomputable def ofFunction (f : I → ℝ) : Lp ℝ 1 (Measure.count : Measure I) :=
  (MemLp.of_discrete : MemLp f 1 Measure.count).toLp f

/-- The final finite cut-coordinate formula, valued in the ACTUAL real L1
space requested by the main theorem, rather than an abstract cut cone. -/
noncomputable def cutMap {V : Type*} (cut : I → Set V) (weight : I → ℝ) (v : V) :
    Lp ℝ 1 (Measure.count : Measure I) := by
  classical
  exact ofFunction (fun i => if v ∈ cut i then weight i else 0)

end PlanarL1.FiniteL1



end

section

namespace PlanarL1.FiniteL1
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] (μ : Measure Ω)

/-- Binary measurable assignments with integrable pair differences; individual
sets may have infinite measure, exactly as for the paper's label half-lines. -/
structure BinarySystem where
  active : Ω → V → Prop
  measurable : ∀ v, MeasurableSet {ω | active ω v}
  integrable : ∀ x y, Integrable (fun ω =>
    |(if active ω x then (1:ℝ) else 0)-(if active ω y then (1:ℝ) else 0)|) μ

namespace BinarySystem
variable {μ} (B : BinarySystem (V := V) μ)

noncomputable def indicator (v : V) (ω : Ω) : ℝ := if B.active ω v then 1 else 0
noncomputable def fiber (S : Set V) : Set Ω := {ω | ∀ v, B.active ω v ↔ v ∈ S}
noncomputable def fiberValue (S : Set V) (ω : Ω) : ℝ := if ω ∈ B.fiber S then 1 else 0

def Proper (S : Set V) : Prop := S.Nonempty ∧ Sᶜ.Nonempty

noncomputable def contribution (S : Set V) (ω : Ω) : ℝ :=
  if Proper S then B.fiberValue S ω else 0

noncomputable def weight (S : Set V) : ℝ := ∫ ω, B.contribution S ω ∂μ

omit [Fintype V] in
lemma contribution_nonneg (S : Set V) (ω : Ω) : 0 ≤ B.contribution S ω := by
  unfold contribution fiberValue
  split_ifs <;> norm_num

omit [Fintype V] in
lemma weight_nonneg (S : Set V) : 0 ≤ B.weight S :=
  integral_nonneg (fun ω => B.contribution_nonneg S ω)

noncomputable def cutCost (S : Set V) (x y : V) : ℝ :=
  |(S.indicator (fun _ => (1:ℝ)) x)-(S.indicator (fun _ => (1:ℝ)) y)|

end BinarySystem
end PlanarL1.FiniteL1


end

section

namespace PlanarL1.FiniteL1
open MeasureTheory

/-- All final metrics, and all adaptive averages of them, use the same finite
cut index type. No finite approximation to the label space is made. -/
structure CutFamily (V : Type*) where
  weight : Set V → ℝ
  nonneg : ∀ S, 0 ≤ weight S

namespace CutFamily
variable {V α ι : Type*} [Fintype V]

noncomputable def distance (C : CutFamily V) (x y : V) : ℝ := by
  classical
  exact ∑ S : Set V, C.weight S * BinarySystem.cutCost S x y

noncomputable def ofBinary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (B : BinarySystem (V := V) μ) : CutFamily V := ⟨B.weight,B.weight_nonneg⟩

noncomputable def add (C D : CutFamily V) : CutFamily V where
  weight S := C.weight S+D.weight S
  nonneg S := add_nonneg (C.nonneg S) (D.nonneg S)

noncomputable def sum [Fintype ι] (C : ι → CutFamily V) : CutFamily V where
  weight S := ∑ i, (C i).weight S
  nonneg S := Finset.sum_nonneg (fun i _ => (C i).nonneg S)

noncomputable def average (E : Execution α) (C : α → CutFamily V) : CutFamily V where
  weight S := E.mean (fun a => (C a).weight S)
  nonneg S := E.mean_nonneg (fun a => (C a).nonneg S)

noncomputable def scale (c : ℝ) (hc : 0 ≤ c) (C : CutFamily V) : CutFamily V where
  weight S := c*C.weight S
  nonneg S := mul_nonneg hc (C.nonneg S)

local instance instMeasurableSpaceSet : MeasurableSpace (Set V) := ⊤

noncomputable def embedding (C : CutFamily V) (x : V) : Lp ℝ 1 (Measure.count : Measure (Set V)) :=
  cutMap id C.weight x

end CutFamily
end PlanarL1.FiniteL1



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainStep
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

namespace OrdinaryState
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma represents_named (S : OrdinaryState M κ Ω μ) (ω : Ω) (i : Fin n) (H : ℝ)
    (a : Fin (S.count+1)) (he : S.name i H=a) (hi : H ∈ (S.chart a).band) :
    (S.sets.activity ω).active i H ↔
      Threshold.active (S.labels a) H (κ*(S.chart a).value i ⟨H,hi⟩) ω := by
  subst a
  exact S.represents ω i H

/-- Literal deterministic data of a kept eligible main cell. Fresh signs are
label coordinates, not assumptions of independence between existing labels. -/
structure MainStep (S : OrdinaryState M κ Ω μ) (J : Set ℝ) (root : Fin n) where
  index : Fin (S.count+1)
  tree : Point.RadialTree (M := M) (J := J) (root := root)
  phase : ℝ
  cell : MainCell.Cell tree phase
  anchor : M.Point J root
  anchor_mem : anchor.column ∈ ColumnOrder.componentColumns cell
  lo : ℝ
  band_eq : J=Set.Icc lo (lo+tree.a)
  thin : tree.a ≤ (1/1000:ℝ)/1000
  sub_old : J ⊆ (S.chart index).band
  same_name : ∀ i H, H ∈ MainCell.domain tree phase cell i → S.name i H=index
  noise : Point.RadialTree.Noise (n := n)
  noise_bounds : tree.NoiseBounds noise
  error : ℝ
  error_pos : 0<error
  delta_eq : tree.δ=error/8
  shield_offset : ℝ
  shield_bound : shield_offset ≤ (1:ℝ)/100
  kappa_nonneg : 0≤κ
  vertical_bound : κ*(MainCell.replacementConstant tree : ℝ) ≤ 1
  shield_strict : κ*(3/(9*tree.a/100)) < 1

namespace MainStep
variable {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin n}
variable (U : MainStep S J root)

noncomputable def data : OrdinaryData M := S.chart U.index
noncomputable def comparison : M.Field U.data.band 1 := U.data.comparison

include U in
lemma compact_band : IsCompact J := by rw [U.band_eq]; exact isCompact_Icc

lemma old_agreement (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    Threshold.active ((S.labels U.index).lift) H
      (κ*(U.data.constant+U.data.orientation*MainCell.old U.comparison U.sub_old
        (MainCell.cellPoint U.tree U.phase U.cell i H hi))) ω ↔
      (S.lift.sets.activity ω).active i H := by
  exact (S.represents_named ω.1 i H U.index (U.same_name i H hi)
    (U.sub_old ((MainCell.mem_domain U.tree U.phase U.cell).mp hi).2)).symm

noncomputable def patch : SetPatch S.lift.sets :=
  MainCell.patch U.comparison U.sub_old U.tree U.phase U.cell
    S.lift.sets (S.labels U.index).lift U.compact_band U.lo U.band_eq U.thin
    U.anchor U.anchor_mem U.noise_bounds U.error U.shield_offset U.data.constant
    U.data.orientation κ U.error_pos.le U.delta_eq U.shield_bound
    U.data.unit_orientation U.kappa_nonneg U.vertical_bound U.old_agreement

noncomputable def input : M.Point J root → ℝ :=
  MainCell.input U.comparison U.sub_old U.tree U.phase U.cell U.anchor

noncomputable def shield (H : ℝ) : ℝ :=
  κ*(U.data.constant+U.data.orientation*Clipping.heightShield U.lo U.tree.a
    (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset H)

noncomputable def shieldConstant : ℝ≥0 :=
  ⟨κ*(3/(9*U.tree.a/100)),mul_nonneg U.kappa_nonneg (by positivity [U.tree.width_pos])⟩

lemma shield_lipschitz : LipschitzWith U.shieldConstant U.shield := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have ht := (Clipping.heightShield_lipschitz U.lo
    (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset U.tree.width_pos).dist_le_mul H T
  rw [Real.dist_eq] at ht
  change |shield U H-shield U T| ≤ (κ*(3/(9*U.tree.a/100)))*dist H T
  unfold shield
  rw [show κ*(U.data.constant+U.data.orientation*Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset H)-
    κ*(U.data.constant+U.data.orientation*Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset T) =
    κ*U.data.orientation*(Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset H-
    Clipping.heightShield U.lo U.tree.a
      (MainCell.old U.comparison U.sub_old U.anchor) U.shield_offset T) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.unit_orientation,mul_one]
  exact (mul_le_mul_of_nonneg_left ht U.kappa_nonneg).trans_eq (mul_assoc _ _ _).symm

noncomputable def newData (a : Fin (3*n*U.tree.depthCap+1)) : OrdinaryData M :=
  if a.val=0 then OrdinaryData.initial M else U.tree.atomChart U.data U.input U.noise U.error (a.val-1)

noncomputable def newLabels [SFinite μ] (a : Fin (3*n*U.tree.depthCap+1)) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) :=
  if a.val=0 then (S.labels U.index).rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz
    else (S.labels U.index).lift

noncomputable def choose : Fin n → ℝ → Option (Fin (3*n*U.tree.depthCap+1)) :=
  MainCell.choose U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
    U.error U.shield_offset U.lo

lemma patch_inside (ω : Ω × Bool) (i : Fin n) (H : ℝ)
    (hi : H ∈ MainCell.domain U.tree U.phase U.cell i) :
    (U.patch.apply.activity ω).active i H ↔
      Threshold.active (S.labels U.index).lift H
        (κ*(U.data.constant+U.data.orientation*MainCell.replacement U.comparison U.sub_old
          U.tree U.phase U.cell U.anchor U.noise U.error U.shield_offset U.lo
            (MainCell.cellPoint U.tree U.phase U.cell i H hi))) ω := by
  apply (U.patch.inside hi ω).trans
  change Threshold.active _ H (MainCell.converted U.comparison U.sub_old U.tree U.phase
    U.cell U.anchor U.noise U.error U.shield_offset U.lo U.data.constant U.data.orientation κ i H) ω ↔ _
  rw [MainCell.converted_on U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
    U.error U.shield_offset U.lo U.data.constant U.data.orientation κ hi]

lemma chosen_description [SFinite μ] (i : Fin n) (H : ℝ)
    (a : Fin (3*n*U.tree.depthCap+1)) (hc : U.choose i H=some a) :
    (U.newData a).Contains i H ∧ ∀ (ω : Ω × Bool) (hi : H ∈ (U.newData a).band),
      (U.patch.apply.activity ω).active i H ↔
        Threshold.active (U.newLabels a) H (κ*(U.newData a).value i ⟨H,hi⟩) ω := by
  let Q (D : OrdinaryData M) (Z : Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair)) : Prop :=
    D.Contains i H ∧ ∀ (ω : Ω × Bool) (hi : H ∈ D.band),
      (U.patch.apply.activity ω).active i H ↔ Threshold.active Z H (κ*D.value i ⟨H,hi⟩) ω
  change Q (U.newData a) (U.newLabels a)
  obtain ⟨hd,hn⟩ := MainCell.choose_spec U.comparison U.sub_old U.tree U.phase U.cell U.anchor
    U.noise U.error U.shield_offset U.lo i H a hc
  let x := MainCell.cellPoint U.tree U.phase U.cell i H hd
  change (MainCell.namedReplacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
    U.noise U.error U.shield_offset U.lo x).name=a.val+1 at hn
  rcases MainCell.namedReplacement_cases U.comparison U.sub_old U.tree U.phase U.cell U.anchor
    U.noise U.error U.shield_offset U.lo x with ho | hh | hp
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name ho
    change _=0 at hn'
    omega
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hh
    change _=1 at hn'
    have ha0 : a.val=0 := by omega
    simp only [newData,newLabels,ite_eq_left ha0]
    refine ⟨OrdinaryData.initial_contains i H,?_⟩
    intro ω hi
    have hv : MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x =
        Clipping.heightShield U.lo U.tree.a (MainCell.old U.comparison U.sub_old U.anchor)
          U.shield_offset H := by
      rw [← MainCell.namedReplacement_value U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x,hh]
      rfl
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.constant+U.data.orientation*
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
        U.error U.shield_offset U.lo x)) ω at h0
    rw [hv] at h0
    simpa only [OrdinaryData.initial_value,mul_zero] using
      h0.trans ((S.labels U.index).active_rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz H ω)
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hp
    change _=(U.tree.pasted U.input U.noise x).name+2 at hn'
    have ha0 : a.val≠0 := by omega
    have ha1 : a.val-1=(U.tree.pasted U.input U.noise x).name := by omega
    simp only [newData,newLabels,ite_eq_right ha0,ha1]
    refine ⟨U.tree.atomChart_contains U.data U.input U.noise U.error x,?_⟩
    intro ω hi
    obtain ⟨hb,hvalue⟩ := U.tree.atomChart_value U.data U.input U.noise U.error x
    have hv : MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor
        U.noise U.error U.shield_offset U.lo x = (U.tree.pasted U.input U.noise x).value-4*U.error := by
      rw [← MainCell.namedReplacement_value U.comparison U.sub_old U.tree U.phase U.cell
        U.anchor U.noise U.error U.shield_offset U.lo x,hp]
      rfl
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.constant+U.data.orientation*
      MainCell.replacement U.comparison U.sub_old U.tree U.phase U.cell U.anchor U.noise
        U.error U.shield_offset U.lo x)) ω at h0
    rw [hv] at h0
    exact h0.trans (Iff.of_eq (congrArg (fun p => Threshold.active (S.labels U.index).lift H (κ*p) ω)
      hvalue.symm))


lemma unchosen (ω : Ω × Bool) (i : Fin n) (H : ℝ) (hc : U.choose i H=none) :
    (U.patch.apply.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  by_cases hd : H ∈ MainCell.domain U.tree U.phase U.cell i
  · have hn := MainCell.choose_none_inside U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo i H hd hc
    have hv := (PlanarL1.Interpolation.namedClip_eq_old_iff _ _ _ _).mp hn
    change (MainCell.namedReplacement U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo
        (MainCell.cellPoint U.tree U.phase U.cell i H hd)).value = _ at hv
    rw [MainCell.namedReplacement_value U.comparison U.sub_old U.tree U.phase U.cell
      U.anchor U.noise U.error U.shield_offset U.lo] at hv
    have hp := U.patch_inside ω i H hd
    rw [hv] at hp
    exact hp.trans (U.old_agreement ω i H hd)
  · exact U.patch.unchanged hd ω

lemma choose_switch (i j : Fin n) (H : ℝ) (hh : H ∈ M.heights i j) :
    U.choose i H=U.choose j H :=
  MainCell.choose_switch U.comparison U.sub_old U.tree U.phase U.cell U.compact_band
    U.anchor U.noise_bounds U.error_pos U.delta_eq U.shield_offset U.lo i j H hh

end MainStep
end OrdinaryState
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model.OrdinaryState
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : OrdinaryState M κ Ω μ}

/-- A finite family of the actual main-cell proposals. Distinct cells may meet
at unchanged boundary points; no disjointness of their closed domains is assumed. -/
structure MainBatch (S : OrdinaryState M κ Ω μ) where
  count : ℕ
  band : Fin count → Set ℝ
  root : Fin count → Fin n
  step : ∀ q, MainStep S (band q) (root q)
  overlap : (List.ofFn (fun q => (step q).patch)).Pairwise SetPatch.UnchangedOverlap

namespace MainBatch
variable (B : MainBatch S)

def NewIndex := Σ q : Fin B.count, Fin (3*n*(B.step q).tree.depthCap+1)
noncomputable instance instFintypeNewIndex : Fintype B.NewIndex := inferInstanceAs (Fintype (Sigma _))

noncomputable def newData (a : B.NewIndex) : OrdinaryData M :=
  (B.step a.1).newData a.2
noncomputable def newLabels [SFinite μ] (a : B.NewIndex) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) :=
  (B.step a.1).newLabels a.2

noncomputable def chosen (i : Fin n) (H : ℝ) (a : B.NewIndex) : Prop :=
  (B.step a.1).choose i H = some a.2

noncomputable def choose (i : Fin n) (H : ℝ) : Option B.NewIndex :=
  if h : ∃ a, B.chosen i H a then some h.choose else none

lemma choose_some (i : Fin n) (H : ℝ) (a : B.NewIndex)
    (ha : B.choose i H=some a) : B.chosen i H a := by
  unfold choose at ha
  split_ifs at ha with h
  · have he : h.choose=a := Option.some.inj ha
    exact he ▸ h.choose_spec

lemma choose_none (i : Fin n) (H : ℝ) (ha : B.choose i H=none) (q : Fin B.count) :
    (B.step q).choose i H=none := by
  cases he : (B.step q).choose i H with
  | none => rfl
  | some a =>
    have hex : ∃ a, B.chosen i H a := ⟨⟨q,a⟩,he⟩
    simp [choose,hex] at ha

lemma choose_switch (i j : Fin n) (H : ℝ) (hs : H ∈ M.heights i j) :
    B.choose i H=B.choose j H := by
  have he : B.chosen i H=B.chosen j H := by
    funext a
    simp only [chosen,(B.step a.1).choose_switch i j H hs]
  unfold choose
  simp only [he]

noncomputable def sets : SetSystem M (Ω × Bool) (μ.prod Threshold.fair) :=
  SetPatch.batch (List.ofFn (fun q => (B.step q).patch)) B.overlap

lemma chosen_description [SFinite μ] (i : Fin n) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) : (B.newData a).Contains i H ∧
    ∀ (ω : Ω × Bool) (hi : H ∈ (B.newData a).band),
      (B.sets.activity ω).active i H ↔
        Threshold.active (B.newLabels a) H (κ*(B.newData a).value i ⟨H,hi⟩) ω := by
  have h := (B.step a.1).chosen_description i H a.2 ha
  refine ⟨h.1,?_⟩
  intro ω hi
  obtain ⟨hd,-⟩ := MainCell.choose_spec (B.step a.1).comparison (B.step a.1).sub_old
    (B.step a.1).tree (B.step a.1).phase (B.step a.1).cell (B.step a.1).anchor
    (B.step a.1).noise (B.step a.1).error (B.step a.1).shield_offset (B.step a.1).lo i H a.2 ha
  apply (SetPatch.batch_inside _ B.overlap (List.mem_ofFn.mpr ⟨a.1,rfl⟩) ω i H hd).trans
  exact h.2 ω hi

lemma unchosen (ω : Ω × Bool) (i : Fin n) (H : ℝ) (ha : B.choose i H=none) :
    (B.sets.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  apply SetPatch.batch_old _ B.overlap ω i H
  intro P hP
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.step q).unchosen ω i H (B.choose_none i H ha q)

/-- Actual finite main update, with the chart table containing every ancestor
formula and each shield's rebased label variables. -/
noncomputable def apply [SFinite μ] : OrdinaryState M κ (Ω × Bool) (μ.prod Threshold.fair) := by
  let e := Fintype.equivFin B.NewIndex
  let pick : Fin n → ℝ → Option (Fin (Fintype.card B.NewIndex)) :=
    fun i H => (B.choose i H).map e
  have hpick (i H a) (ha : pick i H=some a) : B.chosen i H (e.symm a) := by
    obtain ⟨b,hb,hba⟩ := Option.map_eq_some_iff.mp ha
    have he : b=e.symm a := by rw [← hba]; simp
    exact he ▸ B.choose_some i H b hb
  exact S.lift.append B.sets (Fintype.card B.NewIndex)
    (B.newData ∘ e.symm) (B.newLabels ∘ e.symm) pick
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.1)
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.2)
    (fun i j H hs => congrArg (Option.map e) (B.choose_switch i j H hs))
    (fun ω i H ha => B.unchosen ω i H (Option.map_eq_none_iff.mp ha))
    (fun ω i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).2 ω _)

end MainBatch
end PlanarL1.Columns.Model.OrdinaryState



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace MainFamily
open Parameters
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable (q L U : ℝ)

noncomputable abbrev BandIndex := Tiling.processed a₁ q L U
noncomputable def lower (b : BandIndex q L U) : ℝ := q+(b.val:ℝ)*a₁
abbrev BandComponent := Σ b : BandIndex q L U, BandTrees.Component M broad (lower q L U b)
noncomputable instance instFintypeBandComponent : Fintype (BandComponent (M := M) q L U) := Fintype.ofFinite _

abbrev CellIndex (phase : BandComponent (M := M) q L U → ℝ) :=
  Σ b : BandComponent (M := M) q L U,
    BandTrees.MainIndex M broad (lower q L U b.1) b.2 (phase b)
noncomputable instance instFintypeCellIndex (phase : BandComponent (M := M) q L U → ℝ) :
    Fintype (CellIndex q L U phase) := Fintype.ofFinite _

variable {q L U} (phase : BandComponent (M := M) q L U → ℝ)
variable (c : CellIndex q L U phase)
noncomputable abbrev tree := BandTrees.tree M broad (lower q L U c.1.1) c.1.2
noncomputable def radial := phase c.1+(c.2.1.val:ℝ)*(1/1000)
noncomputable abbrev anchor := BandTrees.anchor M broad (lower q L U c.1.1) c.1.2 (phase c.1) c.2
noncomputable def domain (i : Fin (k+1)) : Set ℝ := MainCell.domain (tree phase c) (radial phase c) c.2.2 i

/-- Availability is the manuscript's entire closed radius-one neighborhood of
this full-column cell, not just tests at the finite original vertices. -/
def neighborhood : Set (M.Point Set.univ A.root) :=
  {y | ∃ i H, H ∈ domain phase c i ∧ dist y (A.point i H)≤1}
def Available : Prop := ∃ index : Fin (S.count+1),
  ∀ y ∈ neighborhood A phase c, S.name y.column y.height=index

noncomputable def index (hc : Available A S phase c) : Fin (S.count+1) := hc.choose
lemma same_name (hc : Available A S phase c) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ domain phase c i) : S.name i H=index A S phase c hc :=
  hc.choose_spec (A.point i H) ⟨i,H,hi,by simp⟩

lemma sub_old (hc : Available A S phase c) : BandTrees.band broad (lower q L U c.1.1) ⊆
    (S.chart (index A S phase c hc)).band := by
  intro H hH
  have hi : H ∈ domain phase c (anchor phase c).column :=
    (MainCell.mem_domain _ _ _).mpr ⟨BandTrees.anchor_mem _ _ _ _ _ _,hH⟩
  have hh := S.height_in (anchor phase c).column H
  rw [same_name A S phase c hc _ _ hi] at hh
  exact hh

/-- Every kept, available cell becomes an actual MainStep, including its old
chart and exact interpolation tree. All parameters are the fixed constants. -/
noncomputable def step (hc : Available A S phase c)
    (noise : Point.RadialTree.Noise (n := k+1)) (hn : (tree phase c).NoiseBounds noise)
    (beta : ℝ) (hb : beta ≤ EA) :
    OrdinaryState.MainStep S (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2) where
  index := index A S phase c hc
  tree := tree phase c
  phase := radial phase c
  cell := c.2.2
  anchor := anchor phase c
  anchor_mem := BandTrees.anchor_mem _ _ _ _ _ _
  lo := lower q L U c.1.1
  band_eq := rfl
  thin := thinA
  sub_old := sub_old A S phase c hc
  same_name := same_name A S phase c hc
  noise := noise
  noise_bounds := hn
  error := EA
  error_pos := interpolationA.1
  delta_eq := rfl
  shield_offset := beta
  shield_bound := hb.trans (by norm_num [EA,epsilon])
  kappa_nonneg := verticalA.1
  vertical_bound := verticalA.2.1
  shield_strict := verticalA.2.2

lemma cell_column_component {i : Fin (k+1)} (hi : i ∈ ColumnOrder.componentColumns c.2.2) :
    i ∈ c.1.2.supp :=
  BandTrees.reachable_mem M broad (lower q L U c.1.1) c.1.2
    (ColumnOrder.componentColumns_subset c.2.2 hi).choose

lemma unique_in_band {c d : CellIndex q L U phase} (he : c.1.1=d.1.1)
    {i : Fin (k+1)} {H : ℝ} (hi : H ∈ domain phase c i) (hj : H ∈ domain phase d i) : c=d := by
  obtain ⟨⟨b,C⟩,K⟩ := c
  obtain ⟨⟨b',D⟩,T⟩ := d
  dsimp only at he
  subst b'
  have hci := cell_column_component phase (Sigma.mk ⟨b,C⟩ K) ((MainCell.mem_domain _ _ _).mp hi).1
  have hcj := cell_column_component phase (Sigma.mk ⟨b,D⟩ T) ((MainCell.mem_domain _ _ _).mp hj).1
  have hCD : C=D := ((SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp hci).symm.trans
    ((SimpleGraph.ConnectedComponent.mem_supp_iff D i).mp hcj)
  subst D
  have hKT : K=T := by
    by_contra hn
    exact Set.disjoint_left.mp (BandTrees.main_disjoint M broad (lower q L U b) C (phase ⟨b,C⟩) hn)
      ((MainCell.mem_domain _ _ _).mp hi).1 ((MainCell.mem_domain _ _ _).mp hj).1
  subst T
  rfl

lemma domain_band {i : Fin (k+1)} {H : ℝ} (hi : H ∈ domain phase c i) :
    H ∈ Tiling.band a₁ q c.1.1.val := by
  obtain ⟨_,hl,hu⟩ := (MainCell.mem_domain _ _ _).mp hi
  change q+(c.1.1.val:ℝ)*a₁≤H ∧ H≤q+((c.1.1.val:ℝ)+1)*a₁
  dsimp [BandTrees.band,lower,broad] at hl hu
  constructor <;> linarith

end MainFamily

namespace OrdinaryState.MainStep
variable {κ : ℝ} {S : OrdinaryState M κ Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (V : MainStep S J root)
lemma endpoint_old (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ V.patch.domain i) (he : H=V.lo ∨ H=V.lo+V.tree.a) :
    V.patch.active ω i H ↔ (S.lift.sets.activity ω).active i H := by
  apply V.patch.boundary
  change H ∈ frontier (MainCell.domain V.tree V.phase V.cell i)
  have hc := ((MainCell.mem_domain V.tree V.phase V.cell).mp hi).1
  rw [MainCell.domain,ite_eq_left hc,V.band_eq,frontier_Icc (by linarith [V.tree.width_pos])]
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using he
end OrdinaryState.MainStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

abbrev CellSample (c : CellIndex q L U phase) (m : ℕ) :=
  Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m × Fin (m+1) × Bool
abbrev Sample (m : ℕ) := ∀ c : CellIndex q L U phase, CellSample phase c m
noncomputable instance instFintypeSample (m : ℕ) : Fintype (Sample phase m) := inferInstanceAs (Fintype (∀ _, _))
instance instNonemptySample (m : ℕ) : Nonempty (Sample phase m) := inferInstanceAs (Nonempty (∀ _, _))

variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)

def kept (c : CellIndex q L U phase) : Prop := Available A S phase c ∧ (omega c).2.2=true
abbrev Kept := {c : CellIndex q L U phase // kept A S phase omega c}
noncomputable instance instFintypeKept : Fintype (Kept A S phase omega) := Fintype.ofFinite _

include hm in
lemma shield_bound (c : CellIndex q L U phase) : EA/(m:ℝ)*((omega c).2.1.val:ℝ)≤EA := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hi : (((omega c).2.1.val):ℝ)≤ m := by exact_mod_cast (omega c).2.1.is_le
  have hp : 0≤EA/m := div_nonneg (interpolationA.1.le) hmR.le
  calc _ ≤ EA/m*m := mul_le_mul_of_nonneg_left hi hp
       _ = EA := div_mul_cancel₀ _ hmR.ne'

noncomputable def keptStep (c : Kept A S phase omega) :=
  step A S phase c.val c.property.1
    ((tree phase c.val).gridNoise (tree phase c.val).depthCap m (omega c.val).1)
    ((tree phase c.val).gridNoise_bounds _ _ hm (omega c.val).1)
    (EA/m*(omega c.val).2.1.val) (shield_bound phase hm omega c.val)

lemma overlap {c d : Kept A S phase omega} (hne : c≠d) :
    SetPatch.UnchangedOverlap (keptStep A S phase hm omega c).patch
      (keptStep A S phase hm omega d).patch := by
  intro w i H hi hj
  have hi' : H ∈ domain phase c.val i := hi
  have hj' : H ∈ domain phase d.val i := hj
  have hbands : c.val.1.1≠d.val.1.1 := by
    intro he
    exact hne (Subtype.ext (unique_in_band phase he hi' hj'))
  have hne' : c.val.1.1.val≠d.val.1.1.val := fun he => hbands (Subtype.ext he)
  have hc := domain_band phase c.val hi'
  have hd := domain_band phase d.val hj'
  have hout : ∀ {e : Kept A S phase omega}, H ∈ (keptStep A S phase hm omega e).patch.domain i →
      (H=lower q L U e.val.1.1 ∨ H=lower q L U e.val.1.1+a₁) →
      ((keptStep A S phase hm omega e).patch.active w i H ↔ (S.lift.sets.activity w).active i H) := by
    intro e he he'
    exact (keptStep A S phase hm omega e).endpoint_old w i H he he'
  rcases lt_or_gt_of_ne hne' with he | he
  · obtain ⟨h1,h2⟩ := Tiling.overlap interpolationA.2.1 he hc hd
    exact ⟨hout hi (Or.inr (by dsimp [lower]; linarith)),hout hj (Or.inl h2)⟩
  · obtain ⟨h1,h2⟩ := Tiling.overlap interpolationA.2.1 he hd hc
    exact ⟨hout hi (Or.inl h2),hout hj (Or.inr (by dsimp [lower]; linarith))⟩

/-- The simultaneous main mode is now genuinely defined for every old state
and every finite sample. Its family contains exactly the available kept cells. -/
noncomputable def batch : OrdinaryState.MainBatch S where
  count := Fintype.card (Kept A S phase omega)
  band a := BandTrees.band broad (lower q L U ((Fintype.equivFin (Kept A S phase omega)).symm a).val.1.1)
  root a := BandTrees.root M broad
    (lower q L U ((Fintype.equivFin (Kept A S phase omega)).symm a).val.1.1)
    ((Fintype.equivFin (Kept A S phase omega)).symm a).val.1.2
  step a := keptStep A S phase hm omega ((Fintype.equivFin (Kept A S phase omega)).symm a)
  overlap := by
    apply List.pairwise_ofFn.mpr
    intro a b hab
    apply overlap A S phase hm omega
    exact fun he => (ne_of_lt hab) ((Fintype.equivFin (Kept A S phase omega)).symm.injective he)

noncomputable def result [SFinite μ] : OrdinaryState M kappaA (Ω × Bool) (μ.prod Threshold.fair) :=
  (batch A S phase hm omega).apply

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}
namespace BandTrees
variable (P : Parameters.Interpolation) (lo : ℝ) (C : Component M P lo)
lemma main_cover (phase : ℝ) {i : Fin (k+1)} (hi : i ∈ C.supp) :
    ∃ c : MainIndex M P lo C phase, i ∈ ColumnOrder.componentColumns c.2 := by
  let x := point M P lo C ⟨i,hi⟩
  let l := Tiling.index (1/1000) phase (dist (base M P lo C) x)
  have hl : l ∈ levels M P lo C phase (1/1000) :=
    Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,rfl⟩
  have hx : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo)
      (phase+(l:ℝ)*(1/1000)) (1/1000) := by
    refine ⟨x.reachable,?_,?_⟩
    · have h := Int.floor_le ((dist (base M P lo C) x-phase)/(1/1000))
      have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<1/1000)).mp h
      change phase+(l:ℝ)*(1/1000)≤dist (base M P lo C) x
      dsimp [l,Tiling.index]
      linarith
    · have h := Int.lt_floor_add_one ((dist (base M P lo C) x-phase)/(1/1000))
      have hh := (div_lt_iff₀ (by norm_num : (0:ℝ)<1/1000)).mp h
      change dist (base M P lo C) x<phase+(l:ℝ)*(1/1000)+1/1000
      dsimp [l,Tiling.index]
      linarith
  let G := (M.activeGraph (band P lo)).induce ((base M P lo C).layer (middle P lo)
    (middle_mem P lo) (phase+(l:ℝ)*(1/1000)) (1/1000))
  exact ⟨⟨⟨l,hl⟩,G.connectedComponentMk ⟨i,hx⟩⟩,⟨⟨i,hx⟩,rfl,rfl⟩⟩
end BandTrees

namespace MainFamily
open Parameters
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

lemma ambient_dist_le {J : Set ℝ} {root : Fin (k+1)} (x y : M.Point J root) :
    dist (A.point x.column x.height) (A.point y.column y.height)≤dist x y := by
  have h := x.dist_widen_le y (Set.subset_univ J)
  have he := Point.dist_coordinates (x.widen (Set.subset_univ J)) (y.widen (Set.subset_univ J))
    (A.point x.column x.height) (A.point y.column y.height) rfl rfl rfl rfl
  exact he ▸ h

lemma cell_diameter (c : CellIndex q L U phase) {i j : Fin (k+1)} {H T : ℝ}
    (hi : H ∈ domain phase c i) (hj : T ∈ domain phase c j) :
    dist (A.point i H) (A.point j T)≤1/100 := by
  let x := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 i H hi
  let y := MainCell.cellPoint (tree phase c) (radial phase c) c.2.2 j T hj
  have hh := (tree phase c).base.radial_cell_diameter (tree phase c).closed_band
    (tree phase c).base.inBand (tree phase c).width_pos thinA (tree phase c).half_width c.2.2 x y
    ((MainCell.mem_domain _ _ _).mp hi).1 ((MainCell.mem_domain _ _ _).mp hj).1
  exact (ambient_dist_le A x y).trans (by simpa only [show (10:ℝ)*(1/1000)=1/100 by norm_num] using hh)

end MainFamily
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (omega : Sample phase m)
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0≤ρ)
    (hp : Tiling.Padded a₁ q x.height ρ) (hsmall : 4*ρ<3*EA)

noncomputable def sampleName (c : CellIndex q L U phase) (hc : Available A S phase c)
    (w : Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m × Fin (m+1))
    (z : M.Point (BandTrees.band broad (lower q L U c.1.1))
      (BandTrees.root M broad (lower q L U c.1.1) c.1.2)) : ℕ :=
  (MainCell.namedReplacement (S.chart (index A S phase c hc)).comparison
    (sub_old A S phase c hc) (tree phase c) (radial phase c) c.2.2 (anchor phase c)
    ((tree phase c).gridNoise (tree phase c).depthCap m w.1) EA (EA/m*w.2.val)
    (lower q L U c.1.1) z).name

end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.MainFamily
open MeasureTheory Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

noncomputable def localLoss (c : CellIndex q L U phase) (ρ : ℝ) (m : ℕ) : ℝ :=
  (6*((tree phase c).lookback+1)+2 : ℕ)^2 *
    ((4*(MainCell.replacementConstant (tree phase c) : ℝ)*ρ+(tree phase c).q/m)/(tree phase c).q+
      (4*(MainCell.replacementConstant (tree phase c) : ℝ)*ρ+EA/m)/EA)
end PlanarL1.Columns.Model.MainFamily

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryCells
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.SecondaryCell
open scoped NNReal
open Metric

variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))

noncomputable def seedDistance (x : M.Point J root) : ℝ := infDist x (S : Set (M.Point J root))

lemma seedDistance_lipschitz : LipschitzWith 1 (seedDistance S) := lipschitz_infDist_pt _

lemma seedDistance_seed {w : M.Point J root} (hw : w ∈ S) : seedDistance S w = 0 :=
  infDist_zero_of_mem hw

lemma seedDistance_attained (hS : S.Nonempty) (x : M.Point J root) :
    ∃ w ∈ S, seedDistance S x = dist x w := by
  exact S.finite_toSet.isCompact.exists_infDist_eq_dist (by simpa using hS) x

noncomputable def input (x : M.Point J root) : ℝ := (9/10:ℝ)*seedDistance S x

lemma input_lipschitz (hζ : R.ζ = (1:ℝ)/10) : R.InputLip (input S) := by
  intro x y
  have h := (seedDistance_lipschitz S).dist_le_mul x y
  rw [NNReal.coe_one,one_mul] at h
  rw [input,input,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 9/10),hζ]
  rw [Real.dist_eq] at h
  nlinarith

noncomputable def approx (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) : ℝ :=
  (R.pasted (input S) α x).value

noncomputable def shallow (pc radius : ℝ) (α : Point.RadialTree.Noise (n := n))
    (x : M.Point J root) : ℝ := pc+radius/20-approx R S α x

lemma approx_accuracy (hζ : R.ζ = (1:ℝ)/10) {radius : ℝ} (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) (x : M.Point J root) :
    |approx R S α x-(9/10:ℝ)*seedDistance S x| ≤ radius/1000 := by
  have h := R.pasted_accuracy (input_lipschitz R S hζ) hα x
  rw [hδ] at h
  change |approx R S α x-(9/10:ℝ)*seedDistance S x| ≤ _ at h
  have hp := R.delta_pos
  rw [hδ] at hp
  linarith

lemma shallow_lipschitz (pc radius : ℝ) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) : LipschitzWith 1 (shallow R S pc radius α) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [shallow,approx,dist_sub_left] using (R.pasted_lipschitz (input S) hα).dist_le_mul x y

lemma shallow_boundary (hζ : R.ζ = (1:ℝ)/10) {radius pc : ℝ} (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) {x : M.Point J root}
    (hx : seedDistance S x = radius) : shallow R S pc radius α x ≤ pc-(849/1000:ℝ)*radius := by
  have h := (abs_le.mp (approx_accuracy R S hζ hδ hα x)).1
  dsimp only [shallow]
  rw [hx] at h
  linarith

end PlanarL1.Columns.Model.SecondaryCell


end

section

namespace PlanarL1.Columns.Model.Point
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
lemma height_lipschitz : LipschitzWith 1 (fun x : M.Point J root => x.height) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,NNReal.coe_one,one_mul]
  exact x.height_change_le y
end PlanarL1.Columns.Model.Point

namespace PlanarL1.Columns.Model.SecondaryCell
open Set Metric
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (S : Finset (M.Point J root)) (radius : ℝ)

/-- The literal closed union of radius-R seed balls, on each vertical column. -/
def domain (i : Fin n) : Set ℝ :=
  (fun x : M.Point J root => x.height) ''
    {x | x.column = i ∧ seedDistance S x ≤ radius}

lemma mem_domain {i : Fin n} {H : ℝ} : H ∈ domain S radius i ↔
    ∃ x : M.Point J root, x.column = i ∧ x.height = H ∧ seedDistance S x ≤ radius := by
  constructor
  · rintro ⟨x,⟨hi,hd⟩,hH⟩
    exact ⟨x,hi,hH,hd⟩
  · rintro ⟨x,hi,hH,hd⟩
    exact ⟨x,⟨hi,hd⟩,hH⟩

lemma compact_domain (hJ : IsCompact J) (i : Fin n) : IsCompact (domain S radius i) := by
  have hc : IsCompact {x : M.Point J root | x.column = i} := by
    simpa only [mem_singleton_iff] using Point.fullColumns_compact (M := M) (root := root) hJ {i}
  have hd : IsClosed {x : M.Point J root | seedDistance S x ≤ radius} :=
    isClosed_le (seedDistance_lipschitz S).continuous continuous_const
  exact (hc.inter_right hd).image Point.height_lipschitz.continuous

noncomputable def point (i : Fin n) (H : ℝ) (h : H ∈ domain S radius i) : M.Point J root :=
  ((mem_domain S radius).mp h).choose

lemma point_column {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    (point S radius i H h).column = i := ((mem_domain S radius).mp h).choose_spec.1
lemma point_height {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    (point S radius i H h).height = H := ((mem_domain S radius).mp h).choose_spec.2.1
lemma point_distance {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    seedDistance S (point S radius i H h) ≤ radius := ((mem_domain S radius).mp h).choose_spec.2.2

lemma inBand_of_mem {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) : H ∈ J := by
  rw [← point_height S radius h]
  exact (point S radius i H h).inBand

lemma equal_radius_or_endpoint (hJ : IsCompact J) (lo a : ℝ) (_ha : 0 < a)
    (hband : J = Icc lo (lo+a)) {i : Fin n} {H : ℝ} (h : H ∈ frontier (domain S radius i)) :
    ∃ hd : H ∈ domain S radius i,
      seedDistance S (point S radius i H hd) = radius ∨ H = lo ∨ H = lo+a := by
  have hd : H ∈ domain S radius i := (compact_domain S radius hJ i).isClosed.frontier_subset h
  refine ⟨hd,?_⟩
  let x := point S radius i H hd
  by_cases hs : seedDistance S x = radius
  · exact Or.inl hs
  right
  by_cases hl : H = lo
  · exact Or.inl hl
  right
  by_contra hr
  have hH : H ∈ Icc lo (lo+a) := hband ▸ inBand_of_mem S radius hd
  have hlo : lo < H := lt_of_le_of_ne hH.1 (Ne.symm hl)
  have hhi : H < lo+a := lt_of_le_of_ne hH.2 hr
  have hdist : seedDistance S x < radius := lt_of_le_of_ne (point_distance S radius hd) hs
  let ε := min (H-lo) (min (lo+a-H) (radius-seedDistance S x)) / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεl : ε < H-lo := by
    have hh := min_le_left (H-lo) (min (lo+a-H) (radius-seedDistance S x))
    dsimp only [ε]
    linarith
  have hεh : ε < lo+a-H := by
    have hh := (min_le_right (H-lo) (min (lo+a-H) (radius-seedDistance S x))).trans (min_le_left _ _)
    dsimp only [ε]
    linarith
  have hεd : ε < radius-seedDistance S x := by
    have hh := (min_le_right (H-lo) (min (lo+a-H) (radius-seedDistance S x))).trans (min_le_right _ _)
    dsimp only [ε]
    linarith
  have hb : Metric.ball H ε ⊆ domain S radius i := by
    intro T hT
    have ht := abs_lt.mp (by simpa only [Metric.mem_ball,Real.dist_eq] using hT : |T-H| < ε)
    have hTJ : T ∈ J := by rw [hband]; constructor <;> linarith
    let y := x.withHeight T hTJ
    have hy : dist y x = |T-H| := by
      rw [y.dist_same_column x rfl]
      change |T-x.height| = |T-H|
      rw [point_height S radius hd]
    have hbnd := (seedDistance_lipschitz S).dist_le_mul y x
    rw [Real.dist_eq,NNReal.coe_one,one_mul,hy] at hbnd
    have hby := (abs_le.mp hbnd).2
    apply (mem_domain S radius).mpr
    exact ⟨y,point_column S radius hd,rfl,by linarith [(by
      simpa only [Metric.mem_ball,Real.dist_eq] using hT : |T-H| < ε)]⟩
  have hin : H ∈ interior (domain S radius i) :=
    mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨ε,hε,hb⟩)
  exact h.2 hin

/-- The seed-ball domain is saturated under the actual quotient switches. -/
lemma switch_mem {i j : Fin n} {H : ℝ} (hs : H ∈ M.heights i j)
    (hi : H ∈ domain S radius i) : H ∈ domain S radius j := by
  let x := point S radius i H hi
  have hHJ := inBand_of_mem S radius hi
  have hadj : (M.activeGraph J).Adj i j := ⟨H,hHJ,hs⟩
  have hxi := point_column S radius hi
  have hxH := point_height S radius hi
  let y : M.Point J root := ⟨j,H,hHJ,(hxi ▸ x.reachable).trans hadj.reachable⟩
  have hd : dist x y = 0 := by
    apply le_antisymm _ dist_nonneg
    have hiCol : x.column = i := hxi
    have hiHeight : x.height = H := hxH
    have hjCol : y.column = j := rfl
    have hjHeight : y.height = H := rfl
    have h := x.dist_le_switch y hHJ (by rw [hiCol,hjCol]; exact hs)
    simpa only [hiHeight,hjHeight,sub_self,abs_zero,add_zero] using h
  have hf := (seedDistance_lipschitz S).dist_le_mul x y
  rw [hd,mul_zero] at hf
  have he : seedDistance S x = seedDistance S y := dist_le_zero.mp hf
  exact (mem_domain S radius).mpr ⟨y,rfl,rfl,he ▸ point_distance S radius hi⟩

end PlanarL1.Columns.Model.SecondaryCell



namespace PlanarL1.Columns.Model.SecondaryCell
open Set MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))
variable (old L : M.Point J root → ℝ) (ordinary : Bool)

noncomputable def spatial (pc radius αo : ℝ) (α : Point.RadialTree.Noise (n := n))
    (x : M.Point J root) : ℝ :=
  if ordinary then min (shallow R S pc radius α x) (Clipping.orderedBranch pc radius αo L x)
  else shallow R S pc radius α x

noncomputable def replacement (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) : ℝ :=
  max (old x) (min (spatial R S L ordinary pc radius αo α x)
    (Clipping.heightShield lo R.a pc αh x.height))

noncomputable def replacementConstant : ℝ≥0 := max 5 ⟨3/(9*R.a/100),by positivity [R.width_pos]⟩

lemma spatial_lipschitz (pc radius αo : ℝ) {α : Point.RadialTree.Noise (n := n)}
    (hα : R.NoiseBounds α) (hL : LipschitzWith 1 L) :
    LipschitzWith 4 (spatial R S L ordinary pc radius αo α) := by
  have hT := (shallow_lipschitz R S pc radius hα).weaken (by norm_num : (1:ℝ≥0) ≤ 4)
  have hO : LipschitzWith 4 (Clipping.orderedBranch pc radius αo L) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hL.dist_le_mul x y
    rw [Real.dist_eq,NNReal.coe_one,one_mul] at h
    change dist _ _ ≤ (4:ℝ)*dist x y
    rw [Real.dist_eq]
    change |(pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo)| ≤ _
    rw [show (pc+radius/20+4*(L x-pc)+αo)-(pc+radius/20+4*(L y-pc)+αo) =
      4*(L x-L y) by ring, abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
    linarith
  cases ordinary
  · convert hT using 1; funext x; simp only [spatial,Bool.false_eq_true,ite_false]
  · convert hT.min hO using 1
    · exact (max_self _).symm
    · funext x; simp only [spatial,ite_true]

lemma replacement_lipschitz (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α) :
    LipschitzWith (replacementConstant R) (replacement R S old L ordinary pc radius αo αh lo α) := by
  apply Clipping.clip_lipschitz
  · exact hOld.weaken (le_max_left _ _)
  · exact (spatial_lipschitz R S L ordinary pc radius αo hα hL).weaken
      ((by norm_num : (4:ℝ≥0) ≤ 5).trans (le_max_left _ _))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (Clipping.heightShield_lipschitz lo pc αh R.width_pos).dist_le_mul x.height y.height
    have hheight := x.height_change_le y
    change |x.height-y.height| ≤ dist x y at hheight
    change dist _ _ ≤ (replacementConstant R : ℝ)*dist x y
    change dist _ _ ≤ (3/(9*R.a/100))*dist x.height y.height at h
    rw [Real.dist_eq x.height y.height] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hheight (by positivity [R.width_pos])).trans
      (mul_le_mul_of_nonneg_right (le_max_right (5:ℝ) (3/(9*R.a/100))) dist_nonneg))

lemma replacement_near (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    {pc radius : ℝ} (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    {x : M.Point J root} (hx : seedDistance S x ≤ radius) :
    |old x-pc| ≤ 5*radius+(60/1000000:ℝ)*radius := by
  obtain ⟨w,hw,hd⟩ := seedDistance_attained S hS x
  have ho := hOld.dist_le_mul x w
  rw [Real.dist_eq] at ho
  have hs := hseed w hw
  have hh := abs_sub_le (old x) (old w) pc
  change |old x-old w| ≤ 5*dist x w at ho
  linarith

lemma spatial_boundary (hS : S.Nonempty) (hζ : R.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    {x : M.Point J root} (hx : seedDistance S x = radius) :
    spatial R S L ordinary pc radius αo α x ≤ old x-(199/1000:ℝ)*radius := by
  have hT := shallow_boundary R S hζ hδ hα hx (pc := pc)
  cases ordinary with
  | false =>
    simp only [spatial,Bool.false_eq_true,ite_false]
    obtain ⟨w,hw,hd⟩ := seedDistance_attained S hS x
    have ha := hadmit rfl w hw x (by rw [dist_comm,← hd,hx])
    linarith
  | true =>
    simp only [spatial,ite_true]
    exact Clipping.ordinary_boundary_margin hr hαo (hord rfl x) hT

lemma replacement_boundary (hS : S.Nonempty) (hζ : R.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : R.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (αh lo : ℝ) {x : M.Point J root} (hx : seedDistance S x = radius) :
    replacement R S old L ordinary pc radius αo αh lo α x = old x := by
  apply max_eq_left
  have h := spatial_boundary R S old L ordinary hS hζ hr hαo hδ hα hord hadmit hx
  exact (min_le_left _ _).trans (by linarith)

lemma replacement_endpoint (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    {pc radius αo αh lo : ℝ} (hr : radius ≤ (1:ℝ)/100) (hαh : αh ≤ radius/1000)
    (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    (α : Point.RadialTree.Noise (n := n)) {x : M.Point J root}
    (hx : seedDistance S x ≤ radius) (he : x.height = lo ∨ x.height = lo+R.a) :
    replacement R S old L ordinary pc radius αo αh lo α x = old x := by
  apply max_eq_left
  have h := (abs_le.mp (replacement_near S old hS hOld hseed hx)).1
  have hh : Clipping.heightShield lo R.a pc αh x.height = pc-1+αh := by
    rcases he with he | he
    · exact Clipping.heightShield_left (by rw [he])
    · exact Clipping.heightShield_right (by rw [he])
  apply (min_le_right _ _).trans
  rw [hh]
  linarith

lemma point_dist {radius : ℝ} {i : Fin n} {H T : ℝ}
    (hH : H ∈ domain S radius i) (hT : T ∈ domain S radius i) :
    dist (point S radius i H hH) (point S radius i T hT) = |H-T| := by
  rw [Point.dist_same_column _ _ (by rw [point_column S radius hH,point_column S radius hT])]
  rw [point_height S radius hH,point_height S radius hT]

lemma point_dist_switch {radius : ℝ} {i j : Fin n} {H : ℝ}
    (hH : H ∈ domain S radius i) (hT : H ∈ domain S radius j) (hs : H ∈ M.heights i j) :
    dist (point S radius i H hH) (point S radius j H hT) = 0 := by
  apply le_antisymm _ dist_nonneg
  have h := (point S radius i H hH).dist_le_switch (point S radius j H hT)
    (inBand_of_mem S radius hH) (by rw [point_column S radius hH,point_column S radius hT]; exact hs)
  simpa only [point_height S radius hH,point_height S radius hT,sub_self,abs_zero,add_zero] using h

noncomputable def converted (pc radius αo αh lo c η κ : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (i : Fin n) (H : ℝ) : ℝ :=
  if h : H ∈ domain S radius i then
    κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α (point S radius i H h)) else 0

lemma converted_on (pc radius αo αh lo c η κ : ℝ)
    (α : Point.RadialTree.Noise (n := n)) {i : Fin n} {H : ℝ} (h : H ∈ domain S radius i) :
    converted R S old L ordinary pc radius αo αh lo c η κ α i H =
      κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α (point S radius i H h)) := by
  simp only [converted,dite_eq_left h]

lemma converted_lipschitz (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo c η κ : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1) (i : Fin n) :
    LipschitzOnWith 1 (converted R S old L ordinary pc radius αo αh lo c η κ α i) (domain S radius i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro H hH T hT
  rw [converted_on R S old L ordinary pc radius αo αh lo c η κ α hH,
    converted_on R S old L ordinary pc radius αo αh lo c η κ α hT]
  let x := point S radius i H hH
  let y := point S radius i T hT
  have h := (replacement_lipschitz R S old L ordinary hOld hL pc radius αo αh lo hα).dist_le_mul x y
  rw [point_dist S hH hT,Real.dist_eq] at h
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  change |κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α x)-
    κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α y)| ≤ |H-T|
  rw [show κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α x)-
    κ*(c+η*replacement R S old L ordinary pc radius αo αh lo α y) =
    κ*η*(replacement R S old L ordinary pc radius αo αh lo α x-
      replacement R S old L ordinary pc radius αo αh lo α y) by ring,
    abs_mul,abs_mul,abs_of_nonneg hκ,hη,mul_one]
  calc
    _ ≤ κ*((replacementConstant R : ℝ)*|H-T|) := mul_le_mul_of_nonneg_left h hκ
    _ = (κ*(replacementConstant R : ℝ))*|H-T| := by ring
    _ ≤ 1*|H-T| := mul_le_mul_of_nonneg_right hκK (abs_nonneg _)
    _ = _ := one_mul _

/-- Literal secondary clipping on the actual closed seed-ball union, in both
ordinary and admitted ordered orientations, is an invariant-preserving patch. -/
noncomputable def patch {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : SetSystem M Ω μ) (Z : Threshold.Variables Ω μ)
    (hJ : IsCompact J) (lo : ℝ) (hband : J = Icc lo (lo+R.a))
    (hS : S.Nonempty) (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (hζ : R.ζ = (1:ℝ)/10) (pc radius αo αh c η κ : ℝ)
    (hr : 0 ≤ radius) (hrsmall : radius ≤ (1:ℝ)/100) (hαo : αo ≤ radius/1000)
    (hαh : αh ≤ radius/1000) (hδ : R.δ = (radius/1000)/8)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (hseed : ∀ w ∈ S, |old w-pc| ≤ (60/1000000:ℝ)*radius)
    (hη : |η| = 1) (hκ : 0 ≤ κ) (hκK : κ*(replacementConstant R : ℝ) ≤ 1)
    (hchart : ∀ ω i H (h : H ∈ domain S radius i),
      Threshold.active Z H (κ*(c+η*old (point S radius i H h))) ω ↔ (A.activity ω).active i H) :
    SetPatch A := by
  have hclosed := fun i => (compact_domain S radius hJ i).isClosed
  apply Threshold.chartPatch A Z (domain S radius) hclosed
    (converted R S old L ordinary pc radius αo αh lo c η κ α)
    (converted_lipschitz R S old L ordinary hOld hL pc radius αo αh lo c η κ hα hη hκ hκK)
  · intro ω i H hH
    obtain ⟨hd,he⟩ := equal_radius_or_endpoint S radius hJ lo R.a R.width_pos hband hH
    rw [converted_on R S old L ordinary pc radius αo αh lo c η κ α hd]
    have heq : replacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd) =
        old (point S radius i H hd) := by
      rcases he with he | he
      · exact replacement_boundary R S old L ordinary hS hζ hr hαo hδ hα hord hadmit αh lo he
      · exact replacement_endpoint R S old L ordinary hS hOld hrsmall hαh hseed α
          (point_distance S radius hd) (by rw [point_height S radius hd]; exact he)
    rw [heq]
    exact hchart ω i H hd
  · intro i j H hs hi hj
    rw [converted_on R S old L ordinary pc radius αo αh lo c η κ α hi,
      converted_on R S old L ordinary pc radius αo αh lo c η κ α hj]
    have h := (replacement_lipschitz R S old L ordinary hOld hL pc radius αo αh lo hα).dist_le_mul
      (point S radius i H hi) (point S radius j H hj)
    rw [point_dist_switch S hi hj hs,mul_zero] at h
    rw [dist_le_zero.mp h]
  · intro ω i j H hs hi hj
    exact (hj (switch_mem S radius hs hi)).elim

end PlanarL1.Columns.Model.SecondaryCell




end

section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)

noncomputable def namedReplacement (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) : M.Point J root → NamedValue :=
  secondaryNamed (fun x => ⟨(R.pasted (input S) α x).name,shallow R S pc radius α x⟩)
    old (Clipping.orderedBranch pc radius αo L)
    (fun x => Clipping.heightShield lo R.a pc αh x.height) ordinary

lemma namedReplacement_value (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α x).value =
      replacement R S old L ordinary pc radius αo αh lo α x := by
  rw [namedReplacement,secondaryNamed_value]
  rfl

noncomputable def localAtom {k : ℕ} (A : R.Node k)
    (pc radius αo αh lo : ℝ) (α : Point.RadialTree.Noise (n := n)) : ℕ → M.Point J root → ℝ :=
  secondaryAtom (fun i x => pc+radius/20-(R.listedAtom (input S) α A R.lookback i x).value)
    old (Clipping.orderedBranch pc radius αo L)
    (fun x => Clipping.heightShield lo R.a pc αh x.height)

end PlanarL1.Columns.Model.SecondaryCell



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryStep
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData
noncomputable def isOrdinary : BData M → Bool
  | .ordinary _ => true
  | .ordered _ => false

noncomputable def comparison (D : BData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (positive : Bool) : M.Field D.band 5 :=
  match D with
  | .ordinary C => C.comparison.weaken (by norm_num)
  | .ordered C => if positive then C.field lam hlam else (C.field lam hlam).negate

noncomputable def offset : BData M → ℝ
  | .ordinary C => C.constant
  | .ordered _ => 0

noncomputable def orientation (positive : Bool) : BData M → ℝ
  | .ordinary C => C.orientation
  | .ordered _ => if positive then 1 else -1

lemma orientation_unit (positive : Bool) (D : BData M) : |D.orientation positive|=1 := by
  cases D with
  | ordinary C => exact C.unit_orientation
  | ordered C => cases positive <;> norm_num [orientation]

lemma comparison_convert (D : BData M) (lam : ℝ≥0) (hlam : lam ≤ (1:ℝ≥0)/100)
    (positive : Bool) (i : Fin (k+1)) (H : D.band) :
    D.value lam i H = D.offset+D.orientation positive*(D.comparison lam hlam positive).value i H := by
  cases D with
  | ordinary C => rfl
  | ordered C =>
    cases positive
    · change C.value lam i H = 0+(-1)*(-(C.field lam hlam).value i H)
      erw [OrderedData.field_value]; ring
    · change C.value lam i H = 0+1*(C.field lam hlam).value i H
      erw [OrderedData.field_value]; ring
end BData

namespace OrdinaryData
/-- The affine conversion constants, without manufacturing a point source. -/
noncomputable def conversion (M : Model (k+1)) (c η : ℝ) (hη : |η|=1) : OrdinaryData M where
  band := Set.univ
  closed := isClosed_univ
  convex := Set.ordConnected_univ
  origin := none
  constant := c
  orientation := η
  unit_orientation := hη
end OrdinaryData

namespace Point.RadialTree
variable {J : Set ℝ} {root : Fin (k+1)} (R : RadialTree (M := M) (J := J) (root := root))
namespace AtomSource
variable {R} {a : ℕ}
/-- Exact shallow-secondary ordinary chart: c+η(pc+R/20−Q_F). -/
noncomputable def secondaryChart (A : R.AtomSource a) (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) : OrdinaryData M :=
  (OrdinaryData.conversion M c η hη).atom J R.closed_band R.interval_band A.center
    (pc+radius/20-A.intercept p α) (-A.sign) (by rw [abs_neg,A.sign_unit])

lemma secondaryChart_value (A : R.AtomSource a) (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (x : M.Point J root) :
    (A.secondaryChart c η hη p α pc radius).value x.column ⟨x.height,x.inBand⟩ =
      c+η*(pc+radius/20-(A.eval p α x).value) := by
  change ((OrdinaryData.conversion M c η hη).atom J R.closed_band R.interval_band A.center
    (pc+radius/20-A.intercept p α) (-A.sign) _).value x.column ⟨x.height,x.inBand⟩ = _
  rw [OrdinaryData.atom_value,A.eval_formula]
  dsimp only [OrdinaryData.conversion]
  ring
end AtomSource

noncomputable def secondaryChart (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (a : ℕ) : OrdinaryData M :=
  if h : Nonempty (R.AtomSource a) then h.some.secondaryChart c η hη p α pc radius
  else OrdinaryData.initial M

lemma secondaryChart_value (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (x : M.Point J root) :
    ∃ h : x.height ∈ (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name).band,
      (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name).value x.column ⟨x.height,h⟩ =
        c+η*(pc+radius/20-(R.pasted p α x).value) := by
  have h := R.pasted_has_source p α x
  let Q : OrdinaryData M → Prop := fun T => ∃ hi : x.height ∈ T.band,
    T.value x.column ⟨x.height,hi⟩ = c+η*(pc+radius/20-(R.pasted p α x).value)
  change Q (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name)
  rw [show R.secondaryChart c η hη p α pc radius (R.pasted p α x).name =
    h.some.secondaryChart c η hη p α pc radius from dite_eq_left h]
  exact ⟨x.inBand,(h.some.secondaryChart_value c η hη p α pc radius x).trans
    (by rw [R.source_eval_pasted])⟩

lemma secondaryChart_contains (c η : ℝ) (hη : |η|=1)
    (p : M.Point J root → ℝ) (α : Noise (n := k+1)) (pc radius : ℝ) (x : M.Point J root) :
    (R.secondaryChart c η hη p α pc radius (R.pasted p α x).name).Contains x.column x.height := by
  have h := R.pasted_has_source p α x
  rw [show R.secondaryChart c η hη p α pc radius (R.pasted p α x).name =
    h.some.secondaryChart c η hη p α pc radius from dite_eq_left h]
  exact OrdinaryData.atom_contains _ _ _ _ _ x _ _ _
end Point.RadialTree

namespace OrderedData
/-- The source ordered-support branch, including the old affine chart
conversion. The auxiliary field is zero and the circular order reverses exactly
when η is negative. -/
noncomputable def secondaryInstall {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c η pc radius α : ℝ) (_hη : |η|=1) : OrderedData M :=
  install hI hc L a b ho (η*c+pc+radius/20-4*pc+α) (decide (η=1))

lemma secondaryInstall_value {I : Set ℝ} (hI : IsClosed I) (hc : I.OrdConnected)
    (L : M.Field I 1) (a b : Fin (k+1)) (ho : L.OrderedFrom a b)
    (c η pc radius α : ℝ) (hη : |η|=1) (lam : ℝ≥0) (i : Fin (k+1)) (H : I) :
    (secondaryInstall hI hc L a b ho c η pc radius α hη).value lam i H =
      c+η*(pc+radius/20+4*(L.value i H-pc)+α) := by
  change (install hI hc L a b ho (η*c+pc+radius/20-4*pc+α) (decide (η=1))).value lam i H = _
  rw [install_value]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hη with he | he
  · simp only [he,decide_true,ite_true]; ring
  · norm_num [he]; ring
end OrderedData
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root))
variable (old L : M.Point J root → ℝ) (ordinary : Bool)

lemma namedReplacement_cases (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) :
    namedReplacement R S old L ordinary pc radius αo αh lo α x=⟨0,old x⟩ ∨
    namedReplacement R S old L ordinary pc radius αo αh lo α x=
      ⟨1,Clipping.heightShield lo R.a pc αh x.height⟩ ∨
    namedReplacement R S old L ordinary pc radius αo αh lo α x=
      ⟨2,Clipping.orderedBranch pc radius αo L x⟩ ∨
    namedReplacement R S old L ordinary pc radius αo αh lo α x=
      ⟨(R.pasted (input S) α x).name+3,shallow R S pc radius α x⟩ :=
  secondaryNamed_mem _ _ _ _ _ x

lemma namedReplacement_bound (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root) :
    (namedReplacement R S old L ordinary pc radius αo αh lo α x).name < 3*n*R.depthCap+3 := by
  rcases namedReplacement_cases R S old L ordinary pc radius αo αh lo α x with h | h | h | h
  · rw [h]; simp only; omega
  · rw [h]; simp only; omega
  · rw [h]; simp only; omega
  · rw [h]
    exact Nat.add_lt_add_right (R.pasted_name_lt (input S) α x) 3

lemma namedReplacement_congr_zero (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (x y : M.Point J root) (hxy : dist x y=0) :
    namedReplacement R S old L ordinary pc radius αo αh lo α x =
      namedReplacement R S old L ordinary pc radius αo αh lo α y := by
  have hp := R.pasted_congr_zero (input S) hα x y hxy
  have ho : old x=old y := dist_le_zero.mp (by simpa only [hxy,mul_zero] using hOld.dist_le_mul x y)
  have hl : L x=L y := dist_le_zero.mp (by simpa only [hxy,mul_zero] using hL.dist_le_mul x y)
  have hh : x.height=y.height := by
    have ht : |x.height-y.height| ≤ dist x y := x.height_change_le y
    rw [hxy] at ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ht (abs_nonneg _)))
  simp only [namedReplacement,secondaryNamed,shallow,approx,hp,ho,hh,Clipping.orderedBranch,hl]

noncomputable def choose (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (i : Fin n) (H : ℝ) :
    Option (Fin (3*n*R.depthCap+2)) :=
  if hd : H ∈ domain S radius i then
    let t := namedReplacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd)
    if ht : t.name=0 then none else some ⟨t.name-1,by
      have hb := namedReplacement_bound R S old L ordinary pc radius αo αh lo α (point S radius i H hd)
      dsimp only [t] at ht ⊢
      omega⟩
  else none

lemma choose_spec (pc radius αo αh lo : ℝ) (α : Point.RadialTree.Noise (n := n))
    (i : Fin n) (H : ℝ) (a : Fin (3*n*R.depthCap+2))
    (h : choose R S old L ordinary pc radius αo αh lo α i H=some a) :
    ∃ hd : H ∈ domain S radius i,
      (namedReplacement R S old L ordinary pc radius αo αh lo α (point S radius i H hd)).name=a.val+1 := by
  by_cases hd : H ∈ domain S radius i
  · simp only [choose,dite_eq_left hd] at h
    split_ifs at h with ht
    refine ⟨hd,?_⟩
    have he := congrArg Fin.val (Option.some.inj h)
    dsimp only at he ht
    omega
  · simp only [choose,dite_eq_right hd] at h
    cases h

lemma choose_switch (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (pc radius αo αh lo : ℝ) {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    (i j : Fin n) (H : ℝ) (hs : H ∈ M.heights i j) :
    choose R S old L ordinary pc radius αo αh lo α i H =
      choose R S old L ordinary pc radius αo αh lo α j H := by
  by_cases hi : H ∈ domain S radius i
  · have hj := switch_mem S radius hs hi
    have he := namedReplacement_congr_zero R S old L ordinary hOld hL pc radius αo αh lo hα
      (point S radius i H hi) (point S radius j H hj) (point_dist_switch S hi hj hs)
    simp only [choose,dite_eq_left hi,dite_eq_left hj]
    simp only [he]
  · have hj : H ∉ domain S radius j := fun hj => hi (switch_mem S radius (M.symm i j ▸ hs) hj)
    simp only [choose,dite_eq_right hi,dite_eq_right hj]
end PlanarL1.Columns.Model.SecondaryCell


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BState
lemma represents_named (S : BState M κ lam Ω μ) (ω : Ω) (i : Fin (k+1)) (H : ℝ)
    (a : Fin (S.count+1)) (ha : S.name i H=a) (hi : H ∈ (S.chart a).band) :
    (S.sets.activity ω).active i H ↔ Threshold.active (S.labels a) H
      (κ*(S.chart a).value lam i ⟨H,hi⟩) ω := by
  subst a
  exact S.represents ω i H

/-- One kept group's literal secondary clipping. Only the geometric admission,
seed and eligibility data enter; every new chart below is constructed from the
winning formula, not postulated. -/
structure SecondaryStep (S : BState M κ lam Ω μ) (J : Set ℝ) (root : Fin (k+1)) where
  index : Fin (S.count+1)
  positive : Bool
  lambda_bound : lam ≤ (1:ℝ≥0)/100
  tree : Point.RadialTree (M := M) (J := J) (root := root)
  lo : ℝ
  band_eq : J=Set.Icc lo (lo+tree.a)
  sub_old : J ⊆ (S.chart index).band
  seeds : Finset (M.Point J root)
  seeds_nonempty : seeds.Nonempty
  pc : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_small : radius ≤ (1:ℝ)/100
  support : M.Field (S.chart index).band 1
  lower : Fin (k+1)
  upper : Fin (k+1)
  support_ordered : support.OrderedFrom lower upper
  support_le : (S.chart index).isOrdinary=true → ∀ x : M.Point J root,
    support.value x.column ⟨x.height,sub_old x.inBand⟩ ≤
      ((S.chart index).comparison lam lambda_bound positive).value x.column ⟨x.height,sub_old x.inBand⟩
  admitted : (S.chart index).isOrdinary=false → ∀ w ∈ seeds, ∀ x : M.Point J root,
    dist w x=radius → pc-(65/100:ℝ)*radius ≤
      ((S.chart index).comparison lam lambda_bound positive).value x.column ⟨x.height,sub_old x.inBand⟩
  seed_near : ∀ w ∈ seeds,
    |((S.chart index).comparison lam lambda_bound positive).value w.column ⟨w.height,sub_old w.inBand⟩-pc| ≤
      (60/1000000:ℝ)*radius
  zeta_eq : tree.ζ=(1:ℝ)/10
  delta_eq : tree.δ=(radius/1000)/8
  noise : Point.RadialTree.Noise (n := k+1)
  noise_bounds : tree.NoiseBounds noise
  ordered_offset : ℝ
  shield_offset : ℝ
  ordered_bound : ordered_offset ≤ radius/1000
  shield_bound : shield_offset ≤ radius/1000
  same_name : ∀ i H, H ∈ SecondaryCell.domain seeds radius i → S.name i H=index
  kappa_nonneg : 0 ≤ κ
  vertical_bound : κ*(SecondaryCell.replacementConstant tree : ℝ) ≤ 1
  shield_strict : κ*(3/(9*tree.a/100)) < 1

namespace SecondaryStep
variable {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)

noncomputable def data : BData M := S.chart U.index
noncomputable def comparison : M.Field U.data.band 5 := U.data.comparison lam U.lambda_bound U.positive
noncomputable def old (x : M.Point J root) : ℝ := U.comparison.value x.column ⟨x.height,U.sub_old x.inBand⟩
noncomputable def supportValue (x : M.Point J root) : ℝ := U.support.value x.column ⟨x.height,U.sub_old x.inBand⟩

lemma old_lipschitz : LipschitzWith 5 U.old :=
  (U.comparison.restrict U.sub_old).lipschitz U.tree.closed_band root
lemma support_lipschitz : LipschitzWith 1 U.supportValue :=
  (U.support.restrict U.sub_old).lipschitz U.tree.closed_band root
include U in
lemma compact_band : IsCompact J := by rw [U.band_eq]; exact isCompact_Icc

lemma old_agreement (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    Threshold.active (S.labels U.index).lift H
      (κ*(U.data.offset+U.data.orientation U.positive*U.old (SecondaryCell.point U.seeds U.radius i H hi))) ω ↔
        (S.lift.sets.activity ω).active i H := by
  have he := U.data.comparison_convert lam U.lambda_bound U.positive i
    ⟨H,U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hi)⟩
  have hr := S.represents_named ω.1 i H U.index (U.same_name i H hi)
    (U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hi))
  dsimp only [data] at he
  rw [he] at hr
  change Threshold.active (S.labels U.index) H
    (κ*(U.data.offset+U.data.orientation U.positive*U.old (SecondaryCell.point U.seeds U.radius i H hi))) ω.1 ↔
      (S.sets.activity ω.1).active i H
  simpa only [old,comparison,data,SecondaryCell.point_column,SecondaryCell.point_height] using hr.symm

noncomputable def patch : SetPatch S.lift.sets :=
  SecondaryCell.patch U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    S.lift.sets (S.labels U.index).lift U.compact_band U.lo U.band_eq
    U.seeds_nonempty U.old_lipschitz U.support_lipschitz U.zeta_eq
    U.pc U.radius U.ordered_offset U.shield_offset U.data.offset (U.data.orientation U.positive) κ
    U.radius_nonneg U.radius_small U.ordered_bound U.shield_bound U.delta_eq U.noise_bounds
    U.support_le U.admitted U.seed_near (U.data.orientation_unit U.positive)
    U.kappa_nonneg U.vertical_bound U.old_agreement

noncomputable def input : M.Point J root → ℝ := SecondaryCell.input U.seeds
noncomputable def replacement := SecondaryCell.replacement U.tree U.seeds U.old U.supportValue
  U.data.isOrdinary U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
noncomputable def named := SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue
  U.data.isOrdinary U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
noncomputable def shield (H : ℝ) : ℝ :=
  κ*(U.data.offset+U.data.orientation U.positive*Clipping.heightShield U.lo U.tree.a U.pc U.shield_offset H)
noncomputable def shieldConstant : ℝ≥0 :=
  ⟨κ*(3/(9*U.tree.a/100)),mul_nonneg U.kappa_nonneg (by positivity [U.tree.width_pos])⟩

lemma shield_lipschitz : LipschitzWith U.shieldConstant U.shield := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have ht := (Clipping.heightShield_lipschitz U.lo U.pc U.shield_offset U.tree.width_pos).dist_le_mul H T
  rw [Real.dist_eq] at ht
  change |shield U H-shield U T| ≤ (κ*(3/(9*U.tree.a/100)))*dist H T
  unfold shield
  rw [show κ*(U.data.offset+U.data.orientation U.positive*Clipping.heightShield U.lo U.tree.a
      U.pc U.shield_offset H)-κ*(U.data.offset+U.data.orientation U.positive*Clipping.heightShield U.lo U.tree.a
      U.pc U.shield_offset T) = κ*U.data.orientation U.positive*(Clipping.heightShield U.lo U.tree.a
      U.pc U.shield_offset H-Clipping.heightShield U.lo U.tree.a U.pc U.shield_offset T) by ring,
    abs_mul,abs_mul,abs_of_nonneg U.kappa_nonneg,U.data.orientation_unit,mul_one]
  exact (mul_le_mul_of_nonneg_left ht U.kappa_nonneg).trans_eq (mul_assoc _ _ _).symm

noncomputable def orderedChart : OrderedData M :=
  OrderedData.secondaryInstall U.data.closed U.data.convex U.support U.lower U.upper U.support_ordered
    U.data.offset (U.data.orientation U.positive) U.pc U.radius U.ordered_offset (U.data.orientation_unit U.positive)

noncomputable def newData (a : Fin (3*(k+1)*U.tree.depthCap+2)) : BData M :=
  if a.val=0 then .ordinary (OrdinaryData.initial M) else
  if a.val=1 then .ordered U.orderedChart else
    .ordinary (U.tree.secondaryChart U.data.offset (U.data.orientation U.positive)
      (U.data.orientation_unit U.positive) U.input U.noise U.pc U.radius (a.val-2))

noncomputable def newLabels [SFinite μ] (a : Fin (3*(k+1)*U.tree.depthCap+2)) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) :=
  if a.val=0 then (S.labels U.index).rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz
  else (S.labels U.index).lift

noncomputable def choose := SecondaryCell.choose U.tree U.seeds U.old U.supportValue
  U.data.isOrdinary U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise

lemma patch_inside (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    (U.patch.apply.activity ω).active i H ↔ Threshold.active (S.labels U.index).lift H
      (κ*(U.data.offset+U.data.orientation U.positive*U.replacement (SecondaryCell.point U.seeds U.radius i H hi))) ω := by
  apply (U.patch.inside hi ω).trans
  change Threshold.active _ H (SecondaryCell.converted U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.data.offset (U.data.orientation U.positive) κ U.noise i H) ω ↔ _
  rw [SecondaryCell.converted_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi]
  rfl

lemma chosen_description [SFinite μ] (i : Fin (k+1)) (H : ℝ)
    (a : Fin (3*(k+1)*U.tree.depthCap+2)) (hc : U.choose i H=some a) :
    (H ∈ (U.newData a).band ∧ (U.newData a).Uses i) ∧
      ∀ (ω : Ω × Bool) (hi : H ∈ (U.newData a).band),
        (U.patch.apply.activity ω).active i H ↔
          Threshold.active (U.newLabels a) H (κ*(U.newData a).value lam i ⟨H,hi⟩) ω := by
  let Q (D : BData M) (Z : Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair)) : Prop :=
    (H ∈ D.band ∧ D.Uses i) ∧ ∀ (ω : Ω × Bool) (hi : H ∈ D.band),
      (U.patch.apply.activity ω).active i H ↔ Threshold.active Z H (κ*D.value lam i ⟨H,hi⟩) ω
  change Q (U.newData a) (U.newLabels a)
  obtain ⟨hd,hn⟩ := SecondaryCell.choose_spec U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise i H a hc
  let x := SecondaryCell.point U.seeds U.radius i H hd
  have hcol : x.column=i := SecondaryCell.point_column _ _ hd
  have hheight : x.height=H := SecondaryCell.point_height _ _ hd
  change (SecondaryCell.namedReplacement U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x).name=a.val+1 at hn
  rcases SecondaryCell.namedReplacement_cases U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x with ho | hh | hq | hp
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name ho
    change _=0 at hn'
    omega
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hh
    change _=1 at hn'
    have ha0 : a.val=0 := by omega
    simp only [newData,newLabels,ite_eq_left ha0]
    refine ⟨OrdinaryData.initial_contains i H,?_⟩
    intro ω hi
    have hv : U.replacement x=Clipping.heightShield U.lo U.tree.a U.pc U.shield_offset H := by
      change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
      rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,hh]
      change Clipping.heightShield _ _ _ _ x.height = _
      rw [hheight]
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at h0
    rw [hv] at h0
    change _ ↔ Threshold.active _ H (κ*(OrdinaryData.initial M).value i ⟨H,hi⟩) ω
    have hz : (OrdinaryData.initial M).value i ⟨H,hi⟩ = 0 := OrdinaryData.initial_value M i H
    rw [hz,mul_zero]
    exact h0.trans ((S.labels U.index).active_rebase (K := U.shieldConstant) U.shield_strict U.shield_lipschitz H ω)
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hq
    change _=2 at hn'
    have ha0 : a.val≠0 := by omega
    have ha1 : a.val=1 := by omega
    simp only [newData,newLabels,ite_eq_right ha0,ite_eq_left ha1]
    refine ⟨⟨U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hd),trivial⟩,?_⟩
    intro ω hi
    have hv : U.replacement x=Clipping.orderedBranch U.pc U.radius U.ordered_offset U.supportValue x := by
      change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
      rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,hq]
    have h0 := U.patch_inside ω i H hd
    change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at h0
    rw [hv] at h0
    have he := OrderedData.secondaryInstall_value U.data.closed U.data.convex U.support U.lower U.upper
      U.support_ordered U.data.offset (U.data.orientation U.positive) U.pc U.radius U.ordered_offset
      (U.data.orientation_unit U.positive) lam i ⟨H,hi⟩
    change _ ↔ Threshold.active _ H (κ*U.orderedChart.value lam i ⟨H,hi⟩) ω
    rw [show U.orderedChart.value lam i ⟨H,hi⟩ = _ from he]
    have hs : U.supportValue x=U.support.value i ⟨H,hi⟩ := by
      dsimp only [supportValue]
      congr 1
      exact Subtype.ext hheight
    simp only [Clipping.orderedBranch,hs] at h0
    exact h0
  · have hn' := congrArg PlanarL1.Interpolation.NamedValue.name hp
    change _=(U.tree.pasted U.input U.noise x).name+3 at hn'
    have ha0 : a.val≠0 := by omega
    have ha1 : a.val≠1 := by omega
    have ha2 : a.val-2=(U.tree.pasted U.input U.noise x).name := by omega
    simp only [newData,newLabels,ite_eq_right ha0,ite_eq_right ha1,ha2]
    refine ⟨?_,?_⟩
    · change (U.tree.secondaryChart _ _ _ _ _ _ _ _).Contains i H
      simpa only [hcol,hheight] using U.tree.secondaryChart_contains U.data.offset
        (U.data.orientation U.positive) (U.data.orientation_unit U.positive) U.input U.noise U.pc U.radius x
    · intro ω hi
      obtain ⟨hb,hvalue⟩ := U.tree.secondaryChart_value U.data.offset (U.data.orientation U.positive)
        (U.data.orientation_unit U.positive) U.input U.noise U.pc U.radius x
      have hv : U.replacement x=SecondaryCell.shallow U.tree U.seeds U.pc U.radius U.noise x := by
        change SecondaryCell.replacement _ _ _ _ _ _ _ _ _ _ _ _ = _
        rw [← SecondaryCell.namedReplacement_value U.tree U.seeds U.old U.supportValue U.data.isOrdinary
          U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise x,hp]
      have h0 := U.patch_inside ω i H hd
      change _ ↔ Threshold.active _ H (κ*(U.data.offset+U.data.orientation U.positive*U.replacement x)) ω at h0
      rw [hv] at h0
      simp only [hcol,hheight] at hvalue
      exact h0.trans (Iff.of_eq (congrArg (fun p => Threshold.active (S.labels U.index).lift H (κ*p) ω)
        hvalue.symm))

lemma choose_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) : U.choose i H=U.choose j H :=
  SecondaryCell.choose_switch U.tree U.seeds U.old U.supportValue U.data.isOrdinary U.old_lipschitz
    U.support_lipschitz U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise_bounds i j H hs

end SecondaryStep
end BState
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.BState.SecondaryStep
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)

lemma point_old {i : Fin (k+1)} {H : ℝ} (hd : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    U.old (SecondaryCell.point U.seeds U.radius i H hd) =
      U.comparison.value i ⟨H,U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hd)⟩ := by
  simp only [old,SecondaryCell.point_column,SecondaryCell.point_height]

lemma replacement_lipschitz : LipschitzWith (SecondaryCell.replacementConstant U.tree) U.replacement :=
  SecondaryCell.replacement_lipschitz U.tree U.seeds U.old U.supportValue U.data.isOrdinary
    U.old_lipschitz U.support_lipschitz U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise_bounds

lemma replacement_frontier {i : Fin (k+1)} {H : ℝ}
    (hf : H ∈ frontier (SecondaryCell.domain U.seeds U.radius i))
    (hd : H ∈ SecondaryCell.domain U.seeds U.radius i) :
    U.replacement (SecondaryCell.point U.seeds U.radius i H hd) =
      U.old (SecondaryCell.point U.seeds U.radius i H hd) := by
  obtain ⟨_,he⟩ := SecondaryCell.equal_radius_or_endpoint U.seeds U.radius U.compact_band U.lo U.tree.a
    U.tree.width_pos U.band_eq hf
  rcases he with he | he
  · exact SecondaryCell.replacement_boundary U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.seeds_nonempty U.zeta_eq U.radius_nonneg U.ordered_bound U.delta_eq U.noise_bounds
      U.support_le U.admitted U.shield_offset U.lo he
  · exact SecondaryCell.replacement_endpoint U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.seeds_nonempty U.old_lipschitz U.radius_small U.shield_bound U.seed_near U.noise
      (SecondaryCell.point_distance U.seeds U.radius hd)
      (by rw [SecondaryCell.point_height U.seeds U.radius hd]; exact he)

/-- The literal clamped proposal, extended by the old comparison on the rest
of the old band. This is the extension whose finite maximum is required for
simultaneous overlapping secondary groups. -/
noncomputable def fullReplacement (i : Fin (k+1)) (H : U.data.band) : ℝ :=
  if hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i then
    U.replacement (SecondaryCell.point U.seeds U.radius i H.val hd)
  else U.comparison.value i H

lemma fullReplacement_inside (i : Fin (k+1)) (H : U.data.band)
    (hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i) :
    U.fullReplacement i H=U.replacement (SecondaryCell.point U.seeds U.radius i H.val hd) := dite_eq_left hd

lemma fullReplacement_outside (i : Fin (k+1)) (H : U.data.band)
    (hd : H.val ∉ SecondaryCell.domain U.seeds U.radius i) :
    U.fullReplacement i H=U.comparison.value i H := dite_eq_right hd

lemma fullReplacement_vertical (i : Fin (k+1)) :
    LipschitzWith (SecondaryCell.replacementConstant U.tree) (U.fullReplacement i) := by
  let oldColumn (H : ℝ) := if h : H ∈ U.data.band then U.comparison.value i ⟨H,h⟩ else 0
  have ho : LipschitzOnWith 5 oldColumn U.data.band := by
    apply LipschitzOnWith.of_dist_le_mul
    intro H hH T hT
    simpa only [oldColumn,dite_eq_left hH,dite_eq_left hT,Subtype.dist_eq] using
      (U.comparison.vertical i).dist_le_mul ⟨H,hH⟩ ⟨T,hT⟩
  obtain ⟨g,hg,he⟩ := ho.extend_real
  let proposal (H : ℝ) := if hd : H ∈ SecondaryCell.domain U.seeds U.radius i then
    U.replacement (SecondaryCell.point U.seeds U.radius i H hd) else 0
  have hp : LipschitzOnWith (SecondaryCell.replacementConstant U.tree) proposal
      (SecondaryCell.domain U.seeds U.radius i) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro H hH T hT
    have h := U.replacement_lipschitz.dist_le_mul
      (SecondaryCell.point U.seeds U.radius i H hH) (SecondaryCell.point U.seeds U.radius i T hT)
    simpa only [proposal,dite_eq_left hH,dite_eq_left hT,SecondaryCell.point_dist,Real.dist_eq] using h
  have hb : EqOn proposal g (frontier (SecondaryCell.domain U.seeds U.radius i)) := by
    intro H hH
    have hd := (SecondaryCell.compact_domain U.seeds U.radius U.compact_band i).isClosed.frontier_subset hH
    have hi := U.sub_old (SecondaryCell.inBand_of_mem U.seeds U.radius hd)
    simp only [proposal,dite_eq_left hd,U.replacement_frontier hH hd,U.point_old hd]
    have hv : oldColumn H = U.comparison.value i ⟨H,hi⟩ := dite_eq_left hi
    exact hv.symm.trans (he hi)
  have hl := PlanarL1.Gluing.lipschitz_piecewise
    (SecondaryCell.compact_domain U.seeds U.radius U.compact_band i).isClosed
    (hg.weaken (show (5:ℝ≥0) ≤ SecondaryCell.replacementConstant U.tree from le_max_left _ _)) hp hb
  have hv (H : U.data.band) : U.fullReplacement i H=
      (SecondaryCell.domain U.seeds U.radius i).piecewise proposal g H.val := by
    by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
    · simp only [fullReplacement,dite_eq_left hd,piecewise_eq_of_mem _ _ _ hd,proposal]
    · rw [U.fullReplacement_outside i H hd,piecewise_eq_of_notMem _ _ _ hd]
      simpa only [oldColumn,dite_eq_left H.property] using he H.property
  apply LipschitzWith.of_dist_le_mul
  intro H T
  rw [hv H,hv T]
  exact hl.dist_le_mul H.val T.val

end PlanarL1.Columns.Model.BState.SecondaryStep

namespace PlanarL1.Columns.Model.BState.SecondaryStep
open MeasureTheory Set
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {S : BState M κ lam Ω μ} {J : Set ℝ} {root : Fin (k+1)}
variable (U : SecondaryStep S J root)

noncomputable def fullNamed (i : Fin (k+1)) (H : U.data.band) : NamedValue :=
  if hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i then
    U.named (SecondaryCell.point U.seeds U.radius i H.val hd)
  else ⟨0,U.comparison.value i H⟩

lemma fullNamed_value (i : Fin (k+1)) (H : U.data.band) :
    (U.fullNamed i H).value = U.fullReplacement i H := by
  unfold fullNamed fullReplacement
  split_ifs with hd
  · exact SecondaryCell.namedReplacement_value _ _ _ _ _ _ _ _ _ _ _ _
  · rfl

lemma fullNamed_switch (i j : Fin (k+1)) (H : U.data.band)
    (hs : H.val ∈ M.heights i j) : U.fullNamed i H=U.fullNamed j H := by
  by_cases hi : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · have hj := SecondaryCell.switch_mem U.seeds U.radius hs hi
    simp only [fullNamed,dite_eq_left hi,dite_eq_left hj]
    exact SecondaryCell.namedReplacement_congr_zero U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.old_lipschitz U.support_lipschitz U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise_bounds
      _ _ (SecondaryCell.point_dist_switch U.seeds hi hj hs)
  · have hj : H.val ∉ SecondaryCell.domain U.seeds U.radius j := fun hj => hi
      (SecondaryCell.switch_mem U.seeds U.radius (M.symm i j ▸ hs) hj)
    simp only [fullNamed,dite_eq_right hi,dite_eq_right hj,U.comparison.switch i j H hs]

lemma fullNamed_zero (i : Fin (k+1)) (H : U.data.band)
    (h : (U.fullNamed i H).name=0) :
    (U.fullNamed i H).value=U.comparison.value i H := by
  by_cases hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i
  · simp only [fullNamed,dite_eq_left hd] at h ⊢
    rw [← U.point_old hd]
    rcases SecondaryCell.namedReplacement_cases U.tree U.seeds U.old U.supportValue U.data.isOrdinary
      U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
      (SecondaryCell.point U.seeds U.radius i H.val hd) with ho | hh | hq | hp
    · exact congrArg NamedValue.value ho
    · change (U.named _).name=0 at h
      have hn := congrArg NamedValue.name hh
      change (U.named _).name=1 at hn
      omega
    · have hn := congrArg NamedValue.name hq
      change (U.named _).name=2 at hn
      omega
    · have hn := congrArg NamedValue.name hp
      change (U.named _).name=_+3 at hn
      omega
  · simp only [fullNamed,dite_eq_right hd]

lemma fullNamed_choice (i : Fin (k+1)) (H : U.data.band)
    (h : (U.fullNamed i H).name ≠ 0) :
    ∃ a, U.choose i H.val=some a ∧ (U.fullNamed i H).name=a.val+1 ∧
      H.val ∈ SecondaryCell.domain U.seeds U.radius i := by
  have hd : H.val ∈ SecondaryCell.domain U.seeds U.radius i := by
    by_contra hd
    simp only [fullNamed,dite_eq_right hd] at h
    exact h rfl
  have ht : (U.named (SecondaryCell.point U.seeds U.radius i H.val hd)).name ≠ 0 := by
    simpa only [fullNamed,dite_eq_left hd] using h
  let a : Fin (3*(k+1)*U.tree.depthCap+2) :=
    ⟨(U.named (SecondaryCell.point U.seeds U.radius i H.val hd)).name-1,by
      have hb := SecondaryCell.namedReplacement_bound U.tree U.seeds U.old U.supportValue U.data.isOrdinary
        U.pc U.radius U.ordered_offset U.shield_offset U.lo U.noise
        (SecondaryCell.point U.seeds U.radius i H.val hd)
      change (U.named _).name < _ at hb
      omega⟩
  refine ⟨a,?_,?_,hd⟩
  · change (SecondaryCell.namedReplacement _ _ _ _ _ _ _ _ _ _ _ _).name ≠ 0 at ht
    simp only [choose,SecondaryCell.choose,dite_eq_left hd,dite_eq_right ht]
    rfl
  · simp only [fullNamed,dite_eq_left hd,a]
    omega

lemma fullReplacement_scaled_vertical (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : U.data.band => κ*U.fullReplacement i H) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have h := (U.fullReplacement_vertical i).dist_le_mul H T
  rw [Real.dist_eq] at h ⊢
  rw [← mul_sub,abs_mul,abs_of_nonneg U.kappa_nonneg]
  calc
    _ ≤ κ*((SecondaryCell.replacementConstant U.tree : ℝ)*dist H T) :=
      mul_le_mul_of_nonneg_left h U.kappa_nonneg
    _ = (κ*(SecondaryCell.replacementConstant U.tree : ℝ))*dist H T := by ring
    _ ≤ 1*dist H T := mul_le_mul_of_nonneg_right U.vertical_bound dist_nonneg
    _ = _ := by simp

end PlanarL1.Columns.Model.BState.SecondaryStep


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryBatch
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.BState
open MeasureTheory Set
open scoped NNReal
open PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- All kept groups with one old identifier and one common orientation. Their
closed domains may overlap in regions where several clippings act. -/
structure SecondaryBatch (S : BState M κ lam Ω μ) where
  index : Fin (S.count+1)
  positive : Bool
  lambda_bound : lam ≤ (1:ℝ≥0)/100
  count : ℕ
  band : Fin count → Set ℝ
  root : Fin count → Fin (k+1)
  step : ∀ q, SecondaryStep S (band q) (root q)
  same_index : ∀ q, (step q).index=index
  same_positive : ∀ q, (step q).positive=positive
  kappa_nonneg : 0 ≤ κ
  kappa_five : κ*5 ≤ 1

namespace SecondaryBatch
variable {S : BState M κ lam Ω μ} (B : SecondaryBatch S)

noncomputable def data : BData M := S.chart B.index
noncomputable def comparison : M.Field B.data.band 5 := B.data.comparison lam B.lambda_bound B.positive

lemma step_data (q : Fin B.count) : (B.step q).data=B.data := by
  simp only [SecondaryStep.data,data,B.same_index]

noncomputable def groupHeight (q : Fin B.count) (H : B.data.band) : (B.step q).data.band :=
  ⟨H.val,by rw [B.step_data]; exact H.property⟩

lemma step_comparison (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) :
    (B.step q).comparison.value i (B.groupHeight q H)=B.comparison.value i H := by
  have transport (D E : BData M) (he : D=E) (p r : Bool) (hp : p=r)
      (hl hl' : lam ≤ (1:ℝ≥0)/100) (T : E.band) :
      (D.comparison lam hl p).value i ⟨T.val,by rw [he]; exact T.property⟩ =
        (E.comparison lam hl' r).value i T := by
    subst E
    subst r
    rfl
  exact transport (B.step q).data B.data (B.step_data q)
    (B.step q).positive B.positive (B.same_positive q) (B.step q).lambda_bound B.lambda_bound H

noncomputable def groupNamed (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) : NamedValue :=
  ⟨((B.step q).fullNamed i (B.groupHeight q H)).name,
    κ*((B.step q).fullNamed i (B.groupHeight q H)).value⟩

noncomputable def selected (i : Fin (k+1)) : B.data.band → NamedValue :=
  familySelection (fun H => κ*B.comparison.value i H) (fun q => B.groupNamed q i)

lemma groupNamed_value (q : Fin B.count) (i : Fin (k+1)) (H : B.data.band) :
    (B.groupNamed q i H).value=κ*(B.step q).fullReplacement i (B.groupHeight q H) := by
  simp only [groupNamed,SecondaryStep.fullNamed_value]

lemma comparison_scaled (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : B.data.band => κ*B.comparison.value i H) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have h := (B.comparison.vertical i).dist_le_mul H T
  rw [Real.dist_eq] at h ⊢
  rw [← mul_sub,abs_mul,abs_of_nonneg B.kappa_nonneg]
  calc
    _ ≤ κ*(5*dist H T) := mul_le_mul_of_nonneg_left h B.kappa_nonneg
    _ = (κ*5)*dist H T := by ring
    _ ≤ 1*dist H T := mul_le_mul_of_nonneg_right B.kappa_five dist_nonneg
    _ = _ := by simp

lemma groupNamed_vertical (q : Fin B.count) (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : B.data.band => (B.groupNamed q i H).value) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  simp only [B.groupNamed_value]
  exact ((B.step q).fullReplacement_scaled_vertical i).dist_le_mul (B.groupHeight q H) (B.groupHeight q T)

lemma selected_vertical (i : Fin (k+1)) :
    LipschitzWith 1 (fun H : B.data.band => (B.selected i H).value) :=
  familySelection_lipschitz _ _ (B.comparison_scaled i) (fun q => B.groupNamed_vertical q i)

lemma groupNamed_switch (q : Fin B.count) (i j : Fin (k+1)) (H : B.data.band)
    (hs : H.val ∈ M.heights i j) : B.groupNamed q i H=B.groupNamed q j H := by
  unfold groupNamed
  rw [(B.step q).fullNamed_switch i j (B.groupHeight q H) hs]

lemma selected_switch (i j : Fin (k+1)) (H : B.data.band)
    (hs : H.val ∈ M.heights i j) : B.selected i H=B.selected j H := by
  have hm (old : B.data.band → NamedValue) (L : List (B.data.band → NamedValue)) :
      maxSelection old L H=(L.map (fun f => f H)).foldr maxNamed (old H) := by
    induction L with
    | nil => rfl
    | cons f L ih => simp only [maxSelection,List.map_cons,List.foldr_cons,ih]
  unfold selected familySelection
  rw [hm,hm]
  simp only [List.map_ofFn,Function.comp_def,B.comparison.switch i j H hs]
  congr 2
  funext q
  rw [B.groupNamed_switch q i j H hs]

noncomputable def domain (i : Fin (k+1)) : Set ℝ :=
  ⋃ q : Fin B.count, SecondaryCell.domain (B.step q).seeds (B.step q).radius i

lemma mem_domain {i : Fin (k+1)} {H : ℝ} : H ∈ B.domain i ↔
    ∃ q, H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i := mem_iUnion

lemma domain_closed (i : Fin (k+1)) : IsClosed (B.domain i) :=
  isClosed_iUnion_of_finite (fun q => (SecondaryCell.compact_domain (B.step q).seeds
    (B.step q).radius (B.step q).compact_band i).isClosed)

lemma domain_band {i : Fin (k+1)} {H : ℝ} (hd : H ∈ B.domain i) : H ∈ B.data.band := by
  obtain ⟨q,hq⟩ := B.mem_domain.mp hd
  rw [← B.step_data q]
  exact (B.step q).sub_old (SecondaryCell.inBand_of_mem _ _ hq)

lemma domain_name {i : Fin (k+1)} {H : ℝ} (hd : H ∈ B.domain i) : S.name i H=B.index := by
  obtain ⟨q,hq⟩ := B.mem_domain.mp hd
  exact ((B.step q).same_name i H hq).trans (B.same_index q)

lemma domain_switch {i j : Fin (k+1)} {H : ℝ} (hs : H ∈ M.heights i j)
    (hd : H ∈ B.domain i) : H ∈ B.domain j := by
  obtain ⟨q,hq⟩ := B.mem_domain.mp hd
  exact B.mem_domain.mpr ⟨q,SecondaryCell.switch_mem _ _ hs hq⟩

lemma group_frontier {i : Fin (k+1)} {H : ℝ} (hf : H ∈ frontier (B.domain i))
    (q : Fin B.count) (hq : H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i) :
    H ∈ frontier (SecondaryCell.domain (B.step q).seeds (B.step q).radius i) := by
  refine ⟨subset_closure hq,?_⟩
  intro ht
  exact hf.2 (interior_mono (subset_iUnion (fun q : Fin B.count =>
    SecondaryCell.domain (B.step q).seeds (B.step q).radius i) q) ht)

lemma selected_same {i : Fin (k+1)} (H : B.data.band)
    (h : ∀ q, (B.groupNamed q i H).value=κ*B.comparison.value i H) :
    (B.selected i H).value=κ*B.comparison.value i H := by
  rcases maxSelection_mem (fun H => ⟨0,κ*B.comparison.value i H⟩)
    (List.ofFn (fun q => fun H => ⟨familyName q (B.groupNamed q i H).name,(B.groupNamed q i H).value⟩)) H with ho | ⟨F,hF,hFv⟩
  · exact congrArg NamedValue.value ho
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hF
    exact (congrArg NamedValue.value hFv).trans (h q)

lemma selected_frontier {i : Fin (k+1)} {H : ℝ} (hf : H ∈ frontier (B.domain i)) :
    (B.selected i ⟨H,B.domain_band ((B.domain_closed i).frontier_subset hf)⟩).value=
      κ*B.comparison.value i ⟨H,B.domain_band ((B.domain_closed i).frontier_subset hf)⟩ := by
  apply B.selected_same
  intro q
  rw [B.groupNamed_value]
  by_cases hq : H ∈ SecondaryCell.domain (B.step q).seeds (B.step q).radius i
  · rw [(B.step q).fullReplacement_inside _ _ hq]
    change κ*(B.step q).replacement (SecondaryCell.point (B.step q).seeds (B.step q).radius i H hq)=_
    rw [(B.step q).replacement_frontier (B.group_frontier hf q hq) hq,(B.step q).point_old hq]
    congr 1
    exact B.step_comparison q i ⟨H,B.domain_band ((B.domain_closed i).frontier_subset hf)⟩
  · rw [(B.step q).fullReplacement_outside _ _ hq,B.step_comparison]

noncomputable def converted (i : Fin (k+1)) (H : ℝ) : ℝ :=
  if h : H ∈ B.data.band then κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,h⟩).value else 0

lemma converted_on (i : Fin (k+1)) (H : ℝ) (h : H ∈ B.data.band) :
    B.converted i H=κ*B.data.offset+B.data.orientation B.positive*(B.selected i ⟨H,h⟩).value := dite_eq_left h

lemma converted_vertical (i : Fin (k+1)) : LipschitzOnWith 1 (B.converted i) (B.domain i) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro H hH T hT
  rw [B.converted_on i H (B.domain_band hH),B.converted_on i T (B.domain_band hT)]
  have h := (B.selected_vertical i).dist_le_mul ⟨H,B.domain_band hH⟩ ⟨T,B.domain_band hT⟩
  rw [Real.dist_eq] at h ⊢
  simp only [add_sub_add_left_eq_sub,← mul_sub,abs_mul,B.data.orientation_unit,one_mul]
  exact h

noncomputable def patch : SetPatch S.lift.sets := by
  apply Threshold.chartPatch S.lift.sets (S.labels B.index).lift B.domain B.domain_closed
    B.converted B.converted_vertical
  · intro ω i H hf
    have hd := (B.domain_closed i).frontier_subset hf
    have hb := B.domain_band hd
    rw [B.converted_on i H hb,B.selected_frontier hf]
    have he := B.data.comparison_convert lam B.lambda_bound B.positive i ⟨H,hb⟩
    have hr := S.represents_named ω.1 i H B.index (B.domain_name hd) hb
    change Threshold.active (S.labels B.index) H _ ω.1 ↔ (S.sets.activity ω.1).active i H
    have hv : κ*B.data.offset+B.data.orientation B.positive*(κ*B.comparison.value i ⟨H,hb⟩)=
        κ*B.data.value lam i ⟨H,hb⟩ := by
      rw [he]
      change _=κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,hb⟩)
      ring
    rw [hv]
    exact hr.symm
  · intro i j H hs hi hj
    rw [B.converted_on i H (B.domain_band hi),B.converted_on j H (B.domain_band hj),B.selected_switch i j _ hs]
  · intro ω i j H hs hi hj
    exact (hj (B.domain_switch hs hi)).elim

lemma selected_cases (i : Fin (k+1)) (H : B.data.band) :
    B.selected i H=⟨0,κ*B.comparison.value i H⟩ ∨
      ∃ q, B.selected i H=⟨familyName q (B.groupNamed q i H).name,(B.groupNamed q i H).value⟩ := by
  rcases maxSelection_mem (fun H => ⟨0,κ*B.comparison.value i H⟩)
    (List.ofFn (fun q => fun H => ⟨familyName q (B.groupNamed q i H).name,(B.groupNamed q i H).value⟩)) H with ho | ⟨F,hF,hFv⟩
  · exact Or.inl ho
  · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hF
    exact Or.inr ⟨q,hFv⟩

lemma selected_zero (i : Fin (k+1)) (H : B.data.band) (hz : (B.selected i H).name=0) :
    (B.selected i H).value=κ*B.comparison.value i H := by
  rcases B.selected_cases i H with ho | ⟨q,hq⟩
  · exact congrArg NamedValue.value ho
  · have hn : (B.groupNamed q i H).name=0 := by
      by_contra hn
      exact familyName_ne_zero q hn ((congrArg NamedValue.name hq).symm.trans hz)
    have hv := (B.step q).fullNamed_zero i (B.groupHeight q H) hn
    have hm := congrArg NamedValue.value hq
    change (B.selected i H).value=κ*((B.step q).fullNamed i (B.groupHeight q H)).value at hm
    rw [hm,hv,B.step_comparison]

abbrev NewIndex := Σ q : Fin B.count, Fin (3*(k+1)*(B.step q).tree.depthCap+2)
noncomputable instance instFintypeNewIndex : Fintype B.NewIndex := inferInstanceAs (Fintype (Sigma _))

noncomputable def chosen (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) : Prop :=
  ∃ hb : H ∈ B.data.band, (B.step a.1).choose i H=some a.2 ∧
    B.selected i ⟨H,hb⟩=⟨familyName a.1 (a.2.val+1),(B.groupNamed a.1 i ⟨H,hb⟩).value⟩

noncomputable def choose (i : Fin (k+1)) (H : ℝ) : Option B.NewIndex :=
  if h : ∃ a, B.chosen i H a then some h.choose else none

lemma choose_some (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.choose i H=some a) : B.chosen i H a := by
  unfold choose at ha
  split_ifs at ha with h
  · have he : h.choose=a := Option.some.inj ha
    exact he ▸ h.choose_spec

lemma none_no_chosen (i : Fin (k+1)) (H : ℝ) (hn : B.choose i H=none) :
    ¬∃ a, B.chosen i H a := by
  intro h
  simp only [choose,dite_eq_left h] at hn
  cases hn

lemma exists_chosen (i : Fin (k+1)) (H : B.data.band) (hn : (B.selected i H).name ≠ 0) :
    ∃ a, B.chosen i H.val a := by
  rcases B.selected_cases i H with ho | ⟨q,hq⟩
  · exact (hn (congrArg NamedValue.name ho)).elim
  · have hqn : ((B.step q).fullNamed i (B.groupHeight q H)).name ≠ 0 := by
      intro hz
      have hn' := congrArg NamedValue.name hq
      change (B.selected i H).name=familyName q ((B.step q).fullNamed i (B.groupHeight q H)).name at hn'
      rw [hz,familyName_zero] at hn'
      exact hn hn'
    obtain ⟨a,ha,hname,hd⟩ := (B.step q).fullNamed_choice i (B.groupHeight q H) hqn
    refine ⟨(⟨q,a⟩ : B.NewIndex),H.property,ha,?_⟩
    change B.selected i H=⟨familyName q (a.val+1),(B.groupNamed q i H).value⟩
    rw [hq]
    change (NamedValue.mk (familyName q ((B.step q).fullNamed i (B.groupHeight q H)).name)
      (B.groupNamed q i H).value)=_
    rw [hname]

lemma chosen_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) (a : B.NewIndex) :
    B.chosen i H a ↔ B.chosen j H a := by
  unfold chosen
  apply exists_congr
  intro hb
  rw [(B.step a.1).choose_switch i j H hs,B.selected_switch i j ⟨H,hb⟩ hs,
    B.groupNamed_switch a.1 i j ⟨H,hb⟩ hs]

lemma choose_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) :
    B.choose i H=B.choose j H := by
  have he : B.chosen i H=B.chosen j H := funext fun a => propext (B.chosen_switch i j H hs a)
  unfold choose
  simp only [he]

noncomputable def newData (a : B.NewIndex) : BData M := (B.step a.1).newData a.2
noncomputable def newLabels [SFinite μ] (a : B.NewIndex) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) := (B.step a.1).newLabels a.2

lemma chosen_domain (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) (ha : B.chosen i H a) :
    H ∈ SecondaryCell.domain (B.step a.1).seeds (B.step a.1).radius i := by
  obtain ⟨hb,hc,he⟩ := ha
  obtain ⟨hd,-⟩ := SecondaryCell.choose_spec (B.step a.1).tree (B.step a.1).seeds
    (B.step a.1).old (B.step a.1).supportValue (B.step a.1).data.isOrdinary
    (B.step a.1).pc (B.step a.1).radius (B.step a.1).ordered_offset (B.step a.1).shield_offset
    (B.step a.1).lo (B.step a.1).noise i H a.2 hc
  exact hd

lemma converted_chosen (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) (ha : B.chosen i H a) :
    B.converted i H=κ*((B.step a.1).data.offset+(B.step a.1).data.orientation (B.step a.1).positive*
      (B.step a.1).replacement (SecondaryCell.point (B.step a.1).seeds (B.step a.1).radius i H
        (B.chosen_domain i H a ha))) := by
  obtain ⟨hb,hc,he⟩ := ha
  have hv : (B.selected i ⟨H,hb⟩).value=κ*(B.step a.1).replacement
      (SecondaryCell.point (B.step a.1).seeds (B.step a.1).radius i H
        (B.chosen_domain i H a ⟨hb,hc,he⟩)) := by
    calc
      _ = (B.groupNamed a.1 i ⟨H,hb⟩).value := by
        have h := congrArg NamedValue.value he
        exact h
      _ = κ*(B.step a.1).fullReplacement i (B.groupHeight a.1 ⟨H,hb⟩) :=
        B.groupNamed_value a.1 i ⟨H,hb⟩
      _ = _ := congrArg (κ*·) ((B.step a.1).fullReplacement_inside i
        (B.groupHeight a.1 ⟨H,hb⟩) (B.chosen_domain i H a ⟨hb,hc,he⟩))
  simp only [B.converted_on i H hb,hv]
  have hoff := congrArg BData.offset (B.step_data a.1)
  have hor : (B.step a.1).data.orientation (B.step a.1).positive=B.data.orientation B.positive := by
    rw [B.same_positive,B.step_data]
  rw [hoff,hor]
  change κ*B.data.offset+B.data.orientation B.positive*(κ*(B.step a.1).replacement _)=_
  ring

lemma chosen_agreement (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) :
    (B.patch.apply.activity ω).active i H ↔ ((B.step a.1).patch.apply.activity ω).active i H := by
  have hd := B.chosen_domain i H a ha
  apply (B.patch.inside (B.mem_domain.mpr ⟨a.1,hd⟩) ω).trans
  change Threshold.active (S.labels B.index).lift H (B.converted i H) ω ↔ _
  rw [B.converted_chosen i H a ha]
  have hp := (B.step a.1).patch_inside ω i H hd
  rw [B.same_index] at hp
  exact hp.symm

lemma chosen_description [SFinite μ] (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) :
    (H ∈ (B.newData a).band ∧ (B.newData a).Uses i) ∧
      ∀ (ω : Ω × Bool) (hi : H ∈ (B.newData a).band),
        (B.patch.apply.activity ω).active i H ↔
          Threshold.active (B.newLabels a) H (κ*(B.newData a).value lam i ⟨H,hi⟩) ω := by
  obtain ⟨hb,hc,he⟩ := ha
  have h := (B.step a.1).chosen_description i H a.2 hc
  refine ⟨h.1,fun ω hi => ?_⟩
  exact (B.chosen_agreement ω i H a ⟨hb,hc,he⟩).trans (h.2 ω hi)

lemma unchosen (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (hn : B.choose i H=none) :
    (B.patch.apply.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  by_cases hd : H ∈ B.domain i
  · have hb := B.domain_band hd
    have hz : (B.selected i ⟨H,hb⟩).name=0 := by
      by_contra hz
      exact B.none_no_chosen i H hn (B.exists_chosen i ⟨H,hb⟩ hz)
    apply (B.patch.inside hd ω).trans
    change Threshold.active (S.labels B.index).lift H (B.converted i H) ω ↔ _
    rw [B.converted_on i H hb,B.selected_zero i ⟨H,hb⟩ hz]
    have he := B.data.comparison_convert lam B.lambda_bound B.positive i ⟨H,hb⟩
    have hr := S.represents_named ω.1 i H B.index (B.domain_name hd) hb
    change Threshold.active (S.labels B.index) H _ ω.1 ↔ (S.sets.activity ω.1).active i H
    have hv : κ*B.data.offset+B.data.orientation B.positive*(κ*B.comparison.value i ⟨H,hb⟩)=
        κ*B.data.value lam i ⟨H,hb⟩ := by
      rw [he]
      change _=κ*(B.data.offset+B.data.orientation B.positive*B.comparison.value i ⟨H,hb⟩)
      ring
    rw [hv]
    exact hr.symm
  · exact B.patch.unchanged hd ω

end SecondaryBatch
end PlanarL1.Columns.Model.BState


end

section

namespace PlanarL1.Columns.Model.BState
open MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The simultaneous secondary update, grouped by its actual old identifier.
Within an identifier we take a maximum, not disjoint patching. Distinct old
identifiers have disjoint domains because the old chart name is a function. -/
structure SecondaryLayer (S : BState M κ lam Ω μ) where
  batch : Fin (S.count+1) → SecondaryBatch S
  same_index : ∀ q, (batch q).index=q

namespace SecondaryLayer
variable {S : BState M κ lam Ω μ} (B : SecondaryLayer S)

lemma overlap : (List.ofFn (fun q => (B.batch q).patch)).Pairwise SetPatch.UnchangedOverlap := by
  apply List.pairwise_ofFn.mpr
  intro q r hqr ω i H hq hr
  have hq' := (B.batch q).domain_name hq
  have hr' := (B.batch r).domain_name hr
  rw [B.same_index] at hq' hr'
  exact ((ne_of_lt hqr) (hq'.symm.trans hr')).elim

abbrev NewIndex := Σ q : Fin (S.count+1), (B.batch q).NewIndex
noncomputable instance instFintypeNewIndex : Fintype B.NewIndex := inferInstanceAs (Fintype (Sigma _))

noncomputable def newData (a : B.NewIndex) : BData M := (B.batch a.1).newData a.2
noncomputable def newLabels [SFinite μ] (a : B.NewIndex) :
    Threshold.Variables (Ω × Bool) (μ.prod Threshold.fair) := (B.batch a.1).newLabels a.2

noncomputable def chosen (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex) : Prop :=
  (B.batch a.1).choose i H=some a.2

noncomputable def choose (i : Fin (k+1)) (H : ℝ) : Option B.NewIndex :=
  if h : ∃ a, B.chosen i H a then some h.choose else none

lemma choose_some (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.choose i H=some a) : B.chosen i H a := by
  unfold choose at ha
  split_ifs at ha with h
  · have he : h.choose=a := Option.some.inj ha
    exact he ▸ h.choose_spec

lemma choose_none (i : Fin (k+1)) (H : ℝ) (ha : B.choose i H=none) (q : Fin (S.count+1)) :
    (B.batch q).choose i H=none := by
  cases he : (B.batch q).choose i H with
  | none => rfl
  | some a =>
    have hex : ∃ a, B.chosen i H a := ⟨⟨q,a⟩,he⟩
    simp [choose,hex] at ha

lemma choose_switch (i j : Fin (k+1)) (H : ℝ) (hs : H ∈ M.heights i j) :
    B.choose i H=B.choose j H := by
  have he : B.chosen i H=B.chosen j H := by
    funext a
    simp only [chosen,(B.batch a.1).choose_switch i j H hs]
  unfold choose
  simp only [he]

noncomputable def sets : SetSystem M (Ω × Bool) (μ.prod Threshold.fair) :=
  SetPatch.batch (List.ofFn (fun q => (B.batch q).patch)) B.overlap

lemma chosen_description [SFinite μ] (i : Fin (k+1)) (H : ℝ) (a : B.NewIndex)
    (ha : B.chosen i H a) :
    (H ∈ (B.newData a).band ∧ (B.newData a).Uses i) ∧
    ∀ (ω : Ω × Bool) (hi : H ∈ (B.newData a).band),
      (B.sets.activity ω).active i H ↔
        Threshold.active (B.newLabels a) H (κ*(B.newData a).value lam i ⟨H,hi⟩) ω := by
  have ha' := (B.batch a.1).choose_some i H a.2 ha
  have hd := (B.batch a.1).chosen_domain i H a.2 ha'
  have h := (B.batch a.1).chosen_description i H a.2 ha'
  refine ⟨h.1,fun ω hi => ?_⟩
  apply (SetPatch.batch_inside _ B.overlap (List.mem_ofFn.mpr ⟨a.1,rfl⟩) ω i H
    ((B.batch a.1).mem_domain.mpr ⟨a.2.1,hd⟩)).trans
  exact h.2 ω hi

lemma unchosen (ω : Ω × Bool) (i : Fin (k+1)) (H : ℝ) (ha : B.choose i H=none) :
    (B.sets.activity ω).active i H ↔ (S.lift.sets.activity ω).active i H := by
  apply SetPatch.batch_old _ B.overlap ω i H
  intro P hP
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hP
  exact (B.batch q).unchosen ω i H (B.choose_none i H ha q)

/-- The actual simultaneous layer and selected ordinary/ordered chart table. -/
noncomputable def apply [SFinite μ] : BState M κ lam (Ω × Bool) (μ.prod Threshold.fair) := by
  let e := Fintype.equivFin B.NewIndex
  let pick : Fin (k+1) → ℝ → Option (Fin (Fintype.card B.NewIndex)) :=
    fun i H => (B.choose i H).map e
  have hpick (i H a) (ha : pick i H=some a) : B.chosen i H (e.symm a) := by
    obtain ⟨b,hb,hba⟩ := Option.map_eq_some_iff.mp ha
    have he : b=e.symm a := by rw [← hba]; simp
    exact he ▸ B.choose_some i H b hb
  exact S.lift.append B.sets (Fintype.card B.NewIndex)
    (B.newData ∘ e.symm) (B.newLabels ∘ e.symm) pick
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.1)
    (fun i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).1.2)
    (fun i j H hs => congrArg (Option.map e) (B.choose_switch i j H hs))
    (fun ω i H ha => B.unchosen ω i H (Option.map_eq_none_iff.mp ha))
    (fun ω i H a ha => (B.chosen_description i H (e.symm a) (hpick i H a ha)).2 ω _)

end SecondaryLayer
end PlanarL1.Columns.Model.BState



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Dilation
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n) (c : ℝ) (hc : 0 < c)

/-- Change physical units by a positive factor. This scales the actual switch
sets and vertical path lengths; the cyclic link graph is not changed. -/
noncomputable def dilate : Model n where
  link := M.link
  heights i j := (fun H => c*H) '' M.heights i j
  symm i j := by rw [M.symm i j]
  permitted i j H h := by
    obtain ⟨T,hT,rfl⟩ := h
    exact M.permitted i j T hT
  compact i j := (M.compact i j).image (continuous_const.mul continuous_id)
  noncrossing := M.noncrossing
  terminal i j ha hn := by
    obtain ⟨H,hH,hT⟩ := M.terminal i j ha hn
    refine ⟨c*H,by simp only [hH,image_singleton],?_⟩
    intro k T ht
    rcases ht with ⟨U,hU,rfl⟩ | ⟨U,hU,rfl⟩
    · exact mul_le_mul_of_nonneg_left (hT k U (Or.inl hU)) hc.le
    · exact mul_le_mul_of_nonneg_left (hT k U (Or.inr hU)) hc.le

include hc in
lemma mem_dilate_set {J : Set ℝ} {H : ℝ} :
    H ∈ (fun T => c*T) '' J ↔ H/c ∈ J := by
  constructor
  · rintro ⟨T,hT,rfl⟩
    simpa [hc.ne'] using hT
  · intro h
    exact ⟨H/c,h,mul_div_cancel₀ H hc.ne'⟩

lemma dilate_mem_heights {i j : Fin n} {H : ℝ} :
    H ∈ (M.dilate c hc).heights i j ↔ H/c ∈ M.heights i j :=
  mem_dilate_set c hc

lemma dilate_activeGraph (J : Set ℝ) :
    (M.dilate c hc).activeGraph ((fun T => c*T) '' J)=M.activeGraph J := by
  ext i j
  simp only [activeGraph,mem_dilate_set c hc,dilate_mem_heights]
  constructor
  · rintro ⟨H,hH,hs⟩
    exact ⟨H/c,hH,hs⟩
  · rintro ⟨H,hH,hs⟩
    exact ⟨c*H,by simpa [hc.ne'] using hH,by simpa [hc.ne'] using hs⟩

namespace Path
variable {M c} {J : Set ℝ} {i j : Fin n}

noncomputable def dilate : {i j : Fin n} → M.Path J i j →
    (M.dilate c hc).Path ((fun T => c*T) '' J) i j
  | _,_,.nil i => .nil i
  | _,_,.cons H hH hs p => .cons (c*H) ⟨H,hH,rfl⟩ ⟨H,hs,rfl⟩ (dilate p)

lemma dilate_length (p : M.Path J i j) (a b : ℝ) :
    (p.dilate hc).length (c*a) (c*b)=c*p.length a b := by
  induction p generalizing a with
  | nil => simp only [dilate,length,← mul_sub,abs_mul,abs_of_pos hc]
  | cons H hH hs p ih =>
    simp only [dilate,length,ih,← mul_sub,abs_mul,abs_of_pos hc,mul_add]

noncomputable def undilate : {i j : Fin n} →
    (M.dilate c hc).Path ((fun T => c*T) '' J) i j → M.Path J i j
  | _,_,.nil i => .nil i
  | _,_,.cons H hH hs p => .cons (H/c) ((mem_dilate_set c hc).mp hH)
      ((M.dilate_mem_heights c hc).mp hs) (undilate p)

lemma undilate_length (p : (M.dilate c hc).Path ((fun T => c*T) '' J) i j) (a b : ℝ) :
    c*(p.undilate hc).length (a/c) (b/c)=p.length a b := by
  induction p generalizing a with
  | nil =>
    simp only [undilate,length,← sub_div,abs_div,abs_of_pos hc]
    exact mul_div_cancel₀ _ hc.ne'
  | cons H hH hs p ih =>
    simp only [undilate,length,mul_add,ih,← sub_div,abs_div,abs_of_pos hc,
      mul_div_cancel₀ _ hc.ne']
end Path

namespace Point
variable {M c} {J : Set ℝ} {root : Fin n}

noncomputable def dilate (x : M.Point J root) :
    (M.dilate c hc).Point ((fun T => c*T) '' J) root where
  column := x.column
  height := c*x.height
  inBand := ⟨x.height,x.inBand,rfl⟩
  reachable := by rw [M.dilate_activeGraph]; exact x.reachable

lemma dilate_distance (x y : M.Point J root) :
    (x.dilate hc).distance (y.dilate hc)=c*x.distance y := by
  apply le_antisymm
  · rw [mul_comm c]
    apply (div_le_iff₀ hc).mp
    have := x.paths_nonempty y
    apply le_ciInf
    intro p
    have h := (x.dilate hc).distance_le (y.dilate hc) (p.dilate hc)
    change (x.dilate hc).distance (y.dilate hc) ≤
      (p.dilate hc).length (c*x.height) (c*y.height) at h
    rw [Path.dilate_length hc] at h
    exact (div_le_iff₀ hc).mpr (by nlinarith only [h])
  · have := (x.dilate hc).paths_nonempty (y.dilate hc)
    apply le_ciInf
    intro p
    have h := mul_le_mul_of_nonneg_left (x.distance_le y (p.undilate hc)) hc.le
    have he := p.undilate_length hc (c*x.height) (c*y.height)
    simp only [mul_div_cancel_left₀ _ hc.ne'] at he
    exact h.trans_eq he

lemma dilate_dist (x y : M.Point J root) :
    dist (x.dilate hc) (y.dilate hc)=c*dist x y := x.dilate_distance hc y

end Point

include hc in
lemma dilate_set_closed {J : Set ℝ} (hJ : IsClosed J) :
    IsClosed ((fun T => c*T) '' J) := by
  have he : (fun T => c*T) '' J = (fun T => T/c) ⁻¹' J := by
    ext H
    exact mem_dilate_set c hc
  rw [he]
  exact hJ.preimage (continuous_id.div_const c)

include hc in
lemma dilate_set_convex {J : Set ℝ} (hJ : J.OrdConnected) :
    ((fun T => c*T) '' J).OrdConnected := by
  have he : (fun T => c*T) '' J = (fun T => T/c) ⁻¹' J := by
    ext H
    exact mem_dilate_set c hc
  rw [he]
  exact hJ.preimage_mono (fun _ _ h => div_le_div_of_nonneg_right h hc.le)

namespace Field
variable {M c} {J : Set ℝ} {L : ℝ≥0}

/-- Field values have length units too. The vertical Lipschitz constant does
not change on passing to new physical units. -/
noncomputable def dilate (F : M.Field J L) :
    (M.dilate c hc).Field ((fun T => c*T) '' J) L where
  value i H := c*F.value i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩
  vertical i := by
    apply LipschitzWith.of_dist_le_mul
    intro H T
    have h := (F.vertical i).dist_le_mul
      ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩
      ⟨T.val/c,(mem_dilate_set c hc).mp T.property⟩
    simp only [Real.dist_eq,Subtype.dist_eq] at h ⊢
    rw [← mul_sub,abs_mul,abs_of_pos hc]
    apply (mul_le_mul_of_nonneg_left h hc.le).trans_eq
    rw [← sub_div,abs_div,abs_of_pos hc]
    field_simp
  switch i j H hs := by
    rw [F.switch i j ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩
      ((M.dilate_mem_heights c hc).mp hs)]

lemma dilate_orderedFrom {k : ℕ} {M : Model (k+1)} {J : Set ℝ} {L : ℝ≥0}
    (F : M.Field J L) {a b : Fin (k+1)} (ho : F.OrderedFrom a b) :
    (F.dilate hc).OrderedFrom a b := by
  refine ⟨?_,?_,?_⟩
  · intro H i
    exact mul_le_mul_of_nonneg_left (ho.1 ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ i) hc.le
  · intro H i j hij hjb
    exact mul_le_mul_of_nonneg_left (ho.2.1 ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ i j hij hjb) hc.le
  · intro H i j hbi hij
    exact mul_le_mul_of_nonneg_left (ho.2.2 ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ i j hbi hij) hc.le
end Field

namespace Point
variable {M c} {J : Set ℝ} {root : Fin n}
lemma dilate_radialValue (o : M.Point J root) (i : Fin n)
    (H : (fun T => c*T) '' J) :
    (o.dilate hc).radialValue i H =
      c*o.radialValue i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hi' : ((M.dilate c hc).activeGraph ((fun T => c*T) '' J)).Reachable root i := by
      rwa [M.dilate_activeGraph]
    simp only [radialValue,dite_eq_left hi,dite_eq_left hi']
    let x : M.Point J root := ⟨i,H.val/c,(mem_dilate_set c hc).mp H.property,hi⟩
    have hx : (x.dilate hc)=(⟨i,H.val,H.property,hi'⟩ :
        (M.dilate c hc).Point ((fun T => c*T) '' J) root) := by
      simp only [x,dilate,mul_div_cancel₀ _ hc.ne']
    rw [← hx]
    exact o.dilate_dist hc x
  · have hi' : ¬((M.dilate c hc).activeGraph ((fun T => c*T) '' J)).Reachable root i := by
      rwa [M.dilate_activeGraph]
    simp only [radialValue,dite_eq_right hi,dite_eq_right hi',mul_zero]
end Point

namespace OrdinaryData
variable {M c}
noncomputable def dilate (D : OrdinaryData M) : OrdinaryData (M.dilate c hc) where
  band := (fun T => c*T) '' D.band
  closed := dilate_set_closed c hc D.closed
  convex := dilate_set_convex c hc D.convex
  origin := D.origin.map (fun o => ⟨o.1,o.2.dilate hc⟩)
  constant := c*D.constant
  orientation := D.orientation
  unit_orientation := D.unit_orientation

lemma dilate_comparison (D : OrdinaryData M) (i : Fin n) (H : (D.dilate hc).band) :
    (D.dilate hc).comparison.value i H =
      c*D.comparison.value i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  cases he : D.origin with
  | none => simp only [comparison,dilate,he,Option.map_none,Field.constant,mul_zero]
  | some o =>
    simp only [comparison,dilate,he,Option.map_some,Point.radialField]
    exact o.2.dilate_radialValue hc i H

lemma dilate_value (D : OrdinaryData M) (i : Fin n) (H : (D.dilate hc).band) :
    (D.dilate hc).value i H =
      c*D.value i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  simp only [value,dilate_comparison]
  change c*D.constant+D.orientation*(c*D.comparison.value i _) = _
  ring
end OrdinaryData

namespace OrderedData
variable {k : ℕ} {M : Model (k+1)} {c}
noncomputable def dilate (D : OrderedData M) : OrderedData (M.dilate c hc) where
  band := (fun T => c*T) '' D.band
  closed := dilate_set_closed c hc D.closed
  convex := dilate_set_convex c hc D.convex
  base := D.base.dilate hc
  lower := D.lower
  upper := D.upper
  ordered := D.base.dilate_orderedFrom hc D.ordered
  auxiliary := D.auxiliary.dilate hc

lemma dilate_value (D : OrderedData M) (lam : ℝ≥0) (i : Fin (k+1)) (H : (D.dilate hc).band) :
    (D.dilate hc).value lam i H =
      c*D.value lam i ⟨H.val/c,(mem_dilate_set c hc).mp H.property⟩ := by
  simp only [value,dilate,Field.dilate]
  ring
end OrderedData

namespace BData
variable {k : ℕ} {M : Model (k+1)} {c}
noncomputable def dilate : BData M → BData (M.dilate c hc)
  | .ordinary D => .ordinary (D.dilate hc)
  | .ordered D => .ordered (D.dilate hc)

lemma dilate_band (D : BData M) : (D.dilate hc).band=(fun T => c*T) '' D.band := by
  cases D <;> rfl

lemma dilate_value (D : BData M) (lam : ℝ≥0) (i : Fin (k+1)) (H : (D.dilate hc).band) :
    (D.dilate hc).value lam i H =
      c*D.value lam i ⟨H.val/c,(mem_dilate_set c hc).mp (D.dilate_band hc ▸ H.property)⟩ := by
  cases D with
  | ordinary D => exact D.dilate_value hc i H
  | ordered D => exact D.dilate_value hc lam i H
end BData
end PlanarL1.Columns.Model


namespace PlanarL1.Threshold
open MeasureTheory
open scoped ENNReal NNReal
variable (c : ℝ) (hc : 0 < c)

include hc in
lemma dilation_preserving :
    MeasurePreserving (fun z : Bool × ℝ => (z.1,c*z.2))
      (ENNReal.ofReal c • labelMeasure) labelMeasure := by
  have hreal : MeasurePreserving (fun H : ℝ => c*H)
      (ENNReal.ofReal c • volume) volume := by
    refine ⟨measurable_const.mul measurable_id,?_⟩
    rw [Measure.map_smul (ENNReal.ofReal c) volume (fun H : ℝ => c*H)]
    simpa only [abs_of_pos hc] using Real.smul_map_volume_mul_left hc.ne'
  have hp := (MeasurePreserving.id fair).prod hreal
  have hf : Prod.map (id : Bool → Bool) (fun H : ℝ => c*H) =
      (fun z : Bool × ℝ => (z.1,c*z.2)) := by
    funext z
    cases z
    rfl
  simpa only [Measure.prod_smul_right,← labelMeasure_eq,hf] using hp

namespace Variables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {c}

noncomputable def dilate (Z : Variables Ω μ) :
    Variables Ω (ENNReal.ofReal c • μ) where
  value ω := ((Z.value ω).1,c*(Z.value ω).2)
  preserving := by
    apply (dilation_preserving c hc).comp
    refine ⟨Z.preserving.measurable,?_⟩
    rw [Measure.map_smul,Z.preserving.map_eq]

lemma dilate_active (Z : Variables Ω μ) (H P : ℝ) (ω : Ω) :
    active (Z.dilate hc) H (c*P) ω ↔ active Z (H/c) P ω := by
  change c*(Z.value ω).2 < (if (Z.value ω).1 then H+c*P else H-c*P) ↔ _
  have hH : H=c*(H/c) := (mul_div_cancel₀ H hc.ne').symm
  rw [hH]
  unfold active
  cases hb : (Z.value ω).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [← mul_sub,mul_lt_mul_iff_right₀ hc,mul_div_cancel_left₀ _ hc.ne']
  · rw [← mul_add,mul_lt_mul_iff_right₀ hc,mul_div_cancel_left₀ _ hc.ne']
end Variables
end PlanarL1.Threshold

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped ENNReal NNReal
variable {n : ℕ} {M : Model n} {c : ℝ} (hc : 0 < c)

namespace Activity
noncomputable def dilate (A : Activity M) : Activity (M.dilate c hc) where
  active i H := A.active i (H/c)
  increasing i s t hst := A.increasing i (s/c) (t/c) (div_le_div_of_nonneg_right hst hc.le)
  switch i j H hH := A.switch i j (H/c) ((M.dilate_mem_heights c hc).mp hH)

lemma dilate_indicator (A : Activity M) (i : Fin n) (H : ℝ) :
    (A.dilate hc).indicator i H=A.indicator i (H/c) := rfl

end Activity

namespace SetSystem
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Change a cut system's physical units by the same factor as its columns.
The measure, height-coordinate variables, and every scalar chart are all scaled;
there is no implicit normalization of label mass. -/
noncomputable def dilate (A : SetSystem M Ω μ) :
    SetSystem (M.dilate c hc) Ω (ENNReal.ofReal c • μ) where
  activity ω := (A.activity ω).dilate hc
  measurable_active i H := A.measurable_active i (H/c)
  vertical_integrable i H T := (A.vertical_integrable i (H/c) (T/c)).smul_measure
    ENNReal.ofReal_ne_top
  vertical_bound i H T := by
    simp only [Activity.dilate_indicator,integral_smul_measure,smul_eq_mul,
      ENNReal.toReal_ofReal hc.le]
    calc
      _ ≤ c*|(H/c)-(T/c)| := mul_le_mul_of_nonneg_left (A.vertical_bound i (H/c) (T/c)) hc.le
      _ = |H-T| := by rw [← sub_div,abs_div,abs_of_pos hc,mul_div_cancel₀ _ hc.ne']

end SetSystem
end PlanarL1.Columns.Model


namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped ENNReal NNReal
variable {n : ℕ} {M : Model n} {c : ℝ} (hc : 0 < c)

namespace OrdinaryData
lemma dilate_origin_reachable (D : OrdinaryData M) (i : Fin n)
    (h : ∀ r o, D.origin=some ⟨r,o⟩ → (M.activeGraph D.band).Reachable r i) :
    ∀ r o, (D.dilate hc).origin=some ⟨r,o⟩ →
      ((M.dilate c hc).activeGraph (D.dilate hc).band).Reachable r i := by
  intro r o ho
  obtain ⟨⟨s,p⟩,hp,he⟩ := Option.map_eq_some_iff.mp ho
  have hs : s=r := congrArg Sigma.fst he
  change ((M.dilate c hc).activeGraph ((fun T => c*T) '' D.band)).Reachable r i
  rw [M.dilate_activeGraph,← hs]
  exact h s p hp
end OrdinaryData

namespace BData
variable {k : ℕ} {M : Model (k+1)}
lemma dilate_uses (D : BData M) (i : Fin (k+1)) (h : D.Uses i) :
    (D.dilate hc).Uses i := by
  cases D with
  | ordinary D => exact D.dilate_origin_reachable hc i h
  | ordered D => trivial
end BData

namespace OrdinaryState
variable {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def dilate (S : OrdinaryState M κ Ω μ) :
    OrdinaryState (M.dilate c hc) κ Ω (ENNReal.ofReal c • μ) where
  sets := S.sets.dilate hc
  count := S.count
  chart q := (S.chart q).dilate hc
  labels q := (S.labels q).dilate hc
  name i H := S.name i (H/c)
  height_in i H := (mem_dilate_set c hc).mpr (S.height_in i (H/c))
  component_in i H := (S.chart (S.name i (H/c))).dilate_origin_reachable hc i
    (S.component_in i (H/c))
  switch_name i j H hH := S.switch_name i j (H/c) ((M.dilate_mem_heights c hc).mp hH)
  represents ω i H := by
    change (S.sets.activity ω).active i (H/c) ↔
      Threshold.active ((S.labels (S.name i (H/c))).dilate hc) H
        (κ*((S.chart (S.name i (H/c))).dilate hc).value i _) ω
    rw [OrdinaryData.dilate_value hc]
    rw [show κ*(c*(S.chart (S.name i (H/c))).value i _) =
        c*(κ*(S.chart (S.name i (H/c))).value i _) by ring]
    rw [Threshold.Variables.dilate_active hc]
    exact S.represents ω i (H/c)
end OrdinaryState

namespace BState
variable {k : ℕ} {M : Model (k+1)}
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def dilate (S : BState M κ lam Ω μ) :
    BState (M.dilate c hc) κ lam Ω (ENNReal.ofReal c • μ) where
  sets := S.sets.dilate hc
  count := S.count
  chart q := (S.chart q).dilate hc
  labels q := (S.labels q).dilate hc
  name i H := S.name i (H/c)
  height_in i H := by
    rw [BData.dilate_band]
    exact (mem_dilate_set c hc).mpr (S.height_in i (H/c))
  component_in i H := (S.chart (S.name i (H/c))).dilate_uses hc i (S.component_in i (H/c))
  switch_name i j H hH := S.switch_name i j (H/c) ((M.dilate_mem_heights c hc).mp hH)
  represents ω i H := by
    change (S.sets.activity ω).active i (H/c) ↔
      Threshold.active ((S.labels (S.name i (H/c))).dilate hc) H
        (κ*((S.chart (S.name i (H/c))).dilate hc).value lam i _) ω
    rw [BData.dilate_value hc]
    rw [show κ*(c*(S.chart (S.name i (H/c))).value lam i _) =
        c*(κ*(S.chart (S.name i (H/c))).value lam i _) by ring]
    rw [Threshold.Variables.dilate_active hc]
    exact S.represents ω i (H/c)
end BState
end PlanarL1.Columns.Model



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace BData
/-- A proved ordered support at the actual representative of a group.
The support is needed only in an ordinary chart; ordered charts use their
literal sphere admission test instead. -/
lemma support_at (D : BData M) (lam : ℝ≥0) (hlam : lam≤(1:ℝ≥0)/100)
    (positive : Bool) (i : Fin (k+1)) (H : ℝ) (hi : H ∈ D.band) (hu : D.Uses i) :
    ∃ (F : M.Field D.band 1) (a b : Fin (k+1)), F.OrderedFrom a b ∧
      (D.isOrdinary=true → F.value i ⟨H,hi⟩=(D.comparison lam hlam positive).value i ⟨H,hi⟩) ∧
      ∀ (j : Fin (k+1)) (T : D.band), D.isOrdinary=true → D.Uses j →
        F.value j T≤(D.comparison lam hlam positive).value j T := by
  cases D with
  | ordinary C =>
    obtain ⟨F,a,b,ho,he,hF⟩ := C.support_at i H ⟨hi,hu⟩
    refine ⟨F,a,b,ho,fun _ => he,?_⟩
    intro j T _ hj
    exact hF j T.val ⟨T.property,hj⟩
  | ordered C =>
    exact ⟨Field.constant M C.band 0,0,0,Field.constant_ordered 0 0 0,
      by simp [isOrdinary],by simp [isOrdinary]⟩

lemma uses_reachable (D : BData M) {i j : Fin (k+1)} (hi : D.Uses i)
    (hr : (M.activeGraph D.band).Reachable i j) : D.Uses j := by
  cases D with
  | ordered _ => trivial
  | ordinary C => exact fun r o ho => (hi r o ho).trans hr
end BData

namespace SecondaryGeometry
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ)

/-- The geometric information attached to one actual surviving g-cell group.
The seed collection is finite, lies in one broad component and one narrow
height band, and keeps its TWO chart identifiers through the surviving-pair
selection. The B half needed for its literal update is recorded here. -/
structure Group where
  index : Fin (S.count+1)
  broad : Set ℝ
  broad_root : Fin (k+1)
  broad_closed : IsClosed broad
  lower : ℝ
  narrow_sub : BandTrees.band narrow lower ⊆ broad
  sub_old : broad ⊆ (S.chart index).band
  seeds : Finset (M.Point broad broad_root)
  nonempty : seeds.Nonempty
  height : ∀ w ∈ seeds, w.height ∈ BandTrees.band narrow lower
  diameter : ∀ w ∈ seeds, ∀ v ∈ seeds, dist w v≤10*g
  common : ∀ w ∈ seeds, A.Common S.name (A.point w.column w.height) 5 index

namespace Group
variable {A S} (G : Group A S)
noncomputable def representative : M.Point G.broad G.broad_root := G.nonempty.choose
lemma representative_mem : G.representative ∈ G.seeds := G.nonempty.choose_spec
noncomputable abbrev data : BData M := S.chart G.index
noncomputable def lam : ℝ≥0 := ⟨lambda,by norm_num [lambda,R]⟩
lemma lam_bound : lam≤(1:ℝ≥0)/100 := by
  change lambda≤(1:ℝ)/100
  norm_num [lambda,R]
noncomputable def comparison (positive : Bool) : M.Field G.data.band 5 :=
  G.data.comparison lam lam_bound positive
noncomputable def value (positive : Bool) (x : M.Point G.broad G.broad_root) : ℝ :=
  (G.comparison positive).value x.column ⟨x.height,G.sub_old x.inBand⟩
noncomputable def pc (positive : Bool) : ℝ := G.value positive G.representative

lemma representative_uses : G.data.Uses G.representative.column := by
  apply S.uses_named _ G.representative.height G.index
  exact (G.common G.representative G.representative_mem).center A (by norm_num)

lemma value_lipschitz (positive : Bool) : LipschitzWith 5 (G.value positive) :=
  ((G.comparison positive).restrict G.sub_old).lipschitz G.broad_closed G.broad_root

lemma value_near (positive : Bool) (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) :
    |G.value positive w-G.pc positive|≤50*g := by
  have h := (G.value_lipschitz positive).dist_le_mul w G.representative
  rw [Real.dist_eq] at h
  have hd := G.diameter w hw G.representative G.representative_mem
  change |G.value positive w-G.pc positive|≤5*dist w G.representative at h
  linarith

abbrev Component := BandTrees.Component M narrow G.lower
noncomputable abbrev root (C : G.Component) := BandTrees.root M narrow G.lower C
noncomputable abbrev tree (C : G.Component) := BandTrees.tree M narrow G.lower C

noncomputable def inComponent (C : G.Component) : Finset (M.Point G.broad G.broad_root) :=
  G.seeds.filter (fun w => w.column ∈ C.supp)

noncomputable def narrowPoint (C : G.Component) (w : G.inComponent C) :
    M.Point (BandTrees.band narrow G.lower) (G.root C) :=
  ⟨w.val.column,w.val.height,G.height w.val (Finset.mem_filter.mp w.property).1,
    C.reachable_of_mem_supp (BandTrees.root_mem M narrow G.lower C) (Finset.mem_filter.mp w.property).2⟩

noncomputable def allSeeds (C : G.Component) : Finset (M.Point (BandTrees.band narrow G.lower) (G.root C)) :=
  (G.inComponent C).attach.image (G.narrowPoint C)

lemma allSeeds_description (C : G.Component) (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) :
    x ∈ G.allSeeds C ↔ ∃ w ∈ G.seeds, w.column=x.column ∧ w.height=x.height := by
  constructor
  · intro hx
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨w.val,(Finset.mem_filter.mp w.property).1,rfl,rfl⟩
  · rintro ⟨w,hw,hc,hH⟩
    have hcol : w.column ∈ C.supp := hc ▸ BandTrees.reachable_mem M narrow G.lower C x.reachable
    let w' : G.inComponent C := ⟨w,Finset.mem_filter.mpr ⟨hw,hcol⟩⟩
    refine Finset.mem_image.mpr ⟨w',Finset.mem_attach _ _,?_⟩
    obtain ⟨xc,xh,xi,xr⟩ := x
    dsimp only at hc hH
    cases hc
    cases hH
    rfl

noncomputable def old (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) : ℝ :=
  (G.comparison positive).value x.column ⟨x.height,G.sub_old (G.narrow_sub x.inBand)⟩

/-- Literal admission; every ordinary seed is kept, and in an ordered chart
this tests all points on the intrinsic narrow-band sphere. -/
def Admitted (positive : Bool) (C : G.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C)) : Prop :=
  G.data.isOrdinary=true ∨ ∀ x : M.Point (BandTrees.band narrow G.lower) (G.root C),
    dist w x=R → G.pc positive-(65/100:ℝ)*R≤G.old positive C x

noncomputable def admittedSeeds (positive : Bool) (C : G.Component) :=
  (G.allSeeds C).filter (G.Admitted positive C)

lemma admitted_sphere (positive : Bool) (C : G.Component) (hord : G.data.isOrdinary=false)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C)) (hw : w ∈ G.admittedSeeds positive C) :
    ∀ x : M.Point (BandTrees.band narrow G.lower) (G.root C),
      dist w x=R → G.pc positive-(65/100:ℝ)*R≤G.old positive C x := by
  obtain ⟨_,ha⟩ := Finset.mem_filter.mp hw
  exact ha.resolve_left (by simp [hord])

end Group
end SecondaryGeometry
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

structure Support (positive : Bool) where
  field : M.Field G.data.band 1
  lower : Fin (k+1)
  upper : Fin (k+1)
  ordered : field.OrderedFrom lower upper
  at_center : G.data.isOrdinary=true →
    field.value G.representative.column ⟨G.representative.height,G.sub_old G.representative.inBand⟩=G.pc positive
  below : ∀ (i : Fin (k+1)) (H : G.data.band), G.data.isOrdinary=true → G.data.Uses i →
    field.value i H≤(G.comparison positive).value i H

noncomputable def support (positive : Bool) : G.Support positive := by
  apply Classical.choice
  obtain ⟨F,a,b,ho,he,hF⟩ := G.data.support_at lam lam_bound positive
    G.representative.column G.representative.height (G.sub_old G.representative.inBand) G.representative_uses
  exact ⟨⟨F,a,b,ho,he,hF⟩⟩

lemma old_eq (positive : Bool) (C : G.Component) (w : M.Point G.broad G.broad_root)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hc : w.column=x.column) (hH : w.height=x.height) : G.old positive C x=G.value positive w := by
  dsimp only [old,value]
  congr 1
  exacts [hc.symm,Subtype.ext hH.symm]

lemma seed_common (C : G.Component) (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.allSeeds C) : A.Common S.name (A.point x.column x.height) 5 G.index := by
  obtain ⟨w,hw,hc,hH⟩ := (G.allSeeds_description C x).mp hx
  rw [← hc,← hH]
  exact G.common w hw

lemma component_uses (C : G.Component) (hC : (G.allSeeds C).Nonempty)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) : G.data.Uses x.column := by
  obtain ⟨w,hw⟩ := hC
  have hu : G.data.Uses w.column := S.uses_named w.column w.height G.index
    ((G.seed_common C w hw).center A (by norm_num))
  obtain ⟨p,_,_⟩ := w.exists_shortest isClosed_Icc x
  exact G.data.uses_reachable hu (p.widen (G.narrow_sub.trans G.sub_old)).word.reachable

lemma seed_near (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C)) (hx : x ∈ G.allSeeds C) :
    |G.old positive C x-G.pc positive|≤(60/1000000:ℝ)*R := by
  obtain ⟨w,hw,hc,hH⟩ := (G.allSeeds_description C x).mp hx
  rw [G.old_eq positive C w x hc hH]
  exact (G.value_near positive w hw).trans (by norm_num [g,R])

lemma domain_name (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty) (i : Fin (k+1)) (H : ℝ)
    (hi : H ∈ SecondaryCell.domain (G.admittedSeeds positive C) R i) : S.name i H=G.index := by
  obtain ⟨x,hx,hH,hd⟩ := (SecondaryCell.mem_domain _ _).mp hi
  obtain ⟨w,hw,he⟩ := SecondaryCell.seedDistance_attained _ hC x
  have hc := G.seed_common C w (Finset.mem_filter.mp hw).1
  have hdist : dist (A.point w.column w.height) (A.point i H)≤5 := by
    rw [← hx,← hH]
    have ha := MainFamily.ambient_dist_le A w x
    rw [dist_comm w x,← he] at ha
    exact ha.trans (hd.trans (by norm_num [R]))
  exact hc (A.point i H) hdist

/-- A nonempty admitted component now produces the literal, fully proved
secondary clipping operation. No admission, support, name-gluing or movement
conclusion is added as an assumption of the step. -/
noncomputable def step (positive : Bool) (C : G.Component)
    (hC : (G.admittedSeeds positive C).Nonempty)
    (noise : Point.RadialTree.Noise (n := k+1)) (hn : (G.tree C).NoiseBounds noise)
    (alpha beta : ℝ) (ha : alpha≤EB) (hb : beta≤EB) :
    BState.SecondaryStep S (BandTrees.band narrow G.lower) (G.root C) where
  index := G.index
  positive := positive
  lambda_bound := lam_bound
  tree := G.tree C
  lo := G.lower
  band_eq := rfl
  sub_old := G.narrow_sub.trans G.sub_old
  seeds := G.admittedSeeds positive C
  seeds_nonempty := hC
  pc := G.pc positive
  radius := R
  radius_nonneg := by norm_num [R]
  radius_small := by norm_num [R]
  support := (G.support positive).field
  lower := (G.support positive).lower
  upper := (G.support positive).upper
  support_ordered := (G.support positive).ordered
  support_le := by
    intro ho x
    exact (G.support positive).below x.column _ ho
      (G.component_uses C (hC.mono (Finset.filter_subset _ _)) x)
  admitted := G.admitted_sphere positive C
  seed_near := fun w hw => G.seed_near positive C w (Finset.mem_filter.mp hw).1
  zeta_eq := rfl
  delta_eq := rfl
  noise := noise
  noise_bounds := hn
  ordered_offset := alpha
  shield_offset := beta
  ordered_bound := ha
  shield_bound := hb
  same_name := G.domain_name positive C hC
  kappa_nonneg := verticalB.1
  vertical_bound := verticalB.2.1
  shield_strict := verticalB.2.2.1

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)

/-- Offsets are fresh for each narrow component. The keep coin, by contrast,
is shared by all the components of one surviving group. -/
abbrev ComponentSample (i : I) (C : (G i).Component) (m : ℕ) :=
  Point.RadialTree.GridSample (n := k+1) ((G i).tree C).depthCap m × Fin (m+1) × Fin (m+1)
abbrev Sample (m : ℕ) :=
  (Fin (S.count+1) → Bool) × (I → Bool) × (∀ i C, ComponentSample G i C m)
noncomputable instance instFintypeSample (m : ℕ) : Fintype (Sample G m) := Fintype.ofFinite _
instance instNonemptySample (m : ℕ) : Nonempty (Sample G m) := inferInstanceAs (Nonempty (_ × _ × _))

variable {m : ℕ} (hm : 0 < m) (omega : Sample G m)

def kept (i : I) : Prop := omega.2.1 i=true
abbrev Acting (a : Fin (S.count+1)) :=
  {q : Σ i, (G i).Component // (G q.1).index=a ∧ kept G omega q.1 ∧
    ((G q.1).admittedSeeds (omega.1 a) q.2).Nonempty}
noncomputable instance instFintypeActing (a : Fin (S.count+1)) : Fintype (Acting G omega a) := Fintype.ofFinite _

include hm in
lemma offset_bound (t : Fin (m+1)) :
    EB/(m:ℝ)*(t.val:ℝ)≤EB := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have ht : (t.val:ℝ) ≤ m := by exact_mod_cast t.is_le
  calc _ ≤ EB/m*m := mul_le_mul_of_nonneg_left ht (div_nonneg (by norm_num [EB,R]) hmR.le)
       _ = EB := div_mul_cancel₀ _ hmR.ne'

noncomputable def actingStep (a : Fin (S.count+1)) (q : Acting G omega a) :=
  (G q.val.1).step (omega.1 a) q.val.2 q.property.2.2
    (((G q.val.1).tree q.val.2).gridNoise _ m (omega.2.2 q.val.1 q.val.2).1)
    (((G q.val.1).tree q.val.2).gridNoise_bounds _ _ hm (omega.2.2 q.val.1 q.val.2).1)
    (EB/m*(omega.2.2 q.val.1 q.val.2).2.1.val)
    (EB/m*(omega.2.2 q.val.1 q.val.2).2.2.val)
    (offset_bound hm _)
    (offset_bound hm _)

/-- Literal maximum within an old B identifier. Neither disjoint domains nor
an assumed winning branch replaces the actual overlapping maximum. -/
noncomputable def batch (a : Fin (S.count+1)) : BState.SecondaryBatch S where
  index := a
  positive := omega.1 a
  lambda_bound := Group.lam_bound
  count := Fintype.card (Acting G omega a)
  band j := BandTrees.band narrow
    (G ((Fintype.equivFin (Acting G omega a)).symm j).val.1).lower
  root j := (G ((Fintype.equivFin (Acting G omega a)).symm j).val.1).root
    ((Fintype.equivFin (Acting G omega a)).symm j).val.2
  step j := actingStep G hm omega a ((Fintype.equivFin (Acting G omega a)).symm j)
  same_index j := ((Fintype.equivFin (Acting G omega a)).symm j).property.1
  same_positive _ := rfl
  kappa_nonneg := verticalB.1
  kappa_five := verticalB.2.2.2

noncomputable def layer : BState.SecondaryLayer S where
  batch := batch G hm omega
  same_index _ := rfl

noncomputable def result [SFinite μ] :
    BState M kappaB Group.lam (Ω × Bool) (μ.prod Threshold.fair) :=
  (layer G hm omega).apply

end PlanarL1.Columns.Model.SecondaryGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_ScaleHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) {c t : ℝ} (hc : 0 < c) (hcr : c≤4)

namespace BState
/-- The auxiliary fields are the actual finite recorded histories, with a lower
bound on every previously used scale. Empty fresh histories obey any bound. -/
structure Histories (S : BState M κ lam Ω μ) (t : ℝ) where
  history : Fin (S.count+1) → A.History c
  older : ∀ a j, t≤(history a).radius j
  recorded : ∀ a, (S.chart a).Recorded (history a) hc hcr

namespace Histories
variable {A hc hcr} {S : BState M κ lam Ω μ}

def weaken (H : Histories A hc hcr S t) {s : ℝ} (h : s≤t) : Histories A hc hcr S s where
  history := H.history
  older a j := h.trans (H.older a j)
  recorded := H.recorded

noncomputable def lift (H : Histories A hc hcr S t) : Histories A hc hcr S.lift t where
  history := H.history
  older := H.older
  recorded := H.recorded

noncomputable def ofOrdinary (S : OrdinaryState M κ Ω μ) :
    Histories A hc hcr (BState.ofOrdinary (lam := lam) S) t where
  history _ := Ambient.History.empty A c
  older _ j := Fin.elim0 j
  recorded _ := trivial

noncomputable def append (H : Histories A hc hcr S t)
    (B : SetSystem M Ω μ) (m : ℕ) (D : Fin m → BData M)
    (Z : Fin m → Threshold.Variables Ω μ) (choose : Fin (k+1) → ℝ → Option (Fin m))
    (hin : ∀ i H a, choose i H=some a → H∈(D a).band)
    (hcomp : ∀ i H a, choose i H=some a → (D a).Uses i)
    (hswitch : ∀ i j H, H∈M.heights i j → choose i H=choose j H)
    (hold : ∀ ω i H, choose i H=none →
      ((B.activity ω).active i H ↔ (S.sets.activity ω).active i H))
    (hnew : ∀ ω i H a (h : choose i H=some a),
      ((B.activity ω).active i H ↔ Threshold.active (Z a) H
        (κ*(D a).value lam i ⟨H,hin i H a h⟩) ω))
    (hD : ∀ a, (D a).Recorded (Ambient.History.empty A c) hc hcr) :
    Histories A hc hcr (S.append B m D Z choose hin hcomp hswitch hold hnew) t where
  history := Fin.addCases (m := m) (n := S.count+1) (motive := fun _ : Fin (m+(S.count+1)) => A.History c) (fun _ => Ambient.History.empty A c) H.history
  older a := by
    let P (Z : A.History c) : Prop := ∀ j, t≤Z.radius j
    change P (Fin.addCases (m := m) (n := S.count+1) (motive := fun _ : Fin (m+(S.count+1)) => A.History c) (fun _ => Ambient.History.empty A c) H.history a)
    refine Fin.addCases (m := m) (n := S.count+1) ?_ ?_ a
    · intro i
      rw [Fin.addCases_left]
      exact fun j => Fin.elim0 j
    · intro i
      rw [Fin.addCases_right]
      exact H.older i
  recorded a := by
    refine Fin.addCases (m := m) (n := S.count+1) ?_ ?_ a
    · intro i
      simpa only [BState.append, Fin.addCases_left] using hD i
    · intro i
      simpa only [BState.append, Fin.addCases_right] using H.recorded i

noncomputable def increment (H : Histories A hc hcr S t) {r s : ℝ}
    (sign : Fin (S.count+1) → Bool) (hr : 0 < r) (hs : s ≤ r) (ht : s≤t)
    (hcross : ∀ a j, 10*r ≤ c*(H.history a).radius j)
    (hk : 0≤κ) (hsmall : κ*5≤1/2) (hlam : lam≤(1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10≤1/8) :
    Histories A hc hcr
      (S.increment A H.history sign hc hcr hr hcross H.recorded hk hsmall hlam hboundary) s where
  history a := (S.chart a).incrementHistory (H.history a) r (S.region A a) (sign a) hr (hcross a)
  older a := by
    cases he : S.chart a with
    | ordinary D =>
      intro j
      simpa only [BData.incrementHistory] using ht.trans (H.older a j)
    | ordered D =>
      intro j
      cases j using Fin.lastCases with
      | last => simpa only [BData.incrementHistory,Ambient.History.append,Fin.snoc_last] using hs
      | cast j => simpa only [BData.incrementHistory,Ambient.History.append,Fin.snoc_castSucc] using ht.trans (H.older a j)
  recorded a := S.increment_recorded A H.history sign hc hcr hr hcross H.recorded hk hsmall hlam hboundary a
end Histories
end BState

namespace BState.SecondaryStep
variable {J : Set ℝ} {root : Fin (k+1)} {S : BState M κ lam Ω μ}
variable (U : SecondaryStep S J root)
lemma newData_recorded (a : Fin (3*(k+1)*U.tree.depthCap+2)) :
    (U.newData a).Recorded (Ambient.History.empty A c) hc hcr := by
  classical
  unfold newData
  split_ifs
  · trivial
  · intro i T
    rw [Ambient.History.field_empty]
    rfl
  · trivial
end BState.SecondaryStep

namespace BState.SecondaryLayer
variable {S : BState M κ lam Ω μ} (B : SecondaryLayer S)
noncomputable def histories [SFinite μ] (H : Histories A hc hcr S t) :
    Histories A hc hcr B.apply t := by
  unfold apply
  apply H.lift.append
  intro a
  exact ((B.batch _).step _).newData_recorded A hc hcr _
end BState.SecondaryLayer
end PlanarL1.Columns.Model

end



section

open Set
namespace PlanarL1
/-- The distance to a literal image scales under a surjective homothety,
including the empty set convention for `infDist`. -/
lemma infDist_homothety {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) {q : ℝ} (hq : 0<q) (hd : ∀ x y, dist (f x) (f y)=q*dist x y)
    (x : X) (S : Set X) : Metric.infDist (f x) (f '' S)=q*Metric.infDist x S := by
  by_cases hs : S.Nonempty
  · apply le_antisymm
    · rw [mul_comm q]
      apply (div_le_iff₀ hq).mp
      apply (Metric.le_infDist hs).mpr
      intro y hy
      exact (div_le_iff₀ hq).mpr (by
        rw [mul_comm]
        exact (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem f hy)).trans_eq (hd x y))
    · apply (Metric.le_infDist (hs.image f)).mpr
      rintro _ ⟨y,hy,rfl⟩
      rw [hd]
      exact mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem hy) hq.le
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simp only [he,Set.image_empty,Metric.infDist_empty,mul_zero]

namespace Increment
variable {q : ℝ} (hq : 0<q)
include hq
lemma clamp_scale (a b t : ℝ) : clamp (q*a) (q*b) (q*t)=q*clamp a b t := by
  unfold clamp
  rw [← mul_max_of_nonneg _ _ hq.le,← mul_min_of_nonneg _ _ hq.le]

lemma quadratic_scale (a b c d t : ℝ) :
    quadratic (q*a) (q*b) (q*c) (q*d) (q*t)=q*quadratic a b c d t := by
  unfold quadratic
  rw [clamp_scale hq]
  rw [← mul_sub]
  field_simp

lemma low_scale (a t : ℝ) : low (q*a) (q*t)=q*low a t := by
  unfold low
  rw [show 2*(q*a)=q*(2*a) by ring,quadratic_scale hq]
  ring

lemma high_scale (r t : ℝ) : high (q*r) (q*t)=q*high r t := by
  unfold high splice
  simp only [show 8*(q*r)=q*(8*r) by ring,mul_le_mul_iff_right₀ hq]
  split_ifs
  · rfl
  · rw [show 10*(q*r)=q*(10*r) by ring,show 2*(q*r)=q*(2*r) by ring,
      quadratic_scale hq]

lemma positivePart_scale (a r t : ℝ) : positivePart (q*a) (q*r) (q*t)=q*positivePart a r t := by
  unfold positivePart splice
  simp only [show 2*(q*a)=q*(2*a) by ring,mul_le_mul_iff_right₀ hq]
  split_ifs
  · exact low_scale hq a t
  · exact high_scale hq r t

lemma scalar_scale (a r t : ℝ) : scalar (q*a) (q*r) (q*t)=q*scalar a r t := by
  unfold scalar splice
  simp only [show q*t≤0 ↔ t≤0 by constructor <;> intro h <;> nlinarith only [hq,h]]
  split_ifs
  · rw [show -(q*t)=q*(-t) by ring,positivePart_scale hq]
    ring
  · exact positivePart_scale hq a r t

lemma taper_scale {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (hd : ∀ x y, dist (f x) (f y)=q*dist x y)
    (S : Set X) (r : ℝ) (x : X) : taper (f '' S) (q*r) (f x)=taper S r x := by
  unfold taper
  rw [Set.image_nonempty]
  split_ifs
  · rw [infDist_homothety f hq hd]
    congr 1
    exact mul_div_mul_left _ _ hq.ne'
  · rfl
end Increment
end PlanarL1

namespace PlanarL1.Columns.Model
variable {k : ℕ} {M : Model (k+1)} {q : ℝ} (hq : 0<q)
include hq in
lemma scale_univ : (fun T : ℝ => q*T) '' Set.univ=Set.univ := by
  ext T
  simp only [mem_dilate_set q hq,Set.mem_univ]

namespace Point
lemma dist_band_eq {J I : Set ℝ} {r s : Fin (k+1)} (h : J=I)
    (x y : M.Point J r) (x' y' : M.Point I s)
    (hx : x.column=x'.column) (hX : x.height=x'.height)
    (hy : y.column=y'.column) (hY : y.height=y'.height) : dist x y=dist x' y' := by
  subst I
  exact Point.dist_coordinates x y x' y' hx hX hy hY
end Point
namespace Ambient
variable (A : Ambient M)
noncomputable def dilate : Ambient (M.dilate q hq) where
  root := A.root
  connected i := by
    rw [← scale_univ hq,M.dilate_activeGraph]
    exact A.connected i

noncomputable def scaleEquiv : M.Point Set.univ A.root ≃ (M.dilate q hq).Point Set.univ (A.dilate hq).root where
  toFun x := (A.dilate hq).point x.column (q*x.height)
  invFun x := A.point x.column (x.height/q)
  left_inv x := by cases x; simp only [point,mul_div_cancel_left₀ _ hq.ne']
  right_inv x := by cases x; simp only [point,mul_div_cancel₀ _ hq.ne']

lemma scaleEquiv_dist (x y : M.Point Set.univ A.root) :
    dist (A.scaleEquiv hq x) (A.scaleEquiv hq y)=q*dist x y := by
  rw [← Point.dist_band_eq (scale_univ hq) (x.dilate hq) (y.dilate hq)
    (A.scaleEquiv hq x) (A.scaleEquiv hq y) rfl rfl rfl rfl]
  exact x.dilate_dist hq y

namespace History
variable {A} {c : ℝ}
noncomputable def dilate (H : History A c) : History (A.dilate hq) c where
  count := H.count
  radius j := q*H.radius j
  region j := A.scaleEquiv hq '' H.region j
  sign := H.sign
  positive j := mul_pos hq (H.positive j)
  separated i j hij := by
    rcases H.separated i j hij with h | h
    · left; nlinarith only [hq,h]
    · right; nlinarith only [hq,h]
end History
end Ambient
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {q : ℝ} (hq : 0<q) {J : Set ℝ} {L : ℝ≥0}

def coordinateScale (q : ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (q*z.1,q*z.2)

include hq in
lemma coordinateScale_dist (x y : ℝ×ℝ) :
    dist (coordinateScale q x) (coordinateScale q y)=q*dist x y := by
  simp only [coordinateScale,Prod.dist_eq,Real.dist_eq,← mul_sub,abs_mul,abs_of_pos hq]
  rw [mul_max_of_nonneg _ _ hq.le]

lemma dilate_wall (F : M.Field J L) (a b : Fin (k+1)) :
    (F.dilate hq).wall a b=coordinateScale q '' F.wall a b := by
  ext z
  constructor
  · rintro (⟨H,rfl⟩ | ⟨H,rfl⟩ | ⟨i,j,H,hs,hi,hj,rfl⟩)
    · let U : J := ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩
      exact ⟨(F.value a U,U.val),Or.inl ⟨U,rfl⟩,by
        simp only [coordinateScale,dilate,U,mul_div_cancel₀ _ hq.ne']⟩
    · let U : J := ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩
      exact ⟨(F.value b U,U.val),Or.inr (Or.inl ⟨U,rfl⟩),by
        simp only [coordinateScale,dilate,U,mul_div_cancel₀ _ hq.ne']⟩
    · let U : J := ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩
      exact ⟨(F.value i U,U.val),Or.inr (Or.inr ⟨i,j,U,
        (M.dilate_mem_heights q hq).mp hs,hi,hj,rfl⟩),by
        simp only [coordinateScale,dilate,U,mul_div_cancel₀ _ hq.ne']⟩
  · rintro ⟨z,(⟨H,rfl⟩ | ⟨H,rfl⟩ | ⟨i,j,H,hs,hi,hj,rfl⟩),rfl⟩
    · refine Or.inl ⟨⟨q*H.val,Set.mem_image_of_mem _ H.property⟩,?_⟩
      simp only [coordinateScale,dilate,mul_div_cancel_left₀ _ hq.ne']
    · refine Or.inr (Or.inl ⟨⟨q*H.val,Set.mem_image_of_mem _ H.property⟩,?_⟩)
      simp only [coordinateScale,dilate,mul_div_cancel_left₀ _ hq.ne']
    · refine Or.inr (Or.inr ⟨i,j,⟨q*H.val,Set.mem_image_of_mem _ H.property⟩,
        Set.mem_image_of_mem _ hs,hi,hj,?_⟩)
      simp only [coordinateScale,dilate,mul_div_cancel_left₀ _ hq.ne']

lemma dilate_transverseValue (F : M.Field J L) (a b i : Fin (k+1))
    (H : (fun T => q*T) '' J) :
    (F.dilate hq).transverseValue a b i H=
      q*F.transverseValue a b i ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩ := by
  unfold transverseValue
  rw [dilate_wall hq]
  have he : ((F.dilate hq).value i H,H.val)=
      coordinateScale q (F.value i ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩,H.val/q) := by
    simp only [coordinateScale,dilate,mul_div_cancel₀ _ hq.ne']
  rw [he,PlanarL1.infDist_homothety _ hq (coordinateScale_dist hq)]
  ring
end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {q : ℝ} (hq : 0<q) {A : Ambient M} {c : ℝ}
namespace Ambient.History
lemma dilate_field (H : History A c) {I : Set ℝ} (s : M.Field I 4)
    (a b : Fin (k+1)) (hc : 0 < c) (hcr : c≤4) (i : Fin (k+1))
    (T : (fun U => q*U) '' I) :
    ((H.dilate hq).field (s.dilate hq) a b hc hcr).value i T=
      q*(H.field s a b hc hcr).value i ⟨T.val/q,(mem_dilate_set q hq).mp T.property⟩ := by
  classical
  let U : I := ⟨T.val/q,(mem_dilate_set q hq).mp T.property⟩
  have ht : ((s.dilate hq).transverse (by norm_num) a b).value i T=
      q*(s.transverse (by norm_num) a b).value i U := s.dilate_transverseValue hq a b i T
  have hw (j : Fin H.count) :
      Increment.taper ((A.scaleEquiv hq '' H.region j)ᶜ) (q*H.radius j)
        ((A.dilate hq).point i T.val)=Increment.taper (H.region j)ᶜ (H.radius j) (A.point i U.val) := by
    rw [← Equiv.image_compl]
    have he : (A.dilate hq).point i T.val=A.scaleEquiv hq (A.point i U.val) := by
      change (A.dilate hq).point i T.val=(A.dilate hq).point i (q*(T.val/q))
      rw [mul_div_cancel₀ _ hq.ne']
    rw [he]
    exact Increment.taper_scale hq (A.scaleEquiv hq) (A.scaleEquiv_dist hq) _ _ _
  change (∑ j : Fin H.count, Increment.signedDamped (H.sign j) (c*(q*H.radius j)) (q*H.radius j)
    (((s.dilate hq).transverse (by norm_num) a b).value i)
    (fun W => Increment.taper (A.scaleEquiv hq '' H.region j)ᶜ (q*H.radius j) ((A.dilate hq).point i W.val)) T)=
      q*∑ j : Fin H.count, Increment.signedDamped (H.sign j) (c*H.radius j) (H.radius j)
        ((s.transverse (by norm_num) a b).value i)
        (fun W => Increment.taper (H.region j)ᶜ (H.radius j) (A.point i W.val)) U
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold Increment.signedDamped Increment.damped
  simp only [ht,hw,show c*(q*H.radius j)=q*(c*H.radius j) by ring,Increment.scalar_scale hq]
  cases H.sign j <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring
end Ambient.History

namespace BData
lemma dilate_recorded (D : BData M) (H : A.History c) (hc : 0 < c) (hcr : c≤4)
    (h : D.Recorded H hc hcr) : (D.dilate hq).Recorded (H.dilate hq) hc hcr := by
  cases D with
  | ordinary D => trivial
  | ordered D =>
    intro i T
    change q*D.auxiliary.value i ⟨T.val/q,(mem_dilate_set q hq).mp T.property⟩=
      ((H.dilate hq).field (D.base.dilate hq) D.lower D.upper hc hcr).value i T
    exact (congrArg (q*·) (h i _)).trans (H.dilate_field hq D.base D.lower D.upper hc hcr i T).symm
end BData

namespace BState.Histories
open MeasureTheory
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : BState M κ lam Ω μ} {hc : 0 < c} {hcr : c≤4} {t : ℝ}
noncomputable def dilate (H : BState.Histories A hc hcr S t) :
    BState.Histories (A.dilate hq) hc hcr (S.dilate hq) (q*t) where
  history a := (H.history a).dilate hq
  older a j := mul_le_mul_of_nonneg_left (H.older a j) hq.le
  recorded a := (S.chart a).dilate_recorded hq (H.history a) hc hcr (H.recorded a)
end BState.Histories
end PlanarL1.Columns.Model

end


section

namespace PlanarL1.Columns.Model
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {r s : Fin n}
namespace Point
/-- Changing the bookkeeping root does not change a geometric point. -/
def reRoot (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) : M.Point I s :=
  ⟨x.column,x.height,x.inBand,h.trans x.reachable⟩
@[simp] lemma reRoot_column (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) :
    (x.reRoot h).column=x.column := rfl
@[simp] lemma reRoot_height (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) :
    (x.reRoot h).height=x.height := rfl
@[simp] lemma reRoot_inverse (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) :
    (x.reRoot h).reRoot h.symm=x := by cases x; rfl
@[simp] lemma dist_reRoot (h : (M.activeGraph I).Reachable s r) (x y : M.Point I r) :
    dist (x.reRoot h) (y.reRoot h)=dist x y :=
  dist_coordinates _ _ _ _ rfl rfl rfl rfl
end Point

namespace Field
variable {F : M.Field I 1} {ε : ℝ}
@[simp] lemma eval_reRoot (F : M.Field I 1) (h : (M.activeGraph I).Reachable s r)
    (x : M.Point I r) : F.eval (x.reRoot h)=F.eval x := rfl

def BandDescent.reRoot (h : (M.activeGraph I).Reachable s r) {x : M.Point I r}
    (D : F.BandDescent J x ε) : F.BandDescent J (x.reRoot h) ε where
  start_in := D.start_in
  target := D.target.reRoot h
  target_in := D.target_in
  path := D.path
  shortest := D.shortest
  lower := D.lower
  upper := D.upper
  drop := D.drop

end Field
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SurvivingSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.BandTrees
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (M : Model n) (P : Parameters.Interpolation) (lo : ℝ)
variable (C : Component M P lo)

/-- The very same finite connected radial cells, at an arbitrary prescribed
width; the secondary construction uses width g, not the main width D. -/
abbrev RadialIndex (width phase : ℝ) :=
  Σ l : levels M P lo C phase width,
    ((M.activeGraph (band P lo)).induce ((base M P lo C).layer (middle P lo)
      (middle_mem P lo) (phase+l.val*width) width)).ConnectedComponent
noncomputable instance instFintypeRadialIndex (width phase : ℝ) : Fintype (RadialIndex M P lo C width phase) := Fintype.ofFinite _

variable {M P lo C} {width phase : ℝ}

lemma radial_cover (hw : 0<width) {i : Fin n} (hi : i ∈ C.supp) :
    ∃ K : RadialIndex M P lo C width phase, i ∈ ColumnOrder.componentColumns K.2 := by
  let x := point M P lo C ⟨i,hi⟩
  let l := Tiling.index width phase (dist (base M P lo C) x)
  have hl : l ∈ levels M P lo C phase width :=
    Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,rfl⟩
  have hx : i ∈ (base M P lo C).layer (middle P lo) (middle_mem P lo)
      (phase+(l:ℝ)*width) width := by
    refine ⟨x.reachable,?_,?_⟩
    · have h := Int.floor_le ((dist (base M P lo C) x-phase)/width)
      have hh := (le_div_iff₀ hw).mp h
      change phase+(l:ℝ)*width≤dist (base M P lo C) x
      dsimp [l,Tiling.index]
      linarith
    · have h := Int.lt_floor_add_one ((dist (base M P lo C) x-phase)/width)
      have hh := (div_lt_iff₀ hw).mp h
      change dist (base M P lo C) x<phase+(l:ℝ)*width+width
      dsimp [l,Tiling.index]
      linarith
  let G := (M.activeGraph (band P lo)).induce ((base M P lo C).layer (middle P lo)
    (middle_mem P lo) (phase+(l:ℝ)*width) width)
  exact ⟨⟨⟨l,hl⟩,G.connectedComponentMk ⟨i,hx⟩⟩,⟨⟨i,hx⟩,rfl,rfl⟩⟩

lemma radial_diameter (hthin : P.width≤width/1000) (K : RadialIndex M P lo C width phase)
    (x y : M.Point (band P lo) (root M P lo C))
    (hx : x.column ∈ ColumnOrder.componentColumns K.2)
    (hy : y.column ∈ ColumnOrder.componentColumns K.2) : dist x y≤10*width :=
  (base M P lo C).radial_cell_diameter isClosed_Icc (middle_mem P lo) P.width_pos hthin
    (tree M P lo C).half_width K.2 x y hx hy

end PlanarL1.Columns.Model.BandTrees

end


section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (lo : ℝ) (C : BandTrees.Component M broad lo) (lo₂ phase : ℝ)

/-- Geometric part of a retained endpoint, before witness selection. Both
old identifiers refer to the actual closed unrestricted radius-five ball. -/
structure Position where
  point : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)
  narrow_height : point.height ∈ BandTrees.band narrow lo₂
  cell : BandTrees.RadialIndex M broad lo C g phase
  cell_mem : point.column ∈ ColumnOrder.componentColumns cell.2
  lower_pad : phase+(cell.1.val:ℝ)*g+g/100+2*a₁ <
    dist (BandTrees.base M broad lo C)
      (point.withHeight (BandTrees.middle broad lo) (BandTrees.middle_mem broad lo))
  upper_pad : dist (BandTrees.base M broad lo C)
      (point.withHeight (BandTrees.middle broad lo) (BandTrees.middle_mem broad lo)) <
    phase+(cell.1.val:ℝ)*g+g-g/100-2*a₁
  indexA : Fin (SA.count+1)
  indexB : Fin (SB.count+1)
  commonA : A.Common SA.name (A.point point.column point.height) 5 indexA
  commonB : A.Common SB.name (A.point point.column point.height) 5 indexB

namespace Position
variable {A SA SB lo C lo₂ phase} (p : Position A SA SB lo C lo₂ phase)
lemma band_near {H : ℝ} (hH : H ∈ BandTrees.band broad lo) : |p.point.height-H|≤5 := by
  have hp := p.point.inBand
  change lo≤p.point.height ∧ p.point.height≤lo+a₁ at hp
  change lo≤H ∧ H≤lo+a₁ at hH
  have hsmall : a₁≤5 := by norm_num [a₁]
  exact abs_le.mpr ⟨by linarith [hp.1,hp.2,hH.1,hH.2],by linarith [hp.1,hp.2,hH.1,hH.2]⟩
lemma subA : BandTrees.band broad lo ⊆ (SA.chart p.indexA).band :=
  SA.ball_band A p.commonA (fun _ hH => p.band_near hH)
lemma subB : BandTrees.band broad lo ⊆ (SB.chart p.indexB).band :=
  SB.ball_band A p.commonB (fun _ hH => p.band_near hH)
end Position

/-- Literal geometric data retained after both descent tests and the low-tip
exclusion. These records are finite witnesses of those tests, not estimates or
success/persistence assumptions. -/
structure Seed extends Position A SA SB lo C lo₂ phase where
  partner : M.Point (SA.chart indexA).band (BandTrees.root M broad lo C)
  descent : (SA.chart indexA).comparison.BandDescent (BandTrees.band broad lo)
    (point.widen toPosition.subA) epsilon
  partner_descent : (SA.chart indexA).comparison.BandDescent (BandTrees.band broad lo)
    partner epsilon
  apart : 1≤dist (point.widen toPosition.subA) partner
  close : |(SA.chart indexA).comparison.eval partner-
    (SA.chart indexA).comparison.eval (point.widen toPosition.subA)|≤EA
  retained : (SA.chart indexA).comparison.NoLowCircular
    (point.widen toPosition.subA) partner (BandTrees.band narrow lo₂) j

variable {A SA SB lo C lo₂ phase}

variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)
abbrev Key := BandTrees.RadialIndex M broad lo C g phase × Fin (SA.count+1) × Fin (SB.count+1)
noncomputable def key (w : W) : Key (SA := SA) (SB := SB) (lo := lo) (C := C) (phase := phase) :=
  ((s w).cell,(s w).indexA,(s w).indexB)
noncomputable def keys := Finset.univ.image (key s)
noncomputable abbrev GroupIndex := keys s
noncomputable instance instFintypeSubtypeKeyMemFinsetGroupIndex : Fintype (GroupIndex s) := Fintype.ofFinite _
noncomputable def members (q : GroupIndex s) : Finset W := Finset.univ.filter (fun w => key s w=q.val)
lemma members_nonempty (q : GroupIndex s) : (members s q).Nonempty := by
  obtain ⟨w,_,hw⟩ := Finset.mem_image.mp q.property
  exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩
noncomputable def seeds (q : GroupIndex s) := (members s q).image (fun w => (s w).point)
lemma seed_mem (q : GroupIndex s) {x : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)} :
    x ∈ seeds s q ↔ ∃ w, key s w=q.val ∧ (s w).point=x := by
  simp only [seeds,members,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
lemma seeds_nonempty (q : GroupIndex s) : (seeds s q).Nonempty := (members_nonempty s q).image _

variable (hsub : BandTrees.band narrow lo₂ ⊆ BandTrees.band broad lo)
/-- Group formation: exactly one finite proposal family per g-cell and pair
of old identifiers. The update groups themselves add no chart boundary. -/
noncomputable def group (q : GroupIndex s) : SecondaryGeometry.Group A SB where
  index := q.val.2.2
  broad := BandTrees.band broad lo
  broad_root := BandTrees.root M broad lo C
  broad_closed := isClosed_Icc
  lower := lo₂
  narrow_sub := hsub
  sub_old := by
    obtain ⟨w,hw⟩ := members_nonempty s q
    have he : key s w=q.val := (Finset.mem_filter.mp hw).2
    have hb : (s w).indexB=q.val.2.2 := congrArg (fun t => t.2.2) he
    exact hb ▸ (s w).toPosition.subB
  seeds := seeds s q
  nonempty := seeds_nonempty s q
  height := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := (seed_mem s q).mp hx
    exact (s w).narrow_height
  diameter := by
    intro x hx y hy
    obtain ⟨w,hw,rfl⟩ := (seed_mem s q).mp hx
    obtain ⟨v,hv,rfl⟩ := (seed_mem s q).mp hy
    have hc : (s w).cell=(s v).cell := congrArg Prod.fst (hw.trans hv.symm)
    exact BandTrees.radial_diameter (by norm_num [broad,a₁,g]) (s w).cell
      (s w).point (s v).point (s w).cell_mem (hc ▸ (s v).cell_mem)
  common := by
    intro x hx
    obtain ⟨w,hw,rfl⟩ := (seed_mem s q).mp hx
    have hb : (s w).indexB=q.val.2.2 := congrArg (fun t => t.2.2) hw
    exact hb ▸ (s w).commonB

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν}
variable {lo : ℝ} {C : BandTrees.Component M broad lo} {lo₂ phase : ℝ}
namespace Seed
variable (w : Seed A SA SB lo C lo₂ phase) {a : Fin (SA.count+1)}
noncomputable def partnerAt (he : w.indexA=a) :
    M.Point (SA.chart a).band (BandTrees.root M broad lo C) := he ▸ w.partner
noncomputable def descentAt (he : w.indexA=a)
    (hsub : BandTrees.band broad lo ⊆ (SA.chart a).band) :
    (SA.chart a).comparison.BandDescent (BandTrees.band broad lo)
    (w.point.widen hsub) epsilon := by subst a; exact w.descent
noncomputable def partnerDescentAt (he : w.indexA=a) :
    (SA.chart a).comparison.BandDescent (BandTrees.band broad lo)
    (w.partnerAt he) epsilon := by subst a; exact w.partner_descent
end Seed

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SurvivingGroups
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν}
variable {lo : ℝ} {C : BandTrees.Component M broad lo} {lo₂ phase : ℝ}
variable {W : Type*} [Fintype W] (s : W → Seed A SA SB lo C lo₂ phase)

/-- A real group meets the narrow-band radius-four-R ball through one of its
actual retained endpoints. This test involves no fresh random choices. -/
def Touch (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C))
    (q : GroupIndex s) : Prop := ∃ w, key s w=q.val ∧
      ∃ p : M.Path (BandTrees.band narrow lo₂) c.column (s w).point.column,
        p.length c.height (s w).point.height≤4*R
noncomputable abbrev Hits (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)) :=
  {q : GroupIndex s // Touch s c q}
noncomputable instance instFintypeHits (c : M.Point (BandTrees.band broad lo) (BandTrees.root M broad lo C)) :
    Fintype (Hits s c) := Fintype.ofFinite _

/-- One fixed universal integer, never depending on the finite list, the old
identifiers, or the old chart count. -/
noncomputable def packBound : ℕ := 2+Nat.ceil (1600*R/g)

end PlanarL1.Columns.Model.SurvivingGroups

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma not_admitted_witness (positive : Bool) (C : G.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (h : ¬G.Admitted positive C w) :
    ∃ z : M.Point (BandTrees.band narrow G.lower) (G.root C),
      dist w z=R ∧ G.old positive C z<G.pc positive-(65/100:ℝ)*R := by
  have hn : ¬∀ z : M.Point (BandTrees.band narrow G.lower) (G.root C),
      dist w z=R → G.pc positive-(65/100:ℝ)*R≤G.old positive C z :=
    fun hh => h (Or.inr hh)
  push Not at hn
  exact hn

lemma nonadmission_drop (positive : Bool) (C : G.Component)
    (w z : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hw : w ∈ G.allSeeds C)
    (hz : G.old positive C z<G.pc positive-(65/100:ℝ)*R) :
    G.old positive C z<G.old positive C w-(3/5:ℝ)*R := by
  have hn := (abs_le.mp (G.seed_near positive C w hw)).1
  have hR : 0<R := by norm_num [R]
  linarith

lemma narrow_sub_ordered {D : OrderedData M} (he : G.data=.ordered D) :
    BandTrees.band narrow G.lower ⊆ D.band := by
  intro H hH
  simpa only [he,BData.band] using G.sub_old (G.narrow_sub hH)

lemma old_ordered {D : OrderedData M} (he : G.data=.ordered D)
    (positive : Bool) (C : G.Component)
    (w : M.Point (BandTrees.band narrow G.lower) (G.root C)) :
    G.old positive C w =
      if positive then D.value lam w.column ⟨w.height,G.narrow_sub_ordered he w.inBand⟩
      else -D.value lam w.column ⟨w.height,G.narrow_sub_ordered he w.inBand⟩ := by
  have aux (E : BData M) (hE : E=.ordered D) (i : Fin (k+1)) (H : ℝ) (hH : H ∈ E.band) :
      (E.comparison lam lam_bound positive).value i ⟨H,hH⟩ =
        if positive then D.value lam i ⟨H,by simpa only [hE,BData.band] using hH⟩
        else -D.value lam i ⟨H,by simpa only [hE,BData.band] using hH⟩ := by
    subst E
    cases positive
    · change -(D.field lam lam_bound).value i ⟨H,hH⟩ = -D.value lam i ⟨H,hH⟩
      rw [OrderedData.field_value]
    · exact D.field_value lam lam_bound i ⟨H,hH⟩
  exact aux G.data he _ _ _

/-- Literal rejection of both sphere tests provides actual narrow-band paths
with opposite excursions of the fixed ordered part. No excursion hypothesis
is substituted for the geometric admission test. -/
noncomputable def excursions_of_rejected {D : OrderedData M} (he : G.data=.ordered D)
    (C : G.Component) (w : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hw : w ∈ G.allSeeds C) (hpos : ¬G.Admitted true C w) (hneg : ¬G.Admitted false C w)
    {root : Fin (k+1)} (x : M.Point D.band root)
    (hc : x.column=w.column) (hH : x.height=w.height) :
    D.base.Excursions (G.narrow_sub_ordered he) x (2*R) (2*R/5) := by
  apply Classical.choice
  rcases x with ⟨xc,xh,xi,xr⟩
  change xc=w.column at hc
  change xh=w.height at hH
  subst xc
  subst xh
  have sub : BandTrees.band narrow G.lower ⊆ D.band := G.narrow_sub_ordered he
  obtain ⟨z,hz,hval⟩ := G.not_admitted_witness true C w hpos
  obtain ⟨v,hv,hval'⟩ := G.not_admitted_witness false C w hneg
  obtain ⟨p,_,hp⟩ := w.exists_shortest isClosed_Icc z
  obtain ⟨q,_,hq⟩ := w.exists_shortest isClosed_Icc v
  have hlo := G.nonadmission_drop true C w z hw hval
  have hhi := G.nonadmission_drop false C w v hw hval'
  rw [G.old_ordered he true C z,G.old_ordered he true C w] at hlo
  rw [G.old_ordered he false C v,G.old_ordered he false C w] at hhi
  simp only [ite_true,Bool.false_eq_true,ite_false] at hlo hhi
  have ha := (D.auxiliary.restrict sub).path_bound p ⟨w.height,w.inBand⟩ ⟨z.height,z.inBand⟩
  have hb := (D.auxiliary.restrict sub).path_bound q ⟨w.height,w.inBand⟩ ⟨v.height,v.inBand⟩
  change |D.auxiliary.value w.column ⟨w.height,sub w.inBand⟩-
    D.auxiliary.value z.column ⟨z.height,sub z.inBand⟩|≤100*p.length w.height z.height at ha
  change |D.auxiliary.value w.column ⟨w.height,sub w.inBand⟩-
    D.auxiliary.value v.column ⟨v.height,sub v.inBand⟩|≤100*q.length w.height v.height at hb
  have ha' := ha.trans (le_of_eq (congrArg (fun t : ℝ => 100*t) (hp.trans hz)))
  have hb' := hb.trans (le_of_eq (congrArg (fun t : ℝ => 100*t) (hq.trans hv)))
  have hlow := (abs_le.mp ha').2
  have hhigh := (abs_le.mp hb').1
  dsimp only [OrderedData.value] at hlo hhi
  have hl : (0:ℝ)≤(lam:ℝ) := NNReal.coe_nonneg lam
  have hnum : (lam:ℝ)*100*R < R/5 := by
    change lambda*100*R<R/5
    norm_num [lambda,R]
  have hlo' : D.base.value z.column ⟨z.height,sub z.inBand⟩ <
      D.base.value w.column ⟨w.height,sub w.inBand⟩-2*R/5 := by nlinarith
  have hhi' : D.base.value w.column ⟨w.height,sub w.inBand⟩+2*R/5 <
      D.base.value v.column ⟨v.height,sub v.inBand⟩ := by nlinarith
  refine ⟨⟨w.inBand,z.column,v.column,⟨z.height,z.inBand⟩,⟨v.height,v.inBand⟩,
    p,q,?_,?_,?_,?_⟩⟩
  · exact (le_of_eq (hp.trans hz)).trans (by norm_num [R])
  · exact (le_of_eq (hq.trans hv)).trans (by norm_num [R])
  · exact hlo'
  · exact hhi'

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Separation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)}

namespace OrderedData
variable (D : OrderedData M) {A : Ambient M}
variable (H : A.History (R/200))
variable (region : Set (M.Point Set.univ A.root))
variable (hcross : ∀ j, 10≤(R/200)*H.radius j)
variable (hrec : (BData.ordered D).Recorded H (by norm_num [R]) (by norm_num [R]))

noncomputable def incrementField (e : Bool) : M.Field D.band 5 :=
  (BData.ordered D).auxiliaryField
    ((BData.ordered D).incrementAuxiliary H 1 region e (by norm_num [R])
      (by norm_num [R]) (by norm_num) (by simpa using hcross))
    SecondaryGeometry.Group.lam SecondaryGeometry.Group.lam_bound

end OrderedData
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SetSystem
noncomputable def separation (S : SetSystem M Ω μ) (i : Fin (k+1)) (H : ℝ)
    (j : Fin (k+1)) (T : ℝ) : ℝ :=
  ∫ ω, |(S.activity ω).indicator i H-(S.activity ω).indicator j T| ∂μ
end SetSystem

end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.VertexTests
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)

noncomputable def indexA (x : V) := SA.name (v x).column (v x).height
noncomputable def indexB (x : V) := SB.name (v x).column (v x).height
noncomputable def ordinaryValue (x : V) : ℝ :=
  (SA.chart (indexA A SA v x)).comparison.value (v x).column ⟨(v x).height,SA.height_in _ _⟩
noncomputable def fullValue (x : V) : ℝ :=
  (SB.chart (indexB A SB v x)).value SecondaryGeometry.Group.lam (v x).column
    ⟨(v x).height,SB.height_in _ _⟩

/-- The actual eligibility test in : both unrestricted closed
radius-five balls, with one common identifier in each of the two systems. -/
def Eligible (x y : V) : Prop :=
  A.Common SA.name (v x) 5 (indexA A SA v x) ∧
  A.Common SA.name (v y) 5 (indexA A SA v x) ∧
  A.Common SB.name (v x) 5 (indexB A SB v x) ∧
  A.Common SB.name (v y) 5 (indexB A SB v x)

def PairTest (p : V×V) : Prop :=
  1≤dist (v p.1) (v p.2) ∧ dist (v p.1) (v p.2)<2 ∧ Eligible A SA SB v p.1 p.2

def Cutoffs (x y : V) : Prop :=
  |(v x).height-(v y).height|<a₂/10000 ∧
  |ordinaryValue A SA v x-ordinaryValue A SA v y|<EA ∧
  |fullValue A SB v x-fullValue A SB v y|<R/10000

lemma Eligible.namesA {x y : V} (h : Eligible A SA SB v x y) :
    indexA A SA v y=indexA A SA v x := h.2.1.center A (by norm_num)
lemma Eligible.namesB {x y : V} (h : Eligible A SA SB v x y) :
    indexB A SB v y=indexB A SB v x := h.2.2.2.center A (by norm_num)
lemma Eligible.symm {x y : V} (h : Eligible A SA SB v x y) : Eligible A SA SB v y x := by
  unfold Eligible
  rw [h.namesA A SA SB v,h.namesB A SA SB v]
  exact ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

noncomputable def cutoffGain : ℝ := min (a₂/10000) (min (kappaA*EA) (kappaB*R/10000))

end PlanarL1.Columns.Model.VertexTests

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PairGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Threshold.Variables
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A literal half-sign label rectangle, pulled back through the actual old
chart variables. No independence of different old charts is asserted. -/
noncomputable def slab (Z : Variables Ω μ) (b : Bool) (lo hi : ℝ) : Set Ω :=
  Z.value ⁻¹' ({b} ×ˢ Ico lo hi)
end PlanarL1.Threshold.Variables

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PairSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.BandTrees
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {lo : ℝ} {C : Component M broad lo}

noncomputable def radialValue (x : M.Point (band broad lo) (root M broad lo C)) : ℝ :=
  dist (base M broad lo C) (x.withHeight (middle broad lo) (middle_mem broad lo))

/-- All column representatives, not only the chosen one, pass the radial
interior test. The quantification is over zero-distance geometric points. -/
def RadialInterior (width phase : ℝ) (x : M.Point (band broad lo) (root M broad lo C)) : Prop :=
  ∀ y : M.Point (band broad lo) (root M broad lo C), dist x y=0 →
    ¬Tiling.NearBoundary width phase (radialValue y) (width/50)

lemma radialInterior_padding {width phase : ℝ}
    (hw : 0<width) (hsmall : 2*a₁<width/100)
    (x : M.Point (band broad lo) (root M broad lo C)) (hi : RadialInterior width phase x)
    (K : RadialIndex M broad lo C width phase)
    (hx : x.column ∈ ColumnOrder.componentColumns K.2) :
    phase+(K.1.val:ℝ)*width+width/100+2*a₁ < radialValue x ∧
    radialValue x<phase+(K.1.val:ℝ)*width+width-width/100-2*a₁ := by
  have hl := ColumnOrder.componentColumns_subset K.2 hx
  have he : Tiling.index width phase (radialValue x)=K.1.val :=
    Tiling.index_eq_of_mem_lt hw _ hl.2.1 (by
      have hu : radialValue x<phase+(K.1.val:ℝ)*width+width := hl.2.2
      nlinarith [hu])
  have hp := Tiling.padded_of_avoid hw (hi x (dist_self _))
  rw [Tiling.Padded,he] at hp
  exact ⟨by linarith [hp.1],by linarith [hp.2]⟩

end PlanarL1.Columns.Model.BandTrees

end



section

namespace PlanarL1.Columns.Model.VertexBands
open Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable (L U : ℝ) (hv : ∀ x, (v x).height ∈ Set.Icc L U)

noncomputable def bandIndex (q : ℝ) (x : V) : MainFamily.BandIndex q L U :=
  ⟨Tiling.index a₁ q (v x).height,(Tiling.mem_processed interpolationA.2.1 q L U _).mpr
    ⟨(v x).height,Tiling.mem_band_index interpolationA.2.1 q _,hv x⟩⟩
noncomputable def lower (q : ℝ) (x : V) := MainFamily.lower q L U (bandIndex A v L U hv q x)
noncomputable def component (q : ℝ) (x : V) :
    BandTrees.Component M broad (lower A v L U hv q x) :=
  (M.activeGraph (BandTrees.band broad (lower A v L U hv q x))).connectedComponentMk (v x).column
noncomputable def bandComponent (q : ℝ) (x : V) : MainFamily.BandComponent (M := M) q L U :=
  ⟨bandIndex A v L U hv q x,component A v L U hv q x⟩
lemma height_mem (q : ℝ) (x : V) : (v x).height ∈ BandTrees.band broad (lower A v L U hv q x) := by
  have h := Tiling.mem_band_index interpolationA.2.1 q (v x).height
  change q+(Tiling.index a₁ q (v x).height:ℝ)*a₁≤(v x).height ∧
    (v x).height≤q+(Tiling.index a₁ q (v x).height:ℝ)*a₁+a₁
  constructor <;> dsimp [Tiling.band] at h <;> linarith [h.1,h.2]
noncomputable def point (q : ℝ) (x : V) :
    M.Point (BandTrees.band broad (lower A v L U hv q x))
      (BandTrees.root M broad (lower A v L U hv q x) (component A v L U hv q x)) where
  column := (v x).column
  height := (v x).height
  inBand := height_mem A v L U hv q x
  reachable := (component A v L U hv q x).reachable_of_mem_supp
    (BandTrees.root_mem _ _ _ _) rfl

variable {L U hv}
noncomputable def radial (q : ℝ) (width : ℝ)
    (phase : MainFamily.BandComponent (M := M) q L U → ℝ) (x : V) : Prop :=
  BandTrees.RadialInterior width (phase (bandComponent A v L U hv q x))
    (point A v L U hv q x)

/-- Exactly the literal vertex interior predicate. Narrow containment follows
from broad height padding and is included below as a checked consequence. -/
def Interior (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
    (x : V) : Prop :=
  Tiling.Padded a₁ q (v x).height (a₁/10) ∧
  Tiling.Padded a₂ p (v x).height (a₂/10) ∧
  radial A v (hv := hv) q D phaseD x ∧ radial A v (hv := hv) q g phaseG x

lemma Interior.narrow_sub {q p : ℝ}
    {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ} {x : V}
    (h : Interior A v (hv := hv) q p phaseD phaseG x) :
    Tiling.band a₂ p (Tiling.index a₂ p (v x).height) ⊆
      BandTrees.band broad (lower A v L U hv q x) := by
  have hs := Tiling.narrow_contained (p := p) h.1
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext H
  simp only [BandTrees.band,lower,MainFamily.lower,bandIndex,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤q+(Tiling.index a₁ q (v x).height:ℝ)*a₁+a₁) ↔
    (_≤H ∧ H≤q+((Tiling.index a₁ q (v x).height:ℝ)+1)*a₁)
  ring_nf

end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model.VertexBands
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)

abbrev HeightChoices (m : ℕ) := Fin (m+1) × Fin (m+1)
noncomputable def shift (m : ℕ) (width : ℝ) (i : Fin (m+1)) : ℝ := width/m*i.val
abbrev RadialChoices (m : ℕ) (q L U : ℝ) (M : Model (k+1)) :=
  (MainFamily.BandComponent (M := M) q L U → Fin (m+1)) ×
  (MainFamily.BandComponent (M := M) q L U → Fin (m+1))
abbrev Choices (m : ℕ) (L U : ℝ) (M : Model (k+1)) :=
  Σ h : HeightChoices m, RadialChoices m (shift m a₁ h.1) L U M
noncomputable def phase {m : ℕ} {q L U : ℝ} (width : ℝ)
    (r : MainFamily.BandComponent (M := M) q L U → Fin (m+1)) :
    MainFamily.BandComponent (M := M) q L U → ℝ := fun b => shift m width (r b)

noncomputable def geometricExecution (m : ℕ) (L U : ℝ) (M : Model (k+1)) :
    Execution (Choices m L U M) :=
  Execution.uniform.bind (fun h : HeightChoices m =>
    Execution.uniform.bind (fun r : RadialChoices m (shift m a₁ h.1) L U M =>
      .pure ⟨h,r⟩))

def InteriorAt {m : ℕ} (c : Choices m L U M) (x : V) : Prop :=
  Interior A v (hv := hv) (shift m a₁ c.1.1) (shift m a₂ c.1.2)
    (phase D c.2.1) (phase g c.2.2) x

end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)

noncomputable def narrowLower (x : V) : ℝ := p+(Tiling.index a₂ p (v x).height:ℝ)*a₂
lemma narrow_height (x : V) : (v x).height ∈ BandTrees.band narrow (narrowLower A v p x) := by
  have hh := Tiling.mem_band_index interpolationB.2.1 p (v x).height
  change p+(Tiling.index a₂ p (v x).height:ℝ)*a₂≤(v x).height ∧
    (v x).height≤p+(Tiling.index a₂ p (v x).height:ℝ)*a₂+a₂
  constructor <;> dsimp [Tiling.band] at hh <;> linarith [hh.1,hh.2]

variable {q p phaseD phaseG} {x y : V}
variable (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)

lemma gcell_exists : ∃ c : BandTrees.RadialIndex M broad (VertexBands.lower A v L U hv q x)
    (VertexBands.component A v L U hv q x) g (phaseG (VertexBands.bandComponent A v L U hv q x)),
    (v x).column ∈ ColumnOrder.componentColumns c.2 :=
  BandTrees.radial_cover (hw := by norm_num [g]) (hi := rfl)

noncomputable def position : SurvivingGroups.Position A SA SB
    (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)
    (narrowLower A v p x) (phaseG (VertexBands.bandComponent A v L U hv q x)) where
  point := VertexBands.point A v L U hv q x
  narrow_height := narrow_height A v p x
  cell := (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose
  cell_mem := (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose_spec
  lower_pad := (BandTrees.radialInterior_padding (by norm_num [g]) (by norm_num [a₁,g])
    (VertexBands.point A v L U hv q x) hi.2.2.2 _
    (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose_spec).1
  upper_pad := (BandTrees.radialInterior_padding (by norm_num [g]) (by norm_num [a₁,g])
    (VertexBands.point A v L U hv q x) hi.2.2.2 _
    (gcell_exists A v hv (q := q) (phaseG := phaseG) (x := x)).choose_spec).2
  indexA := indexA A SA v x
  indexB := indexB A SB v x
  commonA := by simpa only [VertexBands.point,A.coordinate_point] using he.1
  commonB := by simpa only [VertexBands.point,A.coordinate_point] using he.2.2.1

variable (hd : dist (v x) (v y)<2)
include hd in
lemma partner_exists : ∃ z : M.Point (SA.chart (indexA A SA v x)).band
    (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)),
    z.column=(v y).column ∧ z.height=(v y).height ∧
    dist ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA) z=
      dist (v x) (v y) := by
  let w := position A SA SB v hv he hi
  apply Point.local_point (v x) (v y) (w.point.widen w.subA) rfl rfl
    isClosed_univ (Set.subset_univ _) (t := 2) ?_ hd.le
  intro H hH
  have hs := SA.ball_band A he.1 (J := {H : ℝ | |H-(v x).height|≤2}) (by
    intro T hT
    rw [abs_sub_comm]
    exact hT.trans (by norm_num))
  exact hs hH

noncomputable def partner : M.Point (SA.chart (indexA A SA v x)).band
    (BandTrees.root M broad (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)) :=
  (partner_exists A SA SB v hv he hi hd).choose
lemma partner_column : (partner A SA SB v hv he hi hd).column=(v y).column :=
  (partner_exists A SA SB v hv he hi hd).choose_spec.1
lemma partner_height : (partner A SA SB v hv he hi hd).height=(v y).height :=
  (partner_exists A SA SB v hv he hi hd).choose_spec.2.1
lemma partner_dist : dist ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)
    (partner A SA SB v hv he hi hd)=dist (v x) (v y) :=
  (partner_exists A SA SB v hv he hi hd).choose_spec.2.2

lemma comparison_transport {D E : OrdinaryData M} (he : D=E)
    (i : Fin (k+1)) (H : ℝ) (hD : H ∈ D.band) (hE : H ∈ E.band) :
    D.comparison.value i ⟨H,hD⟩=E.comparison.value i ⟨H,hE⟩ := by subst E; rfl

lemma partner_value : (SA.chart (indexA A SA v x)).comparison.eval (partner A SA SB v hv he hi hd)=
    ordinaryValue A SA v y := by
  let z := partner A SA SB v hv he hi hd
  have hiZ : z.column=(v y).column := partner_column A SA SB v hv he hi hd
  have hHZ : z.height=(v y).height := partner_height A SA SB v hv he hi hd
  have hHy : (v y).height ∈ (SA.chart (indexA A SA v x)).band := hHZ ▸ z.inBand
  have hcell : (SA.chart (indexA A SA v x)).comparison.eval z=
      (SA.chart (indexA A SA v x)).comparison.value (v y).column ⟨(v y).height,hHy⟩ := by
    change (SA.chart (indexA A SA v x)).comparison.value z.column ⟨z.height,z.inBand⟩=_
    rw [hiZ]
    exact congrArg ((SA.chart (indexA A SA v x)).comparison.value (v y).column) (Subtype.ext hHZ)
  exact hcell.trans (comparison_transport (congrArg SA.chart (he.namesA A SA SB v).symm) _ _ _ _)

lemma position_value : (SA.chart (indexA A SA v x)).comparison.eval
    ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)=ordinaryValue A SA v x := rfl

/-- The actual surviving test is just the two descending-path tests and the
absence of a low separating tip, after the literal earlier tests. -/
def Retained : Prop :=
  Nonempty ((SA.chart (indexA A SA v x)).comparison.BandDescent
    (BandTrees.band broad (VertexBands.lower A v L U hv q x))
    ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA) epsilon) ∧
  Nonempty ((SA.chart (indexA A SA v x)).comparison.BandDescent
    (BandTrees.band broad (VertexBands.lower A v L U hv q x)) (partner A SA SB v hv he hi hd) epsilon) ∧
  (SA.chart (indexA A SA v x)).comparison.NoLowCircular
    ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)
    (partner A SA SB v hv he hi hd) (BandTrees.band narrow (narrowLower A v p x)) j

noncomputable def seed (ha : 1≤dist (v x) (v y)) (hc : Cutoffs A SA SB v x y)
    (hr : Retained A SA SB v hv he hi hd) : SurvivingGroups.Seed A SA SB
    (VertexBands.lower A v L U hv q x) (VertexBands.component A v L U hv q x)
    (narrowLower A v p x) (phaseG (VertexBands.bandComponent A v L U hv q x)) where
  toPosition := position A SA SB v hv he hi
  partner := partner A SA SB v hv he hi hd
  descent := hr.1.some
  partner_descent := hr.2.1.some
  apart := by rw [partner_dist]; exact ha
  close := by
    change |(SA.chart (indexA A SA v x)).comparison.eval (partner A SA SB v hv he hi hd)-
      (SA.chart (indexA A SA v x)).comparison.eval
        ((position A SA SB v hv he hi).point.widen (position A SA SB v hv he hi).subA)|≤EA
    rw [partner_value,position_value,abs_sub_comm]
    exact hc.2.1.le
  retained := hr.2.2

end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable (L U : ℝ) (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)

/-- A literal surviving partner. This is tested before any group coin or
orientation is drawn, and never asserts success of an update. -/
structure Witness (x : V) where
  other : V
  test : PairTest A SA SB v (x,other)
  cutoffs : Cutoffs A SA SB v x other
  interior : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x
  other_interior : VertexBands.Interior A v (hv := hv) q p phaseD phaseG other
  retained : PairGeometry.Retained A SA SB v hv test.2.2 interior test.2.1

noncomputable def remaining : Finset V :=
  Finset.univ.filter (fun x => Nonempty (Witness A SA SB v L U hv q p phaseD phaseG x))
noncomputable abbrev Endpoint := remaining A SA SB v L U hv q p phaseD phaseG
noncomputable instance instFintypeSubtypeMemFinsetEndpoint : Fintype (Endpoint A SA SB v L U hv q p phaseD phaseG) := Fintype.ofFinite _

variable {L U q p phaseD phaseG}
lemma mem_remaining (x : V) : x ∈ remaining A SA SB v L U hv q p phaseD phaseG ↔
    Nonempty (Witness A SA SB v L U hv q p phaseD phaseG x) := by
  simp only [remaining,Finset.mem_filter,Finset.mem_univ,true_and]
noncomputable def witness (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    Witness A SA SB v L U hv q p phaseD phaseG w.val :=
  ((mem_remaining A SA SB v hv w.val).mp w.property).some

/-- Finite processed broad-component/narrow-band blocks. In particular no
infinite family of unused tail bands is randomized. -/
def Block (q p L U : ℝ) := Σ b : MainFamily.BandComponent (M := M) q L U,
  {n : Tiling.processed a₂ p L U //
    Tiling.band a₂ p n.val ⊆ BandTrees.band broad (MainFamily.lower q L U b.1)}
noncomputable instance instFintypeBlock : Fintype (Block (M := M) q p L U) := by
  unfold Block
  exact Fintype.ofFinite _

namespace Block
variable (b : Block (M := M) q p L U)
noncomputable def lower : ℝ := MainFamily.lower q L U b.1.1
noncomputable def lower₂ : ℝ := p+(b.2.val.val:ℝ)*a₂
lemma sub : BandTrees.band narrow b.lower₂ ⊆ BandTrees.band broad b.lower := by
  change _ ⊆ BandTrees.band broad (MainFamily.lower q L U b.1.1)
  convert b.2.property using 1
  all_goals try with_reducible_and_instances rfl
  ext H
  simp only [BandTrees.band,lower₂,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤p+(b.2.val.val:ℝ)*a₂+a₂) ↔ (_≤H ∧ H≤p+((b.2.val.val:ℝ)+1)*a₂)
  ring_nf
end Block

noncomputable def block (w : Endpoint A SA SB v L U hv q p phaseD phaseG) : Block (M := M) q p L U :=
  ⟨VertexBands.bandComponent A v L U hv q w.val,
    ⟨⟨Tiling.index a₂ p (v w.val).height,
      (Tiling.mem_processed interpolationB.2.1 p L U _).mpr
        ⟨(v w.val).height,Tiling.mem_band_index interpolationB.2.1 p _,hv w.val⟩⟩,
      (witness A SA SB v hv w).interior.narrow_sub A v⟩⟩

abbrev LocalSeed (b : Block (M := M) q p L U) :=
  SurvivingGroups.Seed A SA SB b.lower b.1.2 b.lower₂ (phaseG b.1)

noncomputable def rawSeed (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    LocalSeed A SA SB (phaseG := phaseG) (block A SA SB v hv w) :=
  PairGeometry.seed A SA SB v hv (witness A SA SB v hv w).test.2.2
    (witness A SA SB v hv w).interior (witness A SA SB v hv w).test.2.1
    (witness A SA SB v hv w).test.1 (witness A SA SB v hv w).cutoffs
    (witness A SA SB v hv w).retained

abbrev Slice (b : Block (M := M) q p L U) :=
  {w : Endpoint A SA SB v L U hv q p phaseD phaseG // block A SA SB v hv w=b}
noncomputable def localSeeds (b : Block (M := M) q p L U) (w : Slice A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) :
    LocalSeed A SA SB (phaseG := phaseG) b := w.property ▸ rawSeed A SA SB v hv w.val

noncomputable abbrev GroupIndex := Σ b : Block (M := M) q p L U,
  SurvivingGroups.GroupIndex (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b)
noncomputable instance instFintypeGroupIndex : Fintype (GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) :=
  Fintype.ofFinite _

noncomputable def group (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) :
    SecondaryGeometry.Group A SB := SurvivingGroups.group (localSeeds A SA SB v hv i.1) i.1.sub i.2

noncomputable def groupOf (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) :=
  ⟨block A SA SB v hv w,⟨SurvivingGroups.key (localSeeds A SA SB v hv _) ⟨w,rfl⟩,
    Finset.mem_image.mpr ⟨⟨w,rfl⟩,Finset.mem_univ _,rfl⟩⟩⟩

lemma groupOf_seed (w : Endpoint A SA SB v L U hv q p phaseD phaseG) :
    (rawSeed A SA SB v hv w).point ∈ (group A SA SB v hv (groupOf A SA SB v hv w)).seeds := by
  exact (SurvivingGroups.seed_mem _ _).mpr ⟨⟨w,rfl⟩,rfl,rfl⟩

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG x)
variable (hc : Cutoffs A SA SB v x y) (hd : dist (v x) (v y)<2)

/-- The source component certificate on literal active labels and an actual
terminal link. Its labels, tip and positive mass are not extra input. -/
def Certificate (b : ℝ) : Prop :=
  ∃ (a c : Fin (k+1)) (H : ℝ) (E : Set Ω),
    H ∈ M.heights a c ∧ ¬Consecutive a c ∧
    Field.CircularTipSeparates a c (v x).column (v y).column ∧
    MeasurableSet E ∧ b ≤ μ.real E ∧
    (∀ ω ∈ E, (SA.sets.activity ω).active (v x).column (v x).height) ∧
    (∀ ω ∈ E, (SA.sets.activity ω).active (v y).column (v y).height) ∧
    (∀ ω ∈ E, ¬(SA.sets.activity ω).active a H)

end PlanarL1.Columns.Model.PairGeometry

end



section

namespace PlanarL1.Columns.Model.MainFamily
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) (S : OrdinaryState M kappaA Ω μ)
variable {q L U : ℝ} (phase : BandComponent (M := M) q L U → ℝ)

/-- The literal radius-five eligibility test suffices for the full closed
one-neighborhood availability of every cell containing this endpoint. -/
lemma available_of_ball5 (c : CellIndex q L U phase) (x : M.Point Set.univ A.root)
    (hx : x.height ∈ domain phase c x.column) {a : Fin (S.count+1)}
    (hname : A.Common S.name x 5 a) : Available A S phase c := by
  refine ⟨a,fun y hy => hname y ?_⟩
  obtain ⟨i,H,hi,hd⟩ := hy
  have hxpoint : A.point x.column x.height=x := A.coordinate_point x
  have hc := cell_diameter A phase c hx hi
  rw [hxpoint] at hc
  have ht := dist_triangle x (A.point i H) y
  rw [dist_comm (A.point i H) y] at ht
  linarith

end PlanarL1.Columns.Model.MainFamily

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_MainGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.FiniteRandom
attribute [local instance] Classical.propDecidable

/-- Separate coins from all other finite independent local data, including
when the local data type depends on the cell/group. -/
def coinProduct {I : Type*} (D : I → Type*) :
    (∀ i, D i × Bool) ≃ (∀ i, D i) × (I → Bool) where
  toFun f := (fun i => (f i).1,fun i => (f i).2)
  invFun f i := (f.1 i,f.2 i)
  left_inv f := by funext i; rfl
  right_inv f := by cases f; rfl
end PlanarL1.FiniteRandom

namespace PlanarL1.Columns.Model.MainFamily
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {q L U : ℝ}
variable (phase : BandComponent (M := M) q L U → ℝ) (m : ℕ)
abbrev Uncoined (c : CellIndex q L U phase) :=
  Point.RadialTree.GridSample (n := k+1) (tree phase c).depthCap m × Fin (m+1)
def restructure : Sample phase m ≃ (∀ c, Uncoined phase m c × Bool) where
  toFun f c := (((f c).1,(f c).2.1),(f c).2.2)
  invFun f c := ((f c).1.1,((f c).1.2,(f c).2))
  left_inv f := by funext c; rfl
  right_inv f := by funext c; rfl
end PlanarL1.Columns.Model.MainFamily

end



section

namespace PlanarL1.Columns.Model.VertexBands
open Parameters MeasureTheory
variable {k : ℕ} {M : Model (k+1)} {V : Type*}
variable (A : Ambient M) (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phase : MainFamily.BandComponent (M := M) q L U → ℝ)
noncomputable def mainCell (x : V) : MainFamily.CellIndex q L U phase :=
  ⟨bandComponent A v L U hv q x,
    (BandTrees.main_cover broad (lower A v L U hv q x) (component A v L U hv q x)
      (phase (bandComponent A v L U hv q x)) (i := (v x).column) rfl).choose⟩
lemma mainCell_column (x : V) : (v x).column ∈ ColumnOrder.componentColumns (mainCell A v hv phase x).2.2 :=
  (BandTrees.main_cover broad (lower A v L U hv q x) (component A v L U hv q x)
    (phase (bandComponent A v L U hv q x)) (i := (v x).column) rfl).choose_spec
lemma mainCell_mem (x : V) : (v x).height∈MainFamily.domain phase (mainCell A v hv phase x) (v x).column :=
  (MainCell.mem_domain _ _ _).mpr ⟨mainCell_column A v hv phase x,height_mem A v L U hv q x⟩
end PlanarL1.Columns.Model.VertexBands

namespace PlanarL1.Columns.Model.PairGeometry
open Parameters MeasureTheory VertexTests VertexBands
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable {x y : V} (he : Eligible A SA SB v x y)
variable (hi : Interior A v (hv := hv) q p phaseD phaseG x)
variable (hj : Interior A v (hv := hv) q p phaseD phaseG y)
variable (hc : Cutoffs A SA SB v x y) (ha : 1≤dist (v x) (v y))

include he in
lemma main_available : MainFamily.Available A SA phaseD (mainCell A v hv phaseD x) :=
  MainFamily.available_of_ball5 A SA phaseD _ (v x) (mainCell_mem A v hv phaseD x) he.1
end PlanarL1.Columns.Model.PairGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SecondaryGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters
variable {k : ℕ} {M : Model (k+1)} {q p L U : ℝ}
namespace Block
variable (b : Block (M := M) q p L U)
lemma broad_eq : BandTrees.band broad b.lower=Tiling.band a₁ q b.1.1.val := by
  ext H
  simp only [BandTrees.band,lower,MainFamily.lower,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤q+(b.1.1.val:ℝ)*a₁+a₁) ↔ (_≤H ∧ H≤q+((b.1.1.val:ℝ)+1)*a₁)
  ring_nf
lemma narrow_eq : BandTrees.band narrow b.lower₂=Tiling.band a₂ p b.2.val.val := by
  ext H
  simp only [BandTrees.band,lower₂,Tiling.band,Set.mem_Icc]
  change (_≤H ∧ H≤p+(b.2.val.val:ℝ)*a₂+a₂) ↔ (_≤H ∧ H≤p+((b.2.val.val:ℝ)+1)*a₂)
  ring_nf

/-- At a doubly height-interior point, a narrow-band path can reach a seed
only in this very processed broad/component/narrow block. -/
lemma eq_of_path (d : Block (M := M) q p L U)
    (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
    (e : M.Point (BandTrees.band broad d.lower) (BandTrees.root M broad d.lower d.1.2))
    (hc : c.height ∈ BandTrees.band narrow b.lower₂)
    (hd : c.height ∈ BandTrees.band narrow d.lower₂)
    (hp : Tiling.Padded a₁ q c.height (a₁/10))
    (hn : Tiling.Padded a₂ p c.height (a₂/10))
    (path : M.Path (BandTrees.band narrow d.lower₂) c.column e.column) : b=d := by
  have hNb : b.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 (by norm_num [a₂]) hn (b.narrow_eq ▸ hc)
  have hNd : d.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 (by norm_num [a₂]) hn (d.narrow_eq ▸ hd)
  have hBb : b.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp (b.broad_eq ▸ c.inBand)
  have hBd : d.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 (by norm_num [a₁]) hp (d.broad_eq ▸ d.sub hd)
  have hB : b.1.1=d.1.1 := Subtype.ext (hBb.trans hBd.symm)
  rcases b with ⟨⟨bi,bC⟩,bn⟩
  rcases d with ⟨⟨di,dC⟩,dn⟩
  dsimp only at hB
  subst di
  have hC : bC=dC := by
    have hr := c.reachable.trans ((path.widen (Block.sub ⟨⟨bi,dC⟩,dn⟩)).word.reachable.trans e.reachable.symm)
    have hm := SimpleGraph.ConnectedComponent.sound hr
    have hb : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) bC)=bC := BandTrees.root_mem _ _ _ _
    have hd' : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) dC)=dC := BandTrees.root_mem _ _ _ _
    exact hb.symm.trans (hm.trans hd')
  subst dC
  have hN : bn=dn := Subtype.ext (Subtype.ext (hNb.trans hNd.symm))
  subst dn
  rfl
end Block
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

/-- All actual processed groups that can affect this point through their
narrow-band geometry. It is not just the groups having a prescribed ID. -/
def Touch (i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) : Prop :=
  c.height ∈ BandTrees.band narrow i.1.lower₂ ∧
  ∃ w, SurvivingGroups.key (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1) w=i.2.val ∧
    ∃ path : M.Path (BandTrees.band narrow i.1.lower₂) c.column (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point.column,
      path.length c.height (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point.height≤4*R
noncomputable abbrev Hits :=
  {i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) // Touch A SA SB v hv b c i}
noncomputable instance instFintypeHits : Fintype (Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG)) :=
  Fintype.ofFinite _

variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable (hp : Tiling.Padded a₁ q c.height (a₁/10)) (hn : Tiling.Padded a₂ p c.height (a₂/10))
include hc hp hn

lemma touch_block {i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)}
    (h : Touch A SA SB v hv b c i) : i.1=b := by
  obtain ⟨w,_,path,_⟩ := h.2
  exact (b.eq_of_path i.1 c (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point hc h.1 hp hn path).symm

noncomputable def localHit (i : Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG)) :
    SurvivingGroups.Hits (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c := by
  have he := touch_block A SA SB v hv b c hc hp hn i.property
  rcases i with ⟨⟨d,j⟩,hi⟩
  dsimp only at he
  subst d
  exact ⟨j,hi.2⟩

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open MeasureTheory Parameters
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S)

lemma seed_domain (positive : Bool) (C : G.Component)
    (x : M.Point (BandTrees.band narrow G.lower) (G.root C))
    (hx : x ∈ G.admittedSeeds positive C) :
    x.height ∈ SecondaryCell.domain (G.admittedSeeds positive C) R x.column := by
  apply (SecondaryCell.mem_domain _ _).mpr
  exact ⟨x,rfl,rfl,by rw [SecondaryCell.seedDistance_seed _ hx]; norm_num [R]⟩

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_LocalPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters
variable {k : ℕ} {M : Model (k+1)} {q p L U : ℝ}
namespace Block
variable (b : Block (M := M) q p L U)
/-- At a doubly height-interior point, a narrow-band path can reach a seed
only in this very processed broad/component/narrow block. -/
lemma eq_of_path_small (d : Block (M := M) q p L U)
    (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
    (e : M.Point (BandTrees.band broad d.lower) (BandTrees.root M broad d.lower d.1.2))
    (hc : c.height ∈ BandTrees.band narrow b.lower₂)
    (hd : c.height ∈ BandTrees.band narrow d.lower₂)
    {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
    (hp : Tiling.Padded a₁ q c.height ρ)
    (hn : Tiling.Padded a₂ p c.height τ)
    (path : M.Path (BandTrees.band narrow d.lower₂) c.column e.column) : b=d := by
  have hNb : b.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 hτ hn (b.narrow_eq ▸ hc)
  have hNd : d.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 hτ hn (d.narrow_eq ▸ hd)
  have hBb : b.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 hρ hp (b.broad_eq ▸ c.inBand)
  have hBd : d.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 hρ hp (d.broad_eq ▸ d.sub hd)
  have hB : b.1.1=d.1.1 := Subtype.ext (hBb.trans hBd.symm)
  rcases b with ⟨⟨bi,bC⟩,bn⟩
  rcases d with ⟨⟨di,dC⟩,dn⟩
  dsimp only at hB
  subst di
  have hC : bC=dC := by
    have hr := c.reachable.trans ((path.widen (Block.sub ⟨⟨bi,dC⟩,dn⟩)).word.reachable.trans e.reachable.symm)
    have hm := SimpleGraph.ConnectedComponent.sound hr
    have hb : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) bC)=bC := BandTrees.root_mem _ _ _ _
    have hd' : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) dC)=dC := BandTrees.root_mem _ _ _ _
    exact hb.symm.trans (hm.trans hd')
  subst dC
  have hN : bn=dn := Subtype.ext (Subtype.ext (hNb.trans hNd.symm))
  subst dn
  rfl
end Block
end PlanarL1.Columns.Model.RetainedSelection

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
variable (hp : Tiling.Padded a₁ q c.height ρ) (hn : Tiling.Padded a₂ p c.height τ)
include hc hρ hτ hp hn

lemma touch_block_small {i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)}
    (h : Touch A SA SB v hv b c i) : i.1=b := by
  obtain ⟨w,_,path,_⟩ := h.2
  exact (b.eq_of_path_small i.1 c (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point hc h.1 hρ hτ hp hn path).symm

noncomputable def localHit_small (i : Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG)) :
    SurvivingGroups.Hits (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c := by
  have he := touch_block_small A SA SB v hv b c hc hρ hτ hp hn i.property
  rcases i with ⟨⟨d,j⟩,hi⟩
  dsimp only at he
  subst d
  exact ⟨j,hi.2⟩

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Interpolation
/-- A local finite atom expansion, including its proved one-coordinate tests.
This is proof data for an actual named field, not a substitute for a chart. -/
structure LocalList {X W : Type*} [Fintype W] (old : X → ℝ)
    (F : W → X → NamedValue) (x : X) (e b : ℝ) where
  names : Finset ℕ
  atom : W → ℕ → X → ℝ
  zero : ∀ w z, atom w 0 z=old z
  selected : ∀ w z, (F w z).name∈names ∧ (F w z).value=atom w (F w z).name z
  field_variation : ∀ w z, |(F w x).value-(F w z).value|≤e
  atom_variation : ∀ w i z, |atom w i z-atom w i x|≤e
  pair_test : ∀ i∈names, ∀ j∈names, i≠j →
    FiniteRandom.prob (fun w => |atom w i x-atom w j x|≤2*e)≤b
  constant_test : ∀ i∈names, i≠0 → ∀ c : ℝ,
    FiniteRandom.prob (fun w => |atom w i x-c|≤2*e)≤b

noncomputable def oldLocalList {X W : Type*} [Fintype W] (old : X → ℝ)
    (x : X) {e b : ℝ} (ho : ∀ z, |old x-old z|≤e) :
    LocalList old (fun (_ : W) z => ⟨0,old z⟩) x e b where
  names := {0}
  atom _ _ z := old z
  zero _ _ := rfl
  selected _ _ := ⟨Finset.mem_singleton_self _,rfl⟩
  field_variation _ z := ho z
  atom_variation _ _ z := (abs_sub_comm _ _).trans_le (ho z)
  pair_test _i hi _j hj hn := False.elim (hn ((Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm))
  constant_test _i hi hn := False.elim (hn (Finset.mem_singleton.mp hi))

end PlanarL1.Interpolation

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_FamilyPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Parameters
open scoped NNReal
noncomputable def secondaryK : ℝ≥0 := max 5 ⟨3/(9*a₂/100),by norm_num [a₂]⟩
noncomputable def secondaryQ : ℝ := zetaB*(EB/8)/20
noncomputable def secondaryRadius : ℝ := zetaB*(EB/8)/1000
noncomputable def secondaryN : ℕ := 6*(⌈15/zetaB⌉₊+3+1)+3
noncomputable def secondaryTestLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (4*(secondaryK:ℝ)*ρ+secondaryQ/m)/secondaryQ+(4*(secondaryK:ℝ)*ρ+EB/m)/EB
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB lam Ω μ}
variable (G : SecondaryGeometry.Group A S) (positive : Bool) (C : G.Component)
variable (hC : (G.admittedSeeds positive C).Nonempty) {m : ℕ} (hm : 0  <  m)
abbrev Offset := Point.RadialTree.GridSample (n := k+1) (G.tree C).depthCap m × Fin (m+1) × Fin (m+1)
noncomputable def sampledStep (w : Offset G C (m := m)) :=
  G.step positive C hC ((G.tree C).gridNoise _ m w.1) ((G.tree C).gridNoise_bounds _ _ hm w.1)
    (EB/m*w.2.1.val) (EB/m*w.2.2.val) (offset_bound hm _) (offset_bound hm _)

variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0 ≤ ρ)
abbrev Ball := {z : M.Point Set.univ A.root // dist x z ≤ ρ}
noncomputable def ballCenter : Ball x (ρ := ρ) := ⟨x,by simpa using hρ⟩
variable (hBand : ∀ z : Ball x (ρ := ρ), z.val.height∈G.data.band)
noncomputable def oldOnBall (z : Ball x (ρ := ρ)) : ℝ :=
  (G.comparison positive).value z.val.column ⟨z.val.height,hBand z⟩
noncomputable def sampledOnBall (w : Offset G C (m := m)) (z : Ball x (ρ := ρ)) : NamedValue :=
  (G.sampledStep positive C hC hm w).fullNamed z.val.column ⟨z.val.height,hBand z⟩

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Interpolation
noncomputable def scaleNamed (c : ℝ) (a : NamedValue) : NamedValue := ⟨a.name,c*a.value⟩
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters PlanarL1.Interpolation
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
abbrev Coordinate := Σ i, (G i).Component
abbrev Offsets (m : ℕ) := ∀ u : Coordinate G, ComponentSample G u.1 u.2 m
noncomputable instance instFintypeCoordinate : Fintype (Coordinate G) := Fintype.ofFinite _
variable (o : Fin (S.count+1) → Bool) (c : I → Bool) {m : ℕ}
noncomputable def flatSample (w : Offsets G m) : Sample G m := (o,c,fun i C => w ⟨i,C⟩)
noncomputable def fixedSample : Sample G m := flatSample G o c (Classical.arbitrary _)
noncomputable def slot (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))) :
    Acting G (fixedSample G o c (m := m)) a := (Fintype.equivFin _).symm j
noncomputable def coord (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))) :
    Coordinate G := (slot G o c (m := m) a j).val

lemma coord_index (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))) :
    (G (coord G o c (m := m) a j).1).index=a := (slot G o c (m := m) a j).property.1
lemma slot_band (a : Fin (S.count+1)) (j : Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a)))
    (H : (S.chart a).band) : H.val∈(G (coord G o c (m := m) a j).1).data.band := by
  change H.val∈(S.chart (G (coord G o c (m := m) a j).1).index).band
  rw [coord_index]
  exact H.property

end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Columns.Model.SecondaryGeometry
open MeasureTheory Parameters PlanarL1.Interpolation FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB Group.lam Ω μ}
variable {I : Type*} [Fintype I] (G : I → Group A S)
variable (o : Fin (S.count+1) → Bool) (c : I → Bool) {m : ℕ}
variable (a : Fin (S.count+1)) (x : M.Point Set.univ A.root) {ρ : ℝ}
abbrev Slot := Fin (Fintype.card (Acting G (fixedSample G o c (m := m)) a))
variable (hBand : ∀ z : Group.Ball x (ρ := ρ), z.val.height∈(S.chart a).band)
noncomputable def ballOld (z : Group.Ball x (ρ := ρ)) : ℝ :=
  ((S.chart a).comparison Group.lam Group.lam_bound (o a)).value z.val.column ⟨z.val.height,hBand z⟩
include hBand in
lemma ball_slot_band (j : Slot G o c a (m := m)) (z : Group.Ball x (ρ := ρ)) :
    z.val.height∈(G (coord G o c (m := m) a j).1).data.band :=
  slot_band G o c (m := m) a j ⟨z.val.height,hBand z⟩
noncomputable def ballFamily (hm : 0 < m) (j : Slot G o c a (m := m))
    (w : ComponentSample G (coord G o c (m := m) a j).1 (coord G o c (m := m) a j).2 m) (z : Group.Ball x (ρ := ρ)) : NamedValue :=
  (G (coord G o c (m := m) a j).1).sampledOnBall (o a) (coord G o c (m := m) a j).2
    (slot G o c (m := m) a j).property.2.2 hm x (ball_slot_band G o c (m := m) a x hBand j) w z
noncomputable def wholeBallSlots : Finset (Slot G o c a (m := m)) := Finset.univ.filter fun j =>
  ∀ z : Group.Ball x (ρ := ρ), z.val.height∈SecondaryCell.domain
    ((G (coord G o c (m := m) a j).1).admittedSeeds (o a) (coord G o c (m := m) a j).2) R z.val.column

end PlanarL1.Columns.Model.SecondaryGeometry

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
variable (hp : Tiling.Padded a₁ q c.height ρ) (hn : Tiling.Padded a₂ p c.height τ)
variable {m : ℕ} (omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m)
variable (a : Fin (SB.count+1))

noncomputable def centerActs : Finset (Acting (group A SA SB v hv) omega a) :=
  Finset.univ.filter fun u => c.height ∈ SecondaryCell.domain
    ((group A SA SB v hv u.val.1).admittedSeeds (omega.1 a) u.val.2) R c.column

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Parameters
open scoped NNReal
noncomputable def mainK : ℝ≥0 := max 1 ⟨3/(9*a₁/100),by norm_num [a₁]⟩
noncomputable def mainQ : ℝ := zetaA*(EA/8)/20
noncomputable def mainRadius : ℝ := zetaA*(EA/8)/1000
noncomputable def mainN : ℕ := 6*(⌈15/zetaA⌉₊+3+1)+2
noncomputable def mainTestLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (4*(mainK:ℝ)*ρ+mainQ/m)/mainQ+(4*(mainK:ℝ)*ρ+EA/m)/EA
noncomputable def mainLoss (ρ : ℝ) (m : ℕ) : ℝ := (mainN:ℝ)^2*mainTestLoss ρ m
noncomputable def secondaryLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ)^2*secondaryTestLoss ρ m
noncomputable def persistenceRadius : ℝ :=
  min (EA/20) (min mainRadius (min ((199/18000:ℝ)*R) secondaryRadius))
end PlanarL1.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_SelectedGain
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Columns.Model.SecondaryGeometry.Group
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : Ambient M} {S : BState M kappaB (⟨lambda,by norm_num [lambda,R]⟩) Ω μ}
variable (G : SecondaryGeometry.Group A S)

noncomputable def componentOf (w : M.Point G.broad G.broad_root) : G.Component :=
  (M.activeGraph (BandTrees.band narrow G.lower)).connectedComponentMk w.column

noncomputable def endpoint (w : M.Point G.broad G.broad_root) (hw : w ∈ G.seeds) :
    M.Point (BandTrees.band narrow G.lower) (G.root (G.componentOf w)) where
  column := w.column
  height := w.height
  inBand := G.height w hw
  reachable := (G.componentOf w).reachable_of_mem_supp (BandTrees.root_mem _ _ _ _) rfl

end PlanarL1.Columns.Model.SecondaryGeometry.Group

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry VertexTests
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}

variable (w : Endpoint A SA SB v L U hv q p phaseD phaseG)

noncomputable def selectedComponent :=
  (group A SA SB v hv (groupOf A SA SB v hv w)).componentOf (rawSeed A SA SB v hv w).point
noncomputable def selectedPoint :=
  (group A SA SB v hv (groupOf A SA SB v hv w)).endpoint (rawSeed A SA SB v hv w).point
    (groupOf_seed A SA SB v hv w)

variable {y : V}
variable (hi : VertexBands.Interior A v (hv := hv) q p phaseD phaseG y)
noncomputable def blockFor : Block (M := M) q p L U :=
  ⟨VertexBands.bandComponent A v L U hv q y,
    ⟨⟨Tiling.index a₂ p (v y).height,
      (Tiling.mem_processed interpolationB.2.1 p L U _).mpr
        ⟨(v y).height,Tiling.mem_band_index interpolationB.2.1 p _,hv y⟩⟩,
      hi.narrow_sub A v⟩⟩

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Columns.Model
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace BData
variable {A : Ambient M} (H : A.History (R/200)) (region : Set (M.Point Set.univ A.root))
variable (hcross : ∀ j, 10≤(R/200)*H.radius j)
noncomputable def normalizedIncrement (D : BData M) (e : Bool) : M.Field D.band 5 :=
  D.auxiliaryField (D.incrementAuxiliary H 1 region e (by norm_num [R])
    (by norm_num [R]) (by norm_num) (by simpa using hcross))
    SecondaryGeometry.Group.lam SecondaryGeometry.Group.lam_bound
end BData

namespace IncrementStep
variable (A : Ambient M) (S : BState M kappaB SecondaryGeometry.Group.lam Ω μ)
variable (hist : Fin (S.count+1) → A.History (R/200))
variable (hcross : ∀ a j, 10≤(R/200)*(hist a).radius j)
variable (hrec : ∀ a, (S.chart a).Recorded (hist a) (by norm_num [R]) (by norm_num [R]))

noncomputable def update (sign : Fin (S.count+1) → Bool) :
    BState M kappaB SecondaryGeometry.Group.lam Ω μ :=
  S.increment (r := 1) A hist sign (by norm_num [R]) (by norm_num [R]) (by norm_num)
    (by simpa using hcross) hrec verticalB.1 (by norm_num [kappaB,a₂])
    SecondaryGeometry.Group.lam_bound (by change kappaB*lambda*10≤1/8; norm_num [kappaB,a₂,lambda,R])

end IncrementStep
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Parameters
noncomputable def secondaryChance : ℝ := 1/(2:ℝ)^(Columns.Model.SurvivingGroups.packBound+2)
end PlanarL1.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_CoupledState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Parameters
noncomputable def heightLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (2*ρ+2*a₁/m)/a₁+(2*ρ+2*a₂/m)/a₂
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.VertexBands
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {L U : ℝ}

def HeightPadded {m : ℕ} (c : Choices m L U M) (H ρ : ℝ) : Prop :=
  Tiling.Padded a₁ (shift m a₁ c.1.1) H ρ ∧
  Tiling.Padded a₂ (shift m a₂ c.1.2) H ρ

end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}

/-- The two literal cut/chart systems together with every B chart's recorded
increment history. The radius bound is an invariant, not a separation promise. -/
structure CoupledState (A : Ambient M) (Ω Ξ : Type*) [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (t : ℝ) where
  left : OrdinaryState M kappaA Ω μ
  right : BState M kappaB SecondaryGeometry.Group.lam Ξ ν
  histories : BState.Histories A (c := R/200) (by norm_num [R]) (by norm_num [R]) right t

namespace CoupledState
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
noncomputable def lift : CoupledState A (Ω × Bool) (Ξ × Bool)
    (μ.prod Threshold.fair) (ν.prod Threshold.fair) t where
  left := S.left.lift
  right := S.right.lift
  histories := S.histories.lift
noncomputable def weaken {s : ℝ} (h : s≤t) : CoupledState A Ω Ξ μ ν s where
  left := S.left
  right := S.right
  histories := S.histories.weaken h
noncomputable def dilate {q : ℝ} (hq : 0<q) :
    CoupledState (A.dilate hq) Ω Ξ (ENNReal.ofReal q • μ) (ENNReal.ofReal q • ν) (q*t) where
  left := S.left.dilate hq
  right := S.right.dilate hq
  histories := S.histories.dilate hq

variable {V : Type*} (v : V → M.Point Set.univ A.root)
def Successful (b : ℝ) (x y : V) : Prop :=
  b≤S.left.sets.separation (v x).column (v x).height (v y).column (v y).height ∨
  b≤S.right.sets.separation (v x).column (v x).height (v y).column (v y).height ∨
  PairGeometry.Certificate A S.left v (x := x) (y := y) b
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable (ht : 1≤t) (hgap : 10≤(R/200)*t)

include hgap in
lemma cross (a : Fin (S.right.count+1)) (i : Fin ((S.histories.history a).count)) :
    10≤(R/200)*(S.histories.history a).radius i :=
  hgap.trans (mul_le_mul_of_nonneg_left (S.histories.older a i) (by norm_num [R]))

abbrev Next := CoupledState A (Ω × Bool) (Ξ × Bool)
    (μ.prod Threshold.fair) (ν.prod Threshold.fair) 1

noncomputable def unchanged : Next (A := A) (μ := μ) (ν := ν) := (S.weaken ht).lift

variable [SFinite μ] [SFinite ν]
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m)

noncomputable def main (omega : MainFamily.Sample phaseD m) : Next (A := A) (μ := μ) (ν := ν) where
  left := MainFamily.result A S.left phaseD hm omega
  right := S.right.lift
  histories := (S.histories.weaken ht).lift

variable [Fintype V] (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
noncomputable def groups := RetainedSelection.group A S.left S.right v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)

noncomputable def secondary (omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m) :
    Next (A := A) (μ := μ) (ν := ν) where
  left := S.left.lift
  right := SecondaryGeometry.result (S.groups v hv phaseD p phaseG) hm omega
  histories := BState.SecondaryLayer.histories A (by norm_num [R]) (by norm_num [R])
    (SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega) (S.histories.weaken ht)

noncomputable def increment (sign : Fin (S.right.count+1) → Bool) : Next (A := A) (μ := μ) (ν := ν) where
  left := S.left.lift
  right := (IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).lift
  histories := (S.histories.increment sign (by norm_num : (0:ℝ)<1) le_rfl ht (by simpa using S.cross hgap)
    verticalB.1 (by norm_num [kappaB,a₂]) Group.lam_bound
    (by change kappaB*lambda*10≤1/8; norm_num [kappaB,a₂,lambda,R])).lift

noncomputable def branches : Fin 4 → Execution (Next (A := A) (μ := μ) (ν := ν)) :=
  ![.pure (S.unchanged ht),
    Execution.uniform.bind (fun omega => .pure (S.main ht phaseD hm omega)),
    Execution.uniform.bind (fun omega => .pure (S.secondary ht v hv phaseD hm p phaseG omega)),
    Execution.uniform.bind (fun sign => .pure (S.increment ht hgap sign))]
noncomputable def modes : Execution (Next (A := A) (μ := μ) (ν := ν)) :=
  .choose 3 (S.branches ht hgap v hv phaseD hm p phaseG)

noncomputable def step : Execution (Next (A := A) (μ := μ) (ν := ν)) :=
  (geometricExecution m L U M).bind (fun c =>
    S.modes ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2))

end PlanarL1.Columns.Model.CoupledState

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Movement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.Execution
variable {α β : Type*}
def Holds : Execution α → (α → Prop) → Prop
  | .pure x, P => P x
  | .choose _ E, P => ∀ i, Holds (E i) P
end PlanarL1.Execution

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace CoupledState
open Parameters SecondaryGeometry VertexBands
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable {t' : ℝ}
def Moves (T : CoupledState A (Ω × Bool) (Ξ × Bool) (μ.prod Threshold.fair) (ν.prod Threshold.fair) t') (B : ℝ) : Prop :=
  (∀ i H, Integrable (fun w => (T.left.sets.activity w).indicator i H-(S.left.lift.sets.activity w).indicator i H) (μ.prod Threshold.fair)) ∧
  (∀ i H, Integrable (fun w => (T.right.sets.activity w).indicator i H-(S.right.lift.sets.activity w).indicator i H) (ν.prod Threshold.fair)) ∧
  (∀ i H, S.left.lift.sets.movement T.left.sets i H ≤ B) ∧
  (∀ i H, S.right.lift.sets.movement T.right.sets i H ≤ B)

end CoupledState
end PlanarL1.Columns.Model

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Persistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry FiniteRandom
open scoped NNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0 ≤ ρ)
variable (hp : Tiling.Padded a₁ q x.height ρ) (hn : Tiling.Padded a₂ p x.height ρ)
variable (a : Fin (SB.count+1)) (hold : A.Common SB.name x ρ a)
variable (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
variable {m : ℕ} (hm : 0 < m)
noncomputable local instance instFintypeOffsetsGroupIndexGroup : Fintype (Offsets (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m) := Fintype.ofFinite _
noncomputable local instance instFintypeForallForallComponentSampleGroupIndexGroup : Fintype (∀ i C, ComponentSample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) i C m) := Fintype.ofFinite _

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Parameters
noncomputable def persistenceLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  heightLoss ρ m+(mainLoss ρ m+secondaryLoss ρ m)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)

def Coherent (x : M.Point Set.univ A.root) (ρ : ℝ) : Prop :=
  ∀ z : M.Point Set.univ A.root, dist x z ≤ ρ →
    S.left.name z.column z.height=S.left.name x.column x.height ∧
    S.right.name z.column z.height=S.right.name x.column x.height

end PlanarL1.Columns.Model.CoupledState

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_StepSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Parameters
noncomputable def successGain : ℝ := min Columns.Model.VertexTests.cutoffGain
  (min (kappaA*j/4) (min (kappaA*EA) (min (kappaB*R/50) (kappaB*lambda*R/50))))
noncomputable def successChance : ℝ := secondaryChance/16
end PlanarL1.Parameters

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_CutExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M}
namespace SetSystem
local instance instMeasurableSpaceSetFinHAddNatOfNat : MeasurableSpace (Set (Fin (k+1))) := ⊤
variable [Fintype V] (S : SetSystem M Ω μ) (v : V → M.Point Set.univ A.root)
noncomputable def refinedBinary : FiniteL1.BinarySystem (V := V)
    (μ.prod (Measure.count : Measure (Set (Fin (k+1))))) where
  active w x := (S.activity w.1).active (v x).column (v x).height ∧ w.2=(S.activity w.1).component (v x).column
  measurable x := by
    have hm : Measurable (fun w : Ω × Set (Fin (k+1)) => (S.activity w.1).vector (v x).column (v x).height w.2) :=
      measurable_from_prod_countable_left (fun c => S.measurable_vector (v x).column (v x).height c)
    convert measurableSet_eq_fun hm (measurable_const : Measurable (fun _ : Ω × Set (Fin (k+1)) => (1:ℝ))) using 1
    all_goals try with_reducible_and_instances rfl
    ext w
    simp [Activity.vector]
  integrable x y := by
    convert (S.integrable_coordinateDifference (Classical.choice ((v x).paths_nonempty (v y))) (v x).height (v y).height).abs using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hx : (S.activity w.1).active (v x).column (v x).height ∧ w.2=(S.activity w.1).component (v x).column <;>
      by_cases hy : (S.activity w.1).active (v y).column (v y).height ∧ w.2=(S.activity w.1).component (v y).column <;>
      simp [SetSystem.coordinateDifference,Activity.vector,hx,hy]
noncomputable def cuts : FiniteL1.CutFamily V := FiniteL1.CutFamily.ofBinary (S.refinedBinary v)
end SetSystem
namespace CoupledState
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {t : ℝ} (S : CoupledState A Ω Ξ μ ν t) (v : V → M.Point Set.univ A.root)
noncomputable def cuts : FiniteL1.CutFamily V := (S.left.sets.cuts v).add (S.right.sets.cuts v)
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Threshold
open MeasureTheory
instance labelMeasure_sfinite : SFinite labelMeasure := by
  rw [labelMeasure_eq]
  infer_instance
end PlanarL1.Threshold

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters

/-- A state of the actual construction in its current physical units. Both
label spaces are enlarged at every step, even in the no-change mode. -/
structure World (k : ℕ) (V : Type*) (Q : ℝ) where
  model : Model (k+1)
  ambient : Ambient model
  vertex : V → model.Point Set.univ ambient.root
  sample : Type
  [measurable : MeasurableSpace sample]
  measure : Measure sample
  [sfinite : SFinite measure]
  state : CoupledState ambient sample sample measure measure Q

namespace World
attribute [instance] measurable sfinite
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (hQ : 0 < Q) (h1 : 1 ≤ Q) (hgap : 10 ≤ (R/200)*Q)
variable (W : World k V Q)
noncomputable def heightBound : ℝ := ∑ x, |(W.vertex x).height|
lemma height_bounds (x : V) : (W.vertex x).height ∈ Set.Icc (-W.heightBound) W.heightBound := by
  have hh : |(W.vertex x).height| ≤ W.heightBound :=
    Finset.single_le_sum (f := fun y => |(W.vertex y).height|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)
  exact abs_le.mp hh

noncomputable def after (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) : World k V Q where
  model := W.model.dilate Q hQ
  ambient := W.ambient.dilate hQ
  vertex x := W.ambient.scaleEquiv hQ (W.vertex x)
  sample := W.sample × Bool
  measure := ENNReal.ofReal Q • (W.measure.prod Threshold.fair)
  state := (T.dilate hQ).weaken (by simp)

noncomputable def step {m : ℕ} (hm : 0 < m) : Execution (World k V Q) :=
  (W.state.step h1 hgap W.vertex W.height_bounds hm).bind (fun T => .pure (W.after hQ T))

def Coherent (x : V) (ρ : ℝ) : Prop := W.state.Coherent (W.vertex x) ρ
def Successful (b : ℝ) (x y : V) : Prop := W.state.Successful W.vertex b x y
noncomputable def distance (x y : V) : ℝ := dist (W.vertex x) (W.vertex y)
noncomputable def cuts : FiniteL1.CutFamily V := W.state.cuts W.vertex

noncomputable def initial {M : Model (k+1)} (A : Ambient M) (v : V → M.Point Set.univ A.root) : World k V Q where
  model := M
  ambient := A
  vertex := v
  sample := Bool × ℝ
  measure := Threshold.labelMeasure
  state := {
    left := OrdinaryState.initial M kappaA
    right := BState.initial M kappaB SecondaryGeometry.Group.lam
    histories := BState.Histories.ofOrdinary (A := A) (hc := by norm_num [R]) (hcr := by norm_num [R]) (OrdinaryState.initial M kappaB) }
end World
end PlanarL1.Columns.Model

end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Drawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Topology
open Set Metric

/-- The literal topological drawing, with its coordinates identified with the
complex plane. No polygonal or combinatorial planarity assumption is added. -/
structure Drawing {V : Type} (G : SimpleGraph V) where
  point : V → ℂ
  point_injective : Function.Injective point
  edge : ∀ u v, G.Adj u v → Path (point u) (point v)
  edge_injective : ∀ u v h, Function.Injective (edge u v h)
  interior_avoid : ∀ u v h (t : unitInterval) w,
    0<(t:ℝ) → (t:ℝ)<1 → edge u v h t ≠ point w
  interior_disjoint : ∀ u v h x y k (s t : unitInterval),
    0<(s:ℝ) → (s:ℝ)<1 → 0<(t:ℝ) → (t:ℝ)<1 →
    edge u v h s=edge x y k t → (u=x ∧ v=y) ∨ (u=y ∧ v=x)

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

/-- Truncate one actual drawn edge outside disjoint small vertex disks.
The middle arc stays outside every disk, with equality only at its own ends. -/
structure EdgeTrim (r : ℝ) (d : G.Dart) where
  first : unitInterval
  last : unitInterval
  first_pos : 0<(first:ℝ)
  first_lt : (first:ℝ)<1/3
  last_gt : (2/3:ℝ)<(last:ℝ)
  last_lt_one : (last:ℝ)<1
  first_sphere : dist (D.edge d.fst d.snd d.adj first) (D.point d.fst)=r
  last_sphere : dist (D.edge d.fst d.snd d.adj last) (D.point d.snd)=r
  after_first : ∀ t : unitInterval, first<t →
    r<dist (D.edge d.fst d.snd d.adj t) (D.point d.fst)
  before_last : ∀ t : unitInterval, t<last →
    r<dist (D.edge d.fst d.snd d.adj t) (D.point d.snd)

end Drawing

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite chain of straight segments contained in a specified set. -/
def PolygonallyJoined (S : Set E) (x y : E) : Prop :=
  Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ S) x y

end PlanarL1.Topology


namespace PlanarL1.Topology
open Set Metric

/-- Choosing only the forward dart avoids treating the two independently
supplied oriented parametrizations as one geometric edge. -/
def ForwardDart {V : Type} [LinearOrder V] (G : SimpleGraph V) :=
  {d : G.Dart // d.fst<d.snd}

namespace Drawing
variable {V : Type} {G : SimpleGraph V} (D : Drawing G)

namespace EdgeTrim
variable {D} {r : ℝ} {d : G.Dart} (T : D.EdgeTrim r d)
noncomputable def middle : Path (D.edge d.fst d.snd d.adj T.first)
    (D.edge d.fst d.snd d.adj T.last) :=
  (D.edge d.fst d.snd d.adj).subpath T.first T.last

end EdgeTrim

end Drawing
end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_HeightTree
attribute [-instance] _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BState.SecondaryLayer.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeMainIndex _root_.OAI.PlanarL1.Columns.Model.BandTrees.instFintypeRadialIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeBandComponent _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeCellIndex _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeKept _root_.OAI.PlanarL1.Columns.Model.MainFamily.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.MainFamily.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.OrdinaryState.MainBatch.instFintypeNewIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeBlock _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeGroupIndex _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.RetainedSelection.instFintypeSubtypeMemFinsetEndpoint _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeActing _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeCoordinate _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instFintypeSample _root_.OAI.PlanarL1.Columns.Model.SecondaryGeometry.instNonemptySample _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeHits _root_.OAI.PlanarL1.Columns.Model.SurvivingGroups.instFintypeSubtypeKeyMemFinsetGroupIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1

/-- A rooted incidence tree with a nondecreasing metric height. Unlike the
shortest-path tree, added terminal branches are permitted to have zero length.
Termination follows the incidence tree, not strict metric height. -/
structure HeightTree (V : Type*) where
  root : V
  parent : V → V
  at_root : parent root = root
  wf : WellFounded (fun u v => v ≠ root ∧ u = parent v)
  height : V → ℝ
  height_mono : ∀ v, height (parent v) ≤ height v

namespace HeightTree
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : HeightTree V)

abbrev Step (u v : V) : Prop := v ≠ T.root ∧ u = T.parent v
abbrev Ancestor (u v : V) : Prop := Relation.ReflTransGen T.Step u v

lemma ancestor_height {u v : V} (h : T.Ancestor u v) : T.height u ≤ T.height v := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (h.2 ▸ T.height_mono _)

/-- McShane cones over the finite ancestral chain. The recursive minimum is
used instead of linear interpolation, so zero-length incidences need no division. -/
noncomputable def profile (q : V → ℝ) (v : V) : ℝ → ℝ :=
  T.wf.fix (fun v rec => if h : v = T.root then fun H => q v + |H-T.height v|
    else fun H => min (rec (T.parent v) ⟨h,rfl⟩ H) (q v + |H-T.height v|)) v

/-- Discrete one-Lipschitz data along the actual tree edges. -/
def Compatible (q : V → ℝ) : Prop :=
  ∀ v, |q v-q (T.parent v)| ≤ T.height v-T.height (T.parent v)

lemma root_ancestor (v : V) : T.Ancestor T.root v := by
  induction v using T.wf.induction with
  | h v ih =>
    by_cases hv : v = T.root
    · subst v; exact Relation.ReflTransGen.refl
    · exact (ih (T.parent v) ⟨hv,rfl⟩).tail ⟨hv,rfl⟩

noncomputable def depth (v : V) : ℕ :=
  T.wf.fix (fun v rec => if h : v = T.root then 0
    else rec (T.parent v) ⟨h,rfl⟩ + 1) v

lemma depth_eq (v : V) :
    T.depth v = if _h : v = T.root then 0 else T.depth (T.parent v)+1 := by
  rw [depth,WellFounded.fix_eq]
  rfl

lemma step_depth {u v : V} (h : T.Step u v) : T.depth u < T.depth v := by
  rw [T.depth_eq v,dite_eq_right h.1,← h.2]
  omega

def IsLeaf (v : V) : Prop := ∀ w, ¬T.Step v w

lemma exists_leaf [Fintype V] (v : V) : ∃ w, T.Ancestor v w ∧ T.IsLeaf w := by
  classical
  let S := Finset.univ.filter (T.Ancestor v)
  obtain ⟨w,hw,hmax⟩ := Finset.exists_max_image S T.depth ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ v,Relation.ReflTransGen.refl⟩⟩
  have hw' : T.Ancestor v w := (Finset.mem_filter.mp hw).2
  refine ⟨w,hw',fun u hu => ?_⟩
  have hu' : u∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ u,hw'.tail hu⟩
  exact (not_lt_of_ge (hmax u hu')) (T.step_depth hu)

noncomputable def leafAbove [Fintype V] (v : V) : {w : V // T.IsLeaf w} :=
  ⟨(T.exists_leaf v).choose,(T.exists_leaf v).choose_spec.2⟩

end HeightTree
end PlanarL1

namespace PlanarL1.HeightTree
open Set Columns
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {n : ℕ} (T : HeightTree V)

/-- Adjacent copies in the cyclic contour of an ancestral subtree. -/
def prefixGraph (leaf : Fin n → V) (a : V) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ Consecutive i j ∧ T.Ancestor a (leaf i) ∧ T.Ancestor a (leaf j)
  symm := ⟨by
    rintro i j ⟨hij,hc,hi,hj⟩
    refine ⟨hij.symm,?_,hj,hi⟩
    rcases hc with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The combinatorial output of a planar tree contour construction. No metric
realization or metric estimates are part of this data. -/
structure Layout (n : ℕ) where
  leaf : Fin n → V
  isLeaf : ∀ i, T.IsLeaf (leaf i)
  injective : Function.Injective leaf
  covers : ∀ v, T.IsLeaf v → ∃ i, leaf i = v
  prefix_connected : ∀ a i j, T.Ancestor a (leaf i) → T.Ancestor a (leaf j) →
    (T.prefixGraph leaf a).Reachable i j
  pair : SimpleGraph (Fin n)
  noncrossing : ColumnOrder.Noncrossing pair
  paired_height : ∀ i j, pair.Adj i j → T.height (leaf i)=T.height (leaf j)
  matching : ∀ i j k, pair.Adj i j → pair.Adj i k → j=k

namespace Layout
variable {T} (L : T.Layout n)

noncomputable def heights (i j : Fin n) : Set ℝ :=
  (⋃ a : V, if i ≠ j ∧ Consecutive i j ∧ T.Ancestor a (L.leaf i) ∧ T.Ancestor a (L.leaf j)
    then Icc (T.height T.root) (T.height a) else ∅) ∪
  (if L.pair.Adj i j then {T.height (L.leaf i)} else ∅)

omit [Fintype V] in
lemma mem_heights (i j : Fin n) (H : ℝ) : H ∈ L.heights i j ↔
    (∃ a, (T.prefixGraph L.leaf a).Adj i j ∧ T.height T.root ≤ H ∧ H ≤ T.height a) ∨
    (L.pair.Adj i j ∧ H=T.height (L.leaf i)) := by
  classical
  simp only [heights,mem_union,mem_iUnion,mem_ite_empty_right,mem_Icc,mem_singleton_iff,prefixGraph]

omit [Fintype V] in
lemma heights_symm (i j : Fin n) : L.heights i j=L.heights j i := by
  ext H
  simp only [mem_heights]
  constructor <;> intro h
  · rcases h with ⟨a,ha,hH⟩ | ⟨ha,rfl⟩
    · exact Or.inl ⟨a,ha.symm,hH⟩
    · exact Or.inr ⟨ha.symm,L.paired_height i j ha⟩
  · rcases h with ⟨a,ha,hH⟩ | ⟨ha,rfl⟩
    · exact Or.inl ⟨a,ha.symm,hH⟩
    · exact Or.inr ⟨ha.symm,L.paired_height j i ha⟩

lemma heights_compact (i j : Fin n) : IsCompact (L.heights i j) := by
  apply IsCompact.union
  · apply isCompact_iUnion
    intro a
    split_ifs <;> first | exact isCompact_Icc | exact isCompact_empty
  · split_ifs <;> first | exact isCompact_singleton | exact isCompact_empty

omit [Fintype V] in
lemma switch_le_tip {i j : Fin n} {H : ℝ} (h : H ∈ L.heights i j) :
    H ≤ T.height (L.leaf i) := by
  rcases (L.mem_heights i j H).mp h with ⟨a,ha,_,hH⟩ | ⟨_,rfl⟩
  · exact hH.trans (T.ancestor_height ha.2.2.1)
  · rfl

noncomputable def model : Model n where
  link := (T.prefixGraph L.leaf T.root) ⊔ L.pair
  heights := L.heights
  symm := L.heights_symm
  permitted i j H h := by
    rcases (L.mem_heights i j H).mp h with ⟨a,ha,_⟩ | ⟨ha,_⟩
    · exact Or.inl ⟨ha.1,ha.2.1,T.root_ancestor _,T.root_ancestor _⟩
    · exact Or.inr ha
  compact := L.heights_compact
  noncrossing := by
    intro a b c d hab hbc hcd h
    have hac : ¬Consecutive a c := by
      simp only [Consecutive]
      omega
    have hbd : ¬Consecutive b d := by
      simp only [Consecutive]
      omega
    rcases h.1 with ha | ha
    · exact hac ha.2.1
    · rcases h.2 with hb | hb
      · exact hbd hb.2.1
      · exact L.noncrossing a b c d hab hbc hcd ⟨ha,hb⟩
  terminal i j ha hn := by
    have hp : L.pair.Adj i j := ha.resolve_left (fun h => hn h.2.1)
    refine ⟨T.height (L.leaf i),?_,?_⟩
    · ext H
      rw [L.mem_heights]
      constructor
      · rintro (⟨a,ha,_⟩ | ⟨_,he⟩)
        · exact (hn ha.2.1).elim
        · exact he
      · intro he
        exact Or.inr ⟨hp,he⟩
    · intro k H hH
      rcases hH with hH | hH
      · exact L.switch_le_tip hH
      · rw [L.paired_height i j hp]
        exact L.switch_le_tip hH

/-- Constant-height switches connect all copies on a common root prefix. -/
noncomputable def prefixPath {a : V} {i j : Fin n}
    (p : (T.prefixGraph L.leaf a).Walk i j) {H : ℝ}
    (hlo : T.height T.root ≤ H) (hhi : H ≤ T.height a) :
    L.model.Path univ i j :=
  match p with
  | .nil => .nil _
  | .cons h p => .cons H (mem_univ H) ((L.mem_heights _ _ _).mpr (Or.inl ⟨a,h,hlo,hhi⟩))
      (prefixPath p hlo hhi)

lemma prefixPath_length {a : V} {i j : Fin n}
    (p : (T.prefixGraph L.leaf a).Walk i j) {H : ℝ}
    (hlo : T.height T.root ≤ H) (hhi : H ≤ T.height a) :
    (L.prefixPath p hlo hhi).length H H=0 := by
  induction p with
  | nil => simp only [prefixPath,Model.Path.length,sub_self,abs_zero]
  | cons h p ih => simp only [prefixPath,Model.Path.length,sub_self,abs_zero,zero_add,ih]

lemma exists_prefixPath {a : V} {i j : Fin n}
    (hi : T.Ancestor a (L.leaf i)) (hj : T.Ancestor a (L.leaf j)) {H : ℝ}
    (hlo : T.height T.root ≤ H) (hhi : H ≤ T.height a) :
    ∃ p : L.model.Path univ i j, p.length H H=0 := by
  obtain ⟨p⟩ := L.prefix_connected a i j hi hj
  exact ⟨L.prefixPath p hlo hhi,L.prefixPath_length p hlo hhi⟩

noncomputable def column (v : V) : Fin n :=
  (L.covers _ (T.leafAbove v).property).choose

noncomputable def point (v : V) : L.model.Point univ (L.column T.root) where
  column := L.column v
  height := T.height v
  inBand := mem_univ _
  reachable := by
    obtain ⟨p,_⟩ := L.exists_prefixPath (T.root_ancestor (L.leaf (L.column T.root)))
      (T.root_ancestor (L.leaf (L.column v))) le_rfl le_rfl
    exact ⟨p.word⟩

end Layout
end PlanarL1.HeightTree

namespace PlanarL1.HeightTree
open Set Columns
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {n : ℕ} {T : HeightTree V}

omit [Fintype V] in
lemma IsLeaf.ancestor_eq {v w : V} (hv : T.IsLeaf v) (h : T.Ancestor v w) : v=w := by
  induction h with
  | refl => rfl
  | @tail u w hvu huw ih => exact (hv w (ih ▸ huw)).elim

end PlanarL1.HeightTree



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Polygonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Topology
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite segment chain, represented by its value at every integer;
only the first `length + 1` values are used. -/
structure SegmentChain (S : Set E) (x y : E) (length : ℕ) where
  vertex : ℕ → E
  start : vertex 0=x
  finish : vertex length=y
  segment_mem : ∀ i, i<length → segment ℝ (vertex i) (vertex (i+1)) ⊆ S

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

def IsSimple : Prop :=
  Set.InjOn P.vertex (Set.Iic n) ∧
    ∀ i j, i<j → j<n → ∀ z,
      z ∈ segment ℝ (P.vertex i) (P.vertex (i+1)) →
      z ∈ segment ℝ (P.vertex j) (P.vertex (j+1)) →
      j=i+1 ∧ z=P.vertex j

end SegmentChain

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SegmentChain
variable {S : Set E} {x y : E} {n : ℕ} (P : SegmentChain S x y n)

/-- The finite geometric trace, including the degenerate chain's endpoint. -/
def trace : Set E := {x} ∪ ⋃ i : Fin n, segment ℝ (P.vertex i) (P.vertex (i+1))

end SegmentChain

end PlanarL1.Topology

namespace PlanarL1.Topology
open Set

/-- A literal finite polyline drawing. Simplicity is a proved property of the
finite segment chains, not an added planarity promise. -/
structure PLDrawing {V : Type} [LinearOrder V] (G : SimpleGraph V) where
  point : V → ℂ
  point_injective : Function.Injective point
  count : ForwardDart G → ℕ
  chain : ∀ d : ForwardDart G, SegmentChain Set.univ (point d.val.fst) (point d.val.snd) (count d)
  simple : ∀ d, (chain d).IsSimple
  on_vertex : ∀ d w, point w ∈ (chain d).trace → w=d.val.fst ∨ w=d.val.snd
  intersect : ∀ d e, d≠e → ∀ z, z ∈ (chain d).trace → z ∈ (chain e).trace →
    (z=point d.val.fst ∨ z=point d.val.snd) ∧ (z=point e.val.fst ∨ z=point e.val.snd)

end PlanarL1.Topology



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_TreeDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.HeightTree
open Set
attribute [local instance] Classical.propDecidable
variable {V : Type} (T : HeightTree V)

def graph : SimpleGraph V where
  Adj u v := T.Step u v ∨ T.Step v u
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h <;> exact (lt_irrefl (T.depth v)) (T.step_depth h)⟩

end PlanarL1.HeightTree



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Surgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PlanarL1.Topology
open Set

namespace PLDrawing
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def forward (u v : V) (h : G.Adj u v) : ForwardDart G := by
  classical
  exact if huv : u<v then ⟨⟨(u,v),h⟩,huv⟩ else
    ⟨⟨(v,u),h.symm⟩,lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm h.ne)⟩

noncomputable def region (u v : V) : Set ℂ := by
  classical exact if h : G.Adj u v then (P.chain (forward u v h)).trace else ∅

end PLDrawing

end PlanarL1.Topology




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Retubing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PlanarL1.Topology
open Set

variable {V : Type}

/-- Actual disjoint exterior polygonal stems, not a promised contour order. -/
structure ExteriorPorts (p target : V → ℂ) (B : Set V) (S : Set ℂ) where
  region : V → Set ℂ
  compact : ∀ w∈B, IsCompact (region w)
  start : ∀ w∈B, p w∈region w
  joined : ∀ w∈B, PolygonallyJoined (region w) (p w) (target w)
  inside : ∀ w∈B, ∀ z∈region w, z∈closure S → z=p w
  disjoint : ∀ w∈B, ∀ u∈B, w≠u → Disjoint (region w) (region u)

end PlanarL1.Topology




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Stem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PlanarL1.Topology
open Set Metric Filter

variable {V : Type} [LinearOrder V] {G : SimpleGraph V} {B : Set V}

/-- A literal finite polyline core in a bounded convex disk, with specified
leaf ports on its boundary. These data are constructed by the surgeries. -/
structure DiskCore (G : SimpleGraph V) (B : Set V) where
  drawing : PLDrawing G
  disk : Set ℂ
  center : ℂ
  convex : Convex ℝ disk
  isOpen : IsOpen disk
  bounded : Bornology.IsBounded disk
  center_mem : center∈disk
  point_mem : ∀ w, drawing.point w∈closure disk
  trace_mem : ∀ d, (drawing.chain d).trace ⊆ closure disk
  port : ∀ w∈B, drawing.point w∈frontier disk

end PlanarL1.Topology




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PlanarL1.HeightTree
open Set
variable {V : Type} (T : HeightTree V)

lemma parent_ne {v : V} (hv : v≠T.root) : T.parent v≠v := by
  intro he
  have hh := T.step_depth (show T.Step (T.parent v) v from ⟨hv,rfl⟩)
  rw [he] at hh
  exact lt_irrefl _ hh

lemma step_ne {u v : V} (h : T.Step u v) : u≠v := by
  exact h.2 ▸ T.parent_ne h.1

/-- Vertices already absorbed into the disk form a parent-closed set. -/
def ParentClosed (S : Finset V) : Prop := ∀ v∈S, T.parent v∈S

def Frontier (S : Finset V) (v : V) : Prop := v∉S ∧ T.parent v∈S

def Scope (S : Finset V) (v : V) : Prop := v∈S ∨ T.Frontier S v

lemma scope_parent {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Scope S v) : T.parent v∈S := by
  exact hv.elim (hS v) And.right

lemma child_out {S : Finset V} (hS : T.ParentClosed S) {v w : V}
    (hv : T.Frontier S v) (hw : T.Step v w) : ¬T.Scope S w := by
  intro h
  exact hv.1 (hw.2.symm ▸ T.scope_parent hS h)

variable [DecidableEq V]

lemma frontier_insert {S : Finset V} (hS : T.ParentClosed S) {v w : V} (hv : T.Frontier S v) :
    T.Frontier (insert v S) w ↔ (T.Frontier S w ∧ w≠v) ∨ T.Step v w := by
  classical
  simp only [Frontier,Finset.mem_insert,not_or] at *
  constructor
  · rintro ⟨⟨hwv,hwS⟩,hp⟩
    rcases hp with hp|hp
    · exact Or.inr ⟨fun he => by subst w; rw [T.at_root] at hp; exact hwv hp,hp.symm⟩
    · exact Or.inl ⟨⟨hwS,hp⟩,hwv⟩
  · rintro (⟨⟨hwS,hp⟩,hwv⟩|hw)
    · exact ⟨⟨hwv,hwS⟩,Or.inr hp⟩
    · exact ⟨⟨Ne.symm (T.step_ne hw),fun hwS =>
        hv.1 (hw.2.symm ▸ hS w hwS)⟩,Or.inl hw.2.symm⟩

lemma scope_insert {S : Finset V} (hS : T.ParentClosed S) {v w : V} (hv : T.Frontier S v) :
    T.Scope (insert v S) w ↔ T.Scope S w ∨ T.Step v w := by
  classical
  rw [Scope,T.frontier_insert hS hv]
  constructor
  · rintro (h|h)
    · rcases Finset.mem_insert.mp h with rfl|h
      · exact Or.inl (Or.inr hv)
      · exact Or.inl (Or.inl h)
    · exact h.elim (fun h => Or.inl (Or.inr h.1)) Or.inr
  · rintro (h|h)
    · rcases h with h|h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · by_cases he : w=v
        · exact Or.inl (Finset.mem_insert.mpr (Or.inl he))
        · exact Or.inr (Or.inl ⟨h,he⟩)
    · exact Or.inr (Or.inr h)

noncomputable def extensionMap {S : Finset V} (v : V) :
    ({u // T.Scope S u} ⊕ {w // T.Step v w}) → V := Sum.elim Subtype.val Subtype.val

omit [DecidableEq V] in
lemma extensionMap_injective {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    Function.Injective (T.extensionMap (S := S) v) := by
  intro a b he
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b =>
      change a.val=b.val at he
      exact False.elim (T.child_out hS hv b.property (he ▸ a.property))
  | inr a => cases b with
    | inl b =>
      change a.val=b.val at he
      exact False.elim (T.child_out hS hv a.property (he.symm ▸ b.property))
    | inr b => exact congrArg Sum.inr (Subtype.ext he)

noncomputable def extensionEquiv {S : Finset V} (hS : T.ParentClosed S) {v : V} (hv : T.Frontier S v) :
    ({u // T.Scope S u} ⊕ {w // T.Step v w}) ≃ {u // T.Scope (insert v S) u} :=
  Equiv.ofBijective (fun a => ⟨T.extensionMap v a,by
    apply (T.scope_insert hS hv).mpr
    cases a with
    | inl a => exact Or.inl a.property
    | inr a => exact Or.inr a.property⟩) ⟨
    fun a b h => T.extensionMap_injective hS hv (congrArg Subtype.val h),by
      intro a
      rcases (T.scope_insert hS hv).mp a.property with h|h
      · exact ⟨.inl ⟨a.val,h⟩,rfl⟩
      · exact ⟨.inr ⟨a.val,h⟩,rfl⟩⟩

end PlanarL1.HeightTree




namespace PlanarL1.Topology.PLDrawing
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (P : PLDrawing G)

def carrier (S : Set V) : Set ℂ :=
  (⋃ v : S, {P.point v.val}) ∪ ⋃ u : S, ⋃ v : S, P.region u.val v.val

end PlanarL1.Topology.PLDrawing




namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

/-- The raw unprocessed drawing is a fixed closed obstacle at each stage. -/
def outside (S : Finset V) : Set ℂ := P.carrier {v | v∉S}

/-- A partially swallowed tree, retaining real residual stems to the original
frontier vertices in the supplied polygonal drawing. -/
structure Growth (S : Finset V) where
  core : DiskCore (SimpleGraph.comap Subtype.val T.graph)
    {w : {w // T.Scope S w} | T.Frontier S w.val}
  stems : ExteriorPorts core.drawing.point (fun w => P.point w.val)
    {w : {w // T.Scope S w} | T.Frontier S w.val} core.disk
  avoid : Disjoint (closure core.disk) (outside P S)
  contact : ∀ w, T.Frontier S w.val → ∀ z∈stems.region w,
    z∈outside P S → z=P.point w.val

end PlanarL1.HeightTree




namespace PlanarL1.HeightTree
open Set
variable {V : Type} (T : HeightTree V)

lemma frontier_root_iff (v : V) : T.Frontier {T.root} v ↔ T.Step T.root v := by
  simp only [Frontier,Finset.mem_singleton,Step]
  exact and_congr_right (fun _ => eq_comm)

lemma scope_root_iff (v : V) : T.Scope {T.root} v ↔ v=T.root ∨ T.Step T.root v := by
  rw [Scope,T.frontier_root_iff]
  simp only [Finset.mem_singleton]

noncomputable def rootMap : PUnit ⊕ {w // T.Step T.root w} → V := Sum.elim (fun _ => T.root) Subtype.val

lemma rootMap_injective : Function.Injective T.rootMap := by
  intro a b he
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
    | inr b => exact False.elim (b.property.1 he.symm)
  | inr a => cases b with
    | inl b => exact False.elim (a.property.1 he)
    | inr b => exact congrArg Sum.inr (Subtype.ext he)

noncomputable def rootEquiv : (PUnit ⊕ {w // T.Step T.root w}) ≃ {w // T.Scope {T.root} w} :=
  Equiv.ofBijective (fun a => ⟨T.rootMap a,by
    apply (T.scope_root_iff _).mpr
    cases a with
    | inl a => exact Or.inl rfl
    | inr a => exact Or.inr a.property⟩) ⟨
    fun a b h => T.rootMap_injective (congrArg Subtype.val h),by
      intro a
      rcases (T.scope_root_iff _).mp a.property with h|h
      · exact ⟨.inl PUnit.unit,Subtype.ext h.symm⟩
      · exact ⟨.inr ⟨a.val,h⟩,rfl⟩⟩

end PlanarL1.HeightTree




end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.HeightTree
open Set PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] (T : HeightTree V)
  {G : SimpleGraph V} (P : PLDrawing G)

noncomputable def internal : Finset V := Finset.univ.filter (fun v => ¬T.IsLeaf v)

end PlanarL1.HeightTree




namespace PlanarL1.Topology.Drawing
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)

namespace Split
attribute [local instance] Classical.propDecidable
variable (S : Set (ForwardDart G))

abbrev Tip := S × Fin 2
abbrev Node := V ⊕ Tip S
abbrev Piece := {d : ForwardDart G // d∉S} ⊕ (S × Fin 3)

noncomputable def tipTime (k : Fin 2) : unitInterval := ⟨((k.val:ℝ)+1)/3,by
  constructor
  · positivity
  · have hk : (k.val:ℝ)<2 := by exact_mod_cast k.isLt
    linarith⟩

noncomputable def point : Node S → ℂ
  | .inl v => D.point v
  | .inr (d,k) => D.edge d.val.val.fst d.val.val.snd d.val.val.adj (tipTime k)

def meshNode (d : S) (r : Fin 4) : Node S :=
  if h0 : r.val=0 then .inl d.val.val.fst
  else if h3 : r.val=3 then .inl d.val.val.snd
  else .inr (d,⟨r.val-1,by omega⟩)

noncomputable def meshTime (r : Fin 4) : unitInterval := ⟨(r.val:ℝ)/3,by
  constructor
  · positivity
  · have hr : (r.val:ℝ)<4 := by exact_mod_cast r.isLt
    have hr' : r.val≤3 := by omega
    have hr'' : (r.val:ℝ)≤3 := by exact_mod_cast hr'
    linarith⟩

lemma mesh_point (d : S) (r : Fin 4) :
    point D S (meshNode S d r)=D.edge d.val.val.fst d.val.val.snd d.val.val.adj (meshTime r) := by
  fin_cases r <;> norm_num [meshNode,point,meshTime,tipTime]

noncomputable def label : Piece S → ForwardDart G
  | .inl d => d.val
  | .inr (d,_) => d.val

def src : Piece S → Node S
  | .inl d => .inl d.val.val.fst
  | .inr (d,k) => meshNode S d k.castSucc

def dst : Piece S → Node S
  | .inl d => .inl d.val.val.snd
  | .inr (d,k) => meshNode S d k.succ

noncomputable def first : Piece S → unitInterval
  | .inl _ => 0
  | .inr (_,k) => meshTime k.castSucc

noncomputable def last : Piece S → unitInterval
  | .inl _ => 1
  | .inr (_,k) => meshTime k.succ

lemma src_point (p : Piece S) :
    point D S (src S p)=D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj (first S p) := by
  cases p with
  | inl p => exact (Path.source _).symm
  | inr p => exact mesh_point D S p.1 p.2.castSucc

lemma dst_point (p : Piece S) :
    point D S (dst S p)=D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj (last S p) := by
  cases p with
  | inl p => exact (Path.target _).symm
  | inr p => exact mesh_point D S p.1 p.2.succ

end Split
end PlanarL1.Topology.Drawing



end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_PlanarMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PlanarL1.Topology.Drawing.Split
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
  (S : Set (ForwardDart G))

abbrev Directed := Piece S × Bool

def start (d : Directed S) : Node S := if d.2 then dst S d.1 else src S d.1

def finish (d : Directed S) : Node S := if d.2 then src S d.1 else dst S d.1

end PlanarL1.Topology.Drawing.Split




namespace PlanarL1.HeightTree
variable {V : Type} [Fintype V] (T : HeightTree V) (hroot : T.IsLeaf T.root)

noncomputable def rootLeafLayout : T.Layout 1 where
  leaf := fun _ => T.root
  isLeaf := fun _ => hroot
  injective := fun _ _ _ => Subsingleton.elim _ _
  covers := fun v _ => ⟨0,hroot.ancestor_eq (T.root_ancestor v)⟩
  prefix_connected := by
    intro a i j hi hj
    have he : i=j := Subsingleton.elim _ _
    subst j
    exact .rfl
  pair := ⊥
  noncrossing := fun _ _ _ _ _ _ _ h => h.1
  paired_height := fun _ _ h => h.elim
  matching := fun _ _ _ h => h.elim

end PlanarL1.HeightTree


end

end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Schedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PlanarL1.Parameters
open scoped NNReal
noncomputable def persistenceSlope : ℝ :=
  2/a₁+2/a₂+(mainN:ℝ)^2*(4*(mainK:ℝ)/mainQ+4*(mainK:ℝ)/EA)+
  (1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ)^2*
    (4*(secondaryK:ℝ)/secondaryQ+4*(secondaryK:ℝ)/EB)
noncomputable def persistenceCount : ℝ :=
  4+2*(mainN:ℝ)^2+2*(1+Columns.Model.SurvivingGroups.packBound*secondaryN : ℕ)^2

/-- A single universal integer spacing. It is independent of the graph, its
edge lengths, the number of scales, and every finite random grid. -/
def GoodSpacing (Q : ℝ) : Prop :=
  2 ≤ Q ∧ 10 ≤ (R/200)*Q ∧ 20/Q ≤ persistenceRadius ∧
  20*persistenceSlope/(Q-1) ≤ 1/4 ∧ 3/(Q-1) ≤ successGain/2
end PlanarL1.Parameters

end



section

namespace PlanarL1.Execution
variable {α β γ : Type*}

def iterate (F : α → Execution α) (E : Execution α) : ℕ → Execution α
  | 0 => E
  | n+1 => (iterate F E n).bind F
end PlanarL1.Execution

end



section

namespace PlanarL1.Parameters
noncomputable def targetRadius (Q : ℝ) (f n : ℕ) : ℝ := 20*Q^n/Q^f

noncomputable def survivalBudget (Q : ℝ) (t : ℕ) : ℝ :=
  Q^t*(Q*successGain-3*Q/(Q-1))+3*Q/(Q-1)
end PlanarL1.Parameters

end



section

namespace PlanarL1.Parameters.GoodSpacing
variable {Q : ℝ} (h : GoodSpacing Q)
include h
lemma pos : 0 < Q := by linarith [h.1]
lemma one : 1 ≤ Q := by linarith [h.1]
lemma gap : 10 ≤ (R/200)*Q := h.2.1
end PlanarL1.Parameters.GoodSpacing

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
noncomputable def run (n : ℕ) : Execution (World k V Q) :=
  Execution.iterate (fun Z => Z.step g.pos g.one g.gap hm) (.pure W) n

def Distances (n : ℕ) (Z : World k V Q) : Prop := ∀ x y, Z.distance x y=Q^n*W.distance x y

def TargetGood (f : ℕ) (x : V) (n : ℕ) (Z : World k V Q) : Prop :=
  W.Distances n Z ∧ Z.Coherent x (targetRadius Q f n)
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Parameters
noncomputable def scheduleGain : ℝ := successChance*successGain/8
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
noncomputable def averagedCuts (N : ℕ) : FiniteL1.CutFamily V :=
  FiniteL1.CutFamily.average (W.run g hm N) World.cuts
end PlanarL1.Columns.Model.World

end



section

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) {M : Model (k+1)} (A : Ambient M)
variable (v : V → M.Point Set.univ A.root) {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 0 < m)
noncomputable def startAt : World k V Q :=
  initial (Q := Q) (A.dilate hσ) (fun x => A.scaleEquiv hσ (v x))
noncomputable def normalizedCuts (N : ℕ) : FiniteL1.CutFamily V :=
  FiniteL1.CutFamily.scale ((Q^N*σ)⁻¹) (inv_nonneg.mpr (mul_pos (pow_pos g.pos N) hσ).le)
    ((startAt (Q := Q) A v hσ).averagedCuts g hm N)
end PlanarL1.Columns.Model.World

end



end OAI
end

section
-- module Solutions.OAIQ5_T5.PlanarL1_Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PlanarL1.HeightTree.Layout
open Columns
variable {U : Type*} [Fintype U] {T : HeightTree U} {k : ℕ}
noncomputable def ambient (L : T.Layout (k+1)) : Model.Ambient L.model where
  root := L.column T.root
  connected i := by
    obtain ⟨p,_⟩ := L.exists_prefixPath (T.root_ancestor (L.leaf (L.column T.root)))
      (T.root_ancestor (L.leaf i)) le_rfl le_rfl
    exact ⟨p.word⟩
end PlanarL1.HeightTree.Layout


end

end OAI
end


