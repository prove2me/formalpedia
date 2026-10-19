-- Prove2me | Definitions.Def_OAIQWSQN006
-- name    : OAIQWSQN006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:16:04.737605+00:00
-- url     : https://prove2.me/theorems/20428db6-0193-4f0e-8e41-0f010caa4c65
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN006
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It also imports the bundles `OAIQWSQN004`, `OAIQWSQN005` of this split.
--
--   Modules: `BoundedCompleteness`, `ChangedPredual`, `CoordinateDual`, `CoordinatePredual`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWSQN004
import Definitions.Def_OAIQWSQN005

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinateDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
open Filter
universe u
variable {Γ : Type u} (K : NormingSet Γ)

/-- Strong convergence of uniformly contractive coordinate crops whose sets eventually contain every coordinate. -/
lemma tendsto_projection {ι : Type*} {l : Filter ι} (A : ι → Set Γ)
    (hA : ∀ i, K.CropStable (A i)) (hcover : ∀ a, ∀ᶠ i in l, a ∈ A i) (x : K.Space) :
    Tendsto (fun i => K.projection (A i) (hA i) x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := K.denseRange_includeFinite.exists_dist_lt x (by positivity : (0 : ℝ) < ε/3)
  have hevent : ∀ᶠ i in l, ∀ a ∈ v.support, a ∈ A i :=
    (v.support.eventually_all).mpr (fun a _ => hcover a)
  filter_upwards [hevent] with i hi
  have hvfix : K.projection (A i) (hA i) (K.includeFinite v) = K.includeFinite v := by
    rw [K.projection_includeFinite]
    congr 1
    ext a
    by_cases ha : a ∈ A i
    · simp [ha]
    · have hz : v a = 0 := by
        by_contra hn
        exact ha (hi a (Finsupp.mem_support_iff.mpr hn))
      simp [ha, hz]
  rw [dist_eq_norm] at hv ⊢
  calc
    ‖K.projection (A i) (hA i) x - x‖ =
        ‖K.projection (A i) (hA i) (x - K.includeFinite v) + (K.includeFinite v - x)‖ := by
      rw [(K.projection (A i) (hA i)).map_sub, hvfix]
      abel_nf
    _ ≤ ‖K.projection (A i) (hA i) (x - K.includeFinite v)‖ + ‖K.includeFinite v - x‖ :=
      norm_add_le _ _
    _ ≤ ‖x - K.includeFinite v‖ + ‖K.includeFinite v - x‖ := by
      gcongr
      exact K.projection_norm_apply_le _ _ _
    _ < ε := by rw [norm_sub_rev (K.includeFinite v) x]; linarith

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinatePredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma tendsto_colorsBelow (x : E) :
    Tendsto (fun n => projection (Crop.colorsBelow n) x) atTop (𝓝 x) := by
  apply norming.tendsto_projection
  intro a
  filter_upwards [eventually_gt_atTop (Colors.color a)] with n hn
  simpa using hn

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace3
/-- A Type I obstruction to successive uniformly positive normers. -/
lemma no_successive_positive_normers (g : StrongDual ℝ X₀) (t : Family)
    (f : ℕ → Array) (hf : ∀ i, f i ∈ t.normers)
    (hs : ∀ i j, i < j → Successive t (f i) (f j))
    (δ : ℝ) (hδ : 0 < δ) (hlarge : ∀ i, δ ≤ g (norming.rationalPredual (f i))) : False := by
  obtain ⟨j, hj, hratio⟩ := t.exists_large_ratio (‖g‖ / δ)
  let n := t.L j
  let e : TypeI t := {
    weight := j
    weight_pos := hj
    length := n
    length_pos := t.L_pos j
    length_le := le_rfl
    child := fun i => f i.val
    child_nonzero := fun i => by
      intro hz
      have h := hlarge i.val
      rw [hz, map_zero, map_zero] at h
      exact (not_le_of_gt hδ) h
    successive := fun i l hil => hs i.val l.val hil }
  have he : e.value ∈ Full := t.normers_subset_full (t.typeI_mem e (fun i => hf i.val))
  have hbound : g (norming.rationalPredual e.value) ≤ ‖g‖ := by
    calc
      _ ≤ |g (norming.rationalPredual e.value)| := le_abs_self _
      _ ≤ ‖g‖ * ‖norming.rationalPredual e.value‖ := g.le_opNorm _
      _ ≤ ‖g‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (norming.norm_rationalPredual_le e.value he) (norm_nonneg g)
  have heval : g (norming.rationalPredual e.value) =
      (1 / (t.m j : ℝ)) * ∑ i : Fin n, g (norming.rationalPredual (f i.val)) := by
    simp only [e, TypeI.value, map_rat_smul, Rat.smul_def, map_sum,
      Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hsum : (n : ℝ) * δ ≤ ∑ i : Fin n, g (norming.rationalPredual (f i.val)) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hlarge i.val)
  have hm : (0 : ℝ) < t.m j := by exact_mod_cast t.m_pos j
  have hb : (1 / (t.m j : ℝ)) * ((n : ℝ) * δ) ≤ ‖g‖ :=
    (mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hm.le)).trans (by rwa [← heval])
  have hr : ‖g‖ < ((n : ℝ) / (t.m j : ℝ)) * δ := (div_lt_iff₀ hδ).mp hratio
  have heq : (1 / (t.m j : ℝ)) * ((n : ℝ) * δ) = ((n : ℝ) / (t.m j : ℝ)) * δ := by ring
  rw [heq] at hb
  exact (not_lt_of_ge hb) hr

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BoundedCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup4
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace4
lemma exists_pure_piece_normer (g : StrongDual ℝ X₀) (I : Set Γ)
    (hI : Set.OrdConnected I) (k : ℕ) (x : E)
    (hx : IsPiece g (I ∩ colorSet k) x) (r : ℝ) (hr : 0 ≤ r) (hxr : r < ‖x‖) :
    ∃ f ∈ Pure k, (f.support : Set Γ) ⊆ I ∧
      r < g (norming.rationalPredual f) := by
  have hc : ∀ a, Colors.color a ≠ k → coordinate a x = 0 := by
    intro a ha
    apply hx.zero_off
    simp [colorSet, ha]
  obtain ⟨f, hf, hfx⟩ := exists_pure_normer k x hc r hr hxr
  let f' := _root_.OAI.SeparableQuotient.Norming.restrict I f
  have hf' : f' ∈ Pure k := pure_crop k (Crop.ordinalSet I hI) f hf
  have hs : (f'.support : Set Γ) ⊆ I := by
    intro a ha
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (by simp [f', hn])
  have hs' : (f'.support : Set Γ) ⊆ I ∩ colorSet k := by
    intro a ha
    refine ⟨hs ha, ?_⟩
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (pure_vanish k f' hf' a hn)
  refine ⟨f', hf', hs, ?_⟩
  rw [hx.eval_eq f' hs', evaluateArray_crop_of_zero I x]
  · exact hfx
  · intro a ha
    apply hx.zero_off
    simp [ha]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup5
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace5
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup5
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace5
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup5
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace5
lemma successive_pieces_color_tendsto (g : StrongDual ℝ X₀) (I : ℕ → Set Γ)
    (hI : ∀ i, (I i).OrdConnected) (v : ℕ → E) (hv : ∀ i, IsPiece g (I i) (v i))
    (hord : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) (k : ℕ) :
    Tendsto (fun i => projection (Crop.oneColor k) (v i)) atTop (𝓝 0) := by
  by_contra hn
  obtain ⟨ε, hε, φ, hφ, hlarge⟩ := OrderedCauchy.norm_large_subsequence _ hn
  have hp : ∀ i, IsPiece g (I (φ i) ∩ colorSet k) (projection (Crop.oneColor k) (v (φ i))) := by
    intro i
    simpa only [Crop.oneColor_set] using (hv (φ i)).projection (Crop.oneColor k)
  have hex : ∀ i, ∃ f ∈ Pure k, (f.support : Set Γ) ⊆ I (φ i) ∧
      ε/2 < g (norming.rationalPredual f) := by
    intro i
    exact exists_pure_piece_normer g _ (hI _) k _ (hp i) _ (by positivity)
      ((half_lt_self hε).trans_le (hlarge i))
  choose f hf hs he using hex
  apply no_successive_positive_normers g (.pure k) f hf _ (ε/2) (by positivity) (fun i => (he i).le)
  intro i j hij a ha b hb
  exact ⟨hord (φ i) (φ j) (hφ hij) a (hs i ha) b (hs j hb), by simp⟩

lemma exists_large_colorWindow (v : ℕ → E) (δ : ℝ) (hδ : 0 < δ)
    (hv : ∀ i, δ ≤ ‖v i‖)
    (hc : ∀ k, Tendsto (fun i => projection (Crop.oneColor k) (v i)) atTop (𝓝 0))
    (lo N : ℕ) : ∃ n hi : ℕ, N < n ∧ lo < hi ∧
      δ/2 < ‖projection (Crop.colorWindow lo hi) (v n)‖ := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (tendsto_low_colors hc lo) (δ/4) (by positivity)
  let n := max (N+1) N₀
  have hlow : ‖projection (Crop.colorsBelow lo) (v n)‖ < δ/4 := by
    simpa only [dist_zero_right] using hN₀ n (le_max_right _ _)
  obtain ⟨H, hH⟩ := Metric.tendsto_atTop.mp (tendsto_colorsBelow (v n)) (δ/4) (by positivity)
  let hi := max (lo+1) H
  have hhigh : ‖v n - projection (Crop.colorsBelow hi) (v n)‖ < δ/4 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hH hi (le_max_right _ _)
  have hlohi : lo < hi := lt_of_lt_of_le (Nat.lt_succ_self lo) (le_max_left _ _)
  refine ⟨n, hi, lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_left _ _), hlohi, ?_⟩
  rw [projection_colorWindow_eq lo hi hlohi.le]
  have hb : ‖v n‖ ≤ ‖v n - projection (Crop.colorsBelow hi) (v n)‖ +
      ‖projection (Crop.colorsBelow hi) (v n) - projection (Crop.colorsBelow lo) (v n)‖ +
      ‖projection (Crop.colorsBelow lo) (v n)‖ := by
    calc
      _ = ‖(v n - projection (Crop.colorsBelow hi) (v n)) +
          (projection (Crop.colorsBelow hi) (v n) - projection (Crop.colorsBelow lo) (v n)) +
          projection (Crop.colorsBelow lo) (v n)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have := hv n
  linarith

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup6
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace6
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup6
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace6
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup6
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace6
/-- The limit-step contradiction for vector pieces, with normers cropped after norm approximation. -/
lemma no_large_successive_pieces (g : StrongDual ℝ X₀) (I : ℕ → Set Γ)
    (hI : ∀ i, (I i).OrdConnected) (v : ℕ → E) (hv : ∀ i, IsPiece g (I i) (v i))
    (hord : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b)
    (δ : ℝ) (hδ : 0 < δ) (hlarge : ∀ i, δ ≤ ‖v i‖) : False := by
  have hc := successive_pieces_color_tendsto g I hI v hv hord
  have hex := exists_large_colorWindow v δ hδ hlarge hc
  choose n h hn hh hw using hex
  let p : ℕ → ℕ × ℕ := fun i => Nat.rec (0, 0)
    (fun _ prev => (n prev.2 prev.1, h prev.2 prev.1)) i
  have hp1 : StrictMono (fun i => (p i).1) := strictMono_nat_of_lt_succ fun i => hn _ _
  have hp2 : StrictMono (fun i => (p i).2) := strictMono_nat_of_lt_succ fun i => hh _ _
  let idx : ℕ → ℕ := fun i => (p (i+1)).1
  have hidx : StrictMono idx := fun i j hij => hp1 (Nat.add_lt_add_right hij 1)
  let A : ℕ → Crop := fun i => {
    ordinal := I (idx i)
    ordinal_convex := hI (idx i)
    colors := Set.Ico (p i).2 (p (i+1)).2
    colors_convex := Set.ordConnected_Ico }
  let w : ℕ → E := fun i => projection (Crop.colorWindow (p i).2 (p (i+1)).2) (v (idx i))
  have hp : ∀ i, IsPiece g ((A i).set .mixed) (w i) := by
    intro i
    simpa only [w, A, Crop.set, Crop.colorWindow, Crop.colorSet, Set.univ_inter] using
      (hv (idx i)).projection (Crop.colorWindow (p i).2 (p (i+1)).2)
  have hl : ∀ i, δ/2 < ‖w i‖ := fun i => hw (p i).2 (p i).1
  have hex' : ∀ i, ∃ f ∈ Full, (f.support : Set Γ) ⊆ (A i).set .mixed ∧
      δ/4 < g (norming.rationalPredual f) := by
    intro i
    exact exists_piece_normer g (A i) (w i) (hp i) (δ/4) (by positivity)
      (lt_trans (by linarith) (hl i))
  choose f hf hs he using hex'
  apply no_successive_positive_normers g .mixed f hf _ (δ/4) (by positivity) (fun i => (he i).le)
  intro i j hij a ha b hb
  have ha' := hs i ha
  have hb' := hs j hb
  change a ∈ I (idx i) ∧ (p i).2 ≤ Colors.color a ∧ Colors.color a < (p (i+1)).2 at ha'
  change b ∈ I (idx j) ∧ (p j).2 ≤ Colors.color b ∧ Colors.color b < (p (j+1)).2 at hb'
  refine ⟨hord (idx i) (idx j) (hidx hij) a ha'.1 b hb'.1, fun _ => ?_⟩
  exact (ha'.2.2.trans_le (hp2.monotone (by omega : i+1 ≤ j))).trans_le hb'.2.1

/-- The ordinal-prefix net is Cauchy at every limit. It also works at successor
limits and at ω₁, without any cofinality assumption. -/
lemma prefixes_cauchy {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (g : StrongDual ℝ X₀) (a : ι ↪o Γ) (v : ι → E)
    (hv : ∀ i, IsPiece g (Set.Iic (a i)) (v i)) : CauchySeq v := by
  by_contra hn
  obtain ⟨δ, hδ, b, c, hbc, hs, hdist⟩ := OrderedCauchy.separated_pairs_of_not_cauchy v hn
  let I : ℕ → Set Γ := fun i => Set.Ioc (a (b i)) (a (c i))
  let w : ℕ → E := fun i => v (c i) - v (b i)
  have hp : ∀ i, IsPiece g (I i) (w i) := fun i =>
    (hv (b i)).sub_Iic (hv (c i)) (a.monotone (hbc i).le)
  apply no_large_successive_pieces g I (fun _ => Set.ordConnected_Ioc) w hp _ δ hδ
  · intro i
    simpa only [w, dist_eq_norm] using hdist i
  · intro i j hij α hα β hβ
    exact (hα.2.trans (a.monotone (hs i j hij))).trans_lt hβ.1

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup7
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace7
/-- Every strict prefix is the limit of its already constructed inclusive
prefixes. This handles empty, successor, and limit initial segments uniformly. -/
lemma exists_strict_prefix (g : StrongDual ℝ X₀) (β : Γ)
    (h : ∀ a : Γ, a < β → ∃ x : E, IsPiece g (Set.Iic a) x) :
    ∃ x : E, IsPiece g (Set.Iio β) x := by
  by_cases hn : Nonempty (Set.Iio β)
  · let := hn
    choose v hv using (fun a : Set.Iio β => h a.val a.property)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
      (prefixes_cauchy g (OrderEmbedding.subtype (· ∈ Set.Iio β)) v hv)
    refine ⟨x, fun a => ?_⟩
    have ht := (coordinate a).continuous.tendsto x |>.comp hx
    simp only [Set.mem_Iio]
    by_cases ha : a < β
    · rw [ite_eq_left ha]
      have he : ∀ᶠ i : Set.Iio β in atTop, coordinate a (v i) = g (coordinate₀ a) := by
        filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : Set.Iio β)] with i hi
        change a ≤ (i : Γ) at hi
        rw [hv i a, Set.mem_Iic, ite_eq_left hi]
      exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))
    · rw [ite_eq_right ha]
      have he : ∀ i : Set.Iio β, coordinate a (v i) = 0 := by
        intro i
        rw [hv i a, Set.mem_Iic, ite_eq_right (fun hai => ha (lt_of_le_of_lt hai i.property))]
      exact tendsto_nhds_unique ht
        (tendsto_const_nhds.congr' (Filter.Eventually.of_forall
          (fun i : Set.Iio β => (he i).symm)))
  · refine ⟨0, fun a => ?_⟩
    have ha : ¬ a < β := fun ha => hn ⟨⟨a, ha⟩⟩
    simp [ha]

lemma exists_prefix (g : StrongDual ℝ X₀) (β : Γ) :
    ∃ x : E, IsPiece g (Set.Iic β) x := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Γ → Γ → Prop)).induction (C := fun β => ∃ x : E, IsPiece g (Set.Iic β) x) β ?_
  intro β ih
  obtain ⟨x, hx⟩ := exists_strict_prefix g β ih
  exact ⟨_, hx.append⟩

lemma exists_all_coordinates (g : StrongDual ℝ X₀) :
    ∃ x : E, ∀ a, coordinate a x = g (coordinate₀ a) := by
  choose v hv using (fun a => exists_prefix g a)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (prefixes_cauchy g ((OrderIso.refl Γ).toOrderEmbedding) v hv)
  refine ⟨x, fun a => ?_⟩
  have ht := (coordinate a).continuous.tendsto x |>.comp hx
  have he : ∀ᶠ i : Γ in atTop, coordinate a (v i) = g (coordinate₀ a) := by
    filter_upwards [eventually_ge_atTop a] with i hi
    rw [hv i a, Set.mem_Iic, ite_eq_left hi]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))

/-- Evaluation onto the dual of the coordinate predual is surjective. -/
lemma evaluation_surjective : Function.Surjective norming.evaluation := by
  intro g
  obtain ⟨x, hx⟩ := exists_all_coordinates g
  refine ⟨x, predual_dual_ext _ _ (fun a => ?_)⟩
  exact hx a

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ChangedPredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.atDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atDualSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXClosed
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atWGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atWSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0Group
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0Space
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0DualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atX0DualSpace
lemma eval0_surjective : Function.Surjective (evalOn X₀) := evaluation_surjective

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

lemma twist_data :
    (∃ R : E ≃L[ℝ] StrongDual ℝ (X hCH),
      ∀ (e : E) (x : X hCH), R e x = (x : StrongDual ℝ E) e) ∧
    ((X hCH).map (B hCH).toLinearMap).topologicalClosure =
      (X₀.map (B hCH).toLinearMap).topologicalClosure := by
  exact (twist X₀ eval0_isometry eval0_surjective (B hCH) (norm_B_le hCH) (B_adjoint hCH)
    (B_range_mem_predual_closure hCH)).2

attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXSpace
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXDualGroup
attribute [local instance] OAI.SeparableQuotient.ActualSpace.atXDualSpace
def twistedIso : E ≃L[ℝ] StrongDual ℝ (X hCH) := (twist_data hCH).1.choose
@[simp] lemma twistedIso_apply (e : E) (x : X hCH) :
    twistedIso hCH e x = (x : StrongDual ℝ E) e := (twist_data hCH).1.choose_spec e x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

@[reducible] local instance chDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance chDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance chSubGroup (F : Submodule ℝ E) : NormedAddCommGroup F := inferInstance
@[reducible] local instance chSubSpace (F : Submodule ℝ E) : NormedSpace ℝ F := inferInstance
@[reducible] local instance chSubDualGroup (F : Submodule ℝ E) : NormedAddCommGroup (StrongDual ℝ F) := inferInstance
@[reducible] local instance chSubDualSpace (F : Submodule ℝ E) : NormedSpace ℝ (StrongDual ℝ F) := inferInstance

end SeparableQuotient.ActualSpace

end

end OAI
end


