-- Prove2me | Definitions.Def_OAIQWSQN004
-- name    : OAIQWSQN004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:05:13.879969+00:00
-- url     : https://prove2.me/theorems/8b172afa-06c6-412a-bc3b-795f22303ba2
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN004
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It also imports the bundles `OAIQWSQN002`, `OAIQWSQN003` of this split.
--
--   Modules: `BlockEstimates`, `BoundedCompleteness`, `BranchPaths`, `ChangedPredual`, `CoordinateDual`, `CoordinatePredual`, `ExactPairs`, `MarkedEstimates`, `NormingBounds`, `PartitionBlocks`, `PathConvergence`, `PathRigidity`, `RamseyThinning`, `StoppedCharges`, `TailBlocks`, `TreeBounds`, `TreeCharges`, `WindowCharges`, `WindowEstimates`, `WindowThinning`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWSQN002
import Definitions.Def_OAIQWSQN003

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

lemma projection_norm_apply_le (A : Set Γ) (hA : K.CropStable A) (x : K.Space) :
    ‖K.projection A hA x‖ ≤ ‖x‖ :=
  ((K.projection A hA).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (K.norm_projection_le A hA) (norm_nonneg x))

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

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.L_pos (f : Family) (j : ℕ) : 0 < f.L j := Parameters.L_pos _ _

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup3
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace3
lemma predual_array_apply (g : StrongDual ℝ X₀) (f : Array) :
    g (norming.rationalPredual f) = ∑ a ∈ f.support, (f a : ℝ) * g (coordinate₀ a) := by
  simp only [NormingSet.rationalPredual, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_rat_smul, Rat.smul_def, coordinate₀]

lemma predual_array_eq_evaluate (g : StrongDual ℝ X₀) (f : Array) (x : E)
    (hx : ∀ a ∈ f.support, coordinate a x = g (coordinate₀ a)) :
    g (norming.rationalPredual f) = norming.evaluateArray x f := by
  rw [predual_array_apply, norming.evaluateArray_eq]
  exact Finset.sum_congr rfl (fun a ha => by rw [← hx a ha])

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
/-- Coordinates of a proposed prefix or interval coincide with the fixed g. -/
def IsPiece (g : StrongDual ℝ X₀) (S : Set Γ) (x : E) : Prop :=
  ∀ a, coordinate a x = if a ∈ S then g (coordinate₀ a) else 0

lemma IsPiece.zero_off {g : StrongDual ℝ X₀} {S : Set Γ} {x : E}
    (h : IsPiece g S x) (a : Γ) (ha : a ∉ S) : coordinate a x = 0 := by
  rw [h a, ite_eq_right ha]

lemma IsPiece.projection {g : StrongDual ℝ X₀} {S : Set Γ} {x : E}
    (h : IsPiece g S x) (A : Crop) :
    IsPiece g (S ∩ A.set .mixed) (projection A x) := by
  intro a
  rw [coordinate_projection, h a]
  by_cases ha : a ∈ S <;> by_cases hb : a ∈ A.set .mixed <;> simp [ha, hb]

lemma IsPiece.eval_eq {g : StrongDual ℝ X₀} {S : Set Γ} {x : E}
    (h : IsPiece g S x) (f : Array) (hf : (f.support : Set Γ) ⊆ S) :
    g (norming.rationalPredual f) = norming.evaluateArray x f := by
  apply predual_array_eq_evaluate
  intro a ha
  rw [h a, ite_eq_left (hf ha)]

lemma exists_piece_normer (g : StrongDual ℝ X₀) (A : Crop) (x : E)
    (hx : IsPiece g (A.set .mixed) x) (r : ℝ) (hr : 0 ≤ r) (hxr : r < ‖x‖) :
    ∃ f ∈ Full, (f.support : Set Γ) ⊆ A.set .mixed ∧
      r < g (norming.rationalPredual f) := by
  obtain ⟨f, hf, hfx⟩ := exists_full_normer x r hr hxr
  let f' := _root_.OAI.SeparableQuotient.Norming.restrict (A.set .mixed) f
  have hs : (f'.support : Set Γ) ⊆ A.set .mixed := by
    intro a ha
    by_contra hn
    have hz : f' a = 0 := by simp [f', hn]
    exact Finsupp.mem_support_iff.mp ha hz
  refine ⟨f', full_crop A f hf, hs, ?_⟩
  rw [hx.eval_eq f' hs, evaluateArray_crop_of_zero (A.set .mixed) x hx.zero_off]
  exact hfx

lemma tendsto_low_colors {v : ℕ → E}
    (h : ∀ k, Tendsto (fun i => projection (Crop.oneColor k) (v i)) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun i => projection (Crop.colorsBelow n) (v i)) atTop (𝓝 0) := by
  simpa only [projection_colorsBelow_sum, Finset.sum_const_zero] using
    (tendsto_finsetSum (Finset.range n) fun k _ => h k)

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
lemma projection_colorWindow_eq (lo hi : ℕ) (h : lo ≤ hi) (x : E) :
    projection (Crop.colorWindow lo hi) x =
      projection (Crop.colorsBelow hi) x - projection (Crop.colorsBelow lo) x := by
  apply coordinate_ext
  intro a
  simp only [map_sub, coordinate_projection, Crop.colorWindow_set, Crop.colorsBelow_set,
    Set.mem_ofPred_eq]
  by_cases hl : Colors.color a < lo
  · have hh : Colors.color a < hi := hl.trans_le h
    simp [hl, hh, not_le_of_gt hl]
  · by_cases hh : Colors.color a < hi <;> simp [hl, hh, le_of_not_gt hl]

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
lemma IsPiece.sub_Iic {g : StrongDual ℝ X₀} {a b : Γ} {x y : E}
    (hx : IsPiece g (Set.Iic a) x) (hy : IsPiece g (Set.Iic b) y) (hab : a ≤ b) :
    IsPiece g (Set.Ioc a b) (y-x) := by
  intro c
  rw [map_sub, hx c, hy c]
  by_cases hca : c ≤ a
  · have hcb : c ≤ b := hca.trans hab
    simp [hca, hcb, not_lt_of_ge hca]
  · by_cases hcb : c ≤ b <;> simp [hca, hcb, lt_of_not_ge hca]

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
lemma IsPiece.append {g : StrongDual ℝ X₀} {β : Γ} {x : E}
    (hx : IsPiece g (Set.Iio β) x) :
    IsPiece g (Set.Iic β) (x + g (coordinate₀ β) • e β) := by
  intro a
  rw [map_add, map_smul, hx a, coordinate_e]
  by_cases ha : a = β
  · subst a
    simp
  · by_cases hab : a < β
    · simp [ha, hab, hab.le]
    · have hba : ¬ a ≤ β := fun h => hab (lt_of_le_of_ne h ha)
      simp [ha, hab, hba]

lemma dense_span_coordinate₀ : Dense (Submodule.span ℝ (Set.range coordinate₀) : Set X₀) := by
  have him : Subtype.val '' (Submodule.span ℝ (Set.range coordinate₀) : Set X₀) =
      (Submodule.span ℝ (Set.range coordinate) : Set (StrongDual ℝ E)) := by
    change ((Submodule.span ℝ (Set.range coordinate₀)).map X₀.subtype : Set (StrongDual ℝ E)) = _
    rw [Submodule.map_span]
    congr 2
    rw [← Set.range_comp]
    rfl
  intro x
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, him]
  exact x.property

lemma predual_dual_ext (g h : StrongDual ℝ X₀)
    (he : ∀ a, g (coordinate₀ a) = h (coordinate₀ a)) : g = h := by
  apply ContinuousLinearMap.ext_on dense_span_coordinate₀
  rintro _ ⟨a, rfl⟩
  exact he a

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathConvergence
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

lemma path_threshold_cap {f : Family} (x : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖x n‖ ≤ M) (hx : PredualNull x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ (s : Finset (PathIndex f)) (φ : ℕ → ℕ), StrictMono φ →
      (∀ a ∈ s, ∀ n, δ < |pathFunctional a.repr (x (φ n))|) → s.card ≤ K := by
  have hq : 1 < f.q := (Parameters.q_bounds f.s_ge_two).1
  obtain ⟨K, hK⟩ := PathSelection.power_cap (1/f.q) M (δ/2)
    ((div_lt_one (by linarith)).mpr (by linarith)) (by linarith)
  refine ⟨K, fun s φ hφ hs => ?_⟩
  let e : Fin s.card ≃ s := s.equivFin.symm
  let P : Fin s.card → InfinitePath f := fun i => (e i).val.repr
  have hinj : Function.Injective (fun i => (P i).raw) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact PathIndex.repr_injective hij
  obtain ⟨N, hN⟩ := exists_tail_estimate P hinj
  have hsmall (i : Fin s.card) : ∀ᶠ n in atTop,
      |pathFunctional (P i) (x (φ n)) - pathTail (P i) N (x (φ n))| < δ/2 := by
    have ht := (hx ⟨pathFunctional (P i) - pathTail (P i) N,
      pathTail_complement_mem (P i) N⟩).comp hφ.tendsto_atTop
    have hδ0 : |(0 : ℝ)| < δ/2 := by rw [abs_zero]; exact half_pos hδ
    have he := ht.abs.eventually (gt_mem_nhds hδ0)
    simpa only [Function.comp_apply, sub_apply, abs_zero] using he
  obtain ⟨n, hn⟩ := (eventually_all_finset (I := Finset.univ)).mpr
    (fun i _ => hsmall i) |>.exists
  have hlower (i : Fin s.card) : δ/2 ≤ |pathTail (P i) N (x (φ n))| := by
    have hh := hs (e i).val (e i).property n
    have hh' := hn i (Finset.mem_univ i)
    have ht := abs_sub_abs_le_abs_sub
      (pathFunctional (P i) (x (φ n))) (pathTail (P i) N (x (φ n)))
    dsimp only [P] at ht hh'
    linarith
  apply hK s.card
  calc
    δ/2 * (s.card : ℝ) = ∑ _i : Fin s.card, δ/2 := by simp [mul_comm]
    _ ≤ ∑ i, |pathTail (P i) N (x (φ n))| := Finset.sum_le_sum (fun i _ => hlower i)
    _ ≤ (s.card : ℝ)^(1/f.q) * ‖x (φ n)‖ := tail_abs_sum_bound P N hN _
    _ ≤ M * (s.card : ℝ)^(1/f.q) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM (φ n))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma path_all_cauchy {f : Family} (x : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖x n‖ ≤ M) (hx : PredualNull x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a : PathIndex f,
      CauchySeq (fun n => pathFunctional a.repr (x (φ n))) := by
  apply PathSelection.simultaneous_cauchy (fun (a : PathIndex f) (n : ℕ) =>
    pathFunctional a.repr (x n)) M
  · intro a n
    simpa only [Real.norm_eq_abs] using
      (PathLimits.unit_bound _ (norm_pathFunctional_le a.repr) _).trans (hM n)
  · exact path_threshold_cap x M hM hx

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualGroup11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.predualSpace11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualGroup11
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualPredualSpace11
lemma predualNull_of_coordinates (x : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ a : Γ, Tendsto (fun n => coordinate a (x n)) atTop (𝓝 0)) :
    PredualNull x := by
  let V : Submodule ℝ X₀ := {
    carrier := {y | Tendsto (fun n => y.val (x n)) atTop (𝓝 0)}
    zero_mem' := by simp
    add_mem' := by
      intro y z hy hz
      change Tendsto (fun n => (y.val + z.val) (x n)) atTop (𝓝 0)
      simpa only [add_apply, add_zero] using hy.add hz
    smul_mem' := by
      intro c y hy
      change Tendsto (fun n => (c • y.val) (x n)) atTop (𝓝 0)
      simpa only [smul_apply, smul_zero] using hy.const_smul c }
  have hspan : Submodule.span ℝ (Set.range coordinate₀) ≤ V := by
    apply Submodule.span_le.mpr
    rintro y ⟨a, rfl⟩
    exact hx a
  intro y
  exact DenseZero.tendsto_zero_of_dense (fun n => norming.evaluation (x n)) M
    (fun n => (norming.norm_evaluation (x n)).le.trans (hM n))
    (Submodule.span ℝ (Set.range coordinate₀)) dense_span_coordinate₀
    (fun z hz => hspan hz) y

lemma BlockSequence.predualNull {f : Family} (x : BlockSequence f) (M : ℝ)
    (hM : ∀ n, ‖x.embed n‖ ≤ M) : PredualNull x.embed := by
  apply predualNull_of_coordinates x.embed M hM
  intro a
  exact tendsto_const_nhds.congr' ((x.coordinate_eventually_zero a).mono fun _ h => h.symm)

/-- Every bounded block sequence has a subsequence on which every path functional converges. -/
lemma BlockSequence.all_paths_cauchy {f : Family} (x : BlockSequence f) (M : ℝ)
    (hM : ∀ n, ‖x.embed n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ P : InfinitePath f,
      CauchySeq (fun n => pathFunctional P (x.embed (φ n))) := by
  obtain ⟨φ, hφ, hp⟩ := path_all_cauchy x.embed M hM (x.predualNull M hM)
  refine ⟨φ, hφ, fun P => ?_⟩
  let a : PathIndex f := ⟨P.raw, P, rfl⟩
  have he : pathFunctional a.repr = pathFunctional P := pathFunctional_eq_of_raw a.repr_raw
  simpa only [he] using hp a

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

lemma FinitePath.weightCrop_value {f : Family} (P : FinitePath f) (J T : ℕ) :
    restrict ((P.weightCrop J T).set f) P.value = P.window J T := by
  simp only [FinitePath.value, restrict_sum, P.weightCrop_piece, window]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualEGroup13
attribute [local instance] OAI.SeparableQuotient.ActualSpace.dualESpace13
lemma window_disjoint_cap {f : Family} (M δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ (h : ℕ) (P : Fin h → FinitePath f) (J T : ℕ) (x : E),
      (∀ b i j, ((P b).piece i).child j ∈ f.norming) →
      Pairwise (fun i j => Disjoint ((P i).windowWeights J T) ((P j).windowWeights J T)) →
      ‖x‖ ≤ M → (∀ b, δ < |norming.evaluateArray x ((P b).window J T)|) → h ≤ K := by
  have hq : 1 < f.q := (Parameters.q_bounds f.s_ge_two).1
  obtain ⟨K, hK⟩ := PathSelection.power_cap (1/f.q) M δ
    ((div_lt_one (by linarith)).mpr (by linarith)) hδ
  refine ⟨K, fun h P J T x hm hdis hx hh => hK h ?_⟩
  have he (b : Fin h) : croppedPathFunctional (P b) ((P b).weightCrop J T) x =
      norming.evaluateArray x ((P b).window J T) := by
    simp only [croppedPathFunctional, (P b).weightCrop_value, NormingSet.evaluateArray]
    rfl
  calc
    δ * (h : ℝ) = ∑ _b : Fin h, δ := by simp [mul_comm]
    _ ≤ ∑ b, |croppedPathFunctional (P b) ((P b).weightCrop J T) x| :=
      Finset.sum_le_sum (fun b _ => by rw [he b]; exact (hh b).le)
    _ ≤ (h : ℝ) ^ (1/f.q) * ‖x‖ := cropped_abs_sum_bound P _ hm
      (by simpa only [FinitePath.weightCrop_active] using hdis) x
    _ ≤ M * (h : ℝ) ^ (1/f.q) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

lemma FinitePath.window_eq_sum_lowHistory {f : Family} (P : FinitePath f) (J T H : ℕ)
    (hT : T < H) : P.window J T =
      ∑ d ∈ P.lowHistoryFinset H, if J ≤ d.2.1 ∧ d.2.1 ≤ T then d.1 else 0 := by
  rw [lowHistoryFinset, Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T
    · simp only [hi, and_self, ite_true, ite_eq_left (hi.2.trans_lt hT)]
    · simp only [hi, ite_false, ite_self]
  · intro i _ j _ he
    apply P.valid.weight_strict.injective
    exact congrArg (fun d : Array × ℕ × ℕ => d.2.1) he

lemma FinitePath.window_eq_of_lowHistory {f : Family} (P Q : FinitePath f) (J T H : ℕ)
    (hT : T < H) (he : P.lowHistory H = Q.lowHistory H) : P.window J T = Q.window J T := by
  have hf : P.lowHistoryFinset H = Q.lowHistoryFinset H := by
    ext d
    rw [P.mem_lowHistoryFinset, Q.mem_lowHistoryFinset, he]
  rw [P.window_eq_sum_lowHistory J T H hT, Q.window_eq_sum_lowHistory J T H hT, hf]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma window_anchor {f : Family} (P : FinitePath f) (x : Γ →₀ ℝ) (J T : ℕ)
    (hh : norming.evaluateArray (norming.includeFinite x) (P.window J T) ≠ 0) :
    ∃ i : Fin P.length, J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T ∧
      ∃ a ∈ x.support, a ∈ (P.raw.piece i).support := by
  simp only [FinitePath.window, map_sum] at hh
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
  have hw : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T := by
    by_contra hn
    simp only [ite_eq_right hn, map_zero, ne_eq, not_true_eq_false] at hi
  rw [ite_eq_left hw, norming.evaluateArray_eq] at hi
  obtain ⟨a, ha, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  refine ⟨i, hw.1, hw.2, a, ?_, ha⟩
  rw [norming.coordinate_includeFinite] at hh
  exact Finsupp.mem_support_iff.mpr (fun hz => hh (by rw [hz, mul_zero]))

lemma WindowHit.anchor {f : Family} {P : LegalFinitePath f} {x : Γ →₀ ℝ}
    {J T : ℕ} {δ : ℝ} (hδ : 0 < δ) (hh : WindowHit P x J T δ) :
    ∃ i : Fin P.val.length, J ≤ P.val.raw.weight i ∧ P.val.raw.weight i ≤ T ∧
      ∃ a ∈ x.support, a ∈ (P.val.raw.piece i).support := by
  apply window_anchor
  exact abs_pos.mp (hδ.trans hh)

/-- Rigidity of two path histories with shared later weights. -/
lemma disjoint_of_different_histories {f : Family} (P Q : LegalFinitePath f)
    (x : Γ →₀ ℝ) (Jv Tv Jt Tt Jk Tk : ℕ) (hvt : Tv < Jt) (htk : Tt < Jk)
    (δ : ℝ) (hδ : 0 < δ)
    (hp : WindowHit P x Jv Tv δ) (hq : WindowHit Q x Jv Tv δ)
    (ht : ∃ t : Fin P.val.length, Jt ≤ P.val.raw.weight t ∧ P.val.raw.weight t ≤ Tt)
    (hr : ∀ a ∈ x.support, ∀ b ∈ x.support, rho (min a b) (max a b) ≤ Jt)
    (hne : P.val.lowHistory Jv ≠ Q.val.lowHistory Jv) :
    Disjoint (P.val.windowWeights Jk Tk) (Q.val.windowWeights Jk Tk) := by
  obtain ⟨j, hj, hj', a, ha, ha'⟩ := hp.anchor hδ
  obtain ⟨k, hk, hk', b, hb, hb'⟩ := hq.anchor hδ
  obtain ⟨t, ht, ht'⟩ := ht
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  exact hne (P.val.lowHistory_eq_of_shared_later_weight Q.val Jv Tv Jt Tt Jk Tk hvt htk
    j k t ⟨hj, hj'⟩ ⟨hk, hk'⟩ ⟨ht, ht'⟩ a b ha' hb' (hr a ha b hb) ⟨w, hw, hw'⟩)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- Uniform finite covers from the history-class argument. -/
lemma finite_window_covers {f : Family} (x : ℕ → Γ →₀ ℝ) (J T : ℕ → ℕ)
    (horder : ∀ i j, i < j → T i < J j)
    (hcoh : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x i).support,
      rho (min a b) (max a b) ≤ J j)
    (M δ : ℝ) (hM : ∀ i, ‖norming.includeFinite (x i)‖ ≤ M) (hδ : 0 < δ)
    (hall : ∀ w v t k : ℕ, w < v → v < t → t < k →
      ∃ P : LegalFinitePath f, WindowHit P (x w) (J w) (T w) δ ∧
        WindowHit P (x v) (J v) (T v) δ ∧ WindowHit P (x t) (J t) (T t) δ ∧
        WindowHit P (x k) (J k) (T k) δ) :
    ∃ D : ℕ, ∀ n, ∃ R : Finset (LegalFinitePath f), R.card ≤ D ∧
      ∀ i ≤ n, ∃ P ∈ R, WindowHit P (x i) (J i) (T i) δ := by
  obtain ⟨D, hD⟩ := window_disjoint_cap (f := f) M δ hδ
  refine ⟨D, fun n => ?_⟩
  have hex (i : Fin (n+1)) := hall i (n+1) (n+2) (n+3) i.isLt (by omega) (by omega)
  choose P hP using hex
  let H : Fin (n+1) → Set (Array × ℕ × ℕ) := fun i => (P i).val.lowHistory (J (n+1))
  let S : Finset (Set (Array × ℕ × ℕ)) := Finset.univ.image H
  have hrep (d : S) : ∃ i : Fin (n+1), H i = d.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp d.property
    exact ⟨i, hi⟩
  let rep : S → Fin (n+1) := fun d => (hrep d).choose
  have hr (d : S) : H (rep d) = d.val := (hrep d).choose_spec
  let e : Fin S.card ≃ S := S.equivFin.symm
  let Q : Fin S.card → LegalFinitePath f := fun b => P (rep (e b))
  have hQ (b : Fin S.card) : (Q b).val.lowHistory (J (n+1)) = (e b).val := hr (e b)
  have hcard : S.card ≤ D := by
    apply hD S.card (fun b => (Q b).val) (J (n+3)) (T (n+3)) (norming.includeFinite (x (n+3)))
      (fun b => (Q b).property)
    · intro b c hbc
      apply disjoint_of_different_histories (Q b) (Q c) (x (n+1)) (J (n+1)) (T (n+1))
        (J (n+2)) (T (n+2)) (J (n+3)) (T (n+3)) (horder _ _ (by omega))
        (horder _ _ (by omega)) δ hδ
      · exact (hP _).2.1
      · exact (hP _).2.1
      · obtain ⟨i, hi, hi', a, ha, ha'⟩ := ((hP (rep (e b))).2.2.1).anchor hδ
        exact ⟨i, hi, hi'⟩
      · exact hcoh _ _ (by omega)
      · rw [hQ, hQ]
        exact fun hh => hbc (e.injective (Subtype.ext hh))
    · exact hM (n+3)
    · intro b
      exact (hP (rep (e b))).2.2.2
  refine ⟨Finset.univ.image Q, (Finset.card_image_le).trans (by simpa using hcard), fun i hi => ?_⟩
  let ii : Fin (n+1) := ⟨i, by omega⟩
  let d : S := ⟨H ii, Finset.mem_image.mpr ⟨ii, Finset.mem_univ _, rfl⟩⟩
  let b := e.symm d
  have hh : (Q b).val.lowHistory (J (n+1)) = (P ii).val.lowHistory (J (n+1)) := by
    rw [hQ]
    exact congrArg Subtype.val (e.apply_symm_apply d)
  refine ⟨Q b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩, ?_⟩
  change δ < |norming.evaluateArray _ ((Q b).val.window (J i) (T i))|
  rw [(Q b).val.window_eq_of_lowHistory (P ii).val (J i) (T i) (J (n+1))
    (horder i (n+1) (by omega)) hh]
  exact (hP ii).1

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma path_piece_zero_of_earlier_hit {f : Family} (P : LegalFinitePath f)
    (x y : Γ →₀ ℝ) (hs : ∀ a ∈ x.support, ∀ b ∈ y.support, a < b)
    (J T : ℕ) (δ : ℝ) (hδ : 0 < δ) (hh : WindowHit P x J T δ)
    (i : Fin P.val.length) (hi : P.val.raw.weight i < J) :
    norming.evaluateArray (norming.includeFinite y) (P.val.raw.piece i) = 0 := by
  obtain ⟨j, hj, _, a, ha, ha'⟩ := hh.anchor hδ
  have hij : i < j := P.val.valid.weight_strict.lt_iff_lt.mp (hi.trans_le hj)
  rw [evaluateArray_finite]
  apply Finset.sum_eq_zero
  intro b hb
  have hz : P.val.raw.piece i b = 0 := by
    by_contra hn
    have hba := P.val.valid.successive i j hij j.isLt b
      (Finsupp.mem_support_iff.mpr hn) a ha'
    exact (lt_asymm hba (hs a ha b hb))
  simp only [hz, Rat.cast_zero, zero_mul]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma finitePathFunctional_apply {f : Family} (P : LegalFinitePath f) (x : E) :
    finitePathFunctional P.val P.property x = norming.evaluateArray x P.val.value := by
  exact (norming.evaluateArray_eq_functional x ⟨P.val.value, finitePath_mem_full P.val P.property⟩).symm

lemma window_error_bound {f : Family} (P : LegalFinitePath f)
    (x y : Γ →₀ ℝ) (hs : ∀ a ∈ x.support, ∀ b ∈ y.support, a < b)
    (B S J T : ℕ) (hBJ : B ≤ J) (hJT : J ≤ T)
    (δ A : ℝ) (hδ : 0 < δ) (hA : 0 ≤ A) (hh : WindowHit P x B S δ)
    (hl : ∀ e : TypeI f, (∀ j, e.child j ∈ f.norming) → e.weight < J →
      |norming.evaluateArray (norming.includeFinite y) e.value| ≤ A * f.theta e.weight) :
    |finitePathFunctional P.val P.property (norming.includeFinite y) -
      norming.evaluateArray (norming.includeFinite y) (P.val.window J T)| ≤
      A * tail f.theta B + vectorL1 y * tail (fun j => 1 / (f.m j : ℝ)) (T+1) := by
  rw [finitePathFunctional_apply]
  simp only [FinitePath.value, FinitePath.window, map_sum, apply_ite, map_zero]
  apply sum_outside_window_bound Finset.univ (fun i : Fin P.val.length => P.val.raw.weight i)
    _ P.val.valid.weight_strict.injective.injOn B J T hBJ hJT f.theta
    (fun j => 1 / (f.m j : ℝ)) f.theta_summable f.m_inv_summable f.theta_nonneg
    (fun _ => by positivity) A (vectorL1 y) hA (vectorL1_nonneg y)
  · exact fun i _ hi => path_piece_zero_of_earlier_hit P x y hs B S δ hδ hh i hi
  · intro i _ _ hi
    rw [← P.val.weight_eq i] at hi
    simpa only [P.val.value_eq, P.val.weight_eq] using hl (P.val.piece i) (P.property i) hi
  · intro i _ _
    rw [← P.val.value_eq i, ← P.val.weight_eq i]
    exact typeI_eval_le_l1 (P.val.piece i) (P.property i) y

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Pathwise nullity excludes four recurrent hits by reconstruction of a limiting infinite path. -/
lemma not_all_four_hits {f : Family} (x : ℕ → Γ →₀ ℝ) (J T : ℕ → ℕ)
    (hJT : ∀ i, J i ≤ T i)
    (horder : ∀ i j, i < j → T i < J j)
    (hs : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x j).support, a < b)
    (hcoh : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x i).support,
      rho (min a b) (max a b) ≤ J j)
    (M A δ : ℝ) (hM : ∀ i, ‖norming.includeFinite (x i)‖ ≤ M) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hlow : ∀ i (e : TypeI f), (∀ j, e.child j ∈ f.norming) → e.weight < J i →
      |norming.evaluateArray (norming.includeFinite (x i)) e.value| ≤ A * f.theta e.weight)
    (htail : Tendsto (fun i => vectorL1 (x i) * tail (fun j => 1 / (f.m j : ℝ)) (T i+1)) atTop (𝓝 0))
    (hnull : ∀ Q : InfinitePath f, Tendsto (fun i => pathFunctional Q (norming.includeFinite (x i))) atTop (𝓝 0)) :
    ¬ (∀ w v t k : ℕ, w < v → v < t → t < k →
      ∃ P : LegalFinitePath f, WindowHit P (x w) (J w) (T w) δ ∧
        WindowHit P (x v) (J v) (T v) δ ∧ WindowHit P (x t) (J t) (T t) δ ∧
        WindowHit P (x k) (J k) (T k) δ) := by
  intro hall
  obtain ⟨D, hD⟩ := finite_window_covers x J T horder hcoh M δ hM hδ hall
  obtain ⟨P, W, hW, hP⟩ := CoverRecurrence.recurrent_of_covers
    (fun P i => WindowHit P (x i) (J i) (T i) δ) D hD
  have hJ : StrictMono J := fun i j hij => (hJT i).trans_lt (horder i j hij)
  have hwin (B : ℕ) : ∃ T' : ℕ, ∃ s : Finset Γ, ∀ᶠ n in atTop,
      ∃ i < (P n).val.length, B < (P n).val.raw.weight i ∧ (P n).val.raw.weight i ≤ T' ∧
        ∃ a ∈ s, a ∈ ((P n).val.raw.piece i).support := by
    obtain ⟨i, hi, hBi⟩ := hW.exists_gt B
    refine ⟨T i, (x i).support, (hP i hi).mono fun n hn => ?_⟩
    obtain ⟨j, hj, hj', a, ha, ha'⟩ := hn.anchor hδ
    exact ⟨j, j.isLt, hBi.trans_le ((hJ.id_le i).trans hj), hj', a, ha, ha'⟩
  obtain ⟨φ, Q, hφ, hQ⟩ := path_of_recurrent_windows (fun n => (P n).val)
    (fun n => (P n).property) hwin
  have hlim (i : ℕ) := stabilized_path_tendsto (fun n => (P (φ n)).val)
    (fun n => (P (φ n)).property) Q
    (fun j => (hQ j).mono fun _ hn => ⟨hn.1, hn.2.1, hn.2.2.1⟩) (norming.includeFinite (x i))
  have ht : Tendsto (fun i => A * tail f.theta (J i)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul ((tendsto_tail f.theta).comp hJ.tendsto_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/4)))
  obtain ⟨w₀, hw₀, hNw₀⟩ := hW.exists_gt N₀
  have hsmall : A * tail f.theta (J w₀) < δ/4 := hN₀ _ hNw₀.le
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htail.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/4)))
  have hn : Tendsto (fun i => |pathFunctional Q (norming.includeFinite (x i))|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (hnull Q).abs
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds (by linarith : (0:ℝ) < δ/2)))
  obtain ⟨i, hi, hBig⟩ := hW.exists_gt (max w₀ (max N₁ N₂))
  have hwi : w₀ < i := (le_max_left _ _).trans_lt hBig
  have hN1i : N₁ ≤ i := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hBig.le
  have hN2i : N₂ ≤ i := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hBig.le
  have hbound : ∀ᶠ n in atTop,
      δ/2 ≤ |finitePathFunctional (P (φ n)).val (P (φ n)).property (norming.includeFinite (x i))| := by
    filter_upwards [(hP w₀ hw₀).filter_mono hφ.tendsto_atTop, (hP i hi).filter_mono hφ.tendsto_atTop] with n hn₀ hni
    have he := window_error_bound (P (φ n)) (x w₀) (x i) (hs w₀ i hwi)
      (J w₀) (T w₀) (J i) (T i) (hJ.monotone hwi.le) (hJT i) δ A hδ hA hn₀ (hlow i)
    have ht' := hN₁ i hN1i
    have ha := abs_sub_abs_le_abs_sub
      (norming.evaluateArray (norming.includeFinite (x i)) ((P (φ n)).val.window (J i) (T i)))
      (finitePathFunctional (P (φ n)).val (P (φ n)).property (norming.includeFinite (x i)))
    rw [abs_sub_comm] at ha
    change δ < |norming.evaluateArray (norming.includeFinite (x i)) ((P (φ n)).val.window (J i) (T i))| at hni
    linarith
  have hge : δ/2 ≤ |pathFunctional Q (norming.includeFinite (x i))| :=
    ge_of_tendsto (hlim i).abs hbound
  exact (not_lt_of_ge hge) (hN₂ i hN2i)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.RamseyThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

/-- Four-hit thinning under the Type I partition estimate. -/
theorem four_hits_thinning {f : Family} (x : ℕ → Γ →₀ ℝ) (J T : ℕ → ℕ)
    (hJT : ∀ i, J i ≤ T i)
    (horder : ∀ i j, i < j → T i < J j)
    (hs : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x j).support, a < b)
    (hcoh : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x i).support,
      rho (min a b) (max a b) ≤ J j)
    (M A δ : ℝ) (hM : ∀ i, ‖norming.includeFinite (x i)‖ ≤ M) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hlow : ∀ i (e : TypeI f), (∀ j, e.child j ∈ f.norming) → e.weight < J i →
      |norming.evaluateArray (norming.includeFinite (x i)) e.value| ≤ A * f.theta e.weight)
    (htail : Tendsto (fun i => vectorL1 (x i) * tail (fun j => 1 / (f.m j : ℝ)) (T i+1)) atTop (𝓝 0))
    (hnull : ∀ Q : InfinitePath f, Tendsto (fun i => pathFunctional Q (norming.includeFinite (x i))) atTop (𝓝 0))
    (N : Set ℕ) (hN : N.Infinite) :
    ∃ W ⊆ N, W.Infinite ∧ ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ W → S.card = 4 →
      ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S, WindowHit P (x i) (J i) (T i) δ := by
  let pos (S : Finset ℕ) : Prop := ∃ P : LegalFinitePath f, ∀ i ∈ S, WindowHit P (x i) (J i) (T i) δ
  let color : Finset ℕ → Bool := fun S => decide (pos S)
  obtain ⟨W, b, hWN, hW, hhom⟩ := InfiniteRamsey.homogeneous_subset 4 color N hN
  have hfalse : b = false := by
    by_contra hb
    have hb' : b = true := Bool.eq_true_of_not_eq_false hb
    let u : ℕ → ℕ := Nat.nth (· ∈ W)
    have hu : StrictMono u := Nat.nth_strictMono hW
    have humem (i : ℕ) : u i ∈ W := Nat.nth_mem_of_infinite hW i
    apply not_all_four_hits (fun i => x (u i)) (fun i => J (u i)) (fun i => T (u i))
      (fun i => hJT (u i)) (fun i j hij => horder _ _ (hu hij))
      (fun i j hij => hs _ _ (hu hij)) (fun i j hij => hcoh _ _ (hu hij))
      M A δ (fun i => hM (u i)) hA hδ (fun i => hlow (u i))
      (htail.comp hu.tendsto_atTop) (fun Q => (hnull Q).comp hu.tendsto_atTop)
    intro w v t k hwv hvt htk
    let S : Finset ℕ := {u w,u v,u t,u k}
    have hc : color S = true := (hhom S (by
      intro i hi
      simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> exact humem _) (four_distinct_finset _ _ _ _ (hu hwv) (hu hvt) (hu htk))).trans hb'
    have hp : pos S := of_decide_eq_true hc
    obtain ⟨P, hP⟩ := hp
    exact ⟨P, hP _ (by simp [S]), hP _ (by simp [S]), hP _ (by simp [S]), hP _ (by simp [S])⟩
  refine ⟨W, hWN, hW, fun S hS hc hp => ?_⟩
  have he : color S = false := (hhom S hS hc).trans hfalse
  have hp' : pos S := hp
  change decide (pos S) = false at he
  rw [decide_eq_true hp'] at he
  contradiction

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PartitionBlocks
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

lemma UnitBlocks.norm_sum_lower {f S} (j : ℕ) (hj : 1 ≤ j) (v : UnitBlocks f S (f.L j)) :
    (f.L j : ℝ) / (2 * (f.m j : ℝ)) ≤ ‖norming.includeFinite (∑ i, v.vector i)‖ := by
  have hn := fun i => exists_unit_vector_normer (v.vector i) (v.unit i)
    (fun k hk => v.pure_color k hk i)
  choose g hg hgn hgs hgv using hn
  let e : TypeI f := {
    weight := j
    weight_pos := hj
    length := f.L j
    length_pos := f.L_pos j
    length_le := le_rfl
    child := g
    child_nonzero := hgn
    successive := by
      intro i l hil a ha b hb
      exact vectorCrop_successive (v.nonzero i) (v.nonzero l) (v.successive i l hil)
        a (hgs i a ha) b (hgs l b hb) }
  have hall : e.value ∈ Full := f.norming_subset_full (e.mem_family hg)
  have heval (i : Fin (f.L j)) : norming.evaluateArray (norming.includeFinite (∑ l, v.vector l)) (g i) =
      norming.evaluateArray (norming.includeFinite (v.vector i)) (g i) := by
    have hgi : g i ∈ Full := f.norming_subset_full (hg i)
    simp only [norming.evaluateArray_eq_functional _ ⟨g i, hgi⟩, map_sum]
    apply Finset.sum_eq_single i
    · intro l _ hli
      rw [← norming.evaluateArray_eq_functional]
      apply evaluateArray_finite_disjoint
      apply Finset.disjoint_left.mpr
      intro a ha hag
      rcases lt_or_gt_of_ne hli with hli | hil
      · exact (lt_irrefl a) (vectorCrop_successive (v.nonzero l) (v.nonzero i)
          (v.successive l i hli) a (support_mem_vectorCrop f _ _ a ha) a (hgs i a hag)).1
      · exact (lt_irrefl a) (vectorCrop_successive (v.nonzero i) (v.nonzero l)
          (v.successive i l hil) a (hgs i a hag) a (support_mem_vectorCrop f _ _ a ha)).1
    · simp
  have hm : (0 : ℝ) < f.m j := by exact_mod_cast f.m_pos j
  calc
    (f.L j : ℝ)/(2*(f.m j : ℝ)) = (1/(f.m j : ℝ)) * ∑ _ : Fin (f.L j), (1/2 : ℝ) := by simp; ring
    _ ≤ (1/(f.m j : ℝ)) * ∑ i, norming.evaluateArray (norming.includeFinite (v.vector i)) (g i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hgv i).le)) (one_div_nonneg.mpr hm.le)
    _ = norming.evaluateArray (norming.includeFinite (∑ i, v.vector i)) e.value := by
      rw [TypeI.value, map_smul, map_sum]
      simp only [e, Rat.smul_def, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, heval]
    _ ≤ |norming.evaluateArray (norming.includeFinite (∑ i, v.vector i)) e.value| := le_abs_self _
    _ ≤ ‖norming.includeFinite (∑ i, v.vector i)‖ := by
      rw [norming.evaluateArray_eq_functional _ ⟨_, hall⟩]
      exact norming.functional_bound _ _

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BlockEstimates
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

lemma blockSumSup_div_rpow_unbounded {f : Family} (z : BlockSequence f) (a : ℕ)
    (e : ℝ) (he : e < 1/(f.s : ℝ)) :
    ∀ R : ℝ, ∃ k : ℕ, 1 ≤ k ∧ R < blockSumSup f (z.tailSpan a) k / (k : ℝ)^e := by
  have hL : Tendsto (fun n => (Parameters.L f.s n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Parameters.L_strict f.s_ge_two).tendsto_atTop
  have hL1 (n : ℕ) : (1 : ℝ) < Parameters.L f.s n := by
    have hn : 1 < Parameters.L f.s n := by
      apply Nat.one_lt_pow
      · positivity [Family.s_ge_two f, Parameters.t_pos f.s n]
      · norm_num
    exact_mod_cast hn
  have hb (n : ℕ) : (0 : ℝ) < (Parameters.L f.s n : ℝ)/(Parameters.m f.s n : ℝ) :=
    div_pos (by exact_mod_cast Parameters.L_pos f.s n) (by exact_mod_cast Parameters.m_pos f.s n)
  have hg := RecordGrowth.div_rpow_tendsto_atTop hL1 hb hL
    (Parameters.parameter_growth f.s_ge_two) he
  intro R
  obtain ⟨n, hn⟩ := (hg.eventually (eventually_gt_atTop (2*R))).exists
  refine ⟨f.L (n+1), f.L_pos _, ?_⟩
  have hlo := (z.unitBlocks a (f.L (n+1))).norm_sum_lower (n+1) (by omega)
  have hsup := (z.unitBlocks a (f.L (n+1))).norm_sum_le_sup
  change (2*R) < (f.L (n+1) : ℝ)/(f.m (n+1) : ℝ)/(f.L (n+1) : ℝ)^e at hn
  have hp : 0 < (f.L (n+1) : ℝ)^e := Real.rpow_pos_of_pos (by exact_mod_cast f.L_pos _) e
  have hle := (div_le_div_of_nonneg_right (hlo.trans hsup) hp.le)
  have hid : (f.L (n+1) : ℝ)/(2*(f.m (n+1) : ℝ))/(f.L (n+1) : ℝ)^e =
      ((f.L (n+1) : ℝ)/(f.m (n+1) : ℝ)/(f.L (n+1) : ℝ)^e)/2 := by ring
  rw [hid] at hle
  linarith

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma intervalProjection_fixed (I : Set Γ) (hI : Set.OrdConnected I) (x : Γ →₀ ℝ)
    (hx : (x.support : Set Γ) ⊆ I) :
    intervalProjection I hI (norming.includeFinite x) = norming.includeFinite x := by
  apply coordinate_ext
  intro a
  simp only [intervalProjection, coordinate_projection, Crop.ordinalSet_set,
    norming.coordinate_includeFinite]
  split_ifs with ha
  · rfl
  · exact (Finsupp.notMem_support_iff.mp (fun h => ha (hx h))).symm

lemma intervalProjection_eq_zero (I : Set Γ) (hI : Set.OrdConnected I) (x : Γ →₀ ℝ)
    (hx : ∀ a ∈ x.support, a ∉ I) :
    intervalProjection I hI (norming.includeFinite x) = 0 := by
  apply coordinate_ext
  intro a
  simp only [intervalProjection, coordinate_projection, Crop.ordinalSet_set,
    norming.coordinate_includeFinite, map_zero]
  split_ifs with ha
  · exact Finsupp.notMem_support_iff.mp (fun h => hx a h ha)
  · rfl

lemma UnitBlocks.interval_norm_le {f S k} (v : UnitBlocks f S k)
    (I : Set Γ) (hI : Set.OrdConnected I) :
    ‖intervalProjection I hI (norming.includeFinite (∑ i, v.vector i))‖ ≤
      ‖norming.includeFinite (∑ i ∈ Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I), v.vector i)‖ + 2 := by
  let F := Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I)
  let B := Finset.univ.filter (fun i => (∃ a ∈ (v.vector i).support, a ∈ I) ∧
    ¬ ((v.vector i).support : Set Γ) ⊆ I)
  have hB : B.card ≤ 2 := IntervalIncidence.partial_intersections_le_two _ (fun i => (v.vector i).support)
    (fun i j hij a ha b hb => (v.successive i j hij a ha b hb).1) I hI
  have heq : intervalProjection I hI (norming.includeFinite (∑ i, v.vector i)) =
      norming.includeFinite (∑ i ∈ F, v.vector i) +
        ∑ i ∈ B, intervalProjection I hI (norming.includeFinite (v.vector i)) := by
    simp only [map_sum, F, B, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ((v.vector i).support : Set Γ) ⊆ I
    · simp only [hi, not_true_eq_false, and_false, ↓reduceIte, add_zero]
      exact intervalProjection_fixed I hI _ hi
    · by_cases hh : ∃ a ∈ (v.vector i).support, a ∈ I
      · simp only [hi, hh, not_false_eq_true, true_and, ↓reduceIte, map_zero, zero_add]
      · have hz : ∀ a ∈ (v.vector i).support, a ∉ I := by simpa only [not_exists, not_and] using hh
        simp only [hi, hh, false_and, ↓reduceIte, map_zero, add_zero]
        exact intervalProjection_eq_zero I hI _ hz
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  calc
    ‖∑ i ∈ B, intervalProjection I hI (norming.includeFinite (v.vector i))‖ ≤
        ∑ i ∈ B, ‖intervalProjection I hI (norming.includeFinite (v.vector i))‖ := norm_sum_le B _
    _ ≤ ∑ _i ∈ B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_projection_le _ _).trans_eq (v.unit i)
    _ = B.card := by simp
    _ ≤ 2 := by exact_mod_cast hB

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma UnitBlocks.partition_sum_record {f S k} (v : UnitBlocks f S k)
    (e : ℝ) (he : 0 < e) (he1 : e < 1) (hk : 1 ≤ k)
    (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      blockSumSup f S l ≤ blockSumSup f S k * ((l : ℝ)/(k : ℝ))^e)
    (d : ℕ) (I : Fin d → Set Γ) (hI : ∀ b, Set.OrdConnected (I b))
    (hIs : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) :
    ∑ b, ‖intervalProjection (I b) (hI b) (norming.includeFinite (∑ i, v.vector i))‖ ≤
      blockSumSup f S k * (d : ℝ)^(1-e) + 2*d := by
  let F := fun b : Fin d => Finset.univ.filter (fun i => ((v.vector i).support : Set Γ) ⊆ I b)
  have ha : 0 ≤ blockSumSup f S k := blockSumSup_nonneg ⟨v⟩
  have hw0 (b : Fin d) : 0 ≤ ((F b).card : ℝ)/(k : ℝ) := by positivity
  have hws : ∑ b, ((F b).card : ℝ)/(k : ℝ) ≤ 1 := by
    rw [← Finset.sum_div, div_le_one (by exact_mod_cast hk : (0 : ℝ) < k)]
    exact_mod_cast v.full_card_sum_le d I hIs
  have hp := RecordGrowth.sum_rpow_le_card (fun b => ((F b).card : ℝ)/(k : ℝ)) e he he1 hw0 hws
  simp only [Fintype.card_fin] at hp
  calc
    _ ≤ ∑ b, (blockSumSup f S k * (((F b).card : ℝ)/(k : ℝ))^e + 2) := by
      apply Finset.sum_le_sum
      intro b _
      exact (v.interval_norm_le (I b) (hI b)).trans (add_le_add_left (v.subsum_record (F b) e he hk hrec) 2)
    _ = blockSumSup f S k * ∑ b, (((F b).card : ℝ)/(k : ℝ))^e + 2*d := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp; ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hp ha) _

lemma UnitBlocks.normalized_partition {f S k} (v : UnitBlocks f S k)
    (N : ℕ) (hN : 1 ≤ N) (e : ℝ) (he : 0 < e) (he1 : e < 1) (hk : 1 ≤ k)
    (hrec : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      blockSumSup f S l ≤ blockSumSup f S k * ((l : ℝ)/(k : ℝ))^e)
    (hlarge : (N : ℝ) ≤ blockSumSup f S k)
    (hnear : blockSumSup f S k / 2 < ‖norming.includeFinite (∑ i, v.vector i)‖)
    (hexp : ∀ d : ℝ, 1 ≤ d → d ≤ N → d^(1-e) ≤ 2*d^(1/f.r)) :
    PartitionBound (‖norming.includeFinite (∑ i, v.vector i)‖⁻¹ • norming.includeFinite (∑ i, v.vector i)) N 8 f.r := by
  let x := norming.includeFinite (∑ i, v.vector i)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hnearX : blockSumSup f S k / 2 < ‖x‖ := hnear
  have hx : 0 < ‖x‖ := by linarith
  intro d hd hdN I hI hIs
  have hb : ∑ b, ‖intervalProjection (I b) (hI b) x‖ ≤
      blockSumSup f S k * (d : ℝ)^(1-e) + 2*d := v.partition_sum_record e he he1 hk hrec d I hI hIs
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
  have hdexp := hexp d hd0 hdN'
  have hpow : 1 ≤ (d : ℝ)^(1/f.r) := Real.one_le_rpow hd0 (one_div_nonneg.mpr f.r_pos.le)
  have hm : 0 ≤ blockSumSup f S k := by linarith
  have hprod : blockSumSup f S k * (d : ℝ)^(1-e) ≤
      4*‖x‖*(d : ℝ)^(1/f.r) := by
    have hh := mul_le_mul_of_nonneg_left hdexp hm
    have hnear' : blockSumSup f S k ≤ 2*‖x‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hnear' (by positivity : 0 ≤ 2*(d : ℝ)^(1/f.r))
    nlinarith
  have hdlarge : 2*(d : ℝ) ≤ 4*‖x‖ := by linarith
  have hsum : ∑ b, ‖intervalProjection (I b) (hI b) x‖ ≤ 8*‖x‖*(d : ℝ)^(1/f.r) := by
    have hnorm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4*‖x‖)
    nlinarith
  simp only [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm, ← Finset.mul_sum]
  change ‖x‖⁻¹ * (∑ b, ‖intervalProjection (I b) (hI b) x‖) ≤ _
  calc
    _ ≤ ‖x‖⁻¹ * (8*‖x‖*(d : ℝ)^(1/f.r)) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hx.le)
    _ = _ := by field_simp

/-- The constant-eight interval partition estimate in any prescribed algebraic tail of a block sequence. -/
theorem BlockSequence.exists_partition_unit {f : Family} (z : BlockSequence f)
    (a N : ℕ) (hN : 1 ≤ N) :
    ∃ u : Γ →₀ ℝ, u ∈ z.tailSpan a ∧ ‖norming.includeFinite u‖ = 1 ∧
      PartitionBound (norming.includeFinite u) N 8 f.r := by
  have hs : 1 < (f.s : ℝ) := by exact_mod_cast (show 1 < f.s from f.s_ge_two)
  obtain ⟨e, he, hes, hexp⟩ := RecordGrowth.choose_exponent (f.s : ℝ) N hs (by exact_mod_cast hN)
  have he1 : e < 1 := hes.trans ((div_lt_one (by linarith : (0 : ℝ) < f.s)).mpr hs)
  obtain ⟨k, hk, hklarge, hkrec⟩ := RecordGrowth.exists_record
    (blockSumSup f (z.tailSpan a)) e N he.le (Nat.cast_nonneg _)
    (blockSumSup_div_rpow_unbounded z a e hes)
  have hnon : Nonempty (UnitBlocks f (z.tailSpan a) k) := ⟨z.unitBlocks a k⟩
  have hak : 0 < blockSumSup f (z.tailSpan a) k := lt_of_lt_of_le (by exact_mod_cast hN) hklarge
  obtain ⟨v, hv⟩ := unitBlocks_near_sup hnon hak
  let w := ∑ i, v.vector i
  have hvw : blockSumSup f (z.tailSpan a) k / 2 < ‖norming.includeFinite w‖ := hv
  have hw : 0 < ‖norming.includeFinite w‖ := by linarith
  refine ⟨‖norming.includeFinite w‖⁻¹ • w, Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun i _ => v.mem i)), ?_, ?_⟩
  · rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hw.ne']
  · rw [map_smul]
    apply v.normalized_partition N hN e he he1 hk hkrec hklarge hv
    intro d hd hdN
    have hconj := Parameters.s_r_conjugate f.s_ge_two
    have heq : 1/f.r = 1 - 1/(f.s : ℝ) := (eq_sub_iff_add_eq).mpr
      (by simpa only [Family.r, one_div] using hconj.symm.inv_add_inv_eq_one)
    simpa only [heq] using hexp d hd hdN

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TailBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma exists_preliminaryData {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n a B : ℕ) : ∃ d : PreliminaryData z J ε n, d.start = a ∧ B < d.lower := by
  let j := B+J+z.prefixRho a+1
  obtain ⟨u, hu, hunit, hpart⟩ := z.exists_partition_unit a (f.L j) (f.L_pos j)
  obtain ⟨b, hb, hbu⟩ := z.support_subset_prefix a hu
  have ht : Tendsto (fun t => vectorL1 u * tail (fun l => 1/(f.m l : ℝ)) (t+1)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((tendsto_tail (fun l => 1/(f.m l : ℝ))).comp (tendsto_add_atTop_nat 1)))
  have hmin : 0 < min (ε/2) (1/(n+1 : ℝ)) := lt_min (by linarith) (by positivity)
  obtain ⟨T, hTj, hT⟩ := (eventually_ge_atTop j |>.and (ht.eventually (eventually_lt_nhds hmin))).exists
  let d : PreliminaryData z J ε n := {
    vector := u
    start := a
    finish := b
    lower := j
    upper := T
    mem := hu
    support := hbu
    finish_ge := hb
    unit := hunit
    prescribed := by dsimp [j]; omega
    order := hTj
    coherence := by dsimp [j]; omega
    partition := hpart
    tail_small := hT.le.trans (min_le_left _ _)
    tail_vanish := hT.le.trans (min_le_right _ _) }
  exact ⟨d, rfl, by change B < j; dsimp [j]; omega⟩

noncomputable def preliminaryChoice {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n a B : ℕ) : PreliminaryData z J ε n := (exists_preliminaryData z J ε hε n a B).choose

lemma preliminaryChoice_spec {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n a B : ℕ) : (preliminaryChoice z J ε hε n a B).start = a ∧
      B < (preliminaryChoice z J ε hε n a B).lower := (exists_preliminaryData z J ε hε n a B).choose_spec

noncomputable def preliminaryData {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a : ℕ) : (n : ℕ) → PreliminaryData z J ε n
  | 0 => preliminaryChoice z J ε hε 0 a 0
  | n+1 => preliminaryChoice z J ε hε (n+1) (preliminaryData z J ε hε a n).finish
      (preliminaryData z J ε hε a n).upper

lemma preliminaryData_start_zero {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    (preliminaryData z J ε hε a 0).start = a := (preliminaryChoice_spec z J ε hε 0 a 0).1

lemma preliminaryData_start_succ {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a n : ℕ) :
    (preliminaryData z J ε hε a (n+1)).start = (preliminaryData z J ε hε a n).finish :=
  (preliminaryChoice_spec z J ε hε (n+1) _ _).1

lemma preliminaryData_order_succ {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a n : ℕ) :
    (preliminaryData z J ε hε a n).upper < (preliminaryData z J ε hε a (n+1)).lower :=
  (preliminaryChoice_spec z J ε hε (n+1) _ _).2

lemma preliminaryData_start_mono {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    Monotone (fun n => (preliminaryData z J ε hε a n).start) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [preliminaryData_start_succ]
  exact (preliminaryData z J ε hε a n).finish_ge

lemma preliminaryData_finish_le_start {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a i j : ℕ) (hij : i < j) :
    (preliminaryData z J ε hε a i).finish ≤ (preliminaryData z J ε hε a j).start := by
  rw [← preliminaryData_start_succ]
  exact preliminaryData_start_mono z J ε hε a (by omega)

lemma preliminaryData_order {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a i j : ℕ) (hij : i < j) :
    (preliminaryData z J ε hε a i).upper < (preliminaryData z J ε hε a j).lower := by
  have hlow : StrictMono (fun n => (preliminaryData z J ε hε a n).lower) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (preliminaryData z J ε hε a n).order.trans_lt (preliminaryData_order_succ z J ε hε a n)
  exact (preliminaryData_order_succ z J ε hε a i).trans_le (hlow.monotone (by omega))

noncomputable def preliminaryBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    BlockSequence f where
  vector n := (preliminaryData z J ε hε a n).vector
  nonzero n := by
    intro hz
    have hh := (preliminaryData z J ε hε a n).unit
    simp [hz] at hh
  successive i j hij := z.prefix_tail_successive _ (preliminaryData z J ε hε a i).support
    (z.tailSpan_mono (preliminaryData_finish_le_start z J ε hε a i j hij) (preliminaryData z J ε hε a j).mem)
  pure_color c hc n := z.tail_pure_color _ (preliminaryData z J ε hε a n).mem c hc

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma BlockSequence.norm_sub_ge_one {f : Family} (z : BlockSequence f) {i j : ℕ} (hij : i < j)
    (hi : ‖z.embed i‖ = 1) : 1 ≤ ‖norming.includeFinite (z.vector i-z.vector j)‖ := by
  have hne := Finsupp.support_nonempty_iff.mpr (z.nonzero i)
  let I := ordinalHull (z.vector i).support hne
  have hI : Set.OrdConnected I := ordinalHull_connected _ _
  have hfix : intervalProjection I hI (z.embed i) = z.embed i :=
    intervalProjection_fixed I hI _ (fun _ ha => mem_ordinalHull hne ha)
  have hzero : intervalProjection I hI (z.embed j) = 0 := by
    apply intervalProjection_eq_zero
    intro a ha haI
    have hlt := (z.successive i j hij _ ((z.vector i).support.max'_mem hne) a ha).1
    exact (not_lt_of_ge haI.2) hlt
  have heq : intervalProjection I hI (norming.includeFinite (z.vector i-z.vector j)) = z.embed i := by
    rw [map_sub]
    change intervalProjection I hI (z.embed i-z.embed j) = z.embed i
    rw [map_sub, hfix, hzero, sub_zero]
  calc
    1 = ‖intervalProjection I hI (norming.includeFinite (z.vector i-z.vector j))‖ := by rw [heq, hi]
    _ ≤ _ := norm_projection_le _ _

noncomputable def BlockSequence.pairDifferences {f : Family} (z : BlockSequence f)
    (hz : ∀ n, ‖z.embed n‖ = 1) : BlockSequence f where
  vector n := z.vector (2*n)-z.vector (2*n+1)
  nonzero n := by
    intro hh
    have hi := z.norm_sub_ge_one (by omega : 2*n < 2*n+1) (hz (2*n))
    simp [hh] at hi
    norm_num at hi
  successive i j hij a ha b hb := by
    have ha' := Finset.mem_union.mp (Finsupp.support_sub ha)
    have hb' := Finset.mem_union.mp (Finsupp.support_sub hb)
    rcases ha' with ha | ha <;> rcases hb' with hb | hb
    all_goals exact z.successive _ _ (by omega) a ha b hb
  pure_color c hc n a ha := by
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with ha | ha
    · exact z.pure_color c hc (2*n) a ha
    · exact z.pure_color c hc (2*n+1) a ha

lemma BlockSequence.pairDifferences_norm {f : Family} (z : BlockSequence f)
    (hz : ∀ n, ‖z.embed n‖ = 1) (n : ℕ) :
    1 ≤ ‖(z.pairDifferences hz).embed n‖ ∧ ‖(z.pairDifferences hz).embed n‖ ≤ 2 := by
  refine ⟨z.norm_sub_ge_one (by omega) (hz (2*n)), ?_⟩
  change ‖norming.includeFinite (z.vector (2*n)-z.vector (2*n+1))‖ ≤ 2
  rw [map_sub]
  exact (norm_sub_le _ _).trans (by change ‖z.embed (2*n)‖+‖z.embed (2*n+1)‖≤2; rw [hz, hz]; norm_num)

lemma BlockSequence.pairDifferences_path_null {f : Family} (z : BlockSequence f)
    (hz : ∀ n, ‖z.embed n‖ = 1) (hC : ∀ P : InfinitePath f, CauchySeq (fun n => pathFunctional P (z.embed n))) :
    ∀ P : InfinitePath f, Tendsto (fun n => pathFunctional P ((z.pairDifferences hz).embed n)) atTop (𝓝 0) := by
  intro P
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hC P)
  have he : StrictMono (fun n : ℕ => 2*n) := by intro i j h; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2*n+1) := by intro i j h; dsimp; omega
  have ht := (ha.comp he.tendsto_atTop).sub (ha.comp ho.tendsto_atTop)
  simpa only [BlockSequence.embed, BlockSequence.pairDifferences, map_sub, sub_self, Function.comp_apply] using ht

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma exists_windowBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    Nonempty (WindowBlocks z J ε a) := by
  let d := preliminaryData z J ε hε a
  let u := preliminaryBlocks z J ε hε a
  have hu (n : ℕ) : ‖u.embed n‖ = 1 := (d n).unit
  obtain ⟨φ, hφ, hC⟩ := u.all_paths_cauchy 1 (fun n => (hu n).le)
  let v := u.subsequence φ hφ
  have hv (n : ℕ) : ‖v.embed n‖ = 1 := hu (φ n)
  let x := v.pairDifferences hv
  let lo (n : ℕ) := (d (φ (2*n))).lower
  let up (n : ℕ) := (d (φ (2*n+1))).upper
  have hx (n : ℕ) : x.vector n = (d (φ (2*n))).vector - (d (φ (2*n+1))).vector := rfl
  have hord {i j : ℕ} (hij : i < j) : (d i).upper < (d j).lower :=
    preliminaryData_order z J ε hε a i j hij
  have hfin {i j : ℕ} (hij : i < j) : (d i).finish ≤ (d j).start :=
    preliminaryData_finish_le_start z J ε hε a i j hij
  have hstart (n : ℕ) : a ≤ (d n).start := by
    rw [← preliminaryData_start_zero z J ε hε a]
    exact preliminaryData_start_mono z J ε hε a (Nat.zero_le n)
  have hup (n : ℕ) : (d (φ (2*n))).upper ≤ (d (φ (2*n+1))).upper :=
    (hord (hφ (by omega))).le.trans (d (φ (2*n+1))).order
  have htail (n : ℕ) : vectorL1 (x.vector n) * tail (fun j => 1/(f.m j : ℝ)) (up n+1) ≤
      vectorL1 (d (φ (2*n))).vector * tail (fun j => 1/(f.m j : ℝ)) ((d (φ (2*n))).upper+1) +
      vectorL1 (d (φ (2*n+1))).vector * tail (fun j => 1/(f.m j : ℝ)) ((d (φ (2*n+1))).upper+1) := by
    rw [hx]
    exact tail_sub_mul_le _ _ _ _ (hup n)
  have hdec (n : ℕ) : vectorL1 (x.vector n) * tail (fun j => 1/(f.m j : ℝ)) (up n+1) ≤ 2/(n+1 : ℝ) := by
    have he : (n : ℝ)+1 ≤ (φ (2*n) : ℝ)+1 := by exact_mod_cast (show n+1 ≤ φ (2*n)+1 by
      have hh : 2*n ≤ φ (2*n) := hφ.id_le (2*n)
      omega)
    have ho : (n : ℝ)+1 ≤ (φ (2*n+1) : ℝ)+1 := by exact_mod_cast (show n+1 ≤ φ (2*n+1)+1 by
      have hh : 2*n+1 ≤ φ (2*n+1) := hφ.id_le (2*n+1)
      omega)
    calc
      _ ≤ 1/(φ (2*n)+1 : ℝ) + 1/(φ (2*n+1)+1 : ℝ) :=
        (htail n).trans (add_le_add (d (φ (2*n))).tail_vanish (d (φ (2*n+1))).tail_vanish)
      _ ≤ 1/(n+1 : ℝ) + 1/(n+1 : ℝ) := add_le_add (one_div_le_one_div_of_le (by positivity) he)
        (one_div_le_one_div_of_le (by positivity) ho)
      _ = _ := by ring
  refine ⟨{
    blocks := x
    lower := lo
    upper := up
    mem_tail := ?_
    lower_norm := fun n => (v.pairDifferences_norm hv n).1
    upper_norm := fun n => (v.pairDifferences_norm hv n).2
    prescribed := fun n => (d (φ (2*n))).prescribed
    order := ?_
    separated := ?_
    coherence := ?_
    partition := ?_
    tail_small := ?_
    tail_vanish := ?_
    path_null := v.pairDifferences_path_null hv hC }⟩
  · intro n
    rw [hx]
    exact (z.tailSpan a).sub_mem (z.tailSpan_mono (hstart _) (d _).mem)
      (z.tailSpan_mono (hstart _) (d _).mem)
  · intro n
    exact ((d (φ (2*n))).order.trans (hup n))
  · intro i j hij
    exact hord (hφ (by omega : 2*i+1 < 2*j))
  · intro i j k hji hki α hα β hβ
    have hprefix (t : ℕ) (hti : t < i) {γ : Γ} (hγ : γ ∈ (x.vector t).support) : γ ∈ z.prefixSupport (d (φ (2*i))).start := by
      rw [hx] at hγ
      rcases Finset.mem_union.mp (Finsupp.support_sub hγ) with hh | hh
      · exact z.prefixSupport_mono (hfin (hφ (by omega))) ((d _).support hh)
      · exact z.prefixSupport_mono (hfin (hφ (by omega))) ((d _).support hh)
    exact (z.le_prefixRho _ (hprefix j hji hα) (hprefix k hki hβ)).trans_lt (d (φ (2*i))).coherence
  · intro n
    have hLow : (d (φ (2*n))).lower ≤ (d (φ (2*n+1))).lower :=
      (d (φ (2*n))).order.trans (hord (hφ (by omega : 2*n < 2*n+1))).le
    have hL := FamilyL_mono f hLow
    have hh := (d (φ (2*n))).partition.sub ((d (φ (2*n+1))).partition.mono hL)
    change PartitionBound (norming.includeFinite (x.vector n)) _ 16 _
    rw [hx, map_sub]
    simpa only [lo, show (8 : ℝ)+8 = 16 by norm_num] using hh
  · intro n
    exact (htail n).trans (by linarith [(d (φ (2*n))).tail_small, (d (φ (2*n+1))).tail_small])
  · have ht : Tendsto (fun n : ℕ => 2/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0)))
    apply squeeze_zero _ hdec ht
    intro n
    exact mul_nonneg (vectorL1_nonneg _) (tail_nonneg _ (fun _ => by positivity) _)

lemma WindowBlocks.four_hits {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : WindowBlocks z J ε a) (δ : ℝ) (hδ : 0 < δ) (N : Set ℕ) (hN : N.Infinite) :
    ∃ W ⊆ N, W.Infinite ∧ ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ W → S.card = 4 →
      ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S, WindowHit P (w.blocks.vector i) (w.lower i) (w.upper i) δ := by
  apply four_hits_thinning _ _ _ w.order w.separated
    (fun i j hij α hα β hβ => (w.blocks.successive i j hij α hα β hβ).1)
    (fun i j hij α hα β hβ => (w.coherence j i i hij hij α hα β hβ).le)
    2 16 δ w.upper_norm (by norm_num) hδ _ w.tail_vanish w.path_null N hN
  intro i e he hj
  exact typeI_eval_le_of_partition _ _ _ (by norm_num) (w.partition i) e he (FamilyL_mono f hj.le)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

noncomputable def WindowBlocks.subsequence {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : WindowBlocks z J ε a) (φ : ℕ → ℕ) (hφ : StrictMono φ) : WindowBlocks z J ε a where
  blocks := w.blocks.subsequence φ hφ
  lower n := w.lower (φ n)
  upper n := w.upper (φ n)
  mem_tail n := w.mem_tail (φ n)
  lower_norm n := w.lower_norm (φ n)
  upper_norm n := w.upper_norm (φ n)
  prescribed n := w.prescribed (φ n)
  order n := w.order (φ n)
  separated i j h := w.separated (φ i) (φ j) (hφ h)
  coherence i j k hji hki := w.coherence (φ i) (φ j) (φ k) (hφ hji) (hφ hki)
  partition n := w.partition (φ n)
  tail_small n := w.tail_small (φ n)
  tail_vanish := w.tail_vanish.comp hφ.tendsto_atTop
  path_null P := (w.path_null P).comp hφ.tendsto_atTop

lemma exists_thinnedWindows {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ)
    (hε : 0 < ε) (a : ℕ) : Nonempty (ThinnedWindows z J ε a) := by
  obtain ⟨w⟩ := exists_windowBlocks z J ε hε a
  let δ (n i : ℕ) : ℝ := ε / (w.upper i+1 : ℝ) * (1/2 : ℝ)^(n+1)
  have hδ (n i : ℕ) : 0 < δ n i := by dsimp [δ]; positivity
  let R (n i : ℕ) (W : Set ℕ) : Prop := ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ W → S.card = 4 →
    ¬ ∃ P : LegalFinitePath f, ∀ k ∈ S,
      WindowHit P (w.blocks.vector k) (w.lower k) (w.upper k) (δ n i)
  have hR (n i : ℕ) (N : Set ℕ) (hN : N.Infinite) : ∃ W ⊆ N, W.Infinite ∧ R n i W :=
    w.four_hits (δ n i) (hδ n i) N hN
  obtain ⟨φ, hφ, W, hW, hlater⟩ := AdaptiveThinning.exists_adaptive R hR
  refine ⟨{
    toWindowBlocks := w.subsequence φ hφ
    threshold n := δ n (φ n)
    threshold_pos n := hδ n (φ n)
    threshold_charge_succ := ?_
    threshold_charge := ?_
    four_hits_after := ?_ }⟩
  · intro n
    change (w.upper (φ n)+1 : ℝ) * (ε / (w.upper (φ n)+1 : ℝ) * (1/2 : ℝ)^(n+1)) = _
    field_simp
  · intro n
    change (w.upper (φ n) : ℝ) * (ε / (w.upper (φ n)+1 : ℝ) * (1/2 : ℝ)^(n+1)) ≤ _
    have hh : (w.upper (φ n) : ℝ) * (ε / (w.upper (φ n)+1 : ℝ)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < w.upper (φ n)+1)]
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^(n+1))
  · intro n S hn hcard hh
    apply hW n (S.image φ) _ _
    · obtain ⟨P, hP⟩ := hh
      refine ⟨P, ?_⟩
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact hP i hi
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact hlater n i (hn i hi)
    · rw [Finset.card_image_of_injective _ hφ.injective, hcard]

lemma ThinnedWindows.hits_after_le_three {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (n : ℕ) (s : Finset ℕ) (P : LegalFinitePath f) :
    (s.filter (fun i => n < i ∧ WindowHit P (w.blocks.vector i) (w.lower i) (w.upper i) (w.threshold n))).card ≤ 3 := by
  by_contra! h
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show 4 ≤ (s.filter (fun i => n < i ∧
    WindowHit P (w.blocks.vector i) (w.lower i) (w.upper i) (w.threshold n))).card by omega)
  exact w.four_hits_after n S (fun i hi => (Finset.mem_filter.mp (hS hi)).2.1) hcard
    ⟨P, fun i hi => (Finset.mem_filter.mp (hS hi)).2.2⟩

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma crop_or_fixed_of_nonzero {f : Family} (z : BlockSequence f) (A : Crop) (i : ℕ) (g : Array)
    (h : norming.evaluateArray (z.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) g) ≠ 0) :
    PartialBlock z A i ∨ norming.evaluateArray (z.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) g) =
      norming.evaluateArray (z.embed i) g := by
  by_cases hh : (↑(z.vector i).support : Set Γ) ⊆ A.set f
  · exact Or.inr (evaluateArray_crop_finite_fixed _ _ hh _)
  · exact Or.inl ⟨evaluateArray_crop_nonzero_support _ _ _ h, hh⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma TypeII.window_column_bound {f : Family} (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming)
    (J T : ℕ) (c : Fin e.length → ℝ) (x : E) :
    (∑ b, |c b| * |norming.evaluateArray x (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window J T))|) ≤
      (∑ b, |c b|^f.q)^(1/f.q) * ‖x‖ := by
  let A (b : Fin e.length) := ((e.path b).weightCrop J T).inter (e.crop b)
  have hd : Pairwise (fun i j => Disjoint ((e.path i).active (A i)) ((e.path j).active (A j))) := by
    intro b c hbc
    exact (e.disjoint_active hbc).mono (TypeII.active_crop_subset _ _ _) (TypeII.active_crop_subset _ _ _)
  have he (b : Fin e.length) : croppedPathFunctional (e.path b) (A b) x =
      norming.evaluateArray x (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window J T)) := by
    change norming.evaluateArray x (_root_.OAI.SeparableQuotient.Norming.restrict ((A b).set f) (e.path b).value) = _
    dsimp only [A]
    rw [Crop.inter_set, Set.inter_comm, ← restrict_restrict, FinitePath.weightCrop_value]
  simpa only [he] using cropped_weighted_abs_sum_bound e.path A hm hd c x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma cropped_window_anchor {f : Family} (P : FinitePath f) (A : Crop) (x : E) (J T : ℕ)
    (h : norming.evaluateArray x (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) (P.window J T)) ≠ 0) :
    ∃ j ∈ P.active A, J ≤ j ∧ j ≤ T := by
  simp only [FinitePath.window, restrict_sum, map_sum] at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hw : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T := by
    by_contra hn
    simp only [ite_eq_right hn, restrict_zero, map_zero, ne_eq, not_true_eq_false] at hi
  rw [ite_eq_left hw] at hi
  refine ⟨P.raw.weight i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩, hw⟩
  intro hh
  exact hi (by rw [hh, map_zero])

/-- Distinct original active weights bound the number of paths contributing
in a window. The +1 version is convenient for zero-based natural indices;
the positive-weight sharper T bound is not needed for the geometric charge. -/
lemma TypeII.cropped_window_count {f : Family} (e : TypeII f) (x : E) (J T : ℕ) :
    (Finset.univ.filter (fun b => norming.evaluateArray x
      (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window J T)) ≠ 0)).card ≤ T+1 := by
  let S := Finset.univ.filter (fun b => norming.evaluateArray x
    (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window J T)) ≠ 0)
  have h (b : S) : ∃ j ∈ (e.path b).active (e.crop b), J ≤ j ∧ j ≤ T :=
    cropped_window_anchor _ _ _ _ _ (Finset.mem_filter.mp b.property).2
  choose w hw hwJ hwT using h
  let v (b : S) : Fin (T+1) := ⟨w b, by have := hwT b; omega⟩
  have hinj : Function.Injective v := by
    intro b c hbc
    apply Subtype.ext
    by_contra hne
    have hd := e.disjoint_active hne
    have he : w b = w c := congrArg Fin.val hbc
    exact Finset.disjoint_left.mp hd (hw b) (he.symm ▸ hw c)
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective v hinj

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def ThinnedWindows.middleEval {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (b : Fin e.length) (i : ℕ) : ℝ :=
  norming.evaluateArray (w.blocks.embed i)
    (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window (w.lower i) (w.upper i)))

noncomputable def ThinnedWindows.marks {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (b : Fin e.length) : Finset ℕ :=
  let n := firstNonzero s (w.middleEval e b)
  ({n} ∩ s) ∪ (s.filter (PartialBlock w.blocks (e.crop b))) ∪
    (s.filter (fun i => n < i ∧ WindowHit ⟨e.path b, hm b⟩ (w.blocks.vector i)
      (w.lower i) (w.upper i) (w.threshold n)))

lemma ThinnedWindows.marks_card {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (b : Fin e.length) :
    (w.marks e hm s b).card ≤ 8 := by
  have h1 : ({firstNonzero s (w.middleEval e b)} ∩ s).card ≤ 1 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h2 := w.blocks.partial_crop_le_four (e.crop b) s
  have h3 := w.hits_after_le_three (firstNonzero s (w.middleEval e b)) s ⟨e.path b, hm b⟩
  unfold marks
  apply (Finset.card_union_le _ _).trans
  have hh := Finset.card_union_le ({firstNonzero s (w.middleEval e b)} ∩ s)
    (s.filter (PartialBlock w.blocks (e.crop b)))
  omega

lemma ThinnedWindows.unmarked_small {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (b : Fin e.length)
    (i : ℕ) (hi : i ∈ s) (ht : w.middleEval e b i ≠ 0) (hmark : i ∉ w.marks e hm s b) :
    firstNonzero s (w.middleEval e b) < i ∧
      |w.middleEval e b i| ≤ w.threshold (firstNonzero s (w.middleEval e b)) := by
  have hle := firstNonzero_le hi ht
  have hne : i ≠ firstNonzero s (w.middleEval e b) := by
    intro hh
    apply hmark
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_singleton.mpr hh, hi⟩))
  have hlt : firstNonzero s (w.middleEval e b) < i := lt_of_le_of_ne hle (Ne.symm hne)
  have hp : ¬ PartialBlock w.blocks (e.crop b) i := by
    intro hh
    exact hmark (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hh⟩)))
  have hn : ¬ WindowHit ⟨e.path b, hm b⟩ (w.blocks.vector i) (w.lower i) (w.upper i)
      (w.threshold (firstNonzero s (w.middleEval e b))) := by
    intro hh
    exact hmark (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hlt,hh⟩))
  have he := (crop_or_fixed_of_nonzero w.blocks (e.crop b) i
    ((e.path b).window (w.lower i) (w.upper i)) ht).resolve_left hp
  refine ⟨hlt, ?_⟩
  change |norming.evaluateArray (w.blocks.embed i) _| ≤ _
  rw [he]
  exact le_of_not_gt hn

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

lemma ThinnedWindows.unmarked_column {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (hε : 0 ≤ ε) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ)
    (i : ℕ) (hi : i ∈ s) :
    (∑ b, if i ∉ w.marks e hm s b then |(e.coefficient b : ℝ)| * |w.middleEval e b i| else 0) ≤ ε := by
  let U : Finset (Fin e.length) := Finset.univ.filter
    (fun b => w.middleEval e b i ≠ 0 ∧ i ∉ w.marks e hm s b)
  let first (b : Fin e.length) := firstNonzero s (w.middleEval e b)
  have hU (b : Fin e.length) (hb : b ∈ U) : first b < i ∧ |w.middleEval e b i| ≤ w.threshold (first b) :=
    w.unmarked_small e hm s b i hi (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  have hcount (n : ℕ) : (U.filter (fun b => first b = n)).card ≤ w.upper n+1 := by
    apply le_trans (Finset.card_le_card ?_) (TypeII.cropped_window_count e (w.blocks.embed n) (w.lower n) (w.upper n))
    intro b hb
    have hbU := Finset.mem_filter.mp hb
    have hn := (firstNonzero_mem hi (Finset.mem_filter.mp hbU.1).2.1).2
    change w.middleEval e b (first b) ≠ 0 at hn
    rw [hbU.2] at hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
  calc
    _ = ∑ b ∈ U, |(e.coefficient b : ℝ)| * |w.middleEval e b i| := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases ht : w.middleEval e b i = 0 <;> by_cases hm' : i ∈ w.marks e hm s b <;> simp [ht,hm']
    _ ≤ ∑ b ∈ U, w.threshold (first b) := Finset.sum_le_sum (fun b hb =>
      (mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (abs_nonneg _)).trans (by simpa using (hU b hb).2))
    _ = ∑ n ∈ Finset.range i, ∑ b ∈ U.filter (fun b => first b = n), w.threshold (first b) :=
      (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_range.mpr (hU b hb).1) _).symm
    _ = ∑ n ∈ Finset.range i, ((U.filter (fun b => first b = n)).card : ℝ)*w.threshold n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [show (∑ b ∈ U.filter (fun b => first b = n), w.threshold (first b)) =
          ∑ b ∈ U.filter (fun b => first b = n), w.threshold n from
        Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
      simp
    _ ≤ ∑ n ∈ Finset.range i, ε*(1/2 : ℝ)^(n+1) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← w.threshold_charge_succ n]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount n) (w.threshold_pos n).le
    _ ≤ ε := geometric_charge_le ε hε i

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.MarkedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

noncomputable def ThinnedWindows.markedCharge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) : ℝ :=
  ∑ b, if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)| *|w.middleEval e b i| else 0

lemma ThinnedWindows.markedCharge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    0 ≤ w.markedCharge e hm s i := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity

lemma ThinnedWindows.marked_column {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    w.markedCharge e hm s i ≤
      2*(∑ b, if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)|^f.q else 0)^(1/f.q) := by
  let c (b : Fin e.length) : ℝ := if i.val ∈ w.marks e hm s b then e.coefficient b else 0
  have he (b : Fin e.length) : |c b| *|w.middleEval e b i| =
      if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)| *|w.middleEval e b i| else 0 := by
    dsimp [c]
    split_ifs <;> simp
  have hp (b : Fin e.length) : |c b|^f.q =
      if i.val ∈ w.marks e hm s b then |(e.coefficient b : ℝ)|^f.q else 0 := by
    dsimp [c]
    split_ifs
    · rfl
    · rw [abs_zero, Real.zero_rpow]
      exact ne_of_gt (show 0 < f.q from zero_lt_one.trans (Parameters.q_bounds f.s_ge_two).1)
  calc
    _ = ∑ b, |c b| *|w.middleEval e b i| := by simp only [he, markedCharge]
    _ ≤ (∑ b, |c b|^f.q)^(1/f.q)*‖w.blocks.embed i‖ :=
      TypeII.window_column_bound e hm (w.lower i) (w.upper i) c (w.blocks.embed i)
    _ ≤ (∑ b, |c b|^f.q)^(1/f.q)*2 :=
      mul_le_mul_of_nonneg_left (w.upper_norm i) (Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) _)
    _ = _ := by simp only [hp]; ring

lemma ThinnedWindows.marked_vector_bounds {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) :
    ‖vec f.exponent (w.markedCharge e hm s)‖ ≤ 16 ∧
      (∑ i : s, w.markedCharge e hm s i) ≤ 16*(s.card : ℝ)^(1-1/f.q) := by
  let marks (b : Fin e.length) : Finset s := (w.marks e hm s b).subtype (· ∈ s)
  have hmarks (b : Fin e.length) : (marks b).card ≤ 8 := by
    rw [show (marks b).card = ((w.marks e hm s b).filter (· ∈ s)).card by simp only [marks,Finset.card_subtype]]
    exact (Finset.card_filter_le _ _).trans (w.marks_card e hm s b)
  have hh := marked_norm_bound f.q (Parameters.q_bounds f.s_ge_two).1 f.exponent
    (by simpa only [Family.exponent_toReal,Family.q,Family.r] using (Parameters.q_bounds f.s_ge_two).2.1.le)
    (fun b => (e.coefficient b : ℝ)) e.bound marks hmarks (w.markedCharge e hm s)
    (w.markedCharge_nonneg e hm s) (fun i => by simpa only [marks,Finset.mem_subtype] using w.marked_column e hm s i)
  simpa only [Fintype.card_coe] using hh

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TreeCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

noncomputable def TypeI.lowAssign {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (h : Fin e.length) : Finset s :=
  I.filter (fun i => e.weight < w.lower i ∧ TypeI.hitChildren e (w.blocks.vector i) = {h})

lemma TypeI.lowAssign_subset {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (h : Fin e.length) :
    TypeI.lowAssign w e s I h ⊆ I := Finset.filter_subset _ _

lemma TypeI.lowAssign_disjoint {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s)
    (h k : Fin e.length) (hhk : h ≠ k) :
    Disjoint (TypeI.lowAssign w e s I h) (TypeI.lowAssign w e s I k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hk
  exact hhk (Finset.singleton_injective ((Finset.mem_filter.mp hi).2.2.symm.trans (Finset.mem_filter.mp hk).2.2))

noncomputable def TypeI.boundaryCharge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  if i ∈ I ∧ e.weight < w.lower i then
    (16 / (f.m e.weight : ℝ)) * (TypeI.boundaryDegree e w.blocks i)^(1/f.r) else 0

lemma TypeI.boundaryCharge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeI.boundaryCharge w e s I i := by
  have hd := TypeI.boundaryDegree_nonneg e w.blocks i
  unfold TypeI.boundaryCharge
  split_ifs <;> positivity

lemma TypeI.boundaryCharge_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) :
    ‖vec f.exponent (TypeI.boundaryCharge w e s I)‖ ≤ 32 * f.theta e.weight := by
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos e.weight
  have hb := norm_degree_le (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    (fun i : s => TypeI.boundaryDegree e w.blocks i) (16/(f.m e.weight : ℝ)) (2*e.length)
    (by positivity) (by positivity) (fun i => TypeI.boundaryDegree_nonneg e w.blocks i)
    (TypeI.boundaryDegree_sum e w.blocks s) (TypeI.boundaryCharge w e s I) (fun i => by
      rw [abs_of_nonneg (TypeI.boundaryCharge_nonneg w e s I i)]
      unfold TypeI.boundaryCharge
      split_ifs
      · simp only [Family.exponent_toReal,le_refl]
      · exact mul_nonneg (by positivity) (Real.rpow_nonneg (TypeI.boundaryDegree_nonneg e w.blocks i) _))
  have hr : 1/f.r ≤ 1 := (div_le_one f.r_pos).mpr f.r_gt_one.le
  have h2 : (2 : ℝ)^(1/f.r) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr
  calc
    _ ≤ (16/(f.m e.weight : ℝ)) * (2*(e.length : ℝ))^(1/f.r) := by simpa only [Family.exponent_toReal] using hb
    _ ≤ (16/(f.m e.weight : ℝ)) * (2*(f.L e.weight : ℝ)^(1/f.r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg _)]
      exact mul_le_mul h2 (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le) (one_div_nonneg.mpr f.r_pos.le))
        (by positivity) (by norm_num)
    _ = _ := by rw [Family.theta_formula]; ring

lemma TypeI.low_eval_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (A : Crop)
    (hm : ∀ h, e.child h ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s)
    (hi : i ∈ I) (hj : e.weight < w.lower i) :
    |norming.evaluateArray (w.blocks.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) e.value)| ≤
      TypeI.boundaryCharge w e s I i + (1/(f.m e.weight : ℝ)) *
      ∑ h, if i ∈ TypeI.lowAssign w e s I h then
        |norming.evaluateArray (w.blocks.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) (e.child h))| else 0 := by
  have hr : 0 < 1/f.r := one_div_pos.mpr f.r_pos
  have hb := TypeI.cropped_child_sum_bound e A hm (w.blocks.vector i) (f.L (w.lower i)) 16
    (by norm_num) (w.partition i) (e.length_le.trans (FamilyL_mono f hj.le))
  rw [TypeI.eval_crop_sum,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity))
  let H := TypeI.hitChildren e (w.blocks.vector i)
  by_cases hd : 2 ≤ H.card
  · have hu : TypeI.boundaryCharge w e s I i = 16/(f.m e.weight : ℝ) * (H.card : ℝ)^(1/f.r) := by
      simp only [TypeI.boundaryCharge,hi,hj,and_self,ite_true,TypeI.boundaryDegree,show 2 ≤ (TypeI.hitChildren e (w.blocks.vector i)).card from hd,H]
    rw [hu]
    have hc := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))
    have hn : 0 ≤ (1/(f.m e.weight : ℝ)) * ∑ h, if i ∈ TypeI.lowAssign w e s I h then
        |norming.evaluateArray (w.blocks.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) (e.child h))| else 0 := by positivity
    dsimp only [BlockSequence.embed] at hc hn ⊢
    dsimp only [H] at ⊢
    calc
      _ ≤ (1/(f.m e.weight : ℝ)) * (16*((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)^(1/f.r)) := hc
      _ = 16/(f.m e.weight : ℝ) * ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)^(1/f.r) := by ring
      _ ≤ _ := le_add_of_nonneg_right hn
  · have hsmall : H.card ≤ 1 := by omega
    have heq (h : Fin e.length) : (if i ∈ TypeI.lowAssign w e s I h then
        |norming.evaluateArray (w.blocks.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) (e.child h))| else 0) =
        |norming.evaluateArray (w.blocks.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) (e.child h))| := by
      by_cases hh : h ∈ H
      · have hH : H = {h} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hh, fun k hk =>
          (Finset.card_le_one.mp hsmall k hk h hh)⟩
        have ha : i ∈ TypeI.lowAssign w e s I h := Finset.mem_filter.mpr ⟨hi,hj,hH⟩
        simp only [ha,ite_true]
      · dsimp only [BlockSequence.embed]
        rw [TypeI.cropped_child_zero e A (w.blocks.vector i) h hh,abs_zero]
        simp
    simp_rw [heq]
    exact le_add_of_nonneg_left (TypeI.boundaryCharge_nonneg w e s I i)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma TypeI.recombine_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s)
    (v : Fin e.length → s → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ h i, i ∉ TypeI.lowAssign w e s I h → v h i = 0)
    (hv : ∀ h, ‖vec f.exponent (v h)‖ ≤ K) :
    ‖vec f.exponent (fun i => (1/(f.m e.weight : ℝ)) * ∑ h, v h i)‖ ≤ K*f.theta e.weight := by
  have hd : ∀ h ∈ (Finset.univ : Finset (Fin e.length)), ∀ k ∈ Finset.univ, h ≠ k →
      ∀ i, v h i = 0 ∨ v k i = 0 := by
    intro h _ k _ hhk i
    by_cases hi : i ∈ TypeI.lowAssign w e s I h
    · exact Or.inr (hs k i (fun hk => Finset.disjoint_left.mp (TypeI.lowAssign_disjoint w e s I h k hhk) hi hk))
    · exact Or.inl (hs h i hi)
  have hb := norm_sum_disjoint_le (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    Finset.univ v K hK hd (fun h _ => hv h)
  change ‖(1/(f.m e.weight : ℝ)) • vec f.exponent (fun i => ∑ h, v h i)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))]
  calc
    _ ≤ (1/(f.m e.weight : ℝ)) * (K*(e.length : ℝ)^(1/f.r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Family.exponent_toReal,Finset.card_univ,Fintype.card_fin] using hb
    _ ≤ (1/(f.m e.weight : ℝ)) * (K*(f.L e.weight : ℝ)^(1/f.r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le) (one_div_nonneg.mpr f.r_pos.le)) hK) (by positivity)
    _ = _ := by rw [Family.theta_formula]; ring

lemma TypeI.boundaryCharge_l1 {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) :
    (∑ i : s, TypeI.boundaryCharge w e s I i) ≤ 32*e.length := by
  have hm : (1 : ℝ) ≤ f.m e.weight := by exact_mod_cast f.m_pos e.weight
  have hb (i : s) : TypeI.boundaryCharge w e s I i ≤ 16*TypeI.boundaryDegree e w.blocks i := by
    have hpos := TypeI.boundaryDegree_nonneg e w.blocks i
    unfold TypeI.boundaryCharge
    split_ifs
    · have hd : (TypeI.boundaryDegree e w.blocks i)^(1/f.r) ≤ TypeI.boundaryDegree e w.blocks i := by
        unfold TypeI.boundaryDegree
        split_ifs with hi
        · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (show 1 ≤ (TypeI.hitChildren e (w.blocks.vector i)).card by omega))
            ((div_le_one f.r_pos).mpr f.r_gt_one.le)
        · rw [Real.zero_rpow (ne_of_gt (one_div_pos.mpr f.r_pos))]
      exact mul_le_mul (div_le_self (by norm_num) hm) hd (by positivity) (by norm_num)
    · positivity
  calc
    _ ≤ ∑ i : s, 16*TypeI.boundaryDegree e w.blocks i := Finset.sum_le_sum (fun i _ => hb i)
    _ = 16 * ∑ i : s, TypeI.boundaryDegree e w.blocks i := (Finset.mul_sum ..).symm
    _ ≤ 16*(2*e.length) := mul_le_mul_of_nonneg_left (TypeI.boundaryDegree_sum e w.blocks s) (by norm_num)
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma TypeII.middle_group_sum {f : Family} (e : TypeII f) (x : E) (lo up : ℕ) :
    (∑ g ∈ TypeII.activeGroups e, if lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) =
    ∑ b, (e.coefficient b : ℝ) * norming.evaluateArray x
      (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window lo up)) := by
  rw [TypeII.sum_group_mask e x (fun j => lo ≤ j ∧ j ≤ up),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  simp only [FinitePath.window,restrict_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [TypeII.groupWeight,TypeII.groupValue,(e.path b).weight_eq,(e.path b).value_eq]
  split_ifs <;> simp [restrict_zero]

lemma TypeII.eval_three_parts {f : Family} (e : TypeII f) (x : E) (lo up : ℕ) (hl : lo ≤ up) :
    norming.evaluateArray x e.value =
    (∑ g ∈ TypeII.activeGroups e, if TypeII.groupWeight e g < lo then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) +
    (∑ b, (e.coefficient b : ℝ) * norming.evaluateArray x
      (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop b).set f) ((e.path b).window lo up))) +
    (∑ g ∈ TypeII.activeGroups e, if up < TypeII.groupWeight e g then
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) else 0) := by
  rw [TypeII.eval_group_sum,← TypeII.middle_group_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hL : TypeII.groupWeight e g < lo
  · have hm : ¬ (lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up) := by omega
    have hU : ¬ up < TypeII.groupWeight e g := by omega
    simp only [hL,hm,hU,ite_true,ite_false,add_zero]
  · by_cases hU : up < TypeII.groupWeight e g
    · have hm : ¬ (lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up) := by omega
      simp only [hL,hm,hU,ite_true,ite_false,zero_add]
    · have hm : lo ≤ TypeII.groupWeight e g ∧ TypeII.groupWeight e g ≤ up := by omega
      simp [hL,hU,hm]

lemma ThinnedWindows.epsilon_pos {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) : 0 < ε := by
  have hh := w.threshold_charge_succ 0
  have ht := w.threshold_pos 0
  have hu : (0 : ℝ) ≤ w.upper 0 := Nat.cast_nonneg _
  norm_num at hh
  nlinarith

lemma ThinnedWindows.middle_abs_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    |∑ b, (e.coefficient b : ℝ) * w.middleEval e b i| ≤ w.markedCharge e hm s i + ε := by
  calc
    _ ≤ ∑ b, |(e.coefficient b : ℝ)| * |w.middleEval e b i| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun b => (e.coefficient b : ℝ)*w.middleEval e b i) Finset.univ
    _ = w.markedCharge e hm s i +
        ∑ b, if i.val ∉ w.marks e hm s b then |(e.coefficient b : ℝ)| * |w.middleEval e b i| else 0 := by
      rw [ThinnedWindows.markedCharge,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hi : i.val ∈ w.marks e hm s b <;> simp [hi]
    _ ≤ _ := add_le_add_right (w.unmarked_column w.epsilon_pos.le e hm s i i.property) _

lemma ThinnedWindows.node_split {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (i : s) :
    |norming.evaluateArray (w.blocks.embed i) e.value| ≤ 2*ε+w.markedCharge e hm s i +
      ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < w.lower i then
          |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0) := by
  have hh : |∑ g ∈ TypeII.activeGroups e, if w.upper i < TypeII.groupWeight e g then
      (e.coefficient g.1 : ℝ)*norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g) else 0| ≤ ε := by
    calc
      _ ≤ ∑ g ∈ TypeII.activeGroups e, |if w.upper i < TypeII.groupWeight e g then
          (e.coefficient g.1 : ℝ)*norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ g ∈ (TypeII.activeGroups e).filter (fun g => w.upper i < TypeII.groupWeight e g),
          |(e.coefficient g.1 : ℝ)| * |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro g _
        split_ifs <;> simp only [abs_mul,abs_zero]
      _ ≤ vectorL1 (w.blocks.vector i) * SeriesTails.tail (fun j => 1/(f.m j : ℝ)) (w.upper i+1) :=
        TypeII.high_weight_bound e hm (w.blocks.vector i) (w.upper i)
      _ ≤ ε := w.tail_small i
  have hmB := w.middle_abs_bound e hm s i
  have hl : |∑ g ∈ TypeII.activeGroups e, if TypeII.groupWeight e g < w.lower i then
      (e.coefficient g.1 : ℝ)*norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g) else 0| ≤
      ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < w.lower i then |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> simp only [abs_mul,abs_zero,mul_zero]
  rw [TypeII.eval_three_parts e _ _ _ (w.order i)]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hl hmB)) hh)).trans_eq (by ring)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology

lemma BlockSequence.base_eval_unique {f : Family} (z : BlockSequence f) (g : Array) (hg : g ∈ f.base)
    (i j : ℕ) (hi : norming.evaluateArray (z.embed i) g ≠ 0)
    (hj : norming.evaluateArray (z.embed j) g ≠ 0) : i = j := by
  obtain ⟨α,hα,hgα⟩ := evaluateArray_nonzero_witness (z.vector i) g hi
  obtain ⟨β,hβ,hgβ⟩ := evaluateArray_nonzero_witness (z.vector j) g hj
  have hbad (i j : ℕ) (hij : i < j) (α β : Γ)
      (hα : α ∈ (z.vector i).support) (hβ : β ∈ (z.vector j).support)
      (hgα : g α ≠ 0) (hgβ : g β ≠ 0) : False := by
    cases f with
    | pure k =>
      rcases hg with rfl | ⟨γ,_hc,rfl | rfl⟩
      · exact hgα rfl
      all_goals
        have hαγ : α = γ := by by_contra hn; exact hgα (Finsupp.single_eq_of_ne hn)
        have hβγ : β = γ := by by_contra hn; exact hgβ (Finsupp.single_eq_of_ne hn)
        subst α; subst β
        exact (lt_irrefl γ) (z.successive i j hij γ hα γ hβ).1
    | mixed =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hg
      have hαc : Colors.color α = k := by by_contra hn; exact hgα (pure_vanish k g hk α hn)
      have hβc : Colors.color β = k := by by_contra hn; exact hgβ (pure_vanish k g hk β hn)
      have hh := (z.successive i j hij α hα β hβ).2 rfl
      rw [hαc,hβc] at hh
      exact (lt_irrefl k) hh
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hbad i j hij α β hα hβ hgα hgβ).elim
  · exact hij
  · exact (hbad j i hij β α hβ hα hgβ hgα).elim

lemma ThinnedWindows.evalVector_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (i : s) :
    0 ≤ w.evalVector s I g i := by unfold ThinnedWindows.evalVector; split_ifs <;> positivity

lemma ThinnedWindows.evalVector_base {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (g : Array) (hg : g ∈ f.base) :
    ‖vec f.exponent (w.evalVector s I g)‖ ≤ 2 ∧ (∑ i : s, w.evalVector s I g i) ≤ 2 := by
  have hb (i : s) : |w.evalVector s I g i| ≤ 2 := by
    rw [abs_of_nonneg (w.evalVector_nonneg s I g i)]
    unfold ThinnedWindows.evalVector
    split_ifs
    · have hgfull : g ∈ Full := f.norming_subset_full (Set.mem_iUnion.mpr ⟨0,hg⟩)
      rw [norming.evaluateArray_eq_functional _ ⟨g,hgfull⟩]
      exact (norming.functional_bound _ _).trans (w.upper_norm i)
    · norm_num
  have hu (i j : s) (hi : w.evalVector s I g i ≠ 0) (hj : w.evalVector s I g j ≠ 0) : i = j := by
    have hn (i : s) (hi : w.evalVector s I g i ≠ 0) : norming.evaluateArray (w.blocks.embed i) g ≠ 0 := by
      intro hz
      apply hi
      simp [ThinnedWindows.evalVector,hz]
    exact Subtype.ext (w.blocks.base_eval_unique g hg i j (hn i hi) (hn j hj))
  have hh := single_support_bounds (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    (w.evalVector s I g) 2 (by norm_num) hb hu
  simpa only [abs_of_nonneg (w.evalVector_nonneg s I g _)] using hh

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.continuation {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (g : TypeII.Group e) (i : s) : ℝ :=
  (1/(f.m (TypeII.groupWeight e g) : ℝ)) * ∑ h,
    w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
      (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)) i

lemma TypeII.continuation_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (g : TypeII.Group e) (i : s) : 0 ≤ TypeII.continuation e w s I g i := by
  unfold TypeII.continuation
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => w.evalVector_nonneg ..))

lemma ThinnedWindows.node_majorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) :
    w.evalVector s I e.value i ≤ (if i ∈ I then 2*ε else 0) +
      (if i ∈ I then w.markedCharge e hm s i else 0) +
      (∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i) +
      ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeII.continuation e w s I g i := by
  by_cases hi : i ∈ I
  · simp only [ThinnedWindows.evalVector,hi,ite_true]
    apply (w.node_split e hm s i).trans
    rw [add_assoc (2*ε+w.markedCharge e hm s i),← Finset.sum_add_distrib]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro g _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    by_cases hj : TypeII.groupWeight e g < w.lower i
    · rw [ite_eq_left hj]
      exact TypeI.low_eval_bound w ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) s I i hi hj
    · rw [ite_eq_right hj]
      exact add_nonneg (TypeI.boundaryCharge_nonneg ..) (TypeII.continuation_nonneg ..)
  · simp only [ThinnedWindows.evalVector,hi,ite_false,zero_add]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.boundaryCharge_nonneg ..)))
      (Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeII.continuation_nonneg ..)))

noncomputable def TypeII.boundaryVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i

noncomputable def TypeII.continuationVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| * TypeII.continuation e w s I g i

lemma ThinnedWindows.epsilonVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) :
    ‖vec f.exponent (fun i : s => if i ∈ I then 2*ε else 0)‖ ≤ 2*(ε*(s.card : ℝ)^(1/f.r)) := by
  have hp : 0 < f.exponent.toReal := by simpa only [Family.exponent_toReal] using f.r_pos
  have hn : f.exponent ≠ 0 := by intro h; simp [h] at hp
  calc
    _ ≤ ‖vec f.exponent (fun _ : s => 2*ε)‖ := norm_mask_le_explicit hn _ I
    _ = _ := by
      rw [norm_const hp,abs_of_nonneg (mul_nonneg (by norm_num) w.epsilon_pos.le)]
      simp only [Fintype.card_coe,Family.exponent_toReal]
      ring

lemma TypeII.boundaryVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) :
    ‖vec f.exponent (TypeII.boundaryVector e w s I)‖ ≤ 4 := by
  exact (TypeII.sum_vector_norm e s (fun g => TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I) 32
    (by norm_num) (fun _ _ => TypeI.boundaryCharge_norm ..)).trans_eq (by norm_num)

lemma TypeII.continuation_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (g : TypeII.Group e) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ h, ‖vec f.exponent (w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
        (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)))‖ ≤ K) :
    ‖vec f.exponent (TypeII.continuation e w s I g)‖ ≤ K*f.theta (TypeII.groupWeight e g) := by
  apply TypeI.recombine_norm w ((e.path g.1).piece g.2) s I _ K hK
  · intro h i hi
    simp only [ThinnedWindows.evalVector,hi,ite_false]
  · exact hc

lemma TypeII.continuationVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (hc : ∀ (g : TypeII.Group e) h, ‖vec f.exponent (w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
        (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)))‖ ≤ 64) :
    ‖vec f.exponent (TypeII.continuationVector e w s I)‖ ≤ 8 := by
  exact (TypeII.sum_vector_norm e s (TypeII.continuation e w s I) 64 (by norm_num)
    (fun g _ => TypeII.continuation_norm e w s I g 64 (by norm_num) (hc g))).trans_eq (by norm_num)

lemma ThinnedWindows.node_uniform {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s)
    (hε : ε*(s.card : ℝ)^(1/f.r) ≤ 1)
    (hc : ∀ (g : TypeII.Group e) h, ‖vec f.exponent
      (w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
        (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h)))‖ ≤ 64) :
    ‖vec f.exponent (w.evalVector s I e.value)‖ ≤ 64 := by
  have hp : 0 < f.exponent.toReal := by simpa only [Family.exponent_toReal] using f.r_pos
  have hn : f.exponent ≠ 0 := by intro h; simp [h] at hp
  have hM : ‖vec f.exponent (fun i : s => if i ∈ I then w.markedCharge e hm s i else 0)‖ ≤ 16 :=
    (norm_mask_le_explicit hn _ I).trans (w.marked_vector_bounds e hm s).1
  have h := norm_le_four hn (w.evalVector s I e.value)
    (fun i : s => if i ∈ I then 2*ε else 0)
    (fun i : s => if i ∈ I then w.markedCharge e hm s i else 0)
    (TypeII.boundaryVector e w s I) (TypeII.continuationVector e w s I)
    (fun i => by split_ifs <;> nlinarith [w.epsilon_pos])
    (fun i => by split_ifs <;> first | exact w.markedCharge_nonneg e hm s i | exact le_rfl)
    (fun i => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.boundaryCharge_nonneg ..)))
    (fun i => Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeII.continuation_nonneg ..)))
    (fun i => by rw [abs_of_nonneg (w.evalVector_nonneg s I e.value i)]; exact w.node_majorant e hm s I i)
  linarith [w.epsilonVector_norm s I, TypeII.boundaryVector_norm e w s I, TypeII.continuationVector_norm e w s I hc]

lemma ThinnedWindows.stage_uniform {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ 1) :
    ∀ n (g : Array), g ∈ stage f.base f n → ∀ I : Finset s,
      ‖vec f.exponent (w.evalVector s I g)‖ ≤ 64 := by
  intro n
  induction n with
  | zero =>
    intro g hg I
    exact (w.evalVector_base s I g hg).1.trans (by norm_num)
  | succ n ih =>
    intro g hg I
    have hn : ∀ g, g ∈ stage f.base f n → g ∈ f.norming := fun g hg => Set.mem_iUnion.mpr ⟨n,hg⟩
    have ht (e : TypeII f) (he : ∀ b i h, ((e.path b).piece i).child h ∈ stage f.base f n) :
        ‖vec f.exponent (w.evalVector s I e.value)‖ ≤ 64 := by
      apply w.node_uniform e (fun b i h => hn _ (he b i h)) s I hε
      intro g h
      exact ih _ (Family.stage_crop f n _ _ (he g.1 g.2 h)) _
    rcases hg with (hg | ⟨e,rfl,he⟩) | ⟨e,rfl,he⟩
    · exact ih _ hg I
    · simpa only [Norming.TypeI.toTypeII_value] using ht e.toTypeII (fun _ _ h => he h)
    · exact ht e he

lemma ThinnedWindows.norming_uniform {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ 1)
    (g : Array) (hg : g ∈ f.norming) (I : Finset s) :
    ‖vec f.exponent (w.evalVector s I g)‖ ≤ 64 := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hg
  exact w.stage_uniform s hε n g hn I

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.StoppedCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeI.stoppedCharge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  if i ∈ I ∧ e.weight < w.lower i then
    (16/(f.m e.weight : ℝ)) * ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)^(1/f.r) else 0

lemma TypeI.stoppedCharge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeI.stoppedCharge w e s I i := by unfold TypeI.stoppedCharge; split_ifs <;> positivity

lemma TypeI.stoppedCharge_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (s : Finset ℕ) (I : Finset s)
    (hs : s.card ≤ f.L J) (hj : J ≤ e.weight) :
    ‖vec f.exponent (TypeI.stoppedCharge w e s I)‖ ≤ 48*f.theta e.weight := by
  have hsum : (∑ i : s, ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)) ≤ 3*(f.L e.weight : ℝ) := by
    have hL : (e.length : ℝ) ≤ f.L e.weight := by exact_mod_cast e.length_le
    have hc : (s.card : ℝ) ≤ f.L e.weight := by exact_mod_cast hs.trans (FamilyL_mono f hj)
    linarith [TypeI.total_incidence e w.blocks s]
  have hb := norm_degree_le (by simpa only [Family.exponent_toReal] using f.r_pos : 0 < f.exponent.toReal)
    (fun i : s => ((TypeI.hitChildren e (w.blocks.vector i)).card : ℝ)) (16/(f.m e.weight : ℝ)) (3*f.L e.weight)
    (by positivity) (by positivity) (fun _ => by positivity) hsum (TypeI.stoppedCharge w e s I) (fun i => by
      rw [abs_of_nonneg (TypeI.stoppedCharge_nonneg w e s I i)]
      unfold TypeI.stoppedCharge
      split_ifs
      · simp only [Family.exponent_toReal,le_refl]
      · positivity)
  have h3 : (3 : ℝ)^(1/f.r) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
      ((div_le_one f.r_pos).mpr f.r_gt_one.le)
  calc
    _ ≤ (16/(f.m e.weight : ℝ)) * (3*(f.L e.weight : ℝ))^(1/f.r) := by simpa only [Family.exponent_toReal] using hb
    _ ≤ (16/(f.m e.weight : ℝ)) * (3*(f.L e.weight : ℝ)^(1/f.r)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
    _ = _ := by rw [Family.theta_formula]; ring

lemma TypeI.stopped_eval_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeI f) (A : Crop)
    (hm : ∀ h, e.child h ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s)
    (hi : i ∈ I) (hj : e.weight < w.lower i) :
    |norming.evaluateArray (w.blocks.embed i) (_root_.OAI.SeparableQuotient.Norming.restrict (A.set f) e.value)| ≤
      TypeI.stoppedCharge w e s I i := by
  have hb := TypeI.cropped_child_sum_bound e A hm (w.blocks.vector i) (f.L (w.lower i)) 16
    (by norm_num) (w.partition i) (e.length_le.trans (FamilyL_mono f hj.le))
  rw [TypeI.eval_crop_sum,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))]
  have hh := (Finset.abs_sum_le_sum_abs _ _).trans hb
  have hu := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/(f.m e.weight : ℝ))
  simpa only [TypeI.stoppedCharge,hi,hj,and_self,ite_true,BlockSequence.embed,div_mul_eq_mul_div,one_mul,mul_div_assoc] using hu

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma TypeII.recombineEarly_support {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (v : TypeII.ChildVectors e s)
    (hv : ∀ g h i, i ∉ TypeI.lowAssign w ((e.path g.1).piece g.2) s I h → v g h i = 0)
    (i : s) (hi : i ∉ I) : TypeII.recombineEarly e J s v i = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  rw [Finset.sum_eq_zero (fun h _ => hv g h i (fun hh => hi (TypeI.lowAssign_subset w _ s I h hh))),mul_zero,mul_zero]

lemma TypeII.recombineEarly_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (v : TypeII.ChildVectors e s) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ g h i, i ∉ TypeI.lowAssign w ((e.path g.1).piece g.2) s I h → v g h i = 0)
    (hv : ∀ g h, ‖vec f.exponent (v g h)‖ ≤ K) :
    ‖vec f.exponent (TypeII.recombineEarly e J s v)‖ ≤ K/8 := by
  have hg (g : TypeII.Group e) : ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| *
      ((1/(f.m (TypeII.groupWeight e g) : ℝ))*∑ h, v g h i))‖ ≤ K*f.theta (TypeII.groupWeight e g) := by
    change ‖|(e.coefficient g.1 : ℝ)| • vec f.exponent (fun i => (1/(f.m (TypeII.groupWeight e g) : ℝ))*∑ h, v g h i)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_abs]
    exact ((mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (norm_nonneg _)).trans_eq (one_mul _)).trans
      (TypeI.recombine_norm w ((e.path g.1).piece g.2) s I (v g) K hK (hs g) (hv g))
  calc
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| *
        ((1/(f.m (TypeII.groupWeight e g) : ℝ))*∑ h, v g h i))‖ := by
      unfold TypeII.recombineEarly
      rw [vec_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, K*f.theta (TypeII.groupWeight e g) := Finset.sum_le_sum (fun g _ => hg g)
    _ = K * ∑ g ∈ TypeII.earlyGroups e J, f.theta (TypeII.groupWeight e g) := (Finset.mul_sum ..).symm
    _ ≤ K*(1/8) := mul_le_mul_of_nonneg_left (TypeII.early_theta_bound e J) hK
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.lateVector {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.lateGroups e J, |(e.coefficient g.1 : ℝ)| * TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i

noncomputable def TypeII.earlyBoundary {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  ∑ g ∈ TypeII.earlyGroups e J, |(e.coefficient g.1 : ℝ)| * TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i

lemma TypeII.lateVector_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeII.lateVector e w s I i :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.stoppedCharge_nonneg ..))

lemma TypeII.earlyBoundary_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ TypeII.earlyBoundary e w s I i :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (TypeI.boundaryCharge_nonneg ..))

lemma TypeII.lateVector_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s)
    (hJ : 1 ≤ J) (hs : s.card ≤ f.L J) :
    ‖vec f.exponent (TypeII.lateVector e w s I)‖ ≤ 192*f.theta J := by
  have hg (g : TypeII.Group e) (hg : g ∈ TypeII.lateGroups e J) :
      ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| * TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i)‖ ≤
      48*f.theta (TypeII.groupWeight e g) := by
    change ‖|(e.coefficient g.1 : ℝ)| • vec f.exponent (TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_abs]
    exact ((mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (norm_nonneg _)).trans_eq (one_mul _)).trans
      (TypeI.stoppedCharge_norm w _ s I hs (Finset.mem_filter.mp hg).2)
  calc
    _ ≤ ∑ g ∈ TypeII.lateGroups e J, ‖vec f.exponent (fun i => |(e.coefficient g.1 : ℝ)| *
        TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i)‖ := by
      unfold TypeII.lateVector
      rw [vec_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ g ∈ TypeII.lateGroups e J, 48*f.theta (TypeII.groupWeight e g) := Finset.sum_le_sum hg
    _ = 48 * ∑ g ∈ TypeII.lateGroups e J, f.theta (TypeII.groupWeight e g) := (Finset.mul_sum ..).symm
    _ ≤ 48*(4*f.theta J) := mul_le_mul_of_nonneg_left (Family.sum_theta_tail_le f _ _ J hJ
      (fun _ hg => (Finset.mem_filter.mp hg).2) ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _))) (by norm_num)
    _ = _ := by ring

lemma TypeII.earlyBoundary_l1 {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) :
    (∑ i : s, TypeII.earlyBoundary e w s I i) ≤ 16*(Parameters.B f.s (J-1) : ℝ) := by
  have hlen : 2*(∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)) ≤ Parameters.B f.s (J-1) :=
    by exact_mod_cast TypeII.early_lengths_bound e J
  calc
    _ = ∑ g ∈ TypeII.earlyGroups e J, |(e.coefficient g.1 : ℝ)| * ∑ i : s, TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i := by
      unfold TypeII.earlyBoundary
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ g ∈ TypeII.earlyGroups e J, 32*(((e.path g.1).piece g.2).length : ℝ) := by
      apply Finset.sum_le_sum
      intro g _
      exact ((mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1)
        (Finset.sum_nonneg (fun i _ => TypeI.boundaryCharge_nonneg w _ s I i))).trans_eq (one_mul _)).trans
          (TypeI.boundaryCharge_l1 w _ s I)
    _ = 32*(∑ g ∈ TypeII.earlyGroups e J, (((e.path g.1).piece g.2).length : ℝ)) := (Finset.mul_sum ..).symm
    _ ≤ _ := by linarith

noncomputable def ThinnedWindows.localSmall {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  (if i ∈ I then 2*ε else 0) + TypeII.lateVector e w s I i

noncomputable def ThinnedWindows.localLarge {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming)
    (s : Finset ℕ) (I : Finset s) (i : s) : ℝ :=
  (if i ∈ I then w.markedCharge e hm s i else 0) + TypeII.earlyBoundary e w s I i

lemma ThinnedWindows.localSmall_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ w.localSmall e s I i := by
  apply add_nonneg _ (TypeII.lateVector_nonneg ..)
  split_ifs <;> nlinarith [w.epsilon_pos]

lemma ThinnedWindows.localLarge_nonneg {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) :
    0 ≤ w.localLarge e hm s I i := by
  apply add_nonneg _ (TypeII.earlyBoundary_nonneg ..)
  split_ifs
  · exact w.markedCharge_nonneg e hm s i
  · exact le_rfl

lemma ThinnedWindows.localSmall_support {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s) (i : s) (hi : i ∉ I) :
    w.localSmall e s I i = 0 := by
  simp only [ThinnedWindows.localSmall,hi,ite_false,zero_add,TypeII.lateVector,TypeI.stoppedCharge,false_and]
  simp

lemma ThinnedWindows.localLarge_support {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) (hi : i ∉ I) :
    w.localLarge e hm s I i = 0 := by
  simp only [ThinnedWindows.localLarge,hi,ite_false,zero_add,TypeII.earlyBoundary,TypeI.boundaryCharge,false_and]
  simp

lemma ThinnedWindows.localSmall_norm {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f) (s : Finset ℕ) (I : Finset s)
    (hJ : 1 ≤ J) (hs : s.card ≤ f.L J) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J) :
    ‖vec f.exponent (w.localSmall e s I)‖ ≤ 194*f.theta J := by
  change ‖vec f.exponent (fun i : s => if i ∈ I then 2*ε else 0) + vec f.exponent (TypeII.lateVector e w s I)‖ ≤ _
  have hh := norm_add_le (vec f.exponent (fun i : s => if i ∈ I then 2*ε else 0)) (vec f.exponent (TypeII.lateVector e w s I))
  linarith [w.epsilonVector_norm s I,TypeII.lateVector_norm e w s I hJ hs]

lemma ThinnedWindows.localLarge_l1 {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) :
    (∑ i : s, w.localLarge e hm s I i) ≤ 16*(1+(Parameters.B f.s (J-1) : ℝ)+(s.card : ℝ)^(1-1/f.q)) := by
  have hM : (∑ i : s, if i ∈ I then w.markedCharge e hm s i else 0) ≤ ∑ i : s, w.markedCharge e hm s i := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact w.markedCharge_nonneg e hm s i
  have hh := (w.marked_vector_bounds e hm s).2
  have hB := TypeII.earlyBoundary_l1 e w s I
  simp only [ThinnedWindows.localLarge,Finset.sum_add_distrib]
  linarith

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

noncomputable def TypeII.childEvals {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (e : TypeII f) (w : ThinnedWindows z J ε a) (s : Finset ℕ) (I : Finset s) : TypeII.ChildVectors e s :=
  fun g h => w.evalVector s (TypeI.lowAssign w ((e.path g.1).piece g.2) s I h)
    (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).child h))

lemma ThinnedWindows.low_refined_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s)
    (i : s) (hi : i ∈ I) :
    (∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < w.lower i then
          |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0)) ≤
      TypeII.earlyBoundary e w s I i + TypeII.lateVector e w s I i +
        TypeII.recombineEarly e J s (TypeII.childEvals e w s I) i := by
  have hh (g : TypeII.Group e) : (if TypeII.groupWeight e g < w.lower i then
        |norming.evaluateArray (w.blocks.embed i) (TypeII.groupValue e g)| else 0) ≤
      if TypeII.groupWeight e g < J then TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i +
        TypeII.continuation e w s I g i else TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i := by
    by_cases hlow : TypeII.groupWeight e g < w.lower i
    · rw [ite_eq_left hlow]
      split_ifs with hj
      · exact TypeI.low_eval_bound w ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) s I i hi hlow
      · exact TypeI.stopped_eval_bound w ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) s I i hi hlow
    · rw [ite_eq_right hlow]
      split_ifs
      · exact add_nonneg (TypeI.boundaryCharge_nonneg ..) (TypeII.continuation_nonneg ..)
      · exact TypeI.stoppedCharge_nonneg ..
  calc
    _ ≤ ∑ g ∈ TypeII.activeGroups e, |(e.coefficient g.1 : ℝ)| *
        (if TypeII.groupWeight e g < J then TypeI.boundaryCharge w ((e.path g.1).piece g.2) s I i +
          TypeII.continuation e w s I g i else TypeI.stoppedCharge w ((e.path g.1).piece g.2) s I i) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hh g) (abs_nonneg _))
    _ = _ := by
      unfold TypeII.earlyBoundary TypeII.lateVector TypeII.recombineEarly TypeII.earlyGroups TypeII.lateGroups
      simp only [Finset.sum_filter]
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hj : TypeII.groupWeight e g < J
      · simp only [hj,ite_true,not_le.mpr hj,ite_false,add_zero,TypeII.continuation,TypeII.childEvals,mul_add]
      · simp only [hj,ite_false,not_lt.mp hj,ite_true,zero_add,add_zero]

lemma ThinnedWindows.node_refined_majorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (s : Finset ℕ) (I : Finset s) (i : s) :
    w.evalVector s I e.value i ≤ w.localSmall e s I i+w.localLarge e hm s I i+
      TypeII.recombineEarly e J s (TypeII.childEvals e w s I) i := by
  by_cases hi : i ∈ I
  · have hn := w.node_split e hm s i
    have hl := w.low_refined_bound e hm s I i hi
    simp only [ThinnedWindows.evalVector,ThinnedWindows.localSmall,ThinnedWindows.localLarge,hi,ite_true]
    linarith
  · rw [w.localSmall_support e s I i hi,w.localLarge_support e hm s I i hi]
    simp only [ThinnedWindows.evalVector,hi,ite_false,zero_add]
    exact TypeII.recombineEarly_nonneg e J s (TypeII.childEvals e w s I) (fun _ _ _ => w.evalVector_nonneg ..) i

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma smallBudget_nonneg (f : Family) (J d : ℕ) : 0 ≤ smallBudget f J d := by
  unfold smallBudget
  have := f.theta_nonneg J
  positivity
lemma largeUnit_ge (f : Family) (J : ℕ) (s : Finset ℕ) : 16 ≤ largeUnit f J s := by
  unfold largeUnit
  have : 0 ≤ (s.card : ℝ)^(1-1/f.q) := Real.rpow_nonneg (by positivity) _
  have : 0 ≤ (Parameters.B f.s (J-1) : ℝ) := by positivity
  linarith
lemma largeBudget_ge (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : largeUnit f J s ≤ largeBudget f J s d := by
  unfold largeBudget
  exact le_mul_of_one_le_right (by linarith [largeUnit_ge f J s]) (one_le_pow₀ (by
    have hb : 0 ≤ (Parameters.B f.s (J-1) : ℝ) := by positivity
    linarith))
lemma largeBudget_nonneg (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) : 0 ≤ largeBudget f J s d := by
  linarith [largeUnit_ge f J s,largeBudget_ge f J s d]
lemma smallBudget_succ (f : Family) (J d : ℕ) :
    194*f.theta J+smallBudget f J d/8 = smallBudget f J (d+1) := by
  unfold smallBudget
  rw [pow_succ]
  ring
lemma largeBudget_step (f : Family) (J : ℕ) (s : Finset ℕ) (d : ℕ) :
    largeUnit f J s+(Parameters.B f.s (J-1) : ℝ)*largeBudget f J s d ≤ largeBudget f J s (d+1) := by
  calc
    _ ≤ largeBudget f J s d+(Parameters.B f.s (J-1) : ℝ)*largeBudget f J s d :=
      add_le_add (largeBudget_ge f J s d) le_rfl
    _ = _ := by unfold largeBudget; rw [pow_succ]; ring

lemma ThinnedWindows.exists_depthMajorant {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ)
    (hJ : 1 ≤ J) (hs : s.card ≤ f.L J) (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J)
    (d : ℕ) (I : Finset s) (g : Array) (hg : g ∈ f.norming) :
    Nonempty (DepthMajorant w s I g d) := by
  induction d generalizing I g with
  | zero =>
    refine ⟨⟨w.evalVector s I g,fun _ => 0,w.evalVector_nonneg s I g,fun _ => le_rfl,?_,?_,?_,?_,?_⟩⟩
    · intro i hi
      simp only [ThinnedWindows.evalVector,hi,ite_false]
    · exact fun _ _ => rfl
    · intro i
      exact (add_zero _).ge
    · apply (w.norming_uniform s (hε.trans (Family.theta_le_one f J)) g hg I).trans
      unfold smallBudget
      simp only [pow_zero,mul_one]
      have := f.theta_nonneg J
      linarith
    · simpa only [Finset.sum_const_zero] using largeBudget_nonneg f J s 0
  | succ d ih =>
    rcases Family.norming_cases f g hg with hbase | ⟨e,rfl,he⟩
    · refine ⟨⟨fun _ => 0,w.evalVector s I g,fun _ => le_rfl,w.evalVector_nonneg s I g,?_,?_,?_,?_,?_⟩⟩
      · exact fun _ _ => rfl
      · intro i hi
        simp only [ThinnedWindows.evalVector,hi,ite_false]
      · intro i
        exact (zero_add _).ge
      · simpa only [show vec f.exponent (fun _ : s => (0 : ℝ)) = 0 from rfl,norm_zero] using smallBudget_nonneg f J (d+1)
      · linarith [(w.evalVector_base s I g hbase).2,largeUnit_ge f J s,largeBudget_ge f J s (d+1)]
    · let C (k : TypeII.Group e) (h : Fin ((e.path k.1).piece k.2).length) :=
        Classical.choice (ih (TypeI.lowAssign w ((e.path k.1).piece k.2) s I h)
          (_root_.OAI.SeparableQuotient.Norming.restrict ((e.crop k.1).set f) (((e.path k.1).piece k.2).child h))
          (Family.norming_crop f _ _ (he k.1 k.2 h)))
      let v : TypeII.ChildVectors e s := fun k h => (C k h).small
      let u : TypeII.ChildVectors e s := fun k h => (C k h).large
      refine ⟨⟨fun i => w.localSmall e s I i+TypeII.recombineEarly e J s v i,
        fun i => w.localLarge e he s I i+TypeII.recombineEarly e J s u i,?_,?_,?_,?_,?_,?_,?_⟩⟩
      · intro i
        exact add_nonneg (w.localSmall_nonneg e s I i)
          (TypeII.recombineEarly_nonneg e J s v (fun k h i => (C k h).small_nonneg i) i)
      · intro i
        exact add_nonneg (w.localLarge_nonneg e he s I i)
          (TypeII.recombineEarly_nonneg e J s u (fun k h i => (C k h).large_nonneg i) i)
      · intro i hi
        rw [w.localSmall_support e s I i hi,TypeII.recombineEarly_support e w s I v
          (fun k h i hi => (C k h).small_support i hi) i hi,add_zero]
      · intro i hi
        rw [w.localLarge_support e he s I i hi,TypeII.recombineEarly_support e w s I u
          (fun k h i hi => (C k h).large_support i hi) i hi,add_zero]
      · intro i
        have hh := TypeII.recombineEarly_mono e J s (TypeII.childEvals e w s I)
          (fun k h i => v k h i+u k h i) (fun k h i => (C k h).majorizes i) i
        rw [TypeII.recombineEarly_add] at hh
        linarith [w.node_refined_majorant e he s I i]
      · change ‖vec f.exponent (w.localSmall e s I)+vec f.exponent (TypeII.recombineEarly e J s v)‖ ≤ _
        apply (norm_add_le _ _).trans
        rw [← smallBudget_succ]
        exact add_le_add (w.localSmall_norm e s I hJ hs hε)
          (TypeII.recombineEarly_norm e w s I v (smallBudget f J d) (smallBudget_nonneg f J d)
            (fun k h i hi => (C k h).small_support i hi) (fun k h => (C k h).norm_small))
      · rw [Finset.sum_add_distrib]
        exact (add_le_add (w.localLarge_l1 e he s I)
          (TypeII.recombineEarly_l1 e J s u (largeBudget f J s d) (largeBudget_nonneg f J s d)
            (fun k h i => (C k h).large_nonneg i) (fun k h => (C k h).sum_large))).trans
          (largeBudget_step f J s d)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma Family.holder_theta (f : Family) (J : ℕ) :
    (f.L J : ℝ)^(1-1/f.r)*f.theta J = (f.L J : ℝ)/(f.m J : ℝ) := by
  have hL : (0 : ℝ) < f.L J := by exact_mod_cast f.L_pos J
  rw [f.theta_formula,← mul_div_assoc,← Real.rpow_add hL]
  rw [show 1-1/f.r+1/f.r = 1 by ring,Real.rpow_one]

lemma ThinnedWindows.sum_eval_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hJ : 1 ≤ J) (hs : s.card = f.L J)
    (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J) (g : Array) (hg : g ∈ f.norming) :
    (∑ i : s, |norming.evaluateArray (w.blocks.embed i) g|) ≤ 500*(f.L J : ℝ)/(f.m J : ℝ) := by
  let d := Parameters.d (J-1)
  obtain ⟨c⟩ := w.exists_depthMajorant s hJ hs.le hε d Finset.univ g hg
  have hb : smallBudget f J d ≤ (2000/7)*f.theta J := by
    have hh := Parameters.depth_theta_bound f.s_ge_two (J-1)
    change (1/8 : ℝ)^d ≤ f.theta J at hh
    unfold smallBudget
    linarith
  have hlarge : largeBudget f J s d ≤ 16*((f.L J : ℝ)/(f.m J : ℝ)) := by
    have hh := Parameters.depth_bound f.s_ge_two (J-1)
    unfold largeBudget largeUnit
    rw [hs,Family.qprime_formula]
    change 16*(1+(Parameters.B f.s (J-1) : ℝ)+(Parameters.L f.s (J-1) : ℝ)^(1/((f.s : ℝ)+1))) *
      (1+(Parameters.B f.s (J-1) : ℝ))^d ≤ 16*((Parameters.L f.s (J-1) : ℝ)/(Parameters.m f.s (J-1) : ℝ))
    nlinarith [hh]
  have hsmall : (∑ i : s, c.small i) ≤ (2000/7)*((f.L J : ℝ)/(f.m J : ℝ)) := by
    have hh := sum_abs_le_holder (by simpa only [Family.exponent_toReal] using f.r_gt_one : 1 < f.exponent.toReal) c.small
    simp only [abs_of_nonneg (c.small_nonneg _),Family.exponent_toReal,Fintype.card_coe,hs] at hh
    calc
      _ ≤ (f.L J : ℝ)^(1-1/f.r)*‖vec f.exponent c.small‖ := hh
      _ ≤ (f.L J : ℝ)^(1-1/f.r)*((2000/7)*f.theta J) :=
        mul_le_mul_of_nonneg_left (c.norm_small.trans hb) (Real.rpow_nonneg (by positivity) _)
      _ = _ := by rw [mul_left_comm,Family.holder_theta]
  have hmain : (∑ i : s, |norming.evaluateArray (w.blocks.embed i) g|) ≤
      (∑ i : s, c.small i)+(∑ i : s, c.large i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [ThinnedWindows.evalVector,Finset.mem_univ,ite_true] using c.majorizes i
  have hpos : 0 ≤ (f.L J : ℝ)/(f.m J : ℝ) := by positivity
  have hl := c.sum_large.trans hlarge
  calc
    _ ≤ (2000/7+16)*((f.L J : ℝ)/(f.m J : ℝ)) := by linarith
    _ ≤ 500*((f.L J : ℝ)/(f.m J : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) hpos
    _ = _ := by ring

lemma ThinnedWindows.norm_sum_bound {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (s : Finset ℕ) (hJ : 1 ≤ J) (hs : s.card = f.L J)
    (hε : ε*(s.card : ℝ)^(1/f.r) ≤ f.theta J) :
    ‖norming.includeFinite (∑ i : s, w.blocks.vector i)‖ ≤ 500*(f.L J : ℝ)/(f.m J : ℝ) := by
  have hb (g : Array) (hg : g ∈ f.norming) :
      |norming.evaluateArray (norming.includeFinite (∑ i : s, w.blocks.vector i)) g| ≤
      500*(f.L J : ℝ)/(f.m J : ℝ) := by
    have hf : g ∈ Full := f.norming_subset_full hg
    rw [norming.evaluateArray_eq_functional _ ⟨g,hf⟩,map_sum,map_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [BlockSequence.embed,norming.evaluateArray_eq_functional _ ⟨g,hf⟩] using w.sum_eval_bound s hJ hs hε g hg
  cases f with
  | mixed => exact norming.norm_le_of_evaluateArray _ _ (by positivity) hb
  | pure k =>
    apply norm_le_of_pure k _ _ _ (by positivity) hb
    intro α hα
    rw [norming.coordinate_includeFinite,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact Finsupp.notMem_support_iff.mp (fun hi => hα (w.blocks.pure_color k rfl i α hi))

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ExactPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

lemma BlockSequence.normer_cross {f : Family} (z : BlockSequence f) (i j : ℕ) (hij : i ≠ j)
    (g : Array) (hg : ∀ α ∈ g.support, α ∈ (vectorCrop (z.vector i) (z.nonzero i)).set f) :
    norming.evaluateArray (z.embed j) g = 0 := by
  apply evaluateArray_finite_disjoint
  apply Finset.disjoint_left.mpr
  intro α hα hgα
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (lt_irrefl α) (vectorCrop_successive (z.nonzero i) (z.nonzero j) (z.successive i j hij)
      α (hg α hgα) α (support_mem_vectorCrop f _ _ α hα)).1
  · exact (lt_irrefl α) (vectorCrop_successive (z.nonzero j) (z.nonzero i) (z.successive j i hji)
      α (support_mem_vectorCrop f _ _ α hα) α (hg α hgα)).1

lemma BlockSequence.exists_exactPair {f : Family} (z : BlockSequence f) (a J : ℕ) (hJ : 1 ≤ J) :
    Nonempty (ExactPair z a J) := by
  have hθ : 0 < f.theta J := by rw [Family.theta,Parameters.theta_eq f.s_ge_two]; positivity
  have hL : (0 : ℝ) < f.L J := by exact_mod_cast f.L_pos J
  have hm : (0 : ℝ) < f.m J := by exact_mod_cast f.m_pos J
  let ε := f.theta J / (f.L J : ℝ)^(1/f.r)
  have hε : 0 < ε := div_pos hθ (Real.rpow_pos_of_pos hL _)
  obtain ⟨w⟩ := exists_thinnedWindows z J ε hε a
  have heps : ε*(f.L J : ℝ)^(1/f.r) ≤ f.theta J := by
    dsimp [ε]
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hL _).ne']
  let X := ∑ i : Fin (f.L J), w.blocks.vector i
  have hX : X ≠ 0 := w.blocks.sum_nonzero _ (f.L_pos J)
  let c : ℝ := (f.m J : ℝ)/(f.L J : ℝ)
  have hc : 0 < c := div_pos hm hL
  let y := c • X
  have hy : y ≠ 0 := smul_ne_zero hc.ne' hX
  have hys : y.support = X.support := Finsupp.support_smul_eq hc.ne'
  have hn := fun i : Fin (f.L J) => exists_finite_vector_normer (w.blocks.vector i) (w.blocks.nonzero i)
    (w.lower_norm i) (fun k hk α hα => w.blocks.pure_color k hk i α hα)
  choose g hg hgn hgs hgv using hn
  let e : TypeI f := {
    weight := J
    weight_pos := hJ
    length := f.L J
    length_pos := f.L_pos J
    length_le := le_rfl
    child := g
    child_nonzero := hgn
    successive := by
      intro i j hij α hα β hβ
      exact vectorCrop_successive (w.blocks.nonzero i) (w.blocks.nonzero j)
        (w.blocks.successive i j hij) α (hgs i α hα) β (hgs j β hβ) }
  have hgeval (i : Fin (f.L J)) : norming.evaluateArray (norming.includeFinite X) (g i) =
      norming.evaluateArray (w.blocks.embed i) (g i) := by
    have hgf : g i ∈ Full := f.norming_subset_full (hg i)
    simp only [X,norming.evaluateArray_eq_functional _ ⟨g i,hgf⟩,map_sum]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [← norming.evaluateArray_eq_functional]
      exact w.blocks.normer_cross i j (fun he => hji (Fin.ext he.symm)) (g i) (hgs i)
    · simp
  have hyEval : 1/2 ≤ norming.evaluateArray (norming.includeFinite y) e.value := by
    have hef : e.value ∈ Full := f.norming_subset_full (e.mem_family hg)
    rw [norming.evaluateArray_eq_functional _ ⟨e.value,hef⟩]
    change 1/2 ≤ norming.functional ⟨e.value,hef⟩ (norming.includeFinite (c • X))
    rw [map_smul,map_smul]
    rw [smul_eq_mul, ← norming.evaluateArray_eq_functional (norming.includeFinite X) ⟨e.value,hef⟩]
    change 1/2 ≤ c * norming.evaluateArray (norming.includeFinite X) e.value
    rw [TypeI.value,map_smul,map_sum]
    simp only [show e.weight = J from rfl,show e.child = g from rfl,Rat.smul_def,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
    have he : (f.L J : ℝ)*(1/2 : ℝ) ≤ ∑ i, norming.evaluateArray (norming.includeFinite X) (g i) := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin (f.L J) => (1/2 : ℝ))
          (g := fun i => norming.evaluateArray (norming.includeFinite X) (g i))
          (fun i _ => by rw [hgeval i]; exact (hgv i).le)
    calc
      1/2 = c * ((1/(f.m J : ℝ))*((f.L J : ℝ)*(1/2))) := by dsimp [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) hc.le
  refine ⟨⟨y,hy,?_,?_,?_,e,rfl,hg,hyEval,?_⟩⟩
  · exact Submodule.smul_mem _ c (Submodule.sum_mem _ (fun i _ => w.mem_tail i))
  · have hb := w.norm_sum_bound (Finset.range (f.L J)) hJ (Finset.card_range _) (by simpa using heps)
    have hXnorm : ‖norming.includeFinite X‖ ≤ 500*(f.L J : ℝ)/(f.m J : ℝ) := by
      simpa only [X,Finset.sum_coe_sort,Fin.sum_univ_eq_sum_range] using hb
    change ‖norming.includeFinite (c • X)‖ ≤ 500
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    calc
      _ ≤ c*(500*(f.L J : ℝ)/(f.m J : ℝ)) := mul_le_mul_of_nonneg_left hXnorm hc.le
      _ = 500 := by dsimp [c]; field_simp
  · intro k hk α hα
    rw [hys] at hα
    obtain ⟨i,_,hi⟩ := Finsupp.mem_support_finsetSum α hα
    exact w.blocks.pure_color k hk i α hi
  · intro α hα
    have hh : α ∈ (∑ i : Fin (f.L J),g i).support := Finsupp.support_smul hα
    obtain ⟨i,_,hi⟩ := Finsupp.mem_support_finsetSum α hh
    apply vectorCrop_mono (w.blocks.nonzero i) hy _ (hgs i α hi)
    rw [hys]
    exact w.blocks.support_subset_sum _ i

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

namespace TreeNode
variable {f : Family} (z : BlockSequence f)

def initial : TreeNode z := by
  let e := Classical.choice (z.exists_exactPair 0 1 (by omega))
  let hb := z.support_subset_prefix 0 e.mem_tail
  exact ⟨0,1,by omega,e,hb.choose,hb.choose_spec.1,hb.choose_spec.2,1,by omega,by omega⟩

def lookup (l : List (TreeNode z)) (n : ℕ) : TreeNode z := l.getD n (initial z)

def requested (l : List (TreeNode z)) : ℕ :=
  if l.length = 0 then 1 else sigma (nodeCode z (lookup z l) ((l.length-1)/2))

lemma requested_pos (l : List (TreeNode z)) : 1 ≤ requested z l := by
  unfold requested
  split_ifs
  · omega
  · have := codeBound_lt_sigma (nodeCode z (lookup z l) ((l.length-1)/2))
    omega

def next (l : List (TreeNode z)) : TreeNode z := by
  let e := Classical.choice (z.exists_exactPair (nextStart z l) (requested z l) (requested_pos z l))
  let hb := z.support_subset_prefix _ e.mem_tail
  let S := listSupport z l ∪ e.piece.value.support
  let R := S.sup (fun α => S.sup (fun β => rho α β))
  let p := 1 + requested z l + l.toFinset.sup (fun d => d.metadata) + R
  exact ⟨nextStart z l,requested z l,requested_pos z l,e,hb.choose,hb.choose_spec.1,hb.choose_spec.2,p,by dsimp [p]; omega,
    by dsimp [p]; omega⟩

lemma next_start (l : List (TreeNode z)) : (next z l).start = nextStart z l := rfl
lemma next_weight (l : List (TreeNode z)) : (next z l).weight = requested z l := rfl

lemma next_metadata_gt (l : List (TreeNode z)) (d : TreeNode z) (hd : d ∈ l) :
    d.metadata < (next z l).metadata := by
  have h := Finset.le_sup (f := fun d : TreeNode z => d.metadata) (List.mem_toFinset.mpr hd)
  change _ < 1 + requested z l + l.toFinset.sup (fun d => d.metadata) + _
  omega

lemma next_rho (l : List (TreeNode z)) (α β : Γ)
    (hα : α ∈ listSupport z l ∪ (next z l).pair.piece.value.support)
    (hβ : β ∈ listSupport z l ∪ (next z l).pair.piece.value.support) :
    rho α β ≤ (next z l).metadata := by
  let S := listSupport z l ∪ (next z l).pair.piece.value.support
  have h : rho α β ≤ S.sup (fun x => S.sup (fun y => rho x y)) :=
    (Finset.le_sup (s := S) (f := fun y => rho α y) hβ).trans
      (Finset.le_sup (s := S) (f := fun x => S.sup (fun y => rho x y)) hα)
  change _ ≤ 1 + requested z l + l.toFinset.sup (fun d => d.metadata) + S.sup (fun x => S.sup (fun y => rho x y))
  omega

def state : ℕ → List (TreeNode z)
  | 0 => []
  | n+1 => state n ++ [next z (state n)]

def node (n : ℕ) : TreeNode z := next z (state z n)

lemma state_eq_ofFn (n : ℕ) : state z n = List.ofFn (fun i : Fin n => node z i) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state,List.ofFn_succ_last (f := fun i : Fin (n+1) => node z i)]
    change state z n ++ [node z n] = _
    rw [ih]
    rfl

lemma state_length (n : ℕ) : (state z n).length = n := by rw [state_eq_ofFn,List.length_ofFn]

lemma lookup_state {n k : ℕ} (hk : k < n) : lookup z (state z n) k = node z k := by
  simp [lookup,state_eq_ofFn,List.getD,hk]

lemma mem_state {n k : ℕ} (hk : k < n) : node z k ∈ state z n := by
  rw [state_eq_ofFn]
  exact List.mem_ofFn.mpr ⟨⟨k,hk⟩,rfl⟩

lemma finish_le_start {n k : ℕ} (hk : k < n) : (node z k).finish ≤ (node z n).start := by
  change _ ≤ (next z (state z n)).start
  rw [next_start]
  exact Finset.le_sup (List.mem_toFinset.mpr (mem_state z hk))

lemma metadata_strict : StrictMono (fun n => (node z n).metadata) := by
  intro n k hnk
  exact next_metadata_gt z (state z k) (node z n) (mem_state z hnk)

lemma support_before {n k : ℕ} (hk : k ≤ n) {α : Γ}
    (hα : α ∈ (node z k).pair.piece.value.support) :
    α ∈ listSupport z (state z n) ∪ (node z n).pair.piece.value.support := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · exact Finset.mem_union_right _ hα
  · exact Finset.mem_union_left _ ((mem_listSupport z _ _).mpr ⟨node z k,mem_state z hk,hα⟩)

lemma successive_vector {n k : ℕ} (hk : k < n) :
    ∀ α ∈ (node z k).pair.vector.support, ∀ β ∈ (node z n).pair.vector.support,
      α < β ∧ (f = .mixed → Colors.color α < Colors.color β) :=
  z.prefix_tail_successive _ (node z k).support
    (z.tailSpan_mono (finish_le_start z hk) (node z n).pair.mem_tail)

lemma successive_piece {n k : ℕ} (hk : k < n) :
    Successive f (node z k).pair.piece.value (node z n).pair.piece.value := by
  intro α hα β hβ
  exact vectorCrop_successive _ _ (successive_vector z hk)
    α ((node z k).pair.support α hα) β ((node z n).pair.support β hβ)

lemma nodeCode_eq_branch (b : ℕ → Bool) (n : ℕ) :
    nodeCode z (node z) (BinaryNodes.branch b n) =
      (rawAlong z (node z) (BinaryNodes.branch b)).code n := by
  unfold nodeCode
  rw [BinaryNodes.ancestors_branch,List.length_ofFn]
  simp only [Nat.add_sub_cancel]
  apply RawPath.code_congr_prefix
  all_goals
    intro i hi
    have hlen : i < (List.ofFn (fun j : Fin (n+1) => BinaryNodes.branch b j)).length := by
      rw [List.length_ofFn]; omega
    have he : (List.ofFn (fun j : Fin (n+1) => BinaryNodes.branch b j)).getD i 0 = BinaryNodes.branch b i := by
      rw [List.getD_eq_getElem _ _ hlen,List.getElem_ofFn]
    simp only [rawAlong]
    rw [he]

lemma nodeCode_lookup {n k : ℕ} (hk : k < n) :
    nodeCode z (lookup z (state z n)) k = nodeCode z (node z) k := by
  unfold nodeCode
  apply RawPath.code_congr_prefix
  all_goals
    intro i hi
    have hi' : i < (BinaryNodes.ancestors k).length := by
      have := List.length_pos_iff.mpr (BinaryNodes.ancestors_nonempty k)
      omega
    have hm : (BinaryNodes.ancestors k).getD i 0 ∈ BinaryNodes.ancestors k := by
      simpa only [List.getD_eq_getElem _ _ hi'] using List.getElem_mem hi'
    have hle := BinaryNodes.ancestors_mem_le k _ hm
    have he := lookup_state z (n := n) (k := (BinaryNodes.ancestors k).getD i 0) (hle.trans_lt hk)
    simp only [rawAlong]
    rw [he]

lemma weight_rule (b : ℕ → Bool) (n : ℕ) :
    (node z (BinaryNodes.branch b (n+1))).weight =
      sigma ((rawAlong z (node z) (BinaryNodes.branch b)).code n) := by
  let k := BinaryNodes.branch b (n+1)
  have hk : 0 < k := BinaryNodes.child_pos _ _
  have hp : (k-1)/2 = BinaryNodes.branch b n := BinaryNodes.child_parent _ _
  change (next z (state z k)).weight = _
  rw [next_weight,requested,state_length,ite_eq_right (Nat.ne_of_gt hk),hp]
  have hpk : BinaryNodes.branch b n < k := BinaryNodes.lt_child _ _
  rw [nodeCode_lookup z hpk,nodeCode_eq_branch]

/-- The prescribed-weight exact-pair construction yields actual admissible
paths on all infinite binary branches; records include all original metadata. -/
def branchPath (b : ℕ → Bool) : InfinitePath f where
  raw := rawAlong z (node z) (BinaryNodes.branch b)
  admissible := {
    successive := fun i j hij α hα β hβ => (successive_piece z (BinaryNodes.branch_strict b hij) α hα β hβ).1
    metadata_strict := (metadata_strict z).comp (BinaryNodes.branch_strict b)
    metadata_pos := fun i => (node z (BinaryNodes.branch b i)).metadata_pos
    weight_pos := fun i => (node z (BinaryNodes.branch b i)).weight_pos
    weight_le_metadata := fun i => (node z (BinaryNodes.branch b i)).weight_le_metadata
    rho_bound := by
      intro n α β hα hβ _hab
      apply next_rho z (state z (BinaryNodes.branch b n))
      · obtain ⟨i,hi,hiα⟩ := (RawPath.mem_support_iff _ n α).mp hα
        exact support_before z ((BinaryNodes.branch_strict b).monotone hi) hiα
      · obtain ⟨i,hi,hiβ⟩ := (RawPath.mem_support_iff _ n β).mp hβ
        exact support_before z ((BinaryNodes.branch_strict b).monotone hi) hiβ
    rule := weight_rule z b }
  piece := fun i => (node z (BinaryNodes.branch b i)).pair.piece
  value_eq := fun _ => rfl
  weight_eq := fun i => (node z (BinaryNodes.branch b i)).pair.weight_eq
  successive := fun _i _j hij => successive_piece z (BinaryNodes.branch_strict b hij)
  children_mem := fun i j => (node z (BinaryNodes.branch b i)).pair.child_mem j

end TreeNode
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

@[reducible] local instance crDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance crDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance crSubGroup (F : Submodule ℝ E) : NormedAddCommGroup F := inferInstance
@[reducible] local instance crSubSpace (F : Submodule ℝ E) : NormedSpace ℝ F := inferInstance
@[reducible] local instance crSubDualGroup (F : Submodule ℝ E) : NormedAddCommGroup (StrongDual ℝ F) := inferInstance
@[reducible] local instance crSubDualSpace (F : Submodule ℝ E) : NormedSpace ℝ (StrongDual ℝ F) := inferInstance

def restrict (F : Submodule ℝ E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ F :=
  ContinuousLinearMap.precomp ℝ F.subtypeL

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter Set TopologicalSpace
open scoped Classical Topology

@[reducible] local instance atDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance atDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
local instance atXClosed : IsClosed (X₀ : Set (StrongDual ℝ E)) := norming.predual_isClosed
@[reducible] local instance atWGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance atWSpace : NormedSpace ℝ W := inferInstance

@[reducible] local instance atX0Group : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance atX0Space : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance atX0DualGroup : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance atX0DualSpace : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma eval0_isometry : Isometry (evalOn X₀) := norming.evaluationIsometry.isometry

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

/-- The changed predual is the kernel of the perturbed quotient map. -/
def X : Submodule ℝ (StrongDual ℝ E) := (X₀.mkQL - B hCH).ker
instance X_isClosed : IsClosed (X hCH : Set (StrongDual ℝ E)) := (X₀.mkQL - B hCH).isClosed_ker
instance X_complete : CompleteSpace (X hCH) := (X_isClosed hCH).completeSpace_coe

@[reducible] local instance atXGroup : NormedAddCommGroup (X hCH) := inferInstance
@[reducible] local instance atXSpace : NormedSpace ℝ (X hCH) := inferInstance
@[reducible] local instance atXDualGroup : NormedAddCommGroup (StrongDual ℝ (X hCH)) := inferInstance
@[reducible] local instance atXDualSpace : NormedSpace ℝ (StrongDual ℝ (X hCH)) := inferInstance

end SeparableQuotient.ActualSpace

end

end OAI
end


