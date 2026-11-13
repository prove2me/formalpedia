-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F001
-- name    : ProbabilityTheory_chapter_03_def_3_1_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T16:24:15.984197+00:00
-- url     : https://prove2.me/theorems/281c4fd7-3530-4e3f-893e-603ede3f8415
-- title:
--   Chapter 3, def_3_1: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 3, source module `def_3_1`: `toAddContent`, `toAddContent_apply`, `toAddContent_isSigmaSubadditive`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_1.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic

open Set ENNReal Function MeasureTheory

namespace FieldOfSets

end FieldOfSets

namespace Premeasure

variable {Ω : Type*} {F₀ : FieldOfSets Ω}

/-- Countable additivity of a pre-measure implies finite additivity on its field. -/
private lemma additive_for_content (pm : Premeasure F₀) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) (hst : Disjoint s t)
    (hut : s ∪ t ∈ F₀.carrier) :
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
  let A : ℕ → Set Ω := fun i => if i = 0 then s else if i = 1 then t else ∅
  have hA : ∀ i, A i ∈ F₀.carrier := by
    intro i
    rcases i with (_ | _ | i) <;> simp [A, hs, ht, F₀.empty_mem]
  have hUset : (⋃ i, A i) = s ∪ t := by
    ext x
    simp only [mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      rcases i with (_ | _ | i) <;> simp_all [A]
    · intro hx
      exact hx.elim (fun hxs => ⟨0, by simpa [A] using hxs⟩)
        (fun hxt => ⟨1, by simpa [A] using hxt⟩)
  have hU : (⋃ i, A i) ∈ F₀.carrier := hUset ▸ hut
  have hdisj : Pairwise (Disjoint on A) := by
    intro i j hij
    rcases i with (_ | _ | i) <;> rcases j with (_ | _ | j) <;>
      simp_all [A, Function.onFun, hst.symm]
  have hsigma := pm.sigma_additive A hA hU hdisj
  calc
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨⋃ i, A i, hU⟩ :=
      congrArg pm.μ₀ (Subtype.ext hUset.symm)
    _ = ∑' i, pm.μ₀ ⟨A i, hA i⟩ := hsigma
    _ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
      rw [tsum_eq_sum (s := Finset.range 2)]
      · simp [A, Finset.sum_range_succ]
      · intro j hj
        simp only [Finset.mem_range, not_lt] at hj
        have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        simpa [A, hj0, hj1] using pm.map_empty

noncomputable def toAddContent (pm : Premeasure F₀) : AddContent ℝ≥0∞ F₀.carrier :=
  F₀.isSetRing.addContent_of_union pm.toSetFunction pm.toSetFunction_empty <| by
    intro s t hs ht hst
    rw [pm.toSetFunction_of_mem (F₀.union_mem _ _ hs ht),
      pm.toSetFunction_of_mem hs, pm.toSetFunction_of_mem ht]
    exact additive_for_content pm hs ht hst (F₀.union_mem _ _ hs ht)



end Premeasure


