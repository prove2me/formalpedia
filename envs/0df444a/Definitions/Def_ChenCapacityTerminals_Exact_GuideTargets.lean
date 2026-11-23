-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets
-- name    : ChenCapacityTerminals_Exact_GuideTargets
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:30:34.01296+00:00
-- url     : https://prove2.me/theorems/495cc135-eae7-416d-aed4-dfa2a3d70ceb
-- title:
--   Whole-target and mixed-target guide entries
-- statement:
--   For the charging argument in Lemma 2.3, decorate every virtual guide arc with the merge-forest part used as its target. A join arc is decorated by its nonheavy child, a final predecessor arc by its final nonsource part, and a dummy-root arc by its final source part. Forgetting these decorations recovers exactly the original guide, including list order and multiplicities.
--
--   For a shore $X$, an entering decorated arc is a **whole-target entry** if its target is contained in $X$, and a **mixed-target entry** otherwise. Thus every entering guide arc belongs to exactly one of the two classes, and the list-length identity
--   $$
--   |\delta_T^-(X)|=|\delta_{T,\mathrm{whole}}^-(X)|+|\delta_{T,\mathrm{mixed}}^-(X)|
--   $$
--   holds without any assumptions on the network or construction.
--
--   **Formalization Note** Targets are finite sets of natural-number vertex labels. The entry functions are noncomputable because the underlying guide contains noncomputable final-source data.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 5, PDF p. 6, proof of Lemma 2.3, paragraphs “Targets wholly in X” and “Mixed targets”; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- A guide arc together with the merge-forest part to which the proof of Lemma 2.3 assigns it. -/
structure TargetedGuideEdge where
  tail : ℕ
  head : ℕ
  target : Finset ℕ

/-- Forget the target part attached to a guide arc. -/
def TargetedGuideEdge.toPair (e : TargetedGuideEdge) : ℕ × ℕ := (e.tail, e.head)

/-- Attach to every guide arc its nonheavy child, final nonsource part, or final source part. -/
noncomputable def Construction.targetedGuide (c : Construction) (G : Network) (τ : ℝ) :
    List TargetedGuideEdge := by
  classical
  exact
    (c.joins.flatMap fun j => j.edges.map fun e => ⟨e.1, c.representative e.2, e.2⟩) ++
    (c.finalEdges.map fun e => ⟨e.1, c.representative e.2, e.2⟩) ++
    ((c.finalSources G τ).toList.map fun C => ⟨dummy G, c.representative C, C⟩)

@[simp] theorem Construction.targetedGuide_toPair (c : Construction) (G : Network) (τ : ℝ) :
    (c.targetedGuide G τ).map TargetedGuideEdge.toPair = c.guide G τ := by
  classical
  have hj :
      (c.joins.flatMap fun j => j.edges.map fun e =>
          (⟨e.1, c.representative e.2, e.2⟩ : TargetedGuideEdge)).map TargetedGuideEdge.toPair =
        c.joins.flatMap fun j => j.edges.map fun e => (e.1, c.representative e.2) := by
    induction c.joins with
    | nil => rfl
    | cons j js ih =>
        simp [ih, List.map_map, Function.comp_def, TargetedGuideEdge.toPair]
  have hf :
      (c.finalEdges.map fun e =>
          (⟨e.1, c.representative e.2, e.2⟩ : TargetedGuideEdge)).map TargetedGuideEdge.toPair =
        c.finalEdges.map fun e => (e.1, c.representative e.2) := by
    simp [List.map_map, Function.comp_def, TargetedGuideEdge.toPair]
  unfold Construction.targetedGuide Construction.guide
  simp only [List.map_append, hj, hf]
  simp [List.map_map, Function.comp_def, TargetedGuideEdge.toPair]

/-- Entering guide arcs whose entire associated target part is contained in `X`. -/
noncomputable def wholeTargetEntries (c : Construction) (G : Network) (τ : ℝ) (X : Finset ℕ) : ℕ := by
  classical
  exact ((c.targetedGuide G τ).filter fun e =>
    e.tail ∉ X ∧ e.head ∈ X ∧ e.target ⊆ X).length

/-- Entering guide arcs whose associated target part meets both `X` and its complement. -/
noncomputable def mixedTargetEntries (c : Construction) (G : Network) (τ : ℝ) (X : Finset ℕ) : ℕ := by
  classical
  exact ((c.targetedGuide G τ).filter fun e =>
    e.tail ∉ X ∧ e.head ∈ X ∧ ¬e.target ⊆ X).length

/-- The whole/mixed dichotomy partitions all entering guide arcs, with multiplicities retained. -/
theorem guideEntries_eq_wholeTargetEntries_add_mixedTargetEntries
    (c : Construction) (G : Network) (τ : ℝ) (X : Finset ℕ) :
    guideEntries (c.guide G τ) X =
      wholeTargetEntries c G τ X + mixedTargetEntries c G τ X := by
  classical
  rw [← c.targetedGuide_toPair G τ]
  unfold guideEntries wholeTargetEntries mixedTargetEntries
  generalize c.targetedGuide G τ = es
  induction es with
  | nil => rfl
  | cons e es ih =>
      by_cases htail : e.tail ∈ X
      · simp [TargetedGuideEdge.toPair, htail] at ih ⊢
        exact ih
      · by_cases hhead : e.head ∈ X
        · by_cases ht : e.target ⊆ X
          · simp [TargetedGuideEdge.toPair, htail, hhead, ht] at ih ⊢
            omega
          · simp [TargetedGuideEdge.toPair, htail, hhead, ht] at ih ⊢
            omega
        · simp [TargetedGuideEdge.toPair, htail, hhead] at ih ⊢
          exact ih

end ChenCapacityTerminals.Exact


