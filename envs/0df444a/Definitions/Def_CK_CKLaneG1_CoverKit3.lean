-- Prove2me | Definitions.Def_CK_CKLaneG1_CoverKit3
-- name    : CK_CKLaneG1_CoverKit3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:19:12.841173+00:00
-- url     : https://prove2.me/theorems/a0a129b0-468b-4c3d-942f-06c314d99301
-- title:
--   Courtade–Kumar proof module `CKLaneG1.CoverKit3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG1.CoverKit3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG1.CoverKit3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG1.CoverKit3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG1/CoverKit3.lean)

import Definitions.Def_CK_CKLaneG1_CoverKit

-- ===== source module CKLaneG1.CoverKit3 =====
section

/-!
# Lane G1: cover kit, part 3 — glue between archived label trees and method-lane witness data

Two generic, linear-time ways to attach per-leaf witnesses to an archived tree `T : PT ℕ`
(e.g. `CKLaneG1.FE8.tree`), so that the cover theorems of the `CKLaneG1.<Cover>` modules apply verbatim:

* witness trees (`PT W`, the `CKLaneN1.dbTree` style): `PT.sameShape lab T T'` checks that `T'` has exactly
  the splits of `T` and that `lab` maps every witness to the archived label; then
  `T'.leaves.map (path, lab ·) = T.leaves` (`PT.sameShape_leaves`), `PT.exists_of_sameShape`.
* witness lists in DFS (= lexicographic = archive) order: `PT.walkE skip T [] es = some []` checks that the
  entries' paths are exactly the leaves of `T` whose label is not skipped, in order; then every such leaf
  has an entry with its path (`PT.walkE_mem`, `PT.walkE_all`).
-/

set_option autoImplicit false

namespace CKLaneG1

open CKLaneN1

/-! ## Witness trees of the same shape -/

/-- `T'` has exactly the splits of `T`, and `lab` maps each leaf payload of `T'` to the label of `T`. -/
def PT.sameShape {W : Type} (lab : W → ℕ) : PT ℕ → PT W → Bool
  | .leaf l, .leaf w => lab w == l
  | .node a l r, .node a' l' r' => a == a' && PT.sameShape lab l l' && PT.sameShape lab r r'
  | .leaf _, .node _ _ _ => false
  | .node _ _ _, .leaf _ => false

theorem PT.sameShape_leavesR {W : Type} (lab : W → ℕ) :
    ∀ (T : PT ℕ) (T' : PT W) (rpre : List ℕ), PT.sameShape lab T T' = true →
      (T'.leavesR rpre).map (fun q => (q.1, lab q.2)) = T.leavesR rpre
  | .leaf l, .leaf w, rpre, h => by
      simp only [PT.sameShape, beq_iff_eq] at h
      simp [PT.leavesR, h]
  | .node a l r, .node a' l' r', rpre, h => by
      simp only [PT.sameShape, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨ha, hl⟩, hr⟩ := h
      subst ha
      simp only [PT.leavesR, List.map_append]
      rw [PT.sameShape_leavesR lab l l' _ hl, PT.sameShape_leavesR lab r r' _ hr]
  | .leaf _, .node _ _ _, _, h => by simp [PT.sameShape] at h
  | .node _ _ _, .leaf _, _, h => by simp [PT.sameShape] at h

theorem PT.sameShape_leaves {W : Type} (lab : W → ℕ) {T : PT ℕ} {T' : PT W}
    (h : PT.sameShape lab T T' = true) : T'.leaves.map (fun q => (q.1, lab q.2)) = T.leaves :=
  PT.sameShape_leavesR lab T T' [] h

/-- Every leaf of the archived tree has a witness leaf with the same path and the archived label. -/
theorem PT.exists_of_sameShape {W : Type} (lab : W → ℕ) {T : PT ℕ} {T' : PT W}
    (h : PT.sameShape lab T T' = true) {q : List ℕ × ℕ} (hq : q ∈ T.leaves) :
    ∃ q' ∈ T'.leaves, q'.1 = q.1 ∧ lab q'.2 = q.2 := by
  rw [← PT.sameShape_leaves lab h] at hq
  obtain ⟨q', hq', e⟩ := List.mem_map.mp hq
  subst e
  exact ⟨q', hq', rfl, rfl⟩

/-- Every witness leaf is an archived leaf with label `lab w`. -/
theorem PT.mem_of_sameShape {W : Type} (lab : W → ℕ) {T : PT ℕ} {T' : PT W}
    (h : PT.sameShape lab T T' = true) {q' : List ℕ × W} (hq' : q' ∈ T'.leaves) :
    (q'.1, lab q'.2) ∈ T.leaves := by
  rw [← PT.sameShape_leaves lab h]
  exact List.mem_map.mpr ⟨q', hq', rfl⟩

/-! ## Witness lists in DFS order -/

/-- DFS walk of `T` (reversed path prefix `rpre`) consuming the entries `es` in order: every leaf whose
label is not skipped must carry the head entry's path.  Returns the unconsumed entries. -/
def PT.walkE {W : Type} (skip : ℕ → Bool) : PT ℕ → List ℕ → List (List ℕ × W) →
    Option (List (List ℕ × W))
  | .leaf l, rpre, es =>
      if skip l then some es else
        match es with
        | e :: es' => if e.1 = rpre.reverse then some es' else none
        | [] => none
  | .node ax l r, rpre, es =>
      match PT.walkE skip l (2 * ax :: rpre) es with
      | some es' => PT.walkE skip r ((2 * ax + 1) :: rpre) es'
      | none => none

theorem PT.walkE_suffix {W : Type} (skip : ℕ → Bool) :
    ∀ (T : PT ℕ) (rpre : List ℕ) (es rest : List (List ℕ × W)),
      PT.walkE skip T rpre es = some rest → rest <:+ es
  | .leaf l, rpre, [], rest, h => by
      simp only [PT.walkE] at h
      by_cases hs : skip l = true
      · rw [if_pos hs] at h
        cases h
        exact List.suffix_refl _
      · rw [if_neg hs] at h
        cases h
  | .leaf l, rpre, e :: es', rest, h => by
      simp only [PT.walkE] at h
      by_cases hs : skip l = true
      · rw [if_pos hs] at h
        cases h
        exact List.suffix_refl _
      · rw [if_neg hs] at h
        by_cases he : e.1 = rpre.reverse
        · rw [if_pos he] at h
          cases h
          exact List.suffix_cons _ _
        · rw [if_neg he] at h
          cases h
  | .node ax l r, rpre, es, rest, h => by
      simp only [PT.walkE] at h
      cases hl : PT.walkE skip l (2 * ax :: rpre) es with
      | none => simp [hl] at h
      | some es' =>
          simp only [hl] at h
          exact (PT.walkE_suffix skip r _ es' rest h).trans (PT.walkE_suffix skip l _ es es' hl)

theorem PT.walkE_memR {W : Type} (skip : ℕ → Bool) :
    ∀ (T : PT ℕ) (rpre : List ℕ) (es rest : List (List ℕ × W)),
      PT.walkE skip T rpre es = some rest →
        ∀ q ∈ T.leavesR rpre, skip q.2 = false → ∃ e ∈ es, e.1 = q.1
  | .leaf l, rpre, [], rest, h, q, hq, hsk => by
      simp only [PT.leavesR, List.mem_singleton] at hq
      subst hq
      simp only [PT.walkE] at h
      have hs : ¬ skip l = true := by simpa using hsk
      rw [if_neg hs] at h
      cases h
  | .leaf l, rpre, e :: es', rest, h, q, hq, hsk => by
      simp only [PT.leavesR, List.mem_singleton] at hq
      subst hq
      simp only [PT.walkE] at h
      have hs : ¬ skip l = true := by simpa using hsk
      rw [if_neg hs] at h
      by_cases he : e.1 = rpre.reverse
      · exact ⟨e, List.mem_cons_self .., he⟩
      · rw [if_neg he] at h
        cases h
  | .node ax l r, rpre, es, rest, h, q, hq, hsk => by
      simp only [PT.walkE] at h
      cases hl : PT.walkE skip l (2 * ax :: rpre) es with
      | none => simp [hl] at h
      | some es' =>
          simp only [hl] at h
          simp only [PT.leavesR, List.mem_append] at hq
          rcases hq with hq | hq
          · exact PT.walkE_memR skip l _ es es' hl q hq hsk
          · obtain ⟨e, he, he'⟩ := PT.walkE_memR skip r _ es' rest h q hq hsk
            exact ⟨e, (PT.walkE_suffix skip l _ es es' hl).subset he, he'⟩

/-- A successful walk gives every non-skipped leaf an entry with its path. -/
theorem PT.walkE_mem {W : Type} {skip : ℕ → Bool} {T : PT ℕ} {es rest : List (List ℕ × W)}
    (h : PT.walkE skip T [] es = some rest) :
    ∀ q ∈ T.leaves, skip q.2 = false → ∃ e ∈ es, e.1 = q.1 :=
  PT.walkE_memR skip T [] es rest h

/-- Per-entry facts transfer to every non-skipped leaf. -/
theorem PT.walkE_all {W : Type} {skip : ℕ → Bool} {T : PT ℕ} {es rest : List (List ℕ × W)}
    (h : PT.walkE skip T [] es = some rest) {P : List ℕ → Prop} (hP : ∀ e ∈ es, P e.1) :
    ∀ q ∈ T.leaves, skip q.2 = false → P q.1 := by
  intro q hq hsk
  obtain ⟨e, he, he'⟩ := PT.walkE_mem h q hq hsk
  rw [← he']
  exact hP e he

end CKLaneG1

#check @CKLaneG1.PT.sameShape_leaves
#print axioms CKLaneG1.PT.sameShape_leaves
#check @CKLaneG1.PT.exists_of_sameShape
#print axioms CKLaneG1.PT.exists_of_sameShape
#check @CKLaneG1.PT.walkE_mem
#print axioms CKLaneG1.PT.walkE_mem
#check @CKLaneG1.PT.walkE_all
#print axioms CKLaneG1.PT.walkE_all

end


