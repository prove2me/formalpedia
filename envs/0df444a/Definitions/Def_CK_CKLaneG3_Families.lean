-- Prove2me | Definitions.Def_CK_CKLaneG3_Families
-- name    : CK_CKLaneG3_Families
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:53:40.45647+00:00
-- url     : https://prove2.me/theorems/54cee490-343b-4438-bc68-44d3467bb0a0
-- title:
--   Courtade–Kumar proof module `CKLaneG3.Families` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.Families` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.Families` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.Families (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/Families.lean)

import Definitions.Def_CK_CKLaneG3_Kernel

-- ===== source module CKLaneG3.Families =====
section

/-!
# Lane G3: leaf-family adapters and family algebra for the archived `(u,v,t)` tree

* `goodLabel n` / `goodIn ns`: owner-label predicates of method families (label numbering of
  `CKLaneD.ArchTree`: 0 endpoint_plane_taylor, 1 shifted_logsum, 2 global_cap_slope,
  3 global_feasible_split, 4 global_eight_ratio, 5 outside, 6 global_parent_envelope,
  7 global_parent8, 8 global_low_entropy_025, 9 global_parent16, 10 global_parent_direct,
  11 logsum_direct, 12 global_corner).
* Adapters from the three leaf-module shapes used by method lanes to the kernel's leaf-list form
  `∀ p ∈ L, RegionOn PsiSem (uvtBox p)`: pairs (`psiSem_of_shards`, in `Kernel`), path lists
  (`psiSem_of_paths`), single leaves (`psiSem_single`).
* `leafFacts_good_mono`: restrict / re-express the label predicate.
-/

namespace CKLaneG3

open CKLaneD GeneralCK

/-- Owner label predicate of a single-label family. -/
def goodLabel (n : ℕ) (l : ℕ) : Bool := l == n

/-- Owner label predicate of a union of families. -/
def goodIn (ns : List ℕ) (l : ℕ) : Bool := ns.contains l

theorem psiSem_of_paths {L : List (List ℕ)} (h : ∀ p ∈ L, SemUVT (uvtBox p)) :
    ∀ p ∈ L, RegionOn PsiSem (uvtBox p) := h

theorem psiSem_single {p : List ℕ} (h : SemUVT (uvtBox p)) :
    ∀ q ∈ [p], RegionOn PsiSem (uvtBox q) := by
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  exact h

theorem leafFacts_good_mono {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {g g' : ℕ → Bool}
    {T : PTree} {rpre : List ℕ} (h : LeafFacts P g T rpre) (hg : ∀ l, g' l = true → g l = true) :
    LeafFacts P g' T rpre :=
  fun q hq hq' => h q hq (hg q.2 hq')

/-- Union of two families expressed with `goodIn`. -/
theorem leafFacts_goodIn_append {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {ns ms : List ℕ}
    {T : PTree} {rpre : List ℕ} (h₁ : LeafFacts P (goodIn ns) T rpre)
    (h₂ : LeafFacts P (goodIn ms) T rpre) : LeafFacts P (goodIn (ns ++ ms)) T rpre := by
  intro q hq hg
  simp only [goodIn, List.contains_append, Bool.or_eq_true] at hg
  rcases hg with hg | hg
  · exact h₁ q hq hg
  · exact h₂ q hq hg

theorem leafFacts_goodIn_of_goodLabel {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {n : ℕ}
    {T : PTree} {rpre : List ℕ} (h : LeafFacts P (goodLabel n) T rpre) :
    LeafFacts P (goodIn [n]) T rpre :=
  leafFacts_good_mono h (fun l hl => by
    have e : l = n := by simpa [goodIn] using hl
    simp [goodLabel, e])

theorem leafFacts_goodIn_of_goodEndpoint {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop}
    {T : PTree} {rpre : List ℕ} (h : LeafFacts P goodEndpoint T rpre) :
    LeafFacts P (goodIn [0]) T rpre :=
  leafFacts_good_mono h (fun l hl => by
    have e : l = 0 := by simpa [goodIn] using hl
    simp [goodEndpoint, e])

/-! ## Label-only traversals (no paths are built; cheap in the kernel) -/

/-- Every leaf label of `T` satisfies `f`. -/
def tallLabels (f : ℕ → Bool) : PTree → Bool
  | .leaf l => f l
  | .node _ l r => tallLabels f l && tallLabels f r

theorem all_of_tallLabels {f : ℕ → Bool} : ∀ (T : PTree) (rpre : List ℕ),
    tallLabels f T = true → ∀ q ∈ T.leavesR rpre, f q.2 = true
  | .leaf l, rpre, h, q, hq => by
      simp only [PTree.leavesR, List.mem_singleton] at hq
      subst hq
      simpa [tallLabels] using h
  | .node ax l r, rpre, h, q, hq => by
      simp only [tallLabels, Bool.and_eq_true] at h
      simp only [PTree.leavesR, List.mem_append] at hq
      rcases hq with hq | hq
      · exact all_of_tallLabels l _ h.1 q hq
      · exact all_of_tallLabels r _ h.2 q hq

/-- A subtree without `good` leaves (label-only check) carries a vacuous leaf family. -/
theorem leafFacts_of_tallLabels {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {good : ℕ → Bool}
    (T : PTree) (rpre : List ℕ) (h : tallLabels (fun l => !good l) T = true) :
    LeafFacts P good T rpre := by
  intro q hq hg
  have := all_of_tallLabels T rpre h q hq
  simp [hg] at this

/-- Full box form with a label-only coverage check. -/
theorem regionOn_of_tallLabels {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {good : ℕ → Bool}
    (T : PTree) (rpre : List ℕ) (hall : tallLabels good T = true) (h : LeafFacts P good T rpre) :
    RegionOn P (uvtBox rpre.reverse) :=
  regionOn_of_leafFacts T rpre (List.all_eq_true.mpr (all_of_tallLabels T rpre hall)) h

end CKLaneG3

end


