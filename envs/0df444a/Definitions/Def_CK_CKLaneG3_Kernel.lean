-- Prove2me | Definitions.Def_CK_CKLaneG3_Kernel
-- name    : CK_CKLaneG3_Kernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:42:07.313396+00:00
-- url     : https://prove2.me/theorems/76f125b6-05fc-4672-b1ba-fa786564af32
-- title:
--   Courtade–Kumar proof module `CKLaneG3.Kernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.Kernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.Kernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.Kernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/Kernel.lean)

import Definitions.Def_CK_CKLaneD_Cover

-- ===== source module CKLaneG3.Kernel =====
section

/-!
# Lane G3: generic subtree-aggregation kernel over the archived `(u,v,t)` partition tree

* `RegionOn P U`: the pointwise law predicate `P` holds for every interior law whose data
  `(a, b, meanEntropy)` lie in the exact clipped physical image `InUVT U` of the `(u,v,t)` box `U`.
  `RegionOn PsiSem U` is definitionally Lane D's `SemUVT U`.
* `regionOn_split` / `regionOn_node`: the region Prop is closed under the archived binary halving
  (no side conditions).
* `LeafFacts P good T rpre`: every leaf of the subtree `T` (reversed path prefix `rpre`) whose owner
  label satisfies `good` has `RegionOn P` on its exact box.  Aggregation: `leafFacts_node`,
  `leafFacts_leaf`, `leafFacts_sub_node` (node of the global tree addressed by its path),
  `leafFacts_of_sublist` (bottom level, from a leaf-family list and a kernel-checked sublist test).
* Box forms: `residual_of_leafFacts` (region Prop on the whole subtree box except on the images of
  leaves NOT covered by `good`), `regionOn_of_leafFacts` (fully covered subtree: region Prop on the
  whole subtree box).
* Family algebra: `leafFacts_or` (union of two leaf families), `leafFacts_mono`.
-/

namespace CKLaneG3

open CKLaneD GeneralCK

/-! ## Region Prop on a `(u,v,t)` box and the halving split -/

/-- The region Prop: `P` for every interior law in the physical image of the box `U`. -/
def RegionOn (P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop) (U : UVT) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InUVT U μ.a μ.b μ.meanEntropy → P k μ

/-- Lane D's psi-candidate Bellman predicate. -/
def PsiSem (k : ℕ) (μ : InteriorLaw (Fin k)) : Prop :=
  candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

theorem regionOn_psiSem_iff (U : UVT) : RegionOn PsiSem U ↔ SemUVT U := Iff.rfl

/-- The two halves of an archived halving step cover the physical image of the parent box. -/
theorem inUVT_step (U : UVT) (ax : ℕ) {a b E : ℝ} (h : InUVT U a b E) :
    InUVT (uvtStep U (2 * ax)) a b E ∨ InUVT (uvtStep U (2 * ax + 1)) a b E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rcases ax with _ | _ | _ | ax
  · rcases le_total ((2 : ℝ) ^ (-(((U.u0 + U.u1) / 2 : ℚ) : ℝ))) a with hm | hm
    · left; exact ⟨hm, h2, h3, h4, h5, h6, h7, h8⟩
    · right; exact ⟨h1, hm, h3, h4, h5, h6, h7, h8⟩
  · rcases le_total b (1 - (2 : ℝ) ^ (-(((U.v0 + U.v1) / 2 : ℚ) : ℝ))) with hm | hm
    · left; exact ⟨h1, h2, h3, hm, h5, h6, h7, h8⟩
    · right; exact ⟨h1, h2, hm, h4, h5, h6, h7, h8⟩
  · rcases le_total E ((EMIN : ℝ) + (((U.t0 + U.t1) / 2 : ℚ) : ℝ) * ((H a + H b) / 2 - (EMIN : ℝ)))
      with hm | hm
    · left; exact ⟨h1, h2, h3, h4, h5, h6, h7, hm⟩
    · right; exact ⟨h1, h2, h3, h4, h5, h6, hm, h8⟩
  · left
    have e : 2 * (ax + 3) = 2 * ax + 6 := by ring
    simp only [uvtStep, e]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem regionOn_split {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {U : UVT} (ax : ℕ)
    (h0 : RegionOn P (uvtStep U (2 * ax))) (h1 : RegionOn P (uvtStep U (2 * ax + 1))) :
    RegionOn P U := by
  intro k μ hin
  rcases inUVT_step U ax hin with h | h
  · exact h0 k μ h
  · exact h1 k μ h

/-- Node combination on literal paths. -/
theorem regionOn_node {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} (p : List ℕ) (ax : ℕ)
    (h0 : RegionOn P (uvtBox (p ++ [2 * ax]))) (h1 : RegionOn P (uvtBox (p ++ [2 * ax + 1]))) :
    RegionOn P (uvtBox p) := by
  rw [uvtBox_append] at h0 h1
  exact regionOn_split ax h0 h1

/-! ## Subtrees of a `PTree` addressed by paths -/

/-- Junk label used for invalid addresses (not an archived owner label). -/
def junkLabel : ℕ := 1000000

/-- The child of a node selected by a digit (`2 ax` lower half, `2 ax + 1` upper half). -/
def tchild : PTree → ℕ → PTree
  | .leaf _, _ => .leaf junkLabel
  | .node ax l r, d => if d = 2 * ax then l else if d = 2 * ax + 1 then r else .leaf junkLabel

/-- The subtree at a path. -/
def tsub (T : PTree) (p : List ℕ) : PTree := p.foldl tchild T

/-- `S` is an internal node halving axis `ax`. -/
def tisNodeAx : PTree → ℕ → Bool
  | .leaf _, _ => false
  | .node ax' _ _, ax => ax' == ax

theorem tsub_nil (T : PTree) : tsub T [] = T := rfl

theorem tsub_append (T : PTree) (p : List ℕ) (d : ℕ) :
    tsub T (p ++ [d]) = tchild (tsub T p) d := by
  unfold tsub
  rw [List.foldl_append]
  rfl

theorem eq_node_of_tisNodeAx {S : PTree} {ax : ℕ} (h : tisNodeAx S ax = true) :
    S = .node ax (tchild S (2 * ax)) (tchild S (2 * ax + 1)) := by
  cases S with
  | leaf l => simp [tisNodeAx] at h
  | node ax' l r =>
      simp only [tisNodeAx, beq_iff_eq] at h
      subst h
      simp [tchild]

/-! ## Leaf families over subtrees -/

/-- Every `good`-labelled leaf of the subtree `T` (reversed prefix `rpre`) satisfies the region
Prop on its exact box. -/
def LeafFacts (P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop) (good : ℕ → Bool) (T : PTree)
    (rpre : List ℕ) : Prop :=
  ∀ q ∈ T.leavesR rpre, good q.2 = true → RegionOn P (uvtBox q.1)

section Families

variable {P : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {good : ℕ → Bool}

theorem leafFacts_node {ax : ℕ} {l r : PTree} {rpre : List ℕ}
    (hl : LeafFacts P good l (2 * ax :: rpre)) (hr : LeafFacts P good r ((2 * ax + 1) :: rpre)) :
    LeafFacts P good (.node ax l r) rpre := by
  intro q hq hg
  simp only [PTree.leavesR, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hl q hq hg
  · exact hr q hq hg

theorem leafFacts_leaf {lab : ℕ} {rpre : List ℕ}
    (h : good lab = true → RegionOn P (uvtBox rpre.reverse)) :
    LeafFacts P good (.leaf lab) rpre := by
  intro q hq hg
  simp only [PTree.leavesR, List.mem_singleton] at hq
  subst hq
  exact h hg

/-- Node combination for subtrees of a global tree `T` addressed by literal paths. -/
theorem leafFacts_sub_node (T : PTree) (p : List ℕ) (ax : ℕ)
    (hax : tisNodeAx (tsub T p) ax = true)
    (hl : LeafFacts P good (tsub T (p ++ [2 * ax])) (p ++ [2 * ax]).reverse)
    (hr : LeafFacts P good (tsub T (p ++ [2 * ax + 1])) (p ++ [2 * ax + 1]).reverse) :
    LeafFacts P good (tsub T p) p.reverse := by
  simp only [tsub_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hl hr
  rw [eq_node_of_tisNodeAx hax]
  exact leafFacts_node hl hr

/-- Bottom level: a leaf family given as a list of certified paths `L`; the `good` leaves of the
subtree must form a sublist of `L` (checked by the kernel). -/
theorem leafFacts_of_sublist (T : PTree) (rpre : List ℕ) (L : List (List ℕ))
    (hL : ∀ p ∈ L, RegionOn P (uvtBox p))
    (hc : (((T.leavesR rpre).filter (fun q => good q.2)).map Prod.fst).isSublist L = true) :
    LeafFacts P good T rpre := by
  intro q hq hg
  apply hL
  have hs := List.isSublist_iff_sublist.mp hc
  exact hs.subset (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, hg⟩, rfl⟩)

/-- A subtree without `good` leaves carries a vacuous leaf family. -/
theorem leafFacts_of_no_good (T : PTree) (rpre : List ℕ)
    (hc : (T.leavesR rpre).all (fun q => !good q.2) = true) : LeafFacts P good T rpre := by
  intro q hq hg
  have := List.all_eq_true.mp hc q hq
  simp [hg] at this

/-- Residual box form: on the whole subtree box, the region Prop holds except on the physical
images of leaves not covered by `good`. -/
theorem residual_of_leafFacts : ∀ (T : PTree) (rpre : List ℕ), LeafFacts P good T rpre →
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InUVT (uvtBox rpre.reverse) μ.a μ.b μ.meanEntropy →
      (∃ q ∈ T.leavesR rpre, good q.2 = false ∧ InUVT (uvtBox q.1) μ.a μ.b μ.meanEntropy) ∨
        P k μ
  | .leaf lab, rpre, h, k, μ, hin => by
      cases hg : good lab with
      | false => exact Or.inl ⟨(rpre.reverse, lab), by simp [PTree.leavesR], hg, hin⟩
      | true => exact Or.inr (h (rpre.reverse, lab) (by simp [PTree.leavesR]) hg k μ hin)
  | .node ax l r, rpre, h, k, μ, hin => by
      have hl : LeafFacts P good l (2 * ax :: rpre) := fun q hq hg =>
        h q (by simp only [PTree.leavesR, List.mem_append]; exact Or.inl hq) hg
      have hr : LeafFacts P good r ((2 * ax + 1) :: rpre) := fun q hq hg =>
        h q (by simp only [PTree.leavesR, List.mem_append]; exact Or.inr hq) hg
      rcases inUVT_step _ ax hin with h' | h'
      · rw [← uvtBox_append, ← List.reverse_cons] at h'
        rcases residual_of_leafFacts l _ hl k μ h' with ⟨q, hq, hq'⟩ | hp
        · exact Or.inl ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inl hq, hq'⟩
        · exact Or.inr hp
      · rw [← uvtBox_append, ← List.reverse_cons] at h'
        rcases residual_of_leafFacts r _ hr k μ h' with ⟨q, hq, hq'⟩ | hp
        · exact Or.inl ⟨q, by simp only [PTree.leavesR, List.mem_append]; exact Or.inr hq, hq'⟩
        · exact Or.inr hp

/-- Full box form: if every leaf of the subtree is covered by `good`, the region Prop holds on
the whole subtree box. -/
theorem regionOn_of_leafFacts (T : PTree) (rpre : List ℕ)
    (hall : (T.leavesR rpre).all (fun q => good q.2) = true) (h : LeafFacts P good T rpre) :
    RegionOn P (uvtBox rpre.reverse) := by
  intro k μ hin
  rcases residual_of_leafFacts T rpre h k μ hin with ⟨q, hq, hg, -⟩ | hp
  · have := List.all_eq_true.mp hall q hq
    rw [hg] at this
    exact absurd this (by decide)
  · exact hp

/-- Union of two leaf families (e.g. two method lanes) with a common conclusion. -/
theorem leafFacts_or {P₁ P₂ Q : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {g₁ g₂ : ℕ → Bool}
    {T : PTree} {rpre : List ℕ} (h₁ : LeafFacts P₁ g₁ T rpre) (h₂ : LeafFacts P₂ g₂ T rpre)
    (c₁ : ∀ k (μ : InteriorLaw (Fin k)), P₁ k μ → Q k μ)
    (c₂ : ∀ k (μ : InteriorLaw (Fin k)), P₂ k μ → Q k μ) :
    LeafFacts Q (fun l => g₁ l || g₂ l) T rpre := by
  intro q hq hg
  rcases Bool.or_eq_true_iff.mp hg with hg | hg
  · exact fun k μ hin => c₁ k μ (h₁ q hq hg k μ hin)
  · exact fun k μ hin => c₂ k μ (h₂ q hq hg k μ hin)

theorem leafFacts_mono {Q : ∀ k : ℕ, InteriorLaw (Fin k) → Prop} {T : PTree} {rpre : List ℕ}
    (h : LeafFacts P good T rpre) (c : ∀ k (μ : InteriorLaw (Fin k)), P k μ → Q k μ) :
    LeafFacts Q good T rpre :=
  fun q hq hg k μ hin => c k μ (h q hq hg k μ hin)

end Families

/-! ## List helpers for leaf-family modules -/

theorem forall_append {α : Type*} {Q : α → Prop} {L M : List α}
    (h₁ : ∀ x ∈ L, Q x) (h₂ : ∀ x ∈ M, Q x) : ∀ x ∈ L ++ M, Q x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

/-- Adapter for Lane D fleet shards (`sem : ∀ x ∈ leaves, SemUVT (uvtBox x.1)`). -/
theorem psiSem_of_shards {α : Type*} {M : List (List ℕ × α)}
    (h : ∀ x ∈ M, SemUVT (uvtBox x.1)) : ∀ p ∈ M.map Prod.fst, RegionOn PsiSem (uvtBox p) := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact h x hx

/-- Owner label predicate of Lane D's family (`0 = endpoint_plane_taylor`). -/
def goodEndpoint (l : ℕ) : Bool := l == 0

end CKLaneG3

end


