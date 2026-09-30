-- Prove2me | Definitions.Def_CK_CKLaneG3_PSort
-- name    : CK_CKLaneG3_PSort
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:11:19.736073+00:00
-- url     : https://prove2.me/theorems/04cea6f2-5787-458d-a507-90f73ca0d979
-- title:
--   Courtade–Kumar proof module `CKLaneG3.PSort` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneG3.PSort` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneG3.PSort` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneG3.PSort (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneG3/PSort.lean)

import Definitions.Def_CK_CKLaneG3_Consume

-- ===== source module CKLaneG3.PSort =====
section

/-!
# Lane G3: kernel-friendly lexicographic merge sort of path lists (membership-preserving)

Lane-supplied certified path lists are not always in DFS (= lexicographic path) order, which the
linear consumer `tconsume` needs.  `psort fuel L` is a structurally recursive merge sort (fuel = number
of halving levels; any fuel is sound): `mem_psort : p ∈ psort fuel L ↔ p ∈ L`.  If the fuel is too
small the result is merely less sorted and the consumer check fails — never unsound.
-/

namespace CKLaneG3

/-- Lexicographic `≤` on paths (= left-first DFS order of the halving tree). -/
def plex : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && plex as bs)

/-- Alternating split. -/
def psplit : List (List ℕ) → List (List ℕ) × List (List ℕ)
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t => ((x :: (psplit t).1), (y :: (psplit t).2))

/-- Merge with fuel (fuel exhaustion just concatenates). -/
def pmerge : ℕ → List (List ℕ) → List (List ℕ) → List (List ℕ)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
      if plex x y then x :: pmerge n xs (y :: ys) else y :: pmerge n (x :: xs) ys

/-- Merge sort with `fuel` halving levels. -/
def psort : ℕ → List (List ℕ) → List (List ℕ)
  | 0, l => l
  | n + 1, l =>
      match l with
      | [] => []
      | [x] => [x]
      | _ :: _ :: _ =>
          pmerge (l.length + 1) (psort n (psplit l).1) (psort n (psplit l).2)

theorem mem_psplit : ∀ (l : List (List ℕ)) (p : List ℕ), p ∈ l ↔ p ∈ (psplit l).1 ∨ p ∈ (psplit l).2
  | [], p => by simp [psplit]
  | [x], p => by simp [psplit]
  | x :: y :: t, p => by
      have ih := mem_psplit t p
      simp only [psplit, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · rcases ih.mp h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
      · rintro ((h | h) | (h | h))
        · exact Or.inl h
        · exact Or.inr (Or.inr (ih.mpr (Or.inl h)))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (ih.mpr (Or.inr h)))

theorem mem_pmerge : ∀ (n : ℕ) (xs ys : List (List ℕ)) (p : List ℕ),
    p ∈ pmerge n xs ys ↔ p ∈ xs ∨ p ∈ ys
  | 0, xs, ys, p => by simp [pmerge]
  | _ + 1, [], ys, p => by simp [pmerge]
  | _ + 1, x :: xs, [], p => by simp [pmerge]
  | n + 1, x :: xs, y :: ys, p => by
      unfold pmerge
      split_ifs
      · have ih := mem_pmerge n xs (y :: ys) p
        simp only [List.mem_cons] at ih ⊢
        constructor
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · rcases ih.mp h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (ih.mpr (Or.inl h))
          · exact Or.inr (ih.mpr (Or.inr h))
      · have ih := mem_pmerge n (x :: xs) ys p
        simp only [List.mem_cons] at ih ⊢
        constructor
        · rintro (h | h)
          · exact Or.inr (Or.inl h)
          · rcases ih.mp h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
        · rintro (h | (h | h))
          · exact Or.inr (ih.mpr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (ih.mpr (Or.inr h))

theorem mem_psort : ∀ (n : ℕ) (l : List (List ℕ)) (p : List ℕ), p ∈ psort n l ↔ p ∈ l
  | 0, l, p => by simp [psort]
  | n + 1, [], p => by simp [psort]
  | n + 1, [x], p => by simp [psort]
  | n + 1, x :: y :: t, p => by
      simp only [psort]
      rw [mem_pmerge, mem_psort n, mem_psort n]
      exact (mem_psplit (x :: y :: t) p).symm

/-- Per-label binding of an arbitrarily ordered certified path list (sorted in the kernel). -/
theorem label_family_of_psort {Q : List ℕ → Prop} (T : CKLaneD.PTree) (n fuel : ℕ)
    (L : List (List ℕ)) (hL : ∀ p ∈ L, Q p)
    (hc : (tconsume (fun l => l == n) T [] (psort fuel L)).isSome = true) :
    ∀ q ∈ T.leaves, q.2 = n → Q q.1 :=
  label_family_of_consume T n (psort fuel L) (fun p hp => hL p ((mem_psort fuel L p).mp hp)) hc

end CKLaneG3

end


