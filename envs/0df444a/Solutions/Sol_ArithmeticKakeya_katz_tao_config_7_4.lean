-- Prove2me | solution 1 for ArithmeticKakeya.katz_tao_config_7_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:41:29.493844+00:00
-- url     : https://prove2.me/submissions/4ad80a9e-e6cc-4d42-98e8-272acb491536

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing

set_option autoImplicit false
set_option maxRecDepth 100000

open ArithmeticKakeya

private def lab74 : (i : Fin [2, 2].length) → List ℕ → ℤ × ℤ := fun i e =>
  if i.val = 0 ∧ e = [1] then (1, 0)
  else if i.val = 1 ∧ e = [1, 1] then (0, 1)
  else if i.val = 1 ∧ e = [2, 1] then (1, 2)
  else (0, 0)

private def G74 : ConstructibleGraph ({(1, 0), (0, 1), (1, 2), (1, 1)} : Finset (ℤ × ℤ)) where
  dims := [2, 2]
  f := lab74
  f_support := by
    intro i e h
    unfold lab74 at *
    fin_cases i <;> split_ifs at h ⊢ with h1 h2 h3 <;>
      simp_all <;> decide

private def sg (g : List ℕ) (x : ℤ × ℤ) : List ℕ → ℤ × ℤ := fun e => if e = g then x else (0, 0)

private def R74 : List (List ℕ → ℤ × ℤ) := [sg [1, 2] (1, 1), sg [2, 1] (1, 1), sg [2, 2] (0, 1)]

private lemma forces74 : Forces G74 R74 [] := by
  refine Forces.edge ⟨0, by decide⟩ [1] [1] (by decide) (by decide) ?_
  refine Forces.edge ⟨0, by decide⟩ [1] [2] (by decide) (by decide) ?_
  refine Forces.edge ⟨1, by decide⟩ [1, 1] [] (by decide) (by decide) ?_
  refine Forces.edge ⟨1, by decide⟩ [2, 1] [] (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [1, 1] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [1, 2] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [2, 1] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [2, 2] (by decide) (-2) (by decide) (by decide) (by decide) ?_
  exact Forces.done (by decide)

private lemma sg_ne {g g' : List ℕ} {x x' : ℤ × ℤ} (hx : x ≠ (0, 0)) (h : g ≠ g' ∨ x ≠ x') :
    sg g x ≠ sg g' x' := by
  intro hh
  have := congrFun hh g
  simp only [sg, if_true] at this
  by_cases hg : g = g'
  · subst hg
    simp only [if_true] at this
    rcases h with h | h
    · exact h rfl
    · exact h this
  · rw [if_neg hg] at this
    exact hx this

theorem solution :
    ∃ (G : ConstructibleGraph ({(1, 0), (0, 1), (1, 2), (1, 1)} : Finset (ℤ × ℤ)))
      (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)),
      IsXSet G R T ∧ Forces G R T ∧ T.length < n G ∧
      4 * (m G + R.length) ≤ 7 * (n G - T.length) := by
  refine ⟨G74, R74, [], ⟨?_, List.nodup_nil, ?_, by simp⟩, forces74, by decide, by decide⟩
  · simp only [R74, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨sg_ne (by decide) (Or.inl (by decide)), sg_ne (by decide) (Or.inl (by decide))⟩,
      sg_ne (by decide) (Or.inl (by decide)), by simp⟩
  · intro f hf
    simp only [R74, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨(1, 1), [1, 2], by decide, by decide, by decide, rfl⟩
    · exact ⟨(1, 1), [2, 1], by decide, by decide, by decide, rfl⟩
    · exact ⟨(0, 1), [2, 2], by decide, by decide, by decide, rfl⟩
