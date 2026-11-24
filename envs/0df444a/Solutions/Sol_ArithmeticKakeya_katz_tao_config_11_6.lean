-- Prove2me | solution 1 for ArithmeticKakeya.katz_tao_config_11_6
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:41:32.772162+00:00
-- url     : https://prove2.me/submissions/cc3ae8ac-898b-4756-b3c9-f85d6ac65a4f

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing

set_option autoImplicit false
set_option maxRecDepth 100000

open ArithmeticKakeya

private def labC : (i : Fin [2, 3].length) → List ℕ → ℤ × ℤ := fun i e =>
  if i.val = 0 ∧ e = [1] then (1, 0)
  else if i.val = 1 ∧ e = [1, 1] then (0, 1)
  else if i.val = 1 ∧ e = [1, 2] then (0, 1)
  else if i.val = 1 ∧ e = [2, 1] then (0, 1)
  else if i.val = 1 ∧ e = [2, 2] then (1, 1)
  else (0, 0)

private def GC : ConstructibleGraph ({(1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)) where
  dims := [2, 3]
  f := labC
  f_support := by
    intro i e h
    unfold labC at *
    fin_cases i <;> split_ifs at h ⊢ <;> simp_all <;> decide

private def sg (g : List ℕ) (x : ℤ × ℤ) : List ℕ → ℤ × ℤ := fun e => if e = g then x else (0, 0)

private def RC : List (List ℕ → ℤ × ℤ) := [sg [1, 2] (1, 0), sg [1, 1] (1, 1), sg [1, 3] (1, 1), sg [2, 3] (0, 1)]

private lemma forcesC : Forces GC RC [] := by
  refine Forces.edge ⟨0, by decide⟩ [1] [1] (by decide) (by decide) ?_
  refine Forces.edge ⟨0, by decide⟩ [1] [2] (by decide) (by decide) ?_
  refine Forces.edge ⟨0, by decide⟩ [1] [3] (by decide) (by decide) ?_
  refine Forces.edge ⟨1, by decide⟩ [1, 1] [] (by decide) (by decide) ?_
  refine Forces.edge ⟨1, by decide⟩ [1, 2] [] (by decide) (by decide) ?_
  refine Forces.edge ⟨1, by decide⟩ [2, 1] [] (by decide) (by decide) ?_
  refine Forces.edge ⟨1, by decide⟩ [2, 2] [] (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [2, 1] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [1, 1] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [1, 2] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [1, 3] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [2, 2] (by decide) (-1) (by decide) (by decide) (by decide) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.head _) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))) ?_
  refine Forces.diff _ _ (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ?_
  refine Forces.vertex _ (List.Mem.head _) [2, 3] (by decide) (-1) (by decide) (by decide) (by decide) ?_
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

private lemma RC_nodup : RC.Nodup := by
  simp only [RC, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true]
  repeat' apply And.intro
  all_goals exact sg_ne (by decide) (by decide)

private lemma RC_single : ∀ f ∈ RC, ∃ (x : ℤ × ℤ) (g : List ℕ),
    x ∈ ({(1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)) ∧ x ≠ (0, 0) ∧ g ∈ grid GC.dims ∧
    f = fun e => if e = g then x else (0, 0) := by
  intro f hf
  simp only [RC, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨(1, 0), [1, 2], by decide, by decide, by decide, rfl⟩
  · exact ⟨(1, 1), [1, 1], by decide, by decide, by decide, rfl⟩
  · exact ⟨(1, 1), [1, 3], by decide, by decide, by decide, rfl⟩
  · exact ⟨(0, 1), [2, 3], by decide, by decide, by decide, rfl⟩

theorem solution :
    ∃ (G : ConstructibleGraph ({(1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)))
      (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)),
      IsXSet G R T ∧ Forces G R T ∧ T.length < n G ∧
      6 * (m G + R.length) ≤ 11 * (n G - T.length) := by
  exact ⟨GC, RC, [], ⟨RC_nodup, List.nodup_nil, RC_single, by simp⟩, forcesC, by decide, by decide⟩
