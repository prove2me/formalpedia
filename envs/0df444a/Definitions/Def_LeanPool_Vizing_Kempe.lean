-- Prove2me | Definitions.Def_LeanPool_Vizing_Kempe
-- name    : LeanPool_Vizing_Kempe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:49:26.875712+00:00
-- url     : https://prove2.me/theorems/ce1c8137-7f94-46c8-a9ff-12308cbf0e4a
-- title:
--   Kempe
-- statement:
--   Definitions and structural lemmas for Kempe, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Kempe.lean

module
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Theorems.Thm_LeanPool_Vizing_PEC_Extends_trans
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right


set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace LeanPool.Vizing
namespace PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
def kempeGraph (c : PEC G C) (a b : C) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (c.col u v = some a ∨ c.col u v = some b)
  symm.symm := by
    rintro u v ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    rwa [c.col_symm v u]
  loopless := ⟨fun v h => h.1 rfl⟩
omit [Fintype V] [DecidableEq V] [DecidableEq C] in
lemma kempeGraph_adj_of_col {c : PEC G C} {a b : C} {u v : V}
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Adj u v := by
  refine ⟨?_, h⟩
  rcases h with h | h <;> exact (c.col_adj h).ne
omit [Fintype V] [DecidableEq V] [DecidableEq C] in
/-- Reachability in the Kempe graph propagates along edges coloured `a` or `b`. -/
lemma reachable_of_col {c : PEC G C} {a b : C} {x u v : V}
    (hu : (c.kempeGraph a b).Reachable x u)
    (h : c.col u v = some a ∨ c.col u v = some b) : (c.kempeGraph a b).Reachable x v :=
  hu.trans (kempeGraph_adj_of_col h).reachable
open Classical in
/-- The colour function after swapping `a` and `b` on the Kempe component of `x`. -/
noncomputable def kempeSwapFun (c : PEC G C) (a b : C) (x : V) : V → V → Option C :=
  fun u v => if (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    then (c.col u v).map (Equiv.swap a b) else c.col u v
omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_of_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = (c.col u v).map (Equiv.swap a b) := by
  classical
  unfold kempeSwapFun
  by_cases hv : (c.kempeGraph a b).Reachable x v
  · rw [if_pos ⟨hu, hv⟩]
  · rw [if_neg (by tauto)]
    cases h : c.col u v with
    | none => simp
    | some γ =>
      have hγa : γ ≠ a := by
        rintro rfl
        exact hv (reachable_of_col hu (Or.inl h))
      have hγb : γ ≠ b := by
        rintro rfl
        exact hv (reachable_of_col hu (Or.inr h))
      simp [Equiv.swap_apply_of_ne_of_ne hγa hγb]
omit [Fintype V] [DecidableEq V] in
lemma kempeSwapFun_of_not_reachable (c : PEC G C) (a b : C) {x u : V}
    (hu : ¬ (c.kempeGraph a b).Reachable x u) (v : V) :
    c.kempeSwapFun a b x u v = c.col u v := by
  classical
  unfold kempeSwapFun
  rw [if_neg (by tauto)]
noncomputable def kempeSwap (c : PEC G C) (a b : C) (x : V) : PEC G C where
  col := c.kempeSwapFun a b x
  col_symm := by
    classical
    intro u v
    unfold kempeSwapFun
    by_cases h : (c.kempeGraph a b).Reachable x u ∧ (c.kempeGraph a b).Reachable x v
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, c.col_symm u v]
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩), c.col_symm u v]
  col_adj := by
    intro u v γ h
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · rw [kempeSwapFun_of_reachable c a b hu v] at h
      cases hc : c.col u v with
      | none => rw [hc] at h; simp at h
      | some δ => exact c.col_adj hc
    · rw [kempeSwapFun_of_not_reachable c a b hu v] at h
      exact c.col_adj h
  col_proper := by
    intro u v w γ h1 h2
    by_cases hu : (c.kempeGraph a b).Reachable x u
    · rw [kempeSwapFun_of_reachable c a b hu v] at h1
      rw [kempeSwapFun_of_reachable c a b hu w] at h2
      cases hcv : c.col u v with
      | none => rw [hcv] at h1; simp at h1
      | some δ =>
        cases hcw : c.col u w with
        | none => rw [hcw] at h2; simp at h2
        | some ε =>
          rw [hcv] at h1
          rw [hcw] at h2
          simp only [Option.map_some] at h1 h2
          have : δ = ε := (Equiv.swap a b).injective (by
            rw [Option.some_injective _ h1, Option.some_injective _ h2])
          exact c.col_proper hcv (this ▸ hcw)
    · rw [kempeSwapFun_of_not_reachable c a b hu v] at h1
      rw [kempeSwapFun_of_not_reachable c a b hu w] at h2
      exact c.col_proper h1 h2
end PEC
end LeanPool.Vizing


