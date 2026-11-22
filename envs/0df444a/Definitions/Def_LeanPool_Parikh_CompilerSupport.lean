-- Prove2me | Definitions.Def_LeanPool_Parikh_CompilerSupport
-- name    : LeanPool_Parikh_CompilerSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:51:18.739819+00:00
-- url     : https://prove2.me/theorems/679f1e67-1902-4efb-b9c2-ad97ac6ce86c
-- title:
--   Compiler Support
-- statement:
--   Definitions and structural lemmas for Compiler Support, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerSupport.lean

module
public import Definitions.Def_LeanPool_Parikh_ActivationAlgorithm
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Theorems.Thm_Parikh_ParseTree_height_child_lt

set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
namespace ParseTree
variable {T N : Type*} [DecidableEq T] [DecidableEq N]
@[expose] def equalAt (H : ℕ) : ParseTree T N → ParseTree T N → Bool :=
  Nat.rec
    (fun t u => match t, u with
      | .terminal a, .terminal b => decide (a = b)
      | .hole A, .hole B => decide (A = B)
      | _, _ => false)
    (fun _ next t u => match t, u with
      | .terminal a, .terminal b => decide (a = b)
      | .hole A, .hole B => decide (A = B)
      | .node r cs, .node s ds => decide (r = s) && cs.isEqv ds next
      | _, _ => false) H
theorem equalAt_correct (H : ℕ) (t u : ParseTree T N)
    (ht : t.height ≤ H) (hu : u.height ≤ H) : equalAt H t u = true ↔ t = u := by
  induction H generalizing t u with
  | zero =>
    cases t <;> cases u <;> simp [equalAt]
    all_goals rw [height.eq_3] at ht; omega
  | succ H ih =>
    have hlist : ∀ cs ds : List (ParseTree T N),
        (∀ c ∈ cs, c.height ≤ H) → (∀ d ∈ ds, d.height ≤ H) →
        (cs.isEqv ds (equalAt H) = true ↔ cs = ds) := by
      intro cs ds hc hd
      induction cs generalizing ds with
      | nil => cases ds <;> simp [List.isEqv]
      | cons c cs hcs =>
        cases ds with
        | nil => simp [List.isEqv]
        | cons d ds =>
          simp only [List.isEqv, Bool.and_eq_true]
          rw [ih c d (hc c (by simp)) (hd d (by simp)),
            hcs ds (fun x hx => hc x (by simp [hx]))
              (fun x hx => hd x (by simp [hx]))]
          simp only [List.cons.injEq]
    cases t with
    | terminal a => cases u <;> simp [equalAt]
    | hole A => cases u <;> simp [equalAt]
    | node r cs =>
      cases u with
      | terminal a => simp [equalAt]
      | hole A => simp [equalAt]
      | node s ds =>
        have hc : ∀ c ∈ cs, c.height ≤ H := fun c hc => by
          have := height_child_lt r cs c hc
          omega
        have hd : ∀ d ∈ ds, d.height ≤ H := fun d hd => by
          have := height_child_lt s ds d hd
          omega
        change (decide (r = s) && cs.isEqv ds (equalAt H)) = true ↔ _
        simp only [Bool.and_eq_true, decide_eq_true_eq, hlist cs ds hc hd, node.injEq]
@[expose] def decEq : DecidableEq (ParseTree T N) := fun t u =>
  decidable_of_iff (equalAt (t.height + u.height) t u = true)
    (equalAt_correct _ t u (by omega) (by omega))
end ParseTree
@[expose] def listComponent {T N : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : List (ParseTree T N)) : Component T :=
  ⟨B.weight + (D.map ParseTree.weight).sum, D.map ParseTree.weight⟩
namespace ParseTree
@[expose] def rootLabel {T N : Type*} (default : N) (t : ParseTree T N) : N :=
  match t.root with
  | .terminal _ => default
  | .nonterminal A => A
end ParseTree
@[expose] def contextActivation {T : Type*} (g : ContextFreeGrammar T)
    [DecidableEq g.NT] [DecidableEq (ParseTree T g.NT)]
    (B : ParseTree T g.NT) (D : List (ParseTree T g.NT)) : Bool :=
  (activationTest g.NT (ParseTree T g.NT)).run (ParseTree.rootLabel g.initial)
    (fun C => C.productionLabels.toFinset) B.productionLabels.toFinset D.toFinset
end Parikh


