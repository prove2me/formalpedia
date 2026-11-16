-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Hard
-- name    : MTWalkSAT3CNF_TwoOcc_Supplement_Hard
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:56:28.352226+00:00
-- url     : https://prove2.me/theorems/13222fc1-0623-48f0-a122-8572d5f8cdcb
-- title:
--   The hard formulas and their occurrence completion
-- statement:
--   For an integer $L\ge40$, let $p_{j,i}$, $j\in\{1,2,3\}$, $1\le i\le L$, and $x_{j,i,k}$, $1\le i<L$, $0\le k\le4L+1$, be distinct Boolean variables. The indexed conjunction $F_L$ contains the root $(p_{1,1}\vee p_{2,1}\vee p_{3,1})$, and for every module $(j,i)$ it contains
--
--   $$(\neg p_{j,i}\vee x_{j,i,0}\vee p_{j,i+1}),\quad(\neg p_{j,i}\vee\neg x_{j,i,0}\vee x_{j,i,1}),$$
--   $$(x_{j,i,k}\vee\neg x_{j,i,k-1}\vee\neg x_{j,i,k-2})\quad(2\le k\le4L+1).$$
--
--   The completed formula $\widehat F_L$ uses the same variables and adds $(\neg u_a\vee\neg v_a\vee\neg v_{a+1})$ for the last two variables $u_a,v_a$ of each module in cyclic lexicographic order, and two separately indexed copies of $(\neg p_{1,L}\vee\neg p_{2,L}\vee\neg p_{3,L})$. The Boolean family selector chooses the original or completed formula. Counts, satisfiability and occurrence claims remain separate theorem obligations.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), §4.1, (7)–(11), pp. 17–18; §4.5, (29)–(30), p. 24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Runtime

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc.Supplement

/-- p has indices (branch,position); x has (branch,module,tail position). -/
abbrev HardVar (L : ℕ) := (Fin 3 × Fin L) ⊕ (Fin 3 × Fin (L-1) × Fin (4*L+2))
abbrev Module (L : ℕ) := Fin 3 × Fin (L-1)
abbrev HardIndex (L : ℕ) := Unit ⊕ (Module L × (Fin 2 ⊕ Fin (4*L)))
abbrev CompletedIndex (L : ℕ) := HardIndex L ⊕ (Module L ⊕ Fin 2)

def pvar {L : ℕ} (j : Fin 3) (i : Fin L) : HardVar L := .inl (j,i)
def xvar {L : ℕ} (j : Fin 3) (i : Fin (L-1)) (k : Fin (4*L+2)) : HardVar L :=
  .inr (j,i,k)

/-- Clauses (7)--(11), with the first two indices shifted from one-based to zero-based. -/
def hardClause (L : ℕ) (hL : 40 ≤ L) : HardIndex L → Clause (HardVar L)
  | .inl _ => triple
      (pvar 0 ⟨0, by omega⟩) (pvar 1 ⟨0, by omega⟩) (pvar 2 ⟨0, by omega⟩)
      true true true (by simp [pvar]) (by simp [pvar]) (by simp [pvar])
  | .inr ((j,i), .inl ab) =>
      if ab.val = 0 then
        triple (pvar j ⟨i.val, by omega⟩) (xvar j i 0)
          (pvar j ⟨i.val+1, by omega⟩) false true true
          (by simp [pvar,xvar]) (by simp [pvar]) (by simp [pvar,xvar])
      else
        triple (pvar j ⟨i.val, by omega⟩) (xvar j i 0) (xvar j i 1)
          false false true (by simp [pvar,xvar]) (by simp [pvar,xvar])
          (by simp [xvar])
  | .inr ((j,i), .inr k) =>
      triple (xvar j i ⟨k.val+2, by omega⟩) (xvar j i ⟨k.val+1, by omega⟩)
        (xvar j i ⟨k.val, by omega⟩) true false false
        (by simp [xvar]) (by simp [xvar]) (by simp [xvar])

/-- Lexicographic successor of modules, cyclically. -/
def nextModule (L : ℕ) (_hL : 40 ≤ L) (a : Module L) : Module L :=
  if hi : a.2.val+1 < L-1 then (a.1, ⟨a.2.val+1, hi⟩)
  else (⟨(a.1.val+1)%3, Nat.mod_lt _ (by omega)⟩, ⟨0, by omega⟩)

/-- Completion (29)--(30). The last summand Fin 2 contains two identical E clauses. -/
def completedClause (L : ℕ) (hL : 40 ≤ L) : CompletedIndex L → Clause (HardVar L)
  | .inl c => hardClause L hL c
  | .inr (.inl a) =>
      triple (xvar a.1 a.2 ⟨4*L, by omega⟩) (xvar a.1 a.2 ⟨4*L+1, by omega⟩)
        (xvar (nextModule L hL a).1 (nextModule L hL a).2 ⟨4*L+1, by omega⟩)
        false false false
        (by simp [xvar]) (by simp [xvar])
        (by
          intro heq
          have he : a.1 = (nextModule L hL a).1 ∧ a.2 = (nextModule L hL a).2 := by
            simpa [xvar] using heq
          unfold nextModule at he
          split_ifs at he with hi
          · have hi' := congrArg Fin.val he.2
            simp only at hi'
            omega
          · have hj := a.1.isLt
            have hj' := congrArg Fin.val he.1
            simp only at hj'
            omega)
  | .inr (.inr _) =>
      triple (pvar 0 ⟨L-1, by omega⟩) (pvar 1 ⟨L-1, by omega⟩)
        (pvar 2 ⟨L-1, by omega⟩) false false false
        (by simp [pvar]) (by simp [pvar]) (by simp [pvar])

noncomputable def hardFormula (L : ℕ) (hL : 40 ≤ L) := indexed (hardClause L hL)
noncomputable def completedFormula (L : ℕ) (hL : 40 ≤ L) := indexed (completedClause L hL)

/-- Select either family on their shared variable set; sizes are computed, not postulated. -/
abbrev FamilyIndex (L : ℕ) (completed : Bool) :=
  if completed then CompletedIndex L else HardIndex L

noncomputable instance (L : ℕ) (b : Bool) : Fintype (FamilyIndex L b) := by
  cases b <;> dsimp [FamilyIndex] <;> infer_instance

def familyClause (L : ℕ) (hL : 40 ≤ L) (b : Bool) : FamilyIndex L b → Clause (HardVar L) :=
  match b with
  | false => hardClause L hL
  | true => completedClause L hL

noncomputable def familyFormula (L : ℕ) (hL : 40 ≤ L) (b : Bool) :=
  indexed (familyClause L hL b)

end MTWalkSAT3CNF.TwoOcc.Supplement


