-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Forcing
-- name    : OAI_Probability_RandomSAT_Forcing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:34:16.516123+00:00
-- url     : https://prove2.me/theorems/5a992686-aebe-46dc-80b3-5cf5f50d354e
-- title:
--   Deleting and erasing a variable from random clauses, variable renaming, and mean forced fractions
-- statement:
--   Here formulas live on $v+1$ variables and are split clause by clause according to whether they contain variable $0$, using the bijection of the clause-process module. A *split clause* is either a proper $k$-clause $C$ on the remaining $v$ variables (the clause omits variable $0$) or a pair $(Q,t)$ consisting of a proper $(k-1)$-clause $Q$ on the remaining $v$ variables and a sign $t$ for variable $0$. Assignments $\sigma$ below are assignments of those $v$ variables.
--
--   1. **Deleted and erased satisfaction.** $\sigma$ *deletion-satisfies* a split clause if either the clause is some $C$ and $\sigma$ satisfies $C$, or the clause has the form $(Q,t)$: clauses through variable $0$ are deleted and count as satisfied. $\sigma$ *erasure-satisfies* a split clause if either it is some $C$ and $\sigma$ satisfies $C$, or it is $(Q,t)$ and $\sigma$ satisfies $Q$: the literal on variable $0$ is erased.
--   2. **Deleted and erased survival.** Let $k\ge1$, let $S$ be a set of assignments on $v$ variables, and let $F$ be a uniformly random formula of $m$ proper $k$-clauses on $v+1$ variables. Then
--   $$
--   D_m(S)=\mathbb{E}_F\Big[\operatorname{alive}\big(\{\sigma\in S:\sigma\text{ deletion-satisfies every split clause of }F\}\big)\Big],
--   $$
--   and $E_m(S)$ is the same average with erasure-satisfaction. Both equal $\operatorname{alive}(S)$ when $m=0$.
--   3. **Head forcing.** $h(v,k,m)$ is the probability, over a uniformly random formula $F$ of $m$ proper $k$-clauses on $v+1$ variables, that variable $0$ is forced in the solution set of $F$. That is, $F$ is satisfiable and all of its satisfying assignments agree at variable $0$.
--   4. **Renaming.** A permutation $\pi$ of the variables acts on clauses by $(\pi\cdot C)(i)=C(\pi(i))$, on assignments by $\sigma\mapsto\sigma\circ\pi$, and on formulas clause by clause. The actions on clauses and on formulas are bijections.
--   5. **Mean forced fraction.** With $F$ uniform among formulas of $m$ proper $k$-clauses on $n$ variables and $\operatorname{Sol}(F)$ its set of satisfying assignments,
--   $$
--   \phi(n,k,m)=\mathbb{E}_F\Big[\frac{|\operatorname{Forced}(\operatorname{Sol}(F))|}{n}\Big],
--   $$
--   the expected fraction of variables that are forced.
--
--   Deleting the clauses through variable $0$ can only help satisfiability, while erasing variable $0$ from them can only hurt it. So for $S$ the set of all assignments, $E_m$ and $D_m$ bound the satisfiability probability on $v+1$ variables from below and from above. The gap between them is tied to the event that variable $0$ is forced. By renaming symmetry every variable is forced with the same probability, which links $h$ to the mean forced fraction $\phi$.
--
--   **Formalization Note** A split clause is an element of the sum type `ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)`, and `deletedMean` and `erasedMean` take a proof of `0 < k`. The division by $n$ in $\phi$ is real division, so $\phi(0,k,m)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Forcing.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Forcing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev SplitClause (v k : ℕ) := ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)

def DeletedSatisfied {v k : ℕ} (σ : Assignment v) : SplitClause v k → Prop
  | .inl C => SatisfiesClause σ C
  | .inr _ => True

def ErasedSatisfied {v k : ℕ} (σ : Assignment v) : SplitClause v k → Prop
  | .inl C => SatisfiesClause σ C
  | .inr Q => SatisfiesClause σ Q.1

def deletedSolutions {v k m : ℕ} (S : Finset (Assignment v)) (F : Fin m → SplitClause v k) :
    Finset (Assignment v) := S.filter (fun σ => ∀ i, DeletedSatisfied σ (F i))

def erasedSolutions {v k m : ℕ} (S : Finset (Assignment v)) (F : Fin m → SplitClause v k) :
    Finset (Assignment v) := S.filter (fun σ => ∀ i, ErasedSatisfied σ (F i))

@[simp] theorem mem_deletedSolutions {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) (σ : Assignment v) :
    σ ∈ deletedSolutions S F ↔ σ ∈ S ∧ ∀ i, DeletedSatisfied σ (F i) := by
  simp [deletedSolutions]

@[simp] theorem mem_erasedSolutions {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) (σ : Assignment v) :
    σ ∈ erasedSolutions S F ↔ σ ∈ S ∧ ∀ i, ErasedSatisfied σ (F i) := by
  simp [erasedSolutions]

def deletedMean {v k : ℕ} (hk : 0 < k) (m : ℕ) (S : Finset (Assignment v)) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    alive (deletedSolutions S (fun i => clauseHeadSplit hk (F i))))

def erasedMean {v k : ℕ} (hk : 0 < k) (m : ℕ) (S : Finset (Assignment v)) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    alive (erasedSolutions S (fun i => clauseHeadSplit hk (F i))))

@[simp] theorem deletedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    deletedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      deletedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [deletedMean, h, uniformMean_const]

@[simp] theorem erasedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    erasedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      erasedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [erasedMean, h, uniformMean_const]

def headForcedMean (v k m : ℕ) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    if (0 : Fin (v + 1)) ∈ forcedVariables (restrictSolutions Finset.univ F)
      then (1 : ℝ) else 0)

def renameClause {n k : ℕ} (e : Fin n ≃ Fin n) (C : ProperClause n k) : ProperClause n k :=
  ⟨fun i => C.val (e i), by
    have h := Fintype.card_congr
      (e.subtypeEquivOfSubtype (p := fun i => (C.val i).isSome))
    simp only [Fintype.card_subtype] at h
    exact h.trans C.property⟩

def renameClauseEquiv {n k : ℕ} (e : Fin n ≃ Fin n) : ProperClause n k ≃ ProperClause n k where
  toFun := renameClause e
  invFun := renameClause e.symm
  left_inv C := by apply Subtype.ext; funext i; simp [renameClause]
  right_inv C := by apply Subtype.ext; funext i; simp [renameClause]

def renameAssignment {n : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n) : Assignment n :=
  fun i => σ (e i)

def renameFormula {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) : Formula n k m :=
  fun i => renameClause e (F i)

def renameFormulaEquiv {n k m : ℕ} (e : Fin n ≃ Fin n) : Formula n k m ≃ Formula n k m :=
  Equiv.piCongrRight (fun _ => renameClauseEquiv e)

def forcedFractionMean (n k m : ℕ) : ℝ :=
  uniformMean (fun F : Formula n k m =>
    ((forcedVariables (restrictSolutions Finset.univ F)).card : ℝ) / n)

end

end FixedClauseThreshold

end OAI


