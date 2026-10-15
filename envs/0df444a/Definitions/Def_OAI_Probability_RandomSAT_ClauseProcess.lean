-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
-- name    : OAI_Probability_RandomSAT_ClauseProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:32:22.955633+00:00
-- url     : https://prove2.me/theorems/c6b26e44-3698-4ca9-a342-1fb576444210
-- title:
--   The clause-adding process: splitting clauses at the first variable, clause averages and survival probabilities
-- statement:
--   Assignments, proper $k$-clauses, satisfaction and uniform means $\mathbb{E}$ are as in the previous modules. This module sets up the random process that adds independent uniform proper clauses, one at a time, to a set of candidate solutions.
--
--   1. **Splitting off the first variable.** Let $k\ge1$. A proper $k$-clause on $v+1$ variables either omits variable $0$, in which case it is a proper $k$-clause on the remaining $v$ variables, or contains variable $0$ with some sign $t$, in which case the rest is a proper $(k-1)$-clause on the remaining $v$ variables. This gives a bijection
--   $$
--   \mathcal{C}_{v+1,k}\;\cong\;\mathcal{C}_{v,k}\;\sqcup\;\big(\mathcal{C}_{v,k-1}\times\{\mathrm{T},\mathrm{F}\}\big),
--   $$
--   where $\mathcal{C}_{v,k}$ denotes the set of proper $k$-clauses on $v$ variables. Write an assignment on $v+1$ variables as $(b,\sigma)$, with $b$ the value of variable $0$. Then $(b,\sigma)$ satisfies the clause obtained from $C$ by adding variable $0$ as absent if and only if $\sigma$ satisfies $C$. It satisfies the clause obtained from $Q$ by adding variable $0$ with sign $t$ if and only if $t=b$ or $\sigma$ satisfies $Q$.
--   2. **Restricting solution sets.** For a set $S$ of assignments and a clause $C$, $S\wedge C=\{\sigma\in S:\sigma\text{ satisfies }C\}$. For a finite family $F=(F_i)_{i\in I}$ of clauses, $S\wedge F=\{\sigma\in S:\sigma\text{ satisfies every }F_i\}$. With no clauses $S\wedge F=S$, and $S\wedge(C,F_1,\dots,F_m)=(S\wedge C)\wedge(F_1,\dots,F_m)$.
--   3. **Alive indicator and clause average.** $\operatorname{alive}(S)=1$ if $S\neq\emptyset$ and $0$ otherwise. For a real function $f$ on sets of assignments on $n$ variables, the clause average is
--   $$
--   (A_kf)(S)=\mathbb{E}_C\big[f(S\wedge C)\big],
--   $$
--   with $C$ uniform among the proper $k$-clauses on $n$ variables.
--   4. **Survival probability.** $\operatorname{surv}_k(m,S)=(A_k^m\operatorname{alive})(S)$. Thus $\operatorname{surv}_k(0,S)=\operatorname{alive}(S)$ and $\operatorname{surv}_k(m+1,S)=\mathbb{E}_C[\operatorname{surv}_k(m,S\wedge C)]$. Unrolling the iteration gives
--   $$
--   \operatorname{surv}_k(m,S)=\mathbb{E}_F\big[\operatorname{alive}(S\wedge F)\big],
--   $$
--   the probability that some member of $S$ satisfies all $m$ clauses of a uniformly random formula $F$ of $m$ proper $k$-clauses. The supporting identity is that a mean over $(m+1)$-tuples equals the iterated mean over the first entry and the remaining $m$-tuple.
--
--   When $S$ is the set of all $2^n$ assignments, $\operatorname{surv}_k(m,S)$ is the probability that a random formula with $m$ proper $k$-clauses is satisfiable. The operator form $A_k^m$ lets later arguments analyse satisfiability one clause at a time, and the head-variable bijection is the tool for comparing formulas on $n$ and on $n-1$ variables.
--
--   **Formalization Note** The bijection is `clauseHeadEquiv` (built from `clauseHeadSplit`, `prependAbsent` and `prependPresent`) and takes a proof of `0 < k`. `addClause` and `restrictSolutions` are filters of a `Finset`, and `survival` is the iterate `(clauseAverage k)^[m] alive`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/ClauseProcess.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/ClauseProcess.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem support_card_cons {v : ℕ} (b : Option Bool) (C : Fin v → Option Bool) :
    (Finset.univ.filter fun i : Fin (v + 1) => (Fin.cons (α := fun _ => Option Bool) b C i).isSome).card =
      (if b.isSome then 1 else 0) + (Finset.univ.filter fun i => (C i).isSome).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp

def prependAbsent {v k : ℕ} (C : ProperClause v k) : ProperClause (v + 1) k :=
  ⟨Fin.cons none C.val, by simpa [support_card_cons] using C.property⟩

def prependPresent {v k : ℕ} (hk : 0 < k) (C : ProperClause v (k - 1)) (b : Bool) :
    ProperClause (v + 1) k :=
  ⟨Fin.cons (some b) C.val, by
    rw [support_card_cons]
    simp only [Option.isSome_some, ↓reduceIte, C.property]
    omega⟩

def clauseHeadSplit {v k : ℕ} (hk : 0 < k) (C : ProperClause (v + 1) k) :
    ProperClause v k ⊕ (ProperClause v (k - 1) × Bool) :=
  match hb : C.val 0 with
  | none => Sum.inl ⟨Fin.tail C.val, by
      have h := C.property
      conv_lhs at h => rw [← Fin.cons_self_tail C.val]
      rw [support_card_cons, hb] at h
      simpa using h⟩
  | some b => Sum.inr (⟨Fin.tail C.val, by
      have h := C.property
      conv_lhs at h => rw [← Fin.cons_self_tail C.val]
      rw [support_card_cons, hb] at h
      simp at h
      omega⟩, b)

def clauseHeadEquiv {v k : ℕ} (hk : 0 < k) :
    ProperClause (v + 1) k ≃ ProperClause v k ⊕ (ProperClause v (k - 1) × Bool) where
  toFun := clauseHeadSplit hk
  invFun := Sum.elim prependAbsent (fun p => prependPresent hk p.1 p.2)
  left_inv C := by
    apply Subtype.ext
    simp only [clauseHeadSplit]
    split <;> simp only [Sum.elim_inl, Sum.elim_inr, prependAbsent, prependPresent]
    all_goals simpa only [*] using Fin.cons_self_tail C.val
  right_inv C := by
    cases C with
    | inl C => rfl
    | inr C =>
      rcases C with ⟨C, b⟩
      rfl

@[simp] theorem satisfiesClause_prependAbsent {v k : ℕ}
    (σ : Assignment v) (b : Bool) (C : ProperClause v k) :
    SatisfiesClause (Fin.cons b σ) (prependAbsent C) ↔ SatisfiesClause σ C := by
  simp [SatisfiesClause, prependAbsent, Fin.exists_fin_succ]

@[simp] theorem satisfiesClause_prependPresent {v k : ℕ} (hk : 0 < k)
    (σ : Assignment v) (b t : Bool) (C : ProperClause v (k - 1)) :
    SatisfiesClause (Fin.cons b σ) (prependPresent hk C t) ↔ t = b ∨ SatisfiesClause σ C := by
  simp [SatisfiesClause, prependPresent, Fin.exists_fin_succ]

def addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    Finset (Assignment n) := S.filter (fun σ => SatisfiesClause σ C)

@[simp] theorem mem_addClause {n k : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (σ : Assignment n) :
    σ ∈ addClause S C ↔ σ ∈ S ∧ SatisfiesClause σ C := by
  simp [addClause]

def restrictSolutions {n k : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) : Finset (Assignment n) :=
  S.filter (fun σ => ∀ i, SatisfiesClause σ (F i))

@[simp] theorem mem_restrictSolutions {n k : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) (σ : Assignment n) :
    σ ∈ restrictSolutions S F ↔ σ ∈ S ∧ ∀ i, SatisfiesClause σ (F i) := by
  simp [restrictSolutions]

theorem restrictSolutions_zero {n k : ℕ} (S : Finset (Assignment n))
    (F : Formula n k 0) : restrictSolutions S F = S := by
  ext σ
  simp only [mem_restrictSolutions, Fin.forall_fin_zero, and_true]

theorem restrictSolutions_cons {n k m : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) :
    restrictSolutions S (Fin.cons C F) = restrictSolutions (addClause S C) F := by
  ext σ
  simp only [mem_restrictSolutions, mem_addClause, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]
  tauto

theorem uniformMean_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun F : Fin m → α =>
      f (Fin.cons a F))) := by
  calc
    _ = uniformMean (fun p : α × (Fin m → α) => f (Fin.cons p.1 p.2)) :=
      (uniformMean_equiv (Fin.consEquiv (fun _ => α)) f).symm
    _ = _ := uniformMean_prod _

def alive {n : ℕ} (S : Finset (Assignment n)) : ℝ := if S.Nonempty then 1 else 0

def clauseAverage {n : ℕ} (k : ℕ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) : ℝ :=
  uniformMean (fun C : ProperClause n k => f (addClause S C))

def survival {n : ℕ} (k : ℕ) (m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((clauseAverage k)^[m] alive) S

@[simp] theorem survival_zero {n k : ℕ} (S : Finset (Assignment n)) :
    survival k 0 S = alive S := rfl

theorem survival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k (m + 1) S = uniformMean (fun C : ProperClause n k =>
      survival k m (addClause S C)) := by
  rw [survival, Function.iterate_succ_apply']
  rfl

theorem survival_eq_mean {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformMean (fun F : Formula n k m => alive (restrictSolutions S F)) := by
  induction m generalizing S with
  | zero =>
    simp only [survival_zero, restrictSolutions_zero]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [survival_succ, uniformMean_fin_succ]
    apply uniformMean_congr
    intro C
    rw [ih]
    apply uniformMean_congr
    intro F
    rw [restrictSolutions_cons]

end

end FixedClauseThreshold

end OAI


