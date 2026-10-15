-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Variance
-- name    : OAI_Probability_RandomSAT_Variance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:35:35.401028+00:00
-- url     : https://prove2.me/theorems/d6c0dc71-7cf3-4eca-9fda-dd01f9b2ec91
-- title:
--   Satisfiable lifetimes, insertion delays, killing chances and occupation sums of the clause process
-- statement:
--   Let $S$ be a set of assignments on $n$ variables and let $F=(C_1,\dots,C_m)$ be a formula of $m$ proper $k$-clauses. Write $S_t=S\wedge(C_1,\dots,C_t)$ for the set of members of $S$ that satisfy the first $t$ clauses, with $S_0=S$. The module records that adding clauses to the empty set leaves it empty and that the empty set is not alive, so its survival probability is $0$. It then defines the following.
--
--   1. **Lifetime.**
--   $$
--   L_m(S,F)=\sum_{t=1}^{m}\operatorname{alive}(S_t),
--   $$
--   defined recursively by $L_0=0$ and $L_{m+1}(S,(C,F'))=\operatorname{alive}(S\wedge C)+L_m(S\wedge C,F')$. It counts the $t\in\{1,\dots,m\}$ for which $S_t$ is nonempty. Since the sets $S_t$ decrease, this is the length of the longest prefix of $F$ that keeps $S$ alive. Also $L_m(\emptyset,F)=0$.
--   2. **Lifetime mean and variance.** $\mathbb{E}_F[L_m(S,F)]$ and $\operatorname{Var}_F[L_m(S,F)]$ for $F$ uniformly random.
--   3. **Killing chance.** $\chi_k(S)=\operatorname{alive}(S)-\operatorname{surv}_k(1,S)$. When $S$ is nonempty and $k\le n$, this is the probability that one uniform proper $k$-clause kills $S$. It is $0$ for $S=\emptyset$.
--   4. **Insertion delay.** For an additional clause $C$,
--   $$
--   \delta_m(S,C,F)=\big(\operatorname{alive}(S)+L_m(S,F)\big)-\big(\operatorname{alive}(S\wedge C)+L_m(S\wedge C,F)\big),
--   $$
--   the loss of lifetime, counting time $0$, caused by inserting $C$ in front of $F$. Its second moment $\mathbb{E}_C\,\mathbb{E}_F[\delta_m(S,C,F)^2]$ is taken over independent uniform $C$ and $F$.
--   5. **Truncated killing.** $\min\big(M\chi_k(S),1\big)$ for $M\in\mathbb{N}$.
--   6. **Occupation sum.** For a real function $f$ on sets of assignments, $\operatorname{Occ}_0f=0$ and $\operatorname{Occ}_{m+1}f(S)=f(S)+A_k(\operatorname{Occ}_mf)(S)$, where $A_k$ is the clause average. Thus $\operatorname{Occ}_mf=\sum_{t=0}^{m-1}A_k^tf$ is the expected value of $f(S_0)+\dots+f(S_{m-1})$ along the random clause process.
--   7. **Forced fraction.** $|\operatorname{Forced}(S)|/n$.
--
--   When $S$ is the set of all assignments, $L_m$ counts how many of the first $m$ random clauses can be added before the formula becomes unsatisfiable. The concentration argument bounds its variance by a coordinate-omission bound in terms of the squared insertion delays, and those are controlled through killing chances and forced fractions accumulated along the clause process.
--
--   **Formalization Note** The forced fraction uses real division by $n$, so it is $0$ when $n=0$. If $n<k$ there are no proper $k$-clauses, the uniform mean over them is $0$ by convention, and then $\chi_k(S)=\operatorname{alive}(S)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Variance.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Variance.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_RandomSAT_Forcing

namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem addClause_empty {n k : ℕ} (C : ProperClause n k) :
    addClause ∅ C = ∅ := by simp [addClause]

@[simp] theorem alive_empty {n : ℕ} : alive (∅ : Finset (Assignment n)) = 0 := by simp [alive]

@[simp] theorem survival_empty {n k m : ℕ} : survival k m (∅ : Finset (Assignment n)) = 0 := by
  rw [survival_eq_mean]
  have h (F : Formula n k m) : restrictSolutions ∅ F = ∅ := by simp [restrictSolutions]
  simp only [h, alive_empty, uniformMean_zero]

def lifetime {n : ℕ} (k : ℕ) : (m : ℕ) → Finset (Assignment n) → Formula n k m → ℝ
  | 0, _, _ => 0
  | m + 1, S, F => alive (addClause S (F 0)) +
      lifetime k m (addClause S (F 0)) (Fin.tail F)

@[simp] theorem lifetime_zero {n k : ℕ} (S : Finset (Assignment n)) (F : Formula n k 0) :
    lifetime k 0 S F = 0 := rfl

@[simp] theorem lifetime_cons {n k m : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k)
    (F : Formula n k m) : lifetime k (m + 1) S (Fin.cons C F) =
      alive (addClause S C) + lifetime k m (addClause S C) F := rfl

@[simp] theorem lifetime_empty {n k m : ℕ} (F : Formula n k m) : lifetime k m ∅ F = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [lifetime, ih]

def lifetimeMean {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformMean (lifetime k m S)

def lifetimeVariance {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformVariance (lifetime k m S)

def killingChance {n : ℕ} (k : ℕ) (S : Finset (Assignment n)) : ℝ :=
  alive S - survival k 1 S

def insertionDelay {n : ℕ} (k m : ℕ) (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) : ℝ :=
  (alive S + lifetime k m S F) - (alive (addClause S C) + lifetime k m (addClause S C) F)

def insertionSecond {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformMean (fun C : ProperClause n k => uniformMean (fun F : Formula n k m =>
    insertionDelay k m S C F ^ 2))

def truncatedKilling {n : ℕ} (k M : ℕ) (S : Finset (Assignment n)) : ℝ :=
  min ((M : ℝ) * killingChance k S) 1

def occupation {n : ℕ} (k : ℕ) (f : Finset (Assignment n) → ℝ) :
    ℕ → Finset (Assignment n) → ℝ
  | 0, _ => 0
  | m + 1, S => f S + clauseAverage k (occupation k f m) S

def forcedFraction {n : ℕ} (S : Finset (Assignment n)) : ℝ :=
  ((forcedVariables S).card : ℝ) / n

end

end FixedClauseThreshold

end OAI


