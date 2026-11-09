-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
-- name    : RandomCNFDeficiency_LowerBound_DeficiencyClosure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:29.794405+00:00
-- url     : https://prove2.me/theorems/db89d22c-6288-4a31-bc3b-31172375c506
-- title:
--   Signed deficiency and the computed clause closure
-- statement:
--   For a variable set $T$ and clause set $A$, define signed matching deficiency by
--
--   $$h_T(A)=|A|-|N(A)\setminus T|.$$
--
--   Given a finite CNF $F$ and a real threshold $s$, admissible sets are all $A\subseteq F$ with $|A|\le2s$. A maximizer has the largest deficiency among all these admissible sets. Define $\operatorname{cl}(T)$ to be the union of all admissible maximizers; being a maximizer itself, being largest and having size less than $s$ are not assumed.
--
--   The deterministic criterion means $s\ge1$, $2\le D\le n$, every clause has width at most $D$, every subformula with fewer than $s$ clauses is satisfiable, and every $A\subseteq F$ with $s\le|A|\le2s$ has $|N(A)|>D+|A|$. Real thresholds generalize the integer instances and preserve the unrounded parameters of Equation (21). This is the common model shared by all closure milestones.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem 3.1, Section 3.1 and Equation (14), printed p. 9, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Clause
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

/-- Signed matching deficiency, Equation (14). -/
noncomputable def deficiency {n : ℕ} (T : Finset (Fin n)) (A : CNF n) : ℤ :=
  (A.card : ℤ) - ((neighborhood A \ T).card : ℤ)

def Admissible {n : ℕ} (F : CNF n) (s : ℝ) (A : CNF n) : Prop :=
  A ⊆ F ∧ (A.card : ℝ) ≤ 2 * s

def MaximizesDeficiency {n : ℕ} (F : CNF n) (s : ℝ)
    (T : Finset (Fin n)) (A : CNF n) : Prop :=
  Admissible F s A ∧ ∀ B, Admissible F s B → deficiency T B ≤ deficiency T A

/-- Union of ALL admissible maximizers; no closure property is assumed. -/
noncomputable def closure {n : ℕ} (F : CNF n) (s : ℝ)
    (T : Finset (Fin n)) : CNF n := by
  classical
  exact (F.powerset.filter fun A => MaximizesDeficiency F s T A).biUnion id

def LocalSatisfiability {n : ℕ} (F : CNF n) (s : ℝ) : Prop :=
  ∀ A ⊆ F, (A.card : ℝ) < s → Satisfiable A

def MediumExpansion {n : ℕ} (F : CNF n) (s D : ℝ) : Prop :=
  ∀ A ⊆ F, s ≤ (A.card : ℝ) → (A.card : ℝ) ≤ 2 * s →
    D + (A.card : ℝ) < ((neighborhood A).card : ℝ)

/-- The complete standing assumptions of Theorem 3.1, with real thresholds. -/
def Criterion {n : ℕ} (F : CNF n) (s D : ℝ) : Prop :=
  1 ≤ s ∧ 2 ≤ D ∧ D ≤ (n : ℝ) ∧
    (∀ C ∈ F, (clauseWidth C : ℝ) ≤ D) ∧
    LocalSatisfiability F s ∧ MediumExpansion F s D

end RandomCNFDeficiency.LowerBound


