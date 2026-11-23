-- Prove2me | Definitions.Def_WeightedMajority_Shifting_Supplement_EffectiveBudgets
-- name    : WeightedMajority_Shifting_Supplement_EffectiveBudgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:55:08.543368+00:00
-- url     : https://prove2.me/theorems/449208e3-6eac-406e-abcd-19473e4c7bc4
-- title:
--   Effective online mistake budgets and the four predicates of Theorem 7.3
-- statement:
--   Let $M_i$ be nonnegative integers and $w_i=2^{-M_i}$ for $i=0,1,\ldots$, where $i$ represents the paper's member $i+1$. An online learner sees the complete list of preceding instance/label pairs and the current instance. It has budget $B$ for a target $f$ when, for every finite sequence consistent with $f$, its number of mistakes is at most $B$:
--
--   $$\forall T,\ \forall S=((x_j,y_j))_{j<T},\quad (\forall j,\ y_j=f(x_j))\ \Longrightarrow\ M_A(S)\le B.$$
--
--   The four predicates are: (a) $\sum_iw_i$ converges and is a computable real; (b) one real constant $c$ works for every effectively presented domain and every uniformly recursive binary pool, with an effective learner having budget $M_i+c$ for every $i$; (c) each such domain/pool has its own constant, inclusive cutoff and effective learner with the same eventual budgets; (d) the series converges.
--
--   These predicates retain the quantifier order of Theorem 7.3. Domains carry arbitrary Mathlib primitive-codable presentations; the pool's uncurried evaluator and the learner's uncurried history/current-instance function satisfy Mathlib `Computable`. The published computable-real predicate supplies recursive rational approximations of error at most $2^{-r}$. Summability is asserted separately, so a divergent series cannot use a default sum. The cutoff is zero-based like the member index.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, pp. 247–248, Theorem 7.3(a)–(d); pp. 224–225, computable indexing

import Definitions.Def_UnderstandingML_Online
import Definitions.Def_DetParamSVP_ComputableReal

namespace WeightedMajority.Shifting.Supplement

/-- Dyadic initial weight. Index `i : ℕ` means the paper's positive index `i+1`. -/
noncomputable def budgetWeight (M : ℕ → ℕ) (i : ℕ) : ℝ := 1 / (2 : ℝ) ^ M i

/-- A real mistake budget for one target, over all finite sequences and every horizon.
The learner is the published history/current-instance online algorithm. -/
def HasBudget {X : Type*} (A : UnderstandingML.OnlineAlg X Bool) (f : X → Bool)
    (B : ℝ) : Prop :=
  ∀ (T : ℕ) (S : Fin T → X × Bool), (∀ t, (S t).2 = f (S t).1) →
    (UnderstandingML.mistakes A S : ℝ) ≤ B

/-- Theorem 7.3(a): convergence and arbitrary-precision computability of the sum.
The computable real predicate is reused, including its recursive rational approximation. -/
def BudgetA (M : ℕ → ℕ) : Prop :=
  Summable (budgetWeight M) ∧ DetParamSVP.IsComputableReal (∑' i, budgetWeight M i)

/-- Theorem 7.3(b). The constant precedes every domain, encoding and recursive pool.
`Primcodable X` is an effective presentation; all such presentations are quantified over.
Computability of the uncurried evaluator is uniform in the member index. -/
def BudgetB (M : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, ∀ (X : Type) (_ : Primcodable X) (φ : ℕ → X → Bool),
    Computable (Function.uncurry φ) →
    ∃ A : UnderstandingML.OnlineAlg X Bool, Computable (Function.uncurry A) ∧
      ∀ i, HasBudget A (φ i) ((M i : ℝ) + c)

/-- Theorem 7.3(c). Here the constant, cutoff and effective learner follow the pool.
The cutoff `j : ℕ` denotes the positive paper index `j+1`; `j ≤ i` is inclusive. -/
def BudgetC (M : ℕ → ℕ) : Prop :=
  ∀ (X : Type) (_ : Primcodable X) (φ : ℕ → X → Bool),
    Computable (Function.uncurry φ) →
    ∃ (c : ℝ) (j : ℕ) (A : UnderstandingML.OnlineAlg X Bool),
      Computable (Function.uncurry A) ∧ ∀ i, j ≤ i → HasBudget A (φ i) ((M i : ℝ) + c)

/-- Theorem 7.3(d): convergence, without asserting an effective sum. -/
def BudgetD (M : ℕ → ℕ) : Prop := Summable (budgetWeight M)

end WeightedMajority.Shifting.Supplement


