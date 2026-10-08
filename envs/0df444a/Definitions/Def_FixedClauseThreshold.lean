-- Prove2me | Definitions.Def_FixedClauseThreshold
-- name    : FixedClauseThreshold
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.632143+00:00
-- url     : https://prove2.me/theorems/01934c20-a82b-4743-8081-6a047e57bae2
-- statement:
--   A proper clause on n Boolean variables with clause size k is a partial assignment that fixes exactly k distinct variables, each with a sign (some true or some false), and a formula with m clauses is an ordered m-tuple of proper clauses, so independent uniform clause draws with replacement correspond to the uniform measure on all formulas. An assignment σ satisfies a clause if some variable i in the clause has its prescribed sign equal to σ(i), satisfies a formula if it satisfies every clause, and a formula is satisfiable if some assignment satisfies it. properSATProbability(n,k,m) is the exact ratio of the number of satisfiable formulas to the number of all formulas, as real numbers, so it equals 1 when m=0 and equals 0 when m>0 but n<k because the formula set is empty and division by zero is zero. HasLimitingThreshold(k) is a defined proposition, not a proved theorem: there exists a real α>0 such that for every real c with 0≤c<α the probability properSATProbability(n,k,⌊cn⌋) tends to 1 as n tends to infinity, and for every real c>α it tends to 0. It makes no claim at c=α, gives no value for α, and is stated for a single fixed k rather than for varying clause sizes; the surrounding comment indicates the intended use for fixed k≥3, but the definition itself places no restriction on k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FixedClauseThreshold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FixedClauseThreshold.lean; bytes 16..1991
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
Proper clauses choose distinct variables uniformly and give them independent fair
signs. Formulas consist of independent uniform whole-clause draws with replacement.
Their satisfiability probability is the literal finite cardinality ratio.
For zero clauses this probability is one, including when there are fewer variables
than literals per clause. When there are fewer variables than literals per clause
and the clause count is positive, the ensemble is empty and its probability is zero
by the convention that division by zero is zero.

For each fixed clause size at least three, one positive finite real threshold
governs the limits at every fixed density below or above it. There is no assertion
at the critical density, no explicit threshold value, and no varying-size claim.
-/

namespace FixedClauseThreshold

abbrev Assignment (n : ℕ) := Fin n → Bool

abbrev ProperClause (n k : ℕ) :=
  { C : Fin n → Option Bool // (Finset.univ.filter fun i => (C i).isSome).card = k }

abbrev Formula (n k m : ℕ) := Fin m → ProperClause n k

def SatisfiesClause {n k : ℕ} (σ : Assignment n) (C : ProperClause n k) : Prop :=
  ∃ i : Fin n, C.val i = some (σ i)

def Satisfies {n k m : ℕ} (σ : Assignment n) (F : Formula n k m) : Prop :=
  ∀ j, SatisfiesClause σ (F j)

def Satisfiable {n k m : ℕ} (F : Formula n k m) : Prop :=
  ∃ σ : Assignment n, Satisfies σ F

noncomputable def properSATProbability (n k m : ℕ) : ℝ := by
  classical
  exact (Fintype.card { F : Formula n k m // Satisfiable F } : ℝ) /
    (Fintype.card (Formula n k m) : ℝ)

def HasLimitingThreshold (k : ℕ) : Prop :=
  ∃ α : ℝ, 0 < α ∧
    (∀ c : ℝ, 0 ≤ c → c < α →
      Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
        Filter.atTop (nhds 1)) ∧
    (∀ c : ℝ, α < c →
      Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
        Filter.atTop (nhds 0))



end FixedClauseThreshold
end OAI


