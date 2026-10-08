-- Prove2me | Definitions.Def_SATComputability
-- name    : SATComputability
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:41.062647+00:00
-- url     : https://prove2.me/theorems/97c39983-9723-465e-9741-13b67ce19324
-- statement:
--   An assignment on n variables is a function from Fin n to Bool, and a proper clause of width k is a function C assigning each of the n variables an optional sign (some true, some false, or none) such that exactly k variables receive a sign. An assignment σ satisfies a clause if there is a variable i with C(i)=some(σ(i)), that is, at least one signed literal agrees with σ; it satisfies a formula, an indexed list of m proper clauses (repetitions allowed), if it satisfies every clause, and a formula is satisfiable if some assignment satisfies it. properSATProbability(n,k,m) is the real number equal to the number of satisfiable formulas divided by the total number of formulas, so it is the probability that a uniformly random formula of m width-k clauses on n variables is satisfiable. MainStatement is a defined proposition, not an established theorem. It asserts that there exist a real α>0, a rational-valued sequence q, and a partial recursive code c such that: for every real a with 0≤a<α, properSATProbability(n,3,⌊a·n⌋) tends to 1 as n tends to infinity; for every real a>α, it tends to 0; the map r↦encode(q r) is computable; for every r, c evaluates on input r to exactly the encoding of q r; and |q r − α| ≤ 2^(−r) for all r. So it states that a sharp 3-SAT satisfiability threshold α exists in the clause-density sense and is a computable real number, approximable to within 2^(−r) by a computable rational sequence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SATComputability.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SATComputability.lean; bytes 16..1485
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

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
end FixedClauseThreshold

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology NNReal

def MainStatement : Prop :=
    ∃ (α : ℝ) (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      0 < α ∧
      (∀ a : ℝ, 0 ≤ a → a < α →
        Tendsto (fun n : ℕ => properSATProbability n 3 ⌊a*(n : ℝ)⌋₊) atTop (nhds 1)) ∧
      (∀ a : ℝ, α < a →
        Tendsto (fun n : ℕ => properSATProbability n 3 ⌊a*(n : ℝ)⌋₊) atTop (nhds 0)) ∧
      Computable (fun r => Encodable.encode (q r)) ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ)-α| ≤ (2^r : ℝ)⁻¹)



end FixedClauseThreshold.Computability
end OAI


