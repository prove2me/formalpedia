-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Rounding
-- name    : SmoothedPlanted_FFK_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:30.702735+00:00
-- url     : https://prove2.me/theorems/abd5b897-0798-4736-9746-8c5f20d02fed
-- title:
--   Threshold rounding and the two recovery inequalities
-- statement:
--   Given a lifted Gram matrix, round by selecting exactly the variables with $g(i)\ge1/2$, retaining ties. Recovery of a planted set $S$ of size $k$ with tolerance $\eta$ means both $|\widehat S\cap S|\ge(1-\eta)k$ and $|\widehat S|\le(1+\eta)k$. This predicate specifies the required property; it does not assume an algorithm has it.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Threshold rounding and the two recovery inequalities, printed p. 24 (PDF p. 26), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Theta

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

def roundedSet {V : Type} [Fintype V] [DecidableEq V] {q : ℕ}
    (M : Gram (V × Fin q)) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => 1 / 2 ≤ variableMass M i)
def Recovery {V : Type} [DecidableEq V] (S T : Finset V) (k : ℕ) (η : ℝ) : Prop :=
  (1 - η) * k ≤ ((T ∩ S).card : ℝ) ∧ (T.card : ℝ) ≤ (1 + η) * k

end SmoothedPlanted.FFK


