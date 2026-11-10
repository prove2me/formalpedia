-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_OutsideLaw
-- name    : SmoothedPlanted_FFK_OutsideLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:32:38.183052+00:00
-- url     : https://prove2.me/theorems/b2dc3996-1f3b-4dc5-98f1-d6e3fb8eae9c
-- title:
--   Definition 14(i) — independent outside-label law
-- statement:
--   For every unordered pair of outside variables, $D_{ij}$ is a probability mass function on symmetric relations. The outside law is their product measure. Define $\rho_{ij}[a,b]$ as the probability that the relation sampled at that pair forbids $(a,b)$. The domination predicate is $\rho_{ij}[a,b]\ge\Pi[a,b]$ for every pair and both alphabet symbols. There is no distribution on the planted labels or cut labels. The empty collection of outside pairs has the unique probability law on the singleton sample space.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Definition 14(i) — independent outside-label law, printed p. 16 (PDF p. 18), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_CSP

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

/-- Independent sampling on unordered pairs only. -/
def outsideLaw {V : Type} [Fintype V] [LinearOrder V] {q : ℕ}
    (D : Pair V → PMF (Relation q)) : Measure (CSP V q) :=
  Measure.pi (fun e => (D e).toMeasure)
def rho {q : ℕ} (D : PMF (Relation q)) (a b : Fin q) : ℝ :=
  (D.toOuterMeasure {r | r.val a b = false}).toReal
def Dominates {V : Type} [LinearOrder V] {q : ℕ}
    (D : Pair V → PMF (Relation q)) (Pi : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  ∀ e a b, Pi a b ≤ rho (D e) a b

end SmoothedPlanted.FFK


