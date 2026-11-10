-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_Oracle
-- name    : SFLOracleLowerBound_Hardness_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:26:38.74291+00:00
-- url     : https://prove2.me/theorems/09aef2ba-eb14-4e55-b393-d8fa7b5f387f
-- title:
--   Classical adaptive randomized exact-value oracle strategies
-- statement:
--   An oracle action either queries a subset of clients or returns an assignment. A strategy receives a private random seed and the complete ordered transcript of earlier queried sets and exact real answers. The run appends one transcript entry per query, and permits output immediately after the last allowed answer. Internal computation is unrestricted. An algorithm may use any probability space of seeds; every observable output event is measurable.
--
--   For a query budget $Q$ and factor $\alpha$, its success probability is
--   $$
--   \Pr\left[\sigma\text{ is returned after at most }Q\text{ queries},\ \sigma\text{ feasible},\ \operatorname{cost}(\sigma)\le\alpha\mathrm{OPT}\right].
--   $$
--   A public-data-dependent algorithm family selects one such strategy for every positive client and facility size and every public distance matrix. The hidden function is not an argument to this selection. A polynomial query bound is one natural-coefficient polynomial in $|\mathcal C|+|\mathcal F|$, on every run and every valid matroid-rank SFL input. Every usual polynomial bound is dominated by one of this form. Size query bounds restrict the same requirement to a fixed client count and at most that many facilities, as used in Proposition 26.
--
--   This interface allows adaptive queries, arbitrary stopping before the budget, outputs not previously queried, arbitrary real answers and arbitrary-support randomness. Feasibility is part of success, including for the general allocation theorem with infinite connection costs.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Definition 1, p.2; Theorem 10, pp.9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Allocation

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Definition 1, p.2. An action has no hidden-oracle argument. -/
inductive OracleAction (C F : Type) where
  | query (S : Finset C)
  | output (σ : C → F)

abbrev Transcript (C : Type) := List (Finset C × ℝ)
abbrev Strategy (Ω C F : Type) := Ω → Transcript C → OracleAction C F

/-- Fuel counts oracle calls, not computation steps; output is checked even at fuel zero. -/
def runOracle {Ω C F : Type} (step : Strategy Ω C F) (ω : Ω) (g : Finset C → ℝ) :
    ℕ → Transcript C → Option (C → F)
  | q, h => match step ω h with
    | .output σ => some σ
    | .query S => match q with
      | 0 => none
      | k+1 => runOracle step ω g k (h ++ [(S, g S)])

/-- An arbitrary probability space of private seeds, with measurable observable runs.
No countability or finite-support assumption is made. Exact answers are real numbers. -/
structure RandomAlgorithm (C F : Type) where
  Seed : Type
  measurableSeed : MeasurableSpace Seed
  law : @Measure Seed measurableSeed
  probability : @IsProbabilityMeasure Seed measurableSeed law
  step : Strategy Seed C F
  observable : ∀ (g : Finset C → ℝ) (q : ℕ) (σ : C → F),
    @MeasurableSet Seed measurableSeed {ω | runOracle step ω g q [] = some σ}

def WithinBudget {C F : Type} (A : RandomAlgorithm C F) (g : Finset C → ℝ) (Q : ℕ) : Prop :=
  ∀ ω, ∃ σ, runOracle A.step ω g Q [] = some σ

/-- Feasibility prevents ∞ ≤ α∞ from counting an invalid output as successful. -/
def successProbability {C F : Type} [Fintype C] [Fintype F] [DecidableEq F]
    (A : RandomAlgorithm C F) (D : PublicData C F) (g : Finset C → ℝ)
    (Q : ℕ) (α : ℝ) : ℝ :=
  (A.law {ω | ∃ σ, runOracle A.step ω g Q [] = some σ ∧ Feasible D σ ∧
      allocationCost D g σ ≤ ENNReal.ofReal α * optimum D g}).toReal

/-- Uniform public-data-dependent algorithms: the oracle is not an argument of A. -/
abbrev AlgorithmFamily := (n m : ℕ) → PublicData (Fin n) (Fin m) → RandomAlgorithm (Fin n) (Fin m)

def PolynomialQueryBound (A : AlgorithmFamily) (Q : Polynomial ℕ) : Prop :=
  ∀ (n m : ℕ), 0 < n → 0 < m → ∀ (D : PublicData (Fin n) (Fin m)) (g : Finset (Fin n) → ℝ),
    IsSFL D → FacilityCost g → MatroidRank g → WithinBudget (A n m D) g (Q.eval (n+m))

def SizeQueryBound (A : AlgorithmFamily) (N Q : ℕ) : Prop :=
  ∀ (m : ℕ), 0 < m → m ≤ N → ∀ (D : PublicData (Fin N) (Fin m)) (g : Finset (Fin N) → ℝ),
    IsSFL D → FacilityCost g → MatroidRank g → WithinBudget (A N m D) g Q

end SFLOracleLowerBound.Hardness


