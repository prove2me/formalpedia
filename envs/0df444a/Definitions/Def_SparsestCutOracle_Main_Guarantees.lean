-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Guarantees
-- name    : SparsestCutOracle_Main_Guarantees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:42.284436+00:00
-- url     : https://prove2.me/theorems/92805b55-123a-45b6-83de-387885854e74
-- title:
--   Uniform balanced-oracle guarantees and expected work
-- statement:
--   A balanced oracle has constants $c_1,c_2,c_\beta,C_q>0$ fixed before all instances and failure exponents. For each exponent $a$, one admissible program and one logarithmic exponent $c$ work for all inputs; for each polynomial weight exponent $d$, a time constant $C_d$ is fixed before the input. Set $\beta(n)=c_\beta/(\log n)^5$.
--
--   The two probabilistic conditions are
--
--   $$\operatorname{cap}(S,V\setminus S)\le C_q\phi\sqrt{\log n/\kappa}\,\pi(S),\qquad
--   \pi(S)<\beta(n)\Pi\Rightarrow G[V\setminus S]\text{ is }\pi\text{-expanding with quality }\phi.$$
--
--   Every halted run must satisfy $\pi(S)\le\pi(V\setminus S)$. Almost-sure halting and an integrable expected-work bound are additional mandatory clauses. The positive-only flag changes only the weight domain, providing Claim 5's premise without changing any other guarantee.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 4, Theorem 1; pp. 39–42; paper.md R2–R7

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Machine
import Definitions.Def_SparsestCutOracle_Main_Graph

namespace SparsestCutOracle.Main

noncomputable def instanceState {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (ϕ κ : ℝ) : State :=
  init (graphInts G) (graphReals G π [ϕ, κ])

def GoodCut {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (ϕ κ cβ Cq : ℝ)
    (S : Finset (Fin n)) : Prop :=
  cut G.toWGraph S Sᶜ ≤ Cq * ϕ * Real.sqrt (Real.log n / κ) * mass π S ∧
  (mass π S < (cβ / Real.log n ^ 5) * totalWeight π →
    ExpandingOn G.toWGraph π Sᶜ ϕ)

/-- Every halted run satisfies the smaller-side condition, independently of success. -/
def BalancedRuns {n : ℕ} (P : Program) (s : State) (π : Fin n → ℝ) : Prop :=
  ∀ (ω : Tape) (t : ℕ), (run P s ω t).base.halted = true →
    let S := outputCut n (run P s ω t)
    mass π S ≤ mass π Sᶜ

/-- Integrability is explicit, so a nonintegrable Bochner integral cannot give a free zero bound. -/
def ExpectedWork (P : Program) (s : State) (bound : ℝ) : Prop :=
  (∀ᵐ ω ∂tapeLaw, Halts P s ω) ∧
  MeasureTheory.Integrable (work P s) tapeLaw ∧
  (∫ ω, work P s ω ∂tapeLaw) ≤ bound

def HighProbability (n a : ℕ) (P : Program) (s : State) (Q : State → Prop) : Prop :=
  ∃ E : Set Tape, MeasurableSet E ∧
    ENNReal.ofReal (1 - (n : ℝ) ^ (-(a : ℤ))) ≤ tapeLaw E ∧
    ∀ ω ∈ E, Halts P s ω ∧ Q (final P s ω)

/-- The complete claim, uniformly over graph, real κ, threshold and polynomial weight exponent.
The Bool argument is used only for Claim 5's positive-weight premise. -/
def BalancedOracle (positiveOnly : Bool) : Prop :=
  ∃ c₁ c₂ cβ Cq : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < cβ ∧ 0 < Cq ∧
    ∀ a : ℕ, ∃ P : Program, Admissible P ∧ ∃ c : ℕ,
      ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (G : Graph n) (π : Fin n → ℝ) (ϕ κ : ℝ),
          2 ≤ n → G.NoLoops → G.Connected → G.UnitLowerBound →
          NormalizedWeights π → (positiveOnly = true → ∀ v, 0 < π v) →
          totalWeight π ≤ (n : ℝ) ^ d → 0 < ϕ →
          c₁ / Real.log n ≤ κ → κ ≤ c₂ →
          let s := instanceState G π ϕ κ
          BalancedRuns P s π ∧
          ExpectedWork P s
            (C * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) *
              (1 + Real.log G.total) * Real.log n ^ c) ∧
          HighProbability n a P s
            (fun out => GoodCut G π ϕ κ cβ Cq (outputCut n out))

end SparsestCutOracle.Main


