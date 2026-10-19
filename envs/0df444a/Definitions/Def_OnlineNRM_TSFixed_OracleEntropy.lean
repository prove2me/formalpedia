-- Prove2me | Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
-- name    : OnlineNRM_TSFixed_OracleEntropy
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-17T14:45:22.233456+00:00
-- url     : https://prove2.me/theorems/d2d89f14-034a-48a5-9303-b5151b58f29d
-- title:
--   Entropy of a finite randomized oracle conditional on observations
-- statement:
--   For a finite probability vector w depending on an outcome, finitePosteriorEntropy is the expected Shannon entropy of its conditional mean given a sigma-algebra. oracleActionWeights completes a selector whose total mass is at most one by assigning the remaining mass to the shut-off action.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory

/-- Expected entropy of the conditional mean of a finite probability vector.
For simplex-valued w this is H(J | m), where J has conditional law w given
the underlying outcome. No additional random variable J is required. -/
noncomputable def finitePosteriorEntropy
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (P : Measure Ω) (m : MeasurableSpace Ω) (w : Ω → α → ℝ) : ℝ :=
  ∫ ω, ∑ a : α, Real.negMulLog ((P[fun ω' => w ω' a | m]) ω) ∂P

end ProbabilityTheory

namespace OnlineNRM.TSFixed

/-- Complete a subprobability selector by adding its unused mass at none. -/
def oracleActionWeights {Θ : Type*} {K : ℕ}
    (xsel : Θ → Fin K → ℝ) (ρ : Θ) : Option (Fin K) → ℝ
  | none => 1 - ∑ k : Fin K, xsel ρ k
  | some k => xsel ρ k

end OnlineNRM.TSFixed


