-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Newsvendor
-- name    : MomentAmbiguitySecretary_Secretary_Supplement_Newsvendor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:13.519777+00:00
-- url     : https://prove2.me/theorems/859c2954-8fa0-40f1-a735-a13743d6721d
-- title:
--   Finite-mean demand, newsvendor profit and randomized order laws
-- statement:
--   Expected normalized newsvendor profit is the expectation of the published general realized profit with retail price 1, cost $1-\beta$ and zero salvage. The module defines actual optimal profit, the full optimizer set, open and closed CDFs, and arbitrary finite-first-moment order lotteries. Demand in the generic lemmas needs only a finite first moment.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Definitions, PDF/printed pp.5,9–11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Laws
import Definitions.Def_BlockchainNV_profit

open MeasureTheory Set
open scoped NNReal

namespace MomentAmbiguitySecretary.Secretary.Supplement
noncomputable section

def FiniteMean (ψ : Measure ℝ≥0) : Prop := Integrable (fun x : ℝ≥0 => (x : ℝ)) ψ

/-- General newsvendor profit at retail price 1, cost 1-β and zero salvage; p.5. -/
def profit (ψ : Measure ℝ≥0) (β q : ℝ) : ℝ :=
  ∫ d : ℝ≥0, BlockchainNV.profit 1 (1 - β) 0 q (d : ℝ) ∂ψ

def optimalProfit (ψ : Measure ℝ≥0) (β : ℝ) : ℝ :=
  sSup (Set.range fun q : ℝ≥0 => profit ψ β q)

def optimalOrders (ψ : Measure ℝ≥0) (β : ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ ∀ t : ℝ, 0 ≤ t → profit ψ β t ≤ profit ψ β q}

abbrev OrderLaw := {lottery : Distribution // FiniteMean (lottery : Measure ℝ≥0)}

def randomizedProfit (ψ : Measure ℝ≥0) (β : ℝ) (lottery : OrderLaw) : ℝ :=
  ∫ q : ℝ≥0, profit ψ β q ∂(lottery.val : Measure ℝ≥0)

def meanOrder (lottery : OrderLaw) : ℝ := ∫ q : ℝ≥0, (q : ℝ) ∂(lottery.val : Measure ℝ≥0)

def closedCDF (ψ : Measure ℝ≥0) (q : ℝ) : ℝ := (ψ {x | (x : ℝ) ≤ q}).toReal
def openCDF (ψ : Measure ℝ≥0) (q : ℝ) : ℝ := (ψ {x | (x : ℝ) < q}).toReal

end
end MomentAmbiguitySecretary.Secretary.Supplement


