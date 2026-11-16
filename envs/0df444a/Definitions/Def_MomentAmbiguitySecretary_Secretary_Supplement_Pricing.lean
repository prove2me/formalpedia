-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Pricing
-- name    : MomentAmbiguitySecretary_Secretary_Supplement_Pricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:48:35.998487+00:00
-- url     : https://prove2.me/theorems/47e8f559-ff0f-4994-91d8-7886a22e4464
-- title:
--   Posted-price revenue, unrestricted lotteries and localization intervals
-- statement:
--   Revenue is $v\Pr(X\ge v)$ and its optimum is the supremum over every $v>0$. Price lotteries are all Borel probability laws on the positive reals without a moment restriction. The residue localization interval is open on the left and closed on the right; its constant is the signed-exponent series from Section 5.2.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Definitions, PDF/printed pp.5,12–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators

namespace MomentAmbiguitySecretary.Secretary.Supplement
noncomputable section

abbrev PositivePrice := {v : ℝ // 0 < v}
abbrev PriceLaw := ProbabilityMeasure PositivePrice

/-- Closed buyer acceptance X ≥ v, p.5. -/
def revenue (ψ : Measure ℝ≥0) (v : ℝ) : ℝ := v * (ψ {x | v ≤ (x : ℝ)}).toReal

def optimalRevenue (ψ : Measure ℝ≥0) : ℝ :=
  sSup (Set.range fun v : PositivePrice => revenue ψ v.val)

/-- No moment condition is imposed on the price lottery. -/
def randomizedRevenue (ψ : Measure ℝ≥0) (lottery : PriceLaw) : ℝ :=
  ∫ v : PositivePrice, revenue ψ v.val ∂(lottery : Measure PositivePrice)

def localizationIndex (N h : ℕ) : ℕ := if h = N - 1 then h else N + h

def localizationInterval (B N h : ℕ) : Set ℝ :=
  Ioc ((B : ℝ) ^ (localizationIndex N h - 1)) ((B : ℝ) ^ localizationIndex N h)

def localizationTerm (N j : ℕ) : ℝ :=
  if N - 1 ≤ j ∧ j ≤ 2 * N - 2 then 0 else
    (2 : ℝ) ^ (2 * (j : ℤ) - (exponent N j : ℤ) - ((N : ℤ) - 2))

def localizationC (N : ℕ) : ℝ := ∑' j : ℕ, localizationTerm N j

end
end MomentAmbiguitySecretary.Secretary.Supplement


