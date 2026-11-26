-- Prove2me | Definitions.Def_GRH_OneSidedMoebius
-- name    : GRH_OneSidedMoebius
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T20:55:11.868471+00:00
-- url     : https://prove2.me/theorems/896f3fa5-66ba-4165-8a13-4762b071286d
-- title:
--   One-sided Möbius sums at perfect squares
-- statement:
--   Define the raw Möbius sum in a residue class through n, the ordinary Mertens sum, their square-cutoff power bounds, the ordinary Mellin transform on x greater than one, and the regularized zeta factor used to test singularities.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_MoebiusBilinear
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace GRH.OneSidedMoebius

open MeasureTheory Set
noncomputable section

def residue {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), if (k : ZMod q)=a then (ArithmeticFunction.moebius k : ℝ) else 0

def mertens (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℝ)

def majorant (D θ x : ℝ) : ℝ := D*x^θ - mertens ⌊x⌋₊

def transform (A : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-s-1)

def regularZeta (s : ℂ) : ℂ := if s=1 then 1 else (s-1)*riemannZeta s

def squareUpper : Prop :=
  ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ σ : ℝ, 1/2 < σ → σ < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, residue a (u^2) ≤ C*((u:ℝ)^2+1)^σ

def centeredBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ σ : ℝ, 1/2 < σ → σ < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |GRH.centeredMoebiusBilinear q a n| ≤ C*((n:ℝ)+1)^σ

end
end GRH.OneSidedMoebius


