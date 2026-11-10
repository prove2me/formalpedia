-- Prove2me | Definitions.Def_SmoothedPlanted_FFK_Certifiable
-- name    : SmoothedPlanted_FFK_Certifiable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:31:51.863099+00:00
-- url     : https://prove2.me/theorems/0c03e542-30ca-4c2e-87bb-3c66a2c3f198
-- title:
--   Definition 13 — certifiable contradiction parameters
-- statement:
--   The matrix $\Pi$ has entries in $[0,1]$, $\delta>0$, and $\Pi-\delta\mathbf1\mathbf1^\top\succeq0$. The minimum positive entry $\pi_{\min}$ must be at least $C_0\log(n)/n$, using the natural logarithm. The condition number is defined as $\kappa=\|\Pi\|_{\rm op}/\delta$, not supplied as an independent parameter. The norm is Mathlib's Euclidean operator norm. The positive-entry set is finite and nonempty whenever $q\ge1$ and the PSD inequality holds. Outside that domain, the empty real infimum is zero; asymptotic mission statements require $q\ge1$ and $n\ge2$.
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Definition 13 — certifiable contradiction parameters, printed p. 16 (PDF p. 18), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Mathlib

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

open scoped Matrix.Norms.L2Operator
/-- Spectral (Euclidean operator) norm, fixed independently of other matrix norms. -/
def spectralNorm {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) : ℝ := ‖A‖
def piMin {q : ℕ} (Pi : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  sInf {z | ∃ a b, z = Pi a b ∧ 0 < Pi a b}
def conditionNumber {q : ℕ} (Pi : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ) : ℝ :=
  spectralNorm Pi / δ
def Certifiable {q : ℕ} (n : ℕ) (C0 δ : ℝ) (Pi : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  0 < δ ∧ (∀ a b, 0 ≤ Pi a b ∧ Pi a b ≤ 1) ∧
  (Pi - Matrix.of (fun _ _ => δ)).PosSemidef ∧
  C0 * Real.log n / n ≤ piMin Pi

end SmoothedPlanted.FFK


