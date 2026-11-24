-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Neural
-- name    : RegMT_Classif_Supplement_Neural
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:29:38.438633+00:00
-- url     : https://prove2.me/theorems/a02396d0-38c4-404b-a9a2-50420ffcff5d
-- title:
--   Neural transport objectives and corrected arbitrary-output-norm bound
-- statement:
--   For the full network class and feature support $X$, retain the source constant
--   $$c=\max\{1,2\sup_{W,x\in X}|h_W(x)|\}$$
--   in classification and $c=1$ in regression. Define the robust objectives in (33) using metric (11) in regression and metric (16) in classification. The price $\kappa\in(0,\infty]$ includes label-preserving transport. Finite-price classification reuses the published ball directly.
--   The regularized empirical objectives are those of (34), with the necessary output-coordinate conversion factor in the slope term:
--   $$\frac1N\sum_i\ell(h_W(\hat x_i),\hat y_i)+\rho\operatorname{lip}(L)\max\{\|o\|a(W),c/\kappa\}.$$
--   All nonnegative extended products use $0\cdot\infty=0$; division by infinite label price is zero, including $\infty/\infty$, expressing that labels cannot change. The extra output factor corrects the arbitrary final-layer norm issue documented in DISPROOF.md; it equals one under the usual scalar norm.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.18, Theorem 3.30, (34); proof pp.40–41; output-norm correction documented in DISPROOF.md

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Architecture
import Definitions.Def_RegMT_Classif_Supplement_Transport
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open scoped ENNReal

noncomputable section

namespace RegMT.Classif.Supplement
open DRLogReg.Reformulation WassersteinDRO.Duality
attribute [local instance] Classical.propDecidable

variable {M : ℕ}

def classC (A : Layers M) (X : Set (A.Space 0)) : ℝ≥0∞ :=
  max 1 (2 * ⨆ W : Weights A, ⨆ x ∈ X, ENNReal.ofReal |network A W x|)

def extendedWeightedCost (A : Layers M) (κ : ℝ≥0∞) (z z' : A.Space 0 × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖z.1 - z'.1‖ + κ * ENNReal.ofReal |z.2 - z'.2|

variable (A : Layers M) [MeasurableSpace (A.Space 0)]

def neuralRegRisk {N : ℕ} (X : Set (A.Space 0)) (Y : Set ℝ)
    (x : Fin N → A.Space 0) (y : Fin N → ℝ) (L : ℝ → ℝ) (κ : ℝ≥0∞) (ρ : ℝ)
    (W : Weights A) : ℝ≥0∞ :=
  costRisk (extendedWeightedCost A κ) (X ×ˢ Y) (fun i => (x i, y i)) ρ
    (fun z => L (network A W z.1 - z.2))

def neuralClassRisk {N : ℕ} (X : Set (A.Space 0)) (x : Fin N → A.Space 0)
    (y : Fin N → Bool) (L : ℝ → ℝ) (κ : ℝ≥0∞) (ρ : ℝ) (W : Weights A) : ℝ≥0∞ :=
  if κ = ⊤ then
    costRisk labelPreservingCost (X ×ˢ Set.univ) (fun i => (x i, y i)) ρ
      (fun z => L (sgn z.2 * network A W z.1))
  else classRisk X x y κ.toReal ρ (fun z => L (sgn z.2 * network A W z.1))

def neuralRegBound {N : ℕ} (x : Fin N → A.Space 0) (y : Fin N → ℝ)
    (L : ℝ → ℝ) (κ : ℝ≥0∞) (ρ : ℝ) (W : Weights A) : ℝ≥0∞ :=
  ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, L (network A W (x i) - y i)) +
    ENNReal.ofReal ρ * lipschitzModulus L * max (outputProduct A W) (1 / κ)

def neuralClassBound {N : ℕ} (X : Set (A.Space 0)) (x : Fin N → A.Space 0)
    (y : Fin N → Bool) (L : ℝ → ℝ) (κ : ℝ≥0∞) (ρ : ℝ) (W : Weights A) : ℝ≥0∞ :=
  ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, L (sgn (y i) * network A W (x i))) +
    ENNReal.ofReal ρ * lipschitzModulus L * max (outputProduct A W) (classC A X / κ)

end RegMT.Classif.Supplement


