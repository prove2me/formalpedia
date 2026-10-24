-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
-- name    : KLS408915f_FunctionalInequalities_L2_AffineDecomposition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:55:47.073615+00:00
-- url     : https://prove2.me/theorems/6d5db1e0-0502-4ea7-b227-0ad7badf55a0
-- title:
--   Affine-orthogonal part of an L² function
-- statement:
--   For a measure $\mu$ on $\mathbb{R}^n$ and a real function $g$, `affineOrthPart μ g x` subtracts from $g(x)$ its integral $\int g\,d\mu$ and its standard-basis linear component $\sum_j(\int\langle e_j,y\rangle g(y)\,d\mu)\langle e_j,x\rangle$. Under the centered probability and identity-covariance hypotheses used by the module, this is the component orthogonal to affine functions; the bundle also contains the abstract affine-decomposition norm estimate.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item P71. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L177-L182 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, definition bundle `KLS408915f_FunctionalInequalities_L2_AffineDecomposition`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace L2
section AffineOrthPart
variable {n : ℕ}
/-- The affine-orthogonal part of `g`: `g` minus its mean and its linear component. -/
noncomputable def affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  g x - ∫ y, g y ∂μ -
    ∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫
end AffineOrthPart
end L2
end FunctionalInequalities


