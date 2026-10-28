-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition
-- name    : KLSModular_FunctionalInequalities_L2_AffineDecomposition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:12:56.565019+00:00
-- url     : https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614
-- title:
--   Affine-orthogonal part of an L² function
-- statement:
--   For a measure $\mu$ on $\mathbb{R}^n$ and a real function $g$, `affineOrthPart μ g x` subtracts from $g(x)$ its integral $\int g\,d\mu$ and its standard-basis linear component $\sum_j(\int\langle e_j,y\rangle g(y)\,d\mu)\langle e_j,x\rangle$. Under the centered probability and identity-covariance hypotheses used by the module, this is the component orthogonal to affine functions; the bundle also contains the abstract affine-decomposition norm estimate.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.Projection.Basic
--   import Mathlib.Analysis.InnerProductSpace.Orthogonal
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.Normed.Lp.MeasurableSpace
--   import Mathlib.MeasureTheory.Function.L2Space
--   import Mathlib.Analysis.Calculus.ContDiff.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
--     g x - ∫ y, g y ∂μ -
--       ∑ j, (∫ y, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, y⟫ * g y ∂μ) *
--         ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`eLpNorm_le_eLpNorm_of_integral_sq_le`](https://prove2.me/theorems/a648c1d1-6bfd-4c14-9d9d-0b13ff8fe12d)
--   - [`integral_affineOrthPart`](https://prove2.me/theorems/c7437f0d-1782-4a2e-ab79-cc4f3f38eb24)
--   - [`memLp_affineOrthPart`](https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0)
--   - [`integral_inner_mul_affineOrthPart`](https://prove2.me/theorems/c43097da-d56f-42d1-8178-075a15d4e395)
--   - [`sub_affineOrthPart_eq`](https://prove2.me/theorems/816eb15b-7e4e-4f5f-a7bc-08e3b253675d)
--   - [`contDiff_affineOrthPart`](https://prove2.me/theorems/222184b2-bf0f-4088-b7b6-1869ba885db6)
--   - [`integral_affineOrthPart_mul_sub`](https://prove2.me/theorems/d02bf2d3-cb86-4723-bceb-c6b16db784b1)
--   - [`integral_affineOrthPart_sq_le`](https://prove2.me/theorems/b462f885-9650-4c08-8d18-bf9383fa5a5b)
--   - [`integral_affine_sq`](https://prove2.me/theorems/8e6d6f95-c2c8-4475-91f6-ae7d05ba44fe)
--   - [`integral_sq_eq_affine_decomposition`](https://prove2.me/theorems/77f34311-b8ed-4189-84bc-10fd3772875b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean) · `FunctionalInequalities.L2.AffineDecomposition` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item P71. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L177-L182 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, definition bundle `KLSModular_FunctionalInequalities_L2_AffineDecomposition`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ContDiff.Basic

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


