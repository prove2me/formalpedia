-- Prove2me | Definitions.Def_Helfgott_MajorKernelTightFourierBounds
-- name    : Helfgott_MajorKernelTightFourierBounds
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T01:08:47.018982+00:00
-- url     : https://prove2.me/theorems/8a696917-d4e5-4f75-bb98-edd3b9d54243
-- title:
--   Complete tight Fourier mass and quadratic decay of the actual Goldbach logarithmic kernel
-- statement:
--   Let $K(u)=h(\exp u)$, where $h$ is the actual major-arc kernel defining the Goldbach smoothing $\eta_+$. With Fourier convention $\widehat K(\xi)=\int K(u)\exp(-2\pi i u\xi)\,du$, the transform is integrable and
--   $$\int_{\mathbb R}|K(u)|\,du\le\frac52,\quad|\widehat K(\xi)|\le\frac52,\quad\xi^2|\widehat K(\xi)|\le\frac5{12},\quad\int_{\mathbb R}|\widehat K(\xi)|\,d\xi\le\frac{25}6.$$
--   These unconditional estimates control the complete signed spectral projection used in the actual etaPlus Mellin transform and its conductor-dependent high-zero bound.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Original complete numerical and analytic bounds built on Mathlib Gaussian, Fourier and Mellin analysis. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.FourierTransform
open MeasureTheory Set Complex
open scoped FourierTransform

namespace Helfgott

def MajorKernelTightFourierBounds : Prop :=

    let K : ℝ → ℂ := fun u => (majorKernel (Real.exp u) : ℂ)
    Integrable (𝓕 K) ∧ (∫ u : ℝ,‖K u‖)≤5/2 ∧
      (∀ ξ : ℝ,‖𝓕 K ξ‖≤5/2) ∧
      (∀ ξ : ℝ,ξ^2*‖𝓕 K ξ‖≤5/12) ∧
      (∫ ξ : ℝ,‖𝓕 K ξ‖)≤25/6

end Helfgott


