-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_gaussian
-- name    : SmoothedSimplex_Shadow_gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:04:19.528207+00:00
-- url     : https://prove2.me/theorems/0cfb0858-3e6c-4ff2-89e3-fc5a533b5ed9
-- title:
--   §2.4 — the Gaussian distribution of standard deviation $\sigma$ centered at $c$
-- statement:
--   For $c\in\mathbb R^k$ and $\sigma>0$, the **Gaussian distribution of standard deviation $\sigma$ centered at $c$** is the probability measure on $\mathbb R^k$ with density
--
--   $$
--   \mu(x)=\Big(\frac{1}{\sqrt{2\pi}\,\sigma}\Big)^{k} e^{-\|x-c\|^{2}/2\sigma^{2}}
--   $$
--
--   with respect to Lebesgue measure; equivalently, a Gaussian with covariance matrix $\sigma^2 I$. A family $a_1,\dots,a_n$ "with density $\prod_{i=1}^n\mu_i(a_i)$" is a family of independent vectors, $a_i$ distributed according to $\mu_i$.
--
--   This is the perturbation model of smoothed analysis: each data vector $a_i$ of the linear program is a Gaussian of standard deviation $\sigma$ around an adversarial center $\bar a_i$.
--
--   **Formalization Note** Defined as Lebesgue measure with density `gaussianPdf c σ`. The joint law of $a_1,\dots,a_n$ is the product measure `Measure.pi (fun i => gaussian (ā i) σ)`.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, §2.4, printed p. 19 (PDF p. 19)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussianPdf

namespace SmoothedSimplex.Shadow

open MeasureTheory

/-- The Gaussian distribution of standard deviation `σ` centered at `c` in `ℝ^k`
(Spielman & Teng, arXiv:cs/0111050v7, §2.4, printed p. 19, PDF p. 19): the measure with density
`gaussianPdf c σ` with respect to Lebesgue measure. Its coordinates are independent `N(cᵢ, σ²)`.

**Formalization Note.** Lebesgue measure on `EuclideanSpace ℝ (Fin k)` is Mathlib's `volume`.
For `σ > 0` (assumed by every statement that uses it) this is a probability measure. A family
`a₁, …, aₙ` with joint density `∏ᵢ μᵢ(aᵢ)` is distributed according to
`Measure.pi (fun i => gaussian (ā i) σ)`. -/
noncomputable def gaussian {k : ℕ} (c : EuclideanSpace ℝ (Fin k)) (σ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin k)) :=
  volume.withDensity (fun x => ENNReal.ofReal (gaussianPdf c σ x))

end SmoothedSimplex.Shadow


