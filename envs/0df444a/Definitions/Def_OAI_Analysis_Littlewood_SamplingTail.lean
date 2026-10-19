-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
-- name    : OAI_Analysis_Littlewood_SamplingTail
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:22:51.27116+00:00
-- url     : https://prove2.me/theorems/2faec58a-d3fe-42a4-b8bb-ec52c44c4d7d
-- title:
--   Sampled chirps and stationary waves for Poisson summation of quadratic exponential sums
-- statement:
--   Let $e(\theta)=e^{2\pi i\theta}$ and let $g:\mathbb{R}\to\mathbb{C}$ be an amplitude. The parameters $N$ (scale), $\beta$ (curvature) and $b$ (linear frequency) are real, and $\operatorname{sign}\beta\in\{-1,0,1\}$.
--
--   1. **Lattice weight.** $w(m)=1/(1+|m|)^2$ for $m\in\mathbb{Z}$, a summable weight on $\mathbb{Z}$.
--
--   2. **Sampled chirp.** For $x\in\mathbb{R}$,
--   $$
--   S_{g,N,\beta,b}(x)=g\Bigl(\frac{x}{N}\Bigr)\,e\Bigl(\frac{\beta x^2}{2N}+b x\Bigr),
--   $$
--   so that the exponential sum $\sum_{k\in\mathbb{Z}}g(k/N)\,e\bigl(\beta k^2/(2N)+bk\bigr)$ equals $\sum_{k\in\mathbb{Z}}S_{g,N,\beta,b}(k)$.
--
--   3. **Stationary wave.** For $l\in\mathbb{Z}$,
--   $$
--   W_{g,N,\beta,b}(l)=\frac{1}{\sqrt{|\beta|}}\,e\Bigl(\frac{\operatorname{sign}\beta}{8}-\frac{N(l-b)^2}{2\beta}\Bigr)\,g\Bigl(\frac{l-b}{\beta}\Bigr),
--   $$
--   whose modulus is $|g((l-b)/\beta)|/\sqrt{|\beta|}$.
--
--   By Poisson summation the sampled sum equals $N\sum_{l\in\mathbb{Z}}\int g(x)\,e\bigl(N\beta x^2/2-N(l-b)x\bigr)\,dx$, and stationary phase evaluates $\sqrt N$ times the $l$-th integral as $W_{g,N,\beta,b}(l)$ up to $O(1/N)$, the stationary point being $x=(l-b)/\beta$. For smooth compactly supported $g$ and $\beta\ne0$ only finitely many $l$ contribute and the remaining terms are controlled by the lattice weight, which leads to an estimate of the form
--   $$
--   \frac{1}{\sqrt N}\sum_{k\in\mathbb{Z}}g\Bigl(\frac kN\Bigr)e\Bigl(\frac{\beta k^2}{2N}+bk\Bigr)=\sum_{l\in\mathcal{J}}W_{g,N,\beta,b}(l)+O\Bigl(\frac1N\Bigr),
--   $$
--   uniformly for $N\ge1$ and bounded $b$, with a fixed finite set $\mathcal{J}\subset\mathbb{Z}$.
--
--   **Formalization Note** `latticeWeight` repeats, in the sampling namespace, the weight of the quadratic-tail file. `sampledChirp g N β b x` is `g (x/N) * phase (β/N) (-b) x`, where `phase t u x` $=e(tx^2/2-ux)$, and `stationaryWave g N β b l` is written with `realPhase (2 * Real.pi * _)` and `Real.sign`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SamplingTail.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingTail.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

def latticeWeight (w : ℤ) : ℝ := 1/(1+|(w:ℝ)|)^2

def sampledChirp (g : ℝ → ℂ) (N β b : ℝ) (x : ℝ) : ℂ :=
  g (x/N)*phase (β/N) (-b) x

def stationaryWave (g : ℝ → ℂ) (N β b : ℝ) (l : ℤ) : ℂ :=
  (realPhase (2*Real.pi*(Real.sign β/8-N*((l : ℝ)-b)^2/(2*β))) /
    (Real.sqrt |β| : ℂ))*g (((l : ℝ)-b)/β)

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI


