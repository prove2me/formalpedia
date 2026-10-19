-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
-- name    : OAI_Analysis_Littlewood_ModeSampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:26:14.761216+00:00
-- url     : https://prove2.me/theorems/412caf95-5248-4242-85f6-5e360d68e952
-- title:
--   Superpositions of sampled chirps: the mode sum defining a coefficient sequence of length $N$
-- statement:
--   Let $P$ be a finite set of modes. For each mode $i\in P$ let $g_i:\mathbb{R}\to\mathbb{C}$ be an amplitude, $c_i\in\mathbb{C}$ a coefficient, and $\lambda_i,b_i,d_i\in\mathbb{R}$ a curvature, a linear frequency and a phase offset. With $e(\theta)=e^{2\pi i\theta}$, for $N\in\mathbb{N}$ and $k\in\{0,\dots,N-1\}$ the **mode sum** is
--   $$
--   X_N(k)=\sum_{i\in P}c_i\,e(N d_i)\,g_i\Bigl(\frac kN\Bigr)\,e\Bigl(\frac{\lambda_i k^2}{2N}+b_i k\Bigr).
--   $$
--
--   The sequence $X_N(0),\dots,X_N(N-1)$ samples at the points $k/N$ a superposition of chirps: mode $i$ is the window $g_i$ modulated by a quadratic phase of curvature $\lambda_i$ and linear frequency $b_i$. In the main construction, built from a Fourier packet, the mode sum is real with values in $[-1,1]$, and $(X_N(k))_k$ is the coefficient vector that is subsequently rounded to a vector of signs. For smooth amplitudes supported in $(0,1)$ with $|g_i|\le1$, the normalized energy $\frac1N\sum_k|X_N(k)|^2$ tends to $\sum_i|c_i|^2\int|g_i|^2$ provided distinct modes differ in curvature, have non-integral difference of linear frequencies, or have disjointly supported amplitudes; and if moreover all $\lambda_i\ne0$, $|c_i|/\sqrt{|\lambda_i|}\le K$, and for every $t$ at most one pair $(i,l)\in P\times\mathbb{Z}$ has $g_i\bigl((l-b_i-t)/\lambda_i\bigr)\ne0$, then $\bigl|N^{-1/2}\sum_k X_N(k)\,e(tk)\bigr|\le K+C/N$ for all $t\in[0,1]$ and $N\ge1$, with a constant $C$.
--
--   **Formalization Note** `modeSum g c lam b d N k` is the sum over `P` of `c i * realPhase (2 * Real.pi * N * d i) * g i (k/N) * phase (lam i / N) (-b i) k`, where `realPhase (2 * Real.pi * x)` $=e(x)$ and `phase t u x` $=e(tx^2/2-ux)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ModeSampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ModeSampling.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uP

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

def modeSum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (N : ℕ) (k : Fin N) : ℂ :=
  ∑ i, c i*realPhase (2*Real.pi*N*d i)*g i ((k : ℝ)/N)*phase (lam i/N) (-b i) k

end
end AsymptoticallyMinimalLittlewood.Sampling

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI


