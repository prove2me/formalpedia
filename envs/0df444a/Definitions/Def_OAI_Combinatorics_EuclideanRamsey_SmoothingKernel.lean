-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
-- name    : OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:18:59.979536+00:00
-- url     : https://prove2.me/theorems/fdbfaaf1-46c3-406c-8d73-83c4f7f81998
-- title:
--   Smooth positive part, radial powers, the half-Laplacian and radial bump functions
-- statement:
--   This file defines the one-variable smoothing function and the radial building blocks from which compactly supported smooth test functions with controlled Laplacian are made.
--
--   Let $\psi:\mathbb{R}\to\mathbb{R}$ be the standard smooth gluing function, $\psi(t)=0$ for $t\le0$ and $\psi(t)=e^{-1/t}$ for $t>0$.
--
--   1. **Smooth positive part.** $\sigma(t)=t\,\psi(t)$, so $\sigma(t)=t\,e^{-1/t}$ for $t>0$ and $\sigma(t)=0$ for $t\le0$. Together with it the file defines
--   $$\sigma_1(t)=\bigl(1+t^{-1}\bigr)\psi(t),\qquad \sigma_2(t)=t^{-3}\,\psi(t),$$
--   which are the first and second derivatives of $\sigma$ (all three vanish for $t\le0$).
--   2. **Radial powers.** For a real inner product space $E$ and real parameters $a,p$, $r_{a,p}(x)=(a+\|x\|^2)^p$ for $x\in E$ (a real power).
--   3. **Half-Laplacian.** For a finite-dimensional real inner product space $E$ of dimension $n$ with a fixed orthonormal basis $e_1,\dots,e_n$, and $f:E\to\mathbb{R}$,
--   $$\tfrac12\Delta f(x)=\frac12\sum_{i=1}^{n}D^2f(x)(e_i,e_i),$$
--   where $D^2f(x)$ is the second Fréchet derivative of $f$ at $x$.
--   4. **Radial bumps.** $\beta_{a,p}(x)=\sigma\bigl((a+\|x\|^2)^p-1\bigr)$ for $x\in E$.
--   5. **Smoothing exponent.** For a finite-dimensional real normed space $E$ of dimension $n$, $p_E=\tfrac14-\tfrac n2$.
--
--   For $a>0$ and $p<0$ the bump $\beta_{a,p}$ is smooth and nonnegative, and it is positive exactly on the set where $\|x\|^2<1-a$, so it has compact support. The exponent $p_E$ is negative as soon as $n\ge1$, and it is chosen so that $n+2p_E-2=-\tfrac32$; this makes the half-Laplacian of $r_{a,p_E}$ nonnegative outside a ball of radius comparable to $\sqrt a$. With $p=p_E$ and $a$ small, these bumps yield smooth, compactly supported, nonnegative functions $b$ for which the negative part of $\tfrac12\Delta b$, weighted by $\|x\|^2$, has arbitrarily small integral compared with $\int b$.
--
--   **Formalization Note** `smoothPositivePart`, `smoothPositivePart'` and `smoothPositivePart''` are built from Mathlib's `expNegInvGlue` (the function $\psi$); since Lean sets `0⁻¹ = 0`, the formulas give the value $0$ at $t=0$ as well. `radialPower` uses the real power `Real.rpow`, which is meaningful here only when $a+\|x\|^2>0$ (in applications $a>0$). `halfLaplacian` evaluates `iteratedFDeriv ℝ 2 f x` on the vectors of `stdOrthonormalBasis ℝ E`; for $f$ not twice differentiable, Lean's convention makes these derivatives $0$. `radialBump` and `smoothingExponent` (defined via `Module.finrank`) are as above; a section reserved for integration contains no definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uDomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
namespace EuclideanRamsey

def smoothPositivePart (t : ℝ) : ℝ := t * expNegInvGlue t

def smoothPositivePart' (t : ℝ) : ℝ := (1 + t⁻¹) * expNegInvGlue t

def smoothPositivePart'' (t : ℝ) : ℝ := t⁻¹ ^ 3 * expNegInvGlue t

section Radial
variable {E : Type uDomain} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialPower (a p : ℝ) (x : E) : ℝ := (a + ‖x‖^2) ^ p

variable [FiniteDimensional ℝ E]

def halfLaplacian (f : E → ℝ) (x : E) : ℝ :=
  (1/2 : ℝ) * ∑ i, iteratedFDeriv ℝ 2 f x
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]

def radialBump (a p : ℝ) (x : E) : ℝ :=
  smoothPositivePart (radialPower a p x - 1)

def smoothingExponent (E : Type uDomain) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ := 1/4 - (Module.finrank ℝ E : ℝ)/2

section Integration
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

end Integration

end Radial

end EuclideanRamsey

end

end OAI


