-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
-- name    : OAI_Analysis_DirectCrouzeix_BoundaryKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:42:24.816667+00:00
-- url     : https://prove2.me/theorems/94ff37f7-0138-49ae-926f-cda905f2fce4
-- title:
--   Boundary curve of an exterior map, boundary coefficients and the kernel $K=1+2\operatorname{Re}\widetilde K$
-- statement:
--   Fix $c\in\mathbb{C}$ and $g:\mathbb{C}\to\mathbb{C}$, with complex derivatives $g'$ and $g''$, and let $\Phi(\zeta)=c\,\zeta+g(1/\zeta)$ be the associated exterior map. Put
--   $$
--   \delta g(u,v)=\int_0^1 g'\big((1-\theta)u+\theta v\big)\,d\theta,\qquad \delta_1g(u,v)=\int_0^1(1-\theta)\,g''\big((1-\theta)u+\theta v\big)\,d\theta,
--   $$
--   and define the correction term $Q(u,v)=uv\big(\delta g(u,v)+u\,\delta_1g(u,v)\big)/\big(c-uv\,\delta g(u,v)\big)$. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its normalized Haar measure $dt$ and write $\zeta_t=e^{2\pi it}$ for $t\in\mathbb{T}$. The module defines, for $t,s\in\mathbb{T}$ and $k\in\mathbb{N}$:
--
--   1. **Boundary curve.** $\Gamma(t)=\Phi(\zeta_t)=c\,\zeta_t+g(\zeta_t^{-1})$.
--
--   2. **Boundary correction.** $\widetilde K(t,s)=Q\big(\zeta_t^{-1},\zeta_s^{-1}\big)$.
--
--   3. **Boundary coefficients.**
--   $$
--   \beta_k(s)=\int_{\mathbb{T}}e^{2\pi ikt}\,\widetilde K(t,s)\,dt ,
--   $$
--   the Fourier coefficient of $t\mapsto\widetilde K(t,s)$ at frequency $-k$.
--
--   4. **Boundary kernel.** The real-valued kernel
--   $$
--   K(t,s)=1+2\operatorname{Re}\widetilde K(t,s).
--   $$
--
--   Assume $g$ is holomorphic on a disk $\{|u|<R\}$ with $R>1$ and $c-uv\,\delta g(u,v)\ne0$ whenever $|u|,|v|<R$. The module then proves that $\beta_0\equiv0$, that $K$ has unit marginals, $\int_{\mathbb{T}}K(t,s)\,dt=\int_{\mathbb{T}}K(t,s)\,ds=1$ for all $s$ and $t$, and that $\int_{\mathbb{T}}K(t,s)\,e^{2\pi ikt}\,dt=\beta_k(s)$ for $k\ne0$; if also $c\ne0$, the Faber polynomials $F_k$ of $\Phi$ satisfy $F_k(\Gamma(s))=e^{2\pi iks}+\beta_k(s)$ on the boundary curve. Once $K$ is shown to be nonnegative (which holds for convex boundary curves), it is a doubly stochastic kernel, and this is the mechanism that bounds the boundary energy of Faber expansions.
--
--   **Formalization Note** The definitions are `boundary`, `boundaryCorrection`, `boundaryCoefficient` and `boundaryKernel` in the namespace `DirectCrouzeix.Faber`; `boundaryCoefficient c g k s` is `fourierCoeff (fun t => boundaryCorrection c g t s) (-(k:ℤ))`, and Mathlib's `fourierCoeff f n` is the integral of $e^{-2\pi int}f(t)$ against `AddCircle.haarAddCircle`. The usual Lean conventions for `deriv`, inverses of $0$ and division by zero are in force.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def boundary (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ := exterior c g (unitPoint t)

def boundaryCorrection (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℂ :=
  correction c g ((unitPoint t)⁻¹) ((unitPoint s)⁻¹)

def boundaryCoefficient (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (s : Angle) : ℂ :=
  fourierCoeff (fun t => boundaryCorrection c g t s) (-(k:ℤ))

def boundaryKernel (c : ℂ) (g : ℂ → ℂ) (t s : Angle) : ℝ :=
  1 + 2*(boundaryCorrection c g t s).re

end DirectCrouzeix.Faber

end

end

end OAI


