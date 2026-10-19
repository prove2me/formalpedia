-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
-- name    : OAI_Analysis_DirectCrouzeix_FaberCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:50:02.524544+00:00
-- url     : https://prove2.me/theorems/b9395e4e-ece4-48bf-943e-250731d622eb
-- title:
--   Operator-valued Faber generating function in a Banach algebra
-- statement:
--   Let $\mathfrak A$ be a complex normed algebra with unit $1$ (not necessarily commutative), fix $c\in\mathbb{C}$ and $g:\mathbb{C}\to\mathbb{C}$ with complex derivative $g'$, and let $A\in\mathfrak A$. For $u\in\mathbb{C}$ the module defines:
--
--   1. **Denominator.**
--   $$
--   D_A(u)=\big(c+u\,g(u)\big)\,1-u\,A\in\mathfrak A .
--   $$
--
--   2. **Operator generating function.**
--   $$
--   G_A(u)=\big(c-u^{2}g'(u)\big)\,D_A(u)^{-1},
--   $$
--   where $D_A(u)^{-1}$ is the inverse of $D_A(u)$ in $\mathfrak A$ when it exists, and $0$ otherwise.
--
--   This is the scalar generating function $(c-u^{2}g'(u))/(c+u(g(u)-z))$ of the Faber polynomials of $\Phi(\zeta)=c\,\zeta+g(1/\zeta)$ with the complex variable $z$ replaced by the element $A$. Writing $F_k$ for these Faber polynomials, the module proves that for $c\ne0$ and $g$ holomorphic near $0$ the $k$-th Taylor coefficient of $G_A$ at $u=0$ is $F_k(A)$; that for $\zeta\ne0$, $G_A(1/\zeta)=\zeta\big(c-\zeta^{-2}g'(1/\zeta)\big)\big(\Phi(\zeta)\,1-A\big)^{-1}$, a weighted resolvent of $A$ at the point $\Phi(\zeta)$; and that if $g$ is holomorphic on $\{|u|<R\}$ with $R>1$, $c\ne0$ and $D_A(u)$ is invertible for all $|u|\le1$, then
--   $$
--   F_k(A)=\int_0^1 e^{2\pi ikt}\,G_A\big(e^{-2\pi it}\big)\,dt\qquad(k\in\mathbb{N}),
--   $$
--   while the Fourier coefficients of $t\mapsto G_A(e^{-2\pi it})$ at positive frequencies vanish. This is a Cauchy-type integral representation of $F_k(A)$ over the boundary curve $t\mapsto\Phi(e^{2\pi it})$.
--
--   **Formalization Note** `algebraDenominator c g A u` is `(c+u*g u) • 1-u • A` and `algebraGenerating c g A u` is `(c-u^2*deriv g u) • Ring.inverse (algebraDenominator c g A u)`, where `Ring.inverse` returns the inverse of a unit and $0$ for a non-unit, and `deriv g` is $0$ where $g$ is not differentiable. They take `𝔄` with `[NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]` only (the `[CompleteSpace 𝔄]` of the enclosing section is not an argument of these definitions); the formulas only use the algebra structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberCalculus.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_129 u_130

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

def algebraDenominator (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) (u : ℂ) : 𝔄 :=
  (c+u*g u) • 1-u • A

def algebraGenerating (c : ℂ) (g : ℂ → ℂ) (A : 𝔄) (u : ℂ) : 𝔄 :=
  (c-u^2*deriv g u) • Ring.inverse (algebraDenominator c g A u)

end BanachAlgebra

end DirectCrouzeix.Faber

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

end DirectCrouzeix

end

end

end OAI


