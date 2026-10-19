-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
-- name    : OAI_Analysis_DirectCrouzeix_KernelContraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:44:59.981917+00:00
-- url     : https://prove2.me/theorems/ba9a0fa0-b637-42e3-90df-68ad65e229eb
-- title:
--   Trigonometric polynomials with nonnegative frequencies and Hilbert-space coefficients
-- statement:
--   Let $E$ be a complex inner product space, let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its normalized Haar measure $dt$ (total mass $1$), let $N\in\mathbb{N}$ and let $C_0,\dots,C_{N-1}\in E$. The module defines the $E$-valued trigonometric polynomial
--
--   $$
--   P_C(t)=\sum_{k=0}^{N-1}e^{2\pi ikt}\,C_k,\qquad t\in\mathbb{T}.
--   $$
--
--   Only the nonnegative frequencies $0,1,\dots,N-1$ occur, so $P_C(t)$ is the value at $\zeta=e^{2\pi it}$ of the $E$-valued polynomial $\sum_kC_k\zeta^{k}$ on the unit circle.
--
--   The $k$-th Fourier coefficient of $P_C$ is $C_k$ for $0\le k<N$, so $\int_{\mathbb{T}}\|P_C(t)\|^{2}dt=\sum_k\|C_k\|^{2}$; and if $r:\mathbb{T}\to E$ is continuous with vanishing Fourier coefficients at all frequencies $j\ge0$, then $\int_{\mathbb{T}}\|P_C+r\|^{2}dt=\sum_k\|C_k\|^{2}+\int_{\mathbb{T}}\|r\|^{2}dt$ (both proved in the module). Combined with the contraction estimate $\int\|\int K(x,y)\,u(x)\,d\mu(x)\|^{2}d\nu(y)\le\int\|u(x)\|^{2}d\mu(x)$ for continuous nonnegative kernels $K$ with unit row and column integrals, also proved in the module, this orthogonal splitting yields two-sided bounds for the boundary energy of Faber series in terms of their coefficients.
--
--   **Formalization Note** `positiveSeries C t` is `∑ k : Fin N, fourier (k:ℤ) t • C k` for `C : Fin N → E` and `t : Angle`, where `Angle` is `AddCircle (1 : ℝ)` and `fourier k t` is $e^{2\pi ikt}$. The definition takes `E` with `[NormedAddCommGroup E] [InnerProductSpace ℂ E]` (the `[CompleteSpace E]` of the enclosing section is not an argument of it); the formula itself only uses addition and complex scalar multiplication in $E$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean by skeleton subtraction
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

namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def positiveSeries {N : ℕ} (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, fourier (k:ℤ) t • C k

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI


