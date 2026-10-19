-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
-- name    : OAI_Analysis_DirectCrouzeix_FaberEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:47:23.396923+00:00
-- url     : https://prove2.me/theorems/91ee12d9-f559-4d90-8152-ecde60ab2350
-- title:
--   Faber series on the boundary curve, its negative-frequency remainder and the boundary normal
-- statement:
--   Let $E$ be a complex inner product space, fix $c\in\mathbb{C}$ and $g:\mathbb{C}\to\mathbb{C}$ with complex derivatives $g',g''$, and let $\Phi(\zeta)=c\,\zeta+g(1/\zeta)$. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its normalized Haar measure $dt$, put $\zeta_t=e^{2\pi it}$ and let $\Gamma(t)=\Phi(\zeta_t)$ be the boundary curve. The following objects are used:
--
--   - the Faber polynomials $F_k(z)=\sum_{j=0}^{k}\tau_k\big(NW^{j}\big)z^{j}$, where $\tau_k(f)=f^{(k)}(0)/k!$, $W(u)=u/(c+ug(u))$ and $N(u)=(c-u^{2}g'(u))/(c+ug(u))$;
--   - the boundary coefficients $\beta_k(s)=\int_{\mathbb{T}}e^{2\pi ikt}\,Q(\zeta_t^{-1},\zeta_s^{-1})\,dt$, where $Q(u,v)=uv\big(\delta g(u,v)+u\,\delta_1g(u,v)\big)/\big(c-uv\,\delta g(u,v)\big)$ with $\delta g(u,v)=\int_0^1g'((1-\theta)u+\theta v)\,d\theta$ and $\delta_1g(u,v)=\int_0^1(1-\theta)\,g''((1-\theta)u+\theta v)\,d\theta$.
--
--   For $N\in\mathbb{N}$ and coefficients $C_0,\dots,C_{N-1}\in E$ the module defines:
--
--   1. **Faber series on the boundary.**
--   $$
--   S_C(t)=\sum_{k=0}^{N-1}F_k\big(\Gamma(t)\big)\,C_k .
--   $$
--
--   2. **Boundary remainder.**
--   $$
--   R_C(t)=\sum_{k=0}^{N-1}\beta_k(t)\,C_k .
--   $$
--
--   3. **Nonconstant coefficients.** The family $C'$ with $C'_0=0$ and $C'_k=C_k$ for $1\le k<N$.
--
--   4. **Boundary normal.** For $t\in\mathbb{T}$,
--   $$
--   n(t)=\zeta_t\,\big(c-\zeta_t^{-2}\,g'(\zeta_t^{-1})\big),
--   $$
--   which equals $\zeta_t\Phi'(\zeta_t)=\Gamma'(t)/(2\pi i)$: the velocity of the boundary curve turned by a right angle, a normal vector that points outward when the curve is positively oriented.
--
--   Under the standing hypotheses of the development ($g$ holomorphic on $\{|u|<R\}$ with $R>1$, $c\ne0$, and $c-uv\,\delta g(u,v)\ne0$ for $|u|,|v|<R$) one has $S_C(t)=\sum_ke^{2\pi ikt}C_k+R_C(t)$ with $R_C$ carrying only negative frequencies, and, if the boundary kernel $1+2\operatorname{Re}Q(\zeta_t^{-1},\zeta_s^{-1})$ is nonnegative, $\sum_k\|C_k\|^{2}\le\int_{\mathbb{T}}\|S_C(t)\|^{2}dt\le\|C_0\|^{2}+2\sum_{k\ge1}\|C_k\|^{2}$. The kernel is nonnegative when $\operatorname{Re}\big(\overline{n(t)}\,(\Gamma(t)-\Gamma(s))\big)\ge0$ for all $t,s$, i.e. when, at each of its points, the whole curve lies on the side of the tangent line opposite to $n(t)$, as for positively oriented convex curves. These results are proved in the module.
--
--   **Formalization Note** `faberBoundarySeries c g C t`, `boundaryRemainder c g C t` and `nonconstantCoefficients C k` take `C : Fin N → E`; `faberBoundarySeries` and `boundaryRemainder` require `[NormedAddCommGroup E] [InnerProductSpace ℂ E]` and `nonconstantCoefficients` only `[NormedAddCommGroup E]` (the `[CompleteSpace E]` of the enclosing section is not an argument of these definitions); `boundaryNormal c g t` is defined outside that section. In Lean `deriv g` is $0$ where $g$ is not differentiable and inverses and quotients by $0$ are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberEnergy.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_128 u_129

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def faberBoundarySeries {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, (faberBasis c g k).eval (boundary c g t) • C k

def boundaryRemainder {N : ℕ} (c : ℂ) (g : ℂ → ℂ) (C : Fin N → E) (t : Angle) : E :=
  ∑ k : Fin N, boundaryCoefficient c g k t • C k

def nonconstantCoefficients {N : ℕ} (C : Fin N → E) (k : Fin N) : E :=
  if (k:ℕ) = 0 then 0 else C k

end FaberHilbert

def boundaryNormal (c : ℂ) (g : ℂ → ℂ) (t : Angle) : ℂ :=
  unitPoint t * (c-(unitPoint t)⁻¹^2*deriv g ((unitPoint t)⁻¹))

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

end BanachAlgebra

end DirectCrouzeix.Faber

end

end

end OAI


