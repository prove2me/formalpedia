-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
-- name    : OAI_Analysis_DirectCrouzeix_FaberPolynomials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:40:20.992709+00:00
-- url     : https://prove2.me/theorems/4d1cdd87-b7fe-454f-bb39-84462ed2f2f5
-- title:
--   Faber polynomials of the exterior map $c\zeta+g(1/\zeta)$ via Taylor coefficients of a generating function
-- statement:
--   Fix $c\in\mathbb{C}$ and a function $g:\mathbb{C}\to\mathbb{C}$ (in applications $c\ne0$ and $g$ is holomorphic near $0$), write $g'$ for its complex derivative, and let $\tau_k(f)=f^{(k)}(0)/k!$ denote the $k$-th Taylor coefficient at $0$ of a function $f:\mathbb{C}\to\mathbb{C}$. These data describe the exterior map $\Phi(\zeta)=c\,\zeta+g(1/\zeta)$. The module defines:
--
--   1. **Local functions.** For $u\in\mathbb{C}$,
--   $$
--   L(u)=\frac{1}{c+u\,g(u)},\qquad W(u)=u\,L(u),\qquad N(u)=\big(c-u^{2}g'(u)\big)\,L(u).
--   $$
--   The values $L(0)=1/c$ and $W(0)=0$ are recorded as simplification lemmas, as is $N(0)=1$ under the hypothesis $c\ne0$.
--
--   2. **Faber polynomials.** For $k\in\mathbb{N}$, the polynomial
--   $$
--   F_k(z)=\sum_{j=0}^{k}\tau_k\big(N\,W^{j}\big)\,z^{j}\in\mathbb{C}[z].
--   $$
--
--   3. **Scalar generating function.** For $z,u\in\mathbb{C}$,
--   $$
--   S(z,u)=\frac{c-u^{2}g'(u)}{c+u\,\big(g(u)-z\big)} .
--   $$
--
--   The module also records the simplification rule $e^{2\pi i(-t)}=\big(e^{2\pi it}\big)^{-1}$ for points $t$ of the circle $\mathbb{R}/\mathbb{Z}$.
--
--   Near $u=0$ one has $S(z,u)=N(u)/\big(1-zW(u)\big)=\sum_{j}N(u)W(u)^{j}z^{j}$, and since $W(u)$ vanishes at $0$ only the terms $j\le k$ contribute to the $k$-th Taylor coefficient; accordingly, for $c\ne0$ and $g$ holomorphic near $0$, $\tau_k\big(S(z,\cdot)\big)=F_k(z)$ for every $z$ (proved in the module). Substituting $u=1/\zeta$ gives $S(z,1/\zeta)=\zeta\Phi'(\zeta)/(\Phi(\zeta)-z)$, the classical generating function of the Faber polynomials of $\Phi$; correspondingly $F_0=1$ and $F_k$ has degree $k$ with leading coefficient $c^{-k}$. These polynomials are the basis in which matrix polynomials are expanded on the boundary curve $t\mapsto\Phi(e^{2\pi it})$.
--
--   **Formalization Note** The definitions are `localL`, `localW`, `localN`, `faberBasis` and `scalarGenerating` in the namespace `DirectCrouzeix.Faber`; `faberBasis c g k` is the finite sum of monomials `Polynomial.monomial j (taylorCoeff (fun u => localN c g u * localW c g u ^ j) k)` over `j ∈ Finset.range (k+1)`. Lean's conventions apply: `deriv g` is $0$ where $g$ is not differentiable, $0^{-1}=0$ and division by zero is $0$, and the Taylor coefficient is defined through iterated derivatives for every function. The simplification lemmas are `localL_zero`, `localW_zero`, `localN_zero` (assuming `c ≠ 0`) and `unitPoint_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def localL (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c+u*g u)⁻¹

def localW (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := u*localL c g u

def localN (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : ℂ := (c-u^2*deriv g u)*localL c g u

def faberBasis (c : ℂ) (g : ℂ → ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k+1), Polynomial.monomial j
    (taylorCoeff (fun u => localN c g u * localW c g u ^ j) k)

@[simp] theorem localL_zero (c : ℂ) (g : ℂ → ℂ) : localL c g 0 = c⁻¹ := by simp [localL]

@[simp] theorem localW_zero (c : ℂ) (g : ℂ → ℂ) : localW c g 0 = 0 := by simp [localW]

@[simp] theorem localN_zero {c : ℂ} (hc : c ≠ 0) (g : ℂ → ℂ) : localN c g 0 = 1 := by
  simp [localN,localL,hc]

def scalarGenerating (c : ℂ) (g : ℂ → ℂ) (z u : ℂ) : ℂ :=
  (c-u^2*deriv g u)/(c+u*(g u-z))

@[simp] theorem unitPoint_neg (t : Angle) : unitPoint (-t) = (unitPoint t)⁻¹ := by
  simp [unitPoint,fourier_apply,AddCircle.toCircle_neg,Circle.coe_inv]

end DirectCrouzeix.Faber

end

end

end OAI


