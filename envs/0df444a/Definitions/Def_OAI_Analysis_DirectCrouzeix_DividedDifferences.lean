-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
-- name    : OAI_Analysis_DirectCrouzeix_DividedDifferences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:37:01.349772+00:00
-- url     : https://prove2.me/theorems/bf61729e-eb45-44e2-87cf-f727a3dae973
-- title:
--   Integral divided differences, chord denominator and correction term of an exterior map $c\zeta+g(1/\zeta)$
-- statement:
--   Fix $c\in\mathbb{C}$ and a function $g:\mathbb{C}\to\mathbb{C}$, and write $g'$ and $g''$ for its first and second complex derivatives. For $u,v\in\mathbb{C}$ the module defines:
--
--   1. **Divided difference.**
--   $$
--   \delta g(u,v)=\int_0^1 g'\big((1-t)u+tv\big)\,dt .
--   $$
--
--   2. **Left derivative of the divided difference.**
--   $$
--   \delta_1 g(u,v)=\int_0^1 (1-t)\,g''\big((1-t)u+tv\big)\,dt .
--   $$
--
--   3. **Chord denominator.** $H(u,v)=c-uv\,\delta g(u,v)$.
--
--   4. **Correction term.**
--   $$
--   Q(u,v)=\frac{uv\,\big(\delta g(u,v)+u\,\delta_1 g(u,v)\big)}{H(u,v)} .
--   $$
--   The rules $Q(0,v)=0$ and $Q(u,0)=0$ hold for all $c$, $g$, $u$, $v$ and are recorded as simplification lemmas.
--
--   5. **Exterior map.** $\Phi(\zeta)=c\,\zeta+g(1/\zeta)$ for $\zeta\in\mathbb{C}$.
--
--   If $g$ is holomorphic on an open convex set $s$ containing $u$ and $v$, then $\delta g(u,v)=\frac{g(u)-g(v)}{u-v}$ for $u\ne v$, $\delta g(u,u)=g'(u)$, and $\delta_1g(u,v)$ is the derivative of $\delta g(\cdot,v)$ at $u$. For $u,v\ne0$ with $u\ne v$ one gets $H(u,v)=\frac{\Phi(1/u)-\Phi(1/v)}{1/u-1/v}$, and on the diagonal $H(u,u)=c-u^{2}g'(u)$, which equals $\Phi'(1/u)$ when $u\ne0$; so $H\ne0$ encodes injectivity of $\Phi$ and nonvanishing of $\Phi'$. If moreover $v\ne0$, $u\ne v$ and $H(u,v)\ne0$, the correction term satisfies
--   $$
--   Q(u,v)=\frac{c-u^{2}g'(u)}{c+u\big(g(u)-\Phi(1/v)\big)}-\frac{1}{1-u/v},
--   $$
--   the difference between the generating function $\frac{c-u^{2}g'(u)}{c+u(g(u)-z)}$ of the Faber polynomials of $\Phi$, taken at the point $z=\Phi(1/v)$, and a geometric series in $u/v$. These facts are proved in the module and drive the boundary analysis of Faber polynomials.
--
--   **Formalization Note** In Lean `deriv g` is $0$ at points where $g$ is not differentiable, `ζ⁻¹` is $0$ for $\zeta=0$ (so $\Phi(0)=g(0)$), and division by zero gives $0$, so $Q(u,v)=0$ whenever $H(u,v)=0$. The integrals are chord integrals over the parameter interval $[0,1]$ with weights $1$ and $1-t$. The definitions are `divided`, `dividedLeft`, `chordDenominator`, `correction` and `exterior` in the namespace `DirectCrouzeix.Faber`, with simplification lemmas `correction_zero_left` and `correction_zero_right`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DividedDifferences.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DividedDifferences.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def divided (g : ℂ → ℂ) (u v : ℂ) : ℂ := chordIntegral (deriv g) (fun _ => 1) u v

def dividedLeft (g : ℂ → ℂ) (u v : ℂ) : ℂ :=
  chordIntegral (deriv (deriv g)) (fun t => (1-(t:ℝ) : ℝ)) u v

def chordDenominator (c : ℂ) (g : ℂ → ℂ) (u v : ℂ) : ℂ := c-u*v*divided g u v

def correction (c : ℂ) (g : ℂ → ℂ) (u v : ℂ) : ℂ :=
  u*v*(divided g u v+u*dividedLeft g u v) / chordDenominator c g u v

@[simp] theorem correction_zero_left (c : ℂ) (g : ℂ → ℂ) (v : ℂ) : correction c g 0 v = 0 := by
  simp [correction]

@[simp] theorem correction_zero_right (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : correction c g u 0 = 0 := by
  simp [correction]

def exterior (c : ℂ) (g : ℂ → ℂ) (ζ : ℂ) := c*ζ+g ζ⁻¹

end DirectCrouzeix.Faber

end

end

end OAI


