-- Prove2me | Definitions.Def_GPhNGIDiffusion_OccupationCLT_Jacobian
-- name    : GPhNGIDiffusion_OccupationCLT_Jacobian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:07.734789+00:00
-- url     : https://prove2.me/theorems/bc73e75f-e378-46de-981e-705683f9294d
-- title:
--   p. 14 — ∇g_ε, ∇g̃ and the Jacobians J_{s,t} as propagators of the linearized equation
-- statement:
--   1. $\nabla g_\varepsilon(x)$ is the derivative of the mollified drift; by (3.4) it equals $-R+\dot\rho_\varepsilon(e'x)(R-\alpha I)pe'$.
--   2. $\nabla\tilde g(x)=-R+\mathbf 1_{\{e'x>0\}}(R-\alpha I)pe'$, which equals $\nabla g(x)$ off the hyperplane $e'x=0$.
--   3. For a measurable family of matrices $(A(t))_{t\ge0}$, a **propagator** is a family $(J_{s,t})_{0\le s\le t}$ with $t\mapsto J_{s,t}$ continuous on $[s,\infty)$ and
--   $$
--   J_{s,t}=I+\int_s^tA(r)\,J_{s,r}\,dr,\qquad 0\le s\le t,
--   $$
--   that is, the solution of $\partial_tJ_{s,t}=A(t)J_{s,t}$, $J_{s,s}=I$.
--
--   The Jacobians of the paper are $J^{\varepsilon,x}_{s,t}$, the propagator for $A(r)=\nabla g_\varepsilon(X^{\varepsilon,x}_r)$, and $J^x_{s,t}$, the propagator for $A(r)=\nabla\tilde g(X^x_r)$; one writes $J_t=J_{0,t}$. Then $\nabla_uX^{\varepsilon,x}_t=J^{\varepsilon,x}_tu$ (3.7).
--
--   **Formalization Note** The paper writes $J^{\varepsilon,x}_{s,t}=\exp(\int_s^t\nabla g_\varepsilon(X^{\varepsilon,x}_r)dr)$ and $J^x_{s,t}=\exp(\int_s^t\nabla\tilde g(X^x_r)dr)$. A matrix exponential of an integral solves the linear equation only when the matrices $A(r)$ commute, which these do not for $d\ge2$; the paper itself uses the propagator properties (3.7) and $J_{r,t}J_r=J_t$. The propagator is the object for which (3.7), (3.9) and the statements built on it are true; the exponential formula would make Lemma 3.3 false in $d\ge2$. The equation has a unique continuous solution for every bounded measurable $A$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 13, (3.4); p. 14, (3.7) and the definitions of J^{ε,x}_{s,t}, ∇g̃, J^x_{s,t}

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Mollified

open scoped NNReal

namespace GPhNGIDiffusion.OccupationCLT

variable {d : ℕ}

/-- `∇g_ε(x)`, the derivative of the mollified drift (equal to `−R + ρ̇_ε(e′x)(R − αI)pe′`,
(3.4)). -/
noncomputable def Model.gradEps (M : Model d) (ε : ℝ) (x : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (M.gEps ε) x

/-- `∇g̃(x) = −R + 1{e′x > 0}(R − αI)pe′` (p. 14). -/
noncomputable def Model.gradTilde (M : Model d) (x : E d) : E d →L[ℝ] E d :=
  -mat M.R + (if 0 < eDot x then (1 : ℝ) else 0) • mat M.Q

/-- `J` is the propagator (fundamental solution) of the linear equation
`∂ₜ J_{s,t} = A(t) J_{s,t}`, `J_{s,s} = I`, on `0 ≤ s ≤ t`: for every `s`, the map
`t ↦ J_{s,t}` is continuous on `[s, ∞)` and `J_{s,t} = I + ∫ₛᵗ A(r) J_{s,r} dr`. -/
def IsPropagator (A : ℝ≥0 → E d →L[ℝ] E d) (J : ℝ≥0 → ℝ≥0 → E d →L[ℝ] E d) : Prop :=
  ∀ s : ℝ≥0,
    ContinuousOn (fun t : ℝ => J s t.toNNReal) (Set.Ici (s : ℝ)) ∧
    ∀ t : ℝ≥0, s ≤ t →
      J s t = 1 + ∫ r in (s : ℝ)..(t : ℝ), (A r.toNNReal).comp (J s r.toNNReal)

end GPhNGIDiffusion.OccupationCLT


