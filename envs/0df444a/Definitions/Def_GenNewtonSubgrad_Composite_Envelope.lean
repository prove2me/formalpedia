-- Prove2me | Definitions.Def_GenNewtonSubgrad_Composite_Envelope
-- name    : GenNewtonSubgrad_Composite_Envelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:48.996046+00:00
-- url     : https://prove2.me/theorems/012eb3af-0afa-41b3-957f-33cd22dd5a20
-- title:
--   (6.1), (6.2), (7.2), (7.7) — Moreau envelope, proximal mapping, quadratic composite cost, forward-backward envelope, B = I − γA
-- statement:
--   This file defines the envelopes and the composite data of §§6–7 of Khanh, Mordukhovich and Phat. $E$ is a real inner product space and $\overline{\mathbb R}=[-\infty,+\infty]$.
--
--   1. **Moreau envelope and proximal mapping** (Definition 6.1, (6.1)–(6.2)). For $\varphi:E\to\overline{\mathbb R}$ and $\lambda>0$,
--   $$e_\lambda\varphi(x)=\inf_{y\in E}\Big\{\varphi(y)+\frac1{2\lambda}\|y-x\|^2\Big\},\qquad \operatorname{Prox}_{\lambda\varphi}(x)=\operatorname*{argmin}_{y\in E}\Big\{\varphi(y)+\frac1{2\lambda}\|y-x\|^2\Big\}.$$
--   The proximal mapping is the set of minimizers; it may be empty or contain several points.
--   2. **Quadratic composite cost** ((7.7)). For a continuous linear $A:E\to E$, $b\in E$, $\alpha\in\mathbb R$, the quadratic is $f(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha$, and the cost is $\varphi=f+g$ for $g:E\to\overline{\mathbb R}$, i.e. $\varphi(x)=f(x)+g(x)$.
--   3. **Forward-backward envelope** (Definition 7.1, (7.2)). For $f:E\to\mathbb R$, $g:E\to\overline{\mathbb R}$ and $\gamma>0$,
--   $$\varphi_\gamma(x)=\inf_{y\in E}\Big\{f(x)+\langle\nabla f(x),y-x\rangle+g(y)+\frac1{2\gamma}\|y-x\|^2\Big\}.$$
--   4. **The shifted operator** of Proposition 7.3 and Algorithm 7.6: $B=I-\gamma A$, and $B^{-1}$ its inverse when $B$ is nonsingular.
--
--   The forward-backward envelope turns the nonsmooth composite problem $\min f+g$ into the smooth problem $\min\varphi_\gamma$, on which the paper runs its $C^{1,1}$ Newton method.
--
--   **Formalization Note** All infima are taken in the extended reals (`EReal`), so the envelopes may be $\pm\infty$; statements that differentiate them first assert finiteness and then differentiate the real-valued function $x\mapsto\varphi_\gamma(x)$. $\nabla f$ is Mathlib's `gradient`. The definition (7.2) is used literally; the identity (7.3) $\varphi_\gamma(x)=f(x)-\frac\gamma2\|\nabla f(x)\|^2+e_\gamma g(x-\gamma\nabla f(x))$ is a fact, not a definition. In the theorems $E=\mathbb R^n$, and a symmetric matrix $A$ is a self-adjoint operator on $\mathbb R^n$ (hypothesis `IsSelfAdjoint A`). $B^{-1}$ is `Function.invFun B`, which is the two-sided inverse of $B$ whenever $B$ is bijective, the only case in which it is used.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 26, Definition 6.1, (6.1)–(6.2); p. 31, Definition 7.1, (7.1)–(7.2); pp. 32–33, (7.7), Proposition 7.3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic `f(x) = ½⟨Ax, x⟩ + ⟨b, x⟩ + α` of (7.7), p. 32. -/
noncomputable def quadF (A : E →L[ℝ] E) (b : E) (α : ℝ) : E → ℝ :=
  fun x => (1 / 2) * ⟪A x, x⟫_ℝ + ⟪b, x⟫_ℝ + α

/-- The sum `φ = f + g` of a real-valued `f` and an extended-real-valued `g`, (7.1). -/
noncomputable def sumFn (f : E → ℝ) (g : E → EReal) : E → EReal :=
  fun x => (f x : EReal) + g x

/-- The forward-backward envelope (7.2), p. 31:
`φ_γ(x) = inf_y { f(x) + ⟨∇f(x), y − x⟩ + g(y) + ‖y − x‖² / (2γ) }`. -/
noncomputable def fbe [CompleteSpace E] (f : E → ℝ) (g : E → EReal) (γ : ℝ) (x : E) : EReal :=
  ⨅ y, ((f x + ⟪gradient f x, y - x⟫_ℝ : ℝ) : EReal) + g y +
    ((‖y - x‖ ^ 2 / (2 * γ) : ℝ) : EReal)

/-- The shifted operator `B = I − γA` of Proposition 7.3 and Algorithm 7.6. -/
def shiftOp (A : E →L[ℝ] E) (γ : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - γ • A

/-- `B⁻¹` for `B = I − γA`, as `Function.invFun B`; it is the two-sided inverse of `B` whenever
`B` is bijective, which is the only case in which it is used. -/
noncomputable def shiftInv (A : E →L[ℝ] E) (γ : ℝ) : E → E :=
  Function.invFun (shiftOp A γ)

end GenNewtonSubgrad.Composite


