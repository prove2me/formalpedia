-- Prove2me | Definitions.Def_GenNewtonSubgrad_Composite_Alg76
-- name    : GenNewtonSubgrad_Composite_Alg76
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:43.362701+00:00
-- url     : https://prove2.me/theorems/8d384121-1e36-4c17-838f-0ac8b4b4e545
-- title:
--   Algorithm 7.6 — the Newton-type algorithm in nonconvex composite optimization (steps, runs, well-definedness)
-- statement:
--   This file encodes Algorithm 7.6 (p. 35) of Khanh, Mordukhovich and Phat for the composite problem (7.7), $\min\varphi(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha+g(x)$, with a parameter $\gamma>0$:
--
--   1. **Step 1.** If $0\in\partial\varphi(x^k)$, stop. Otherwise compute
--   $$u^k=x^k-\gamma(Ax^k+b),\qquad v^k\in\operatorname{Prox}_{\gamma g}(u^k).\tag{7.17}$$
--   2. **Step 2.** Choose $d^k$ with
--   $$-\frac1\gamma(x^k-v^k)-Ad^k\in\partial^2g\Big(v^k,\frac1\gamma(u^k-v^k)\Big)(x^k-v^k+d^k).\tag{7.18}$$
--   3. **Step 3.** Set $x^{k+1}=x^k+d^k$.
--
--   A *step* $x\mapsto x'$ is either the stop ($0\in\partial\varphi(x)$ and $x'=x$) or, when $0\notin\partial\varphi(x)$, a point $v$ of $\operatorname{Prox}_{\gamma g}(x-\gamma(Ax+b))$ together with $d=x'-x$ satisfying (7.18). A *run* is a sequence in which every consecutive pair is a step; the starting point is arbitrary. The algorithm is *well-defined from* $U$ if every finite partial run started in $U$ can be continued by one more step, i.e. the proximal point exists and (7.18) is solvable whenever the run has not stopped.
--
--   The algorithm needs only the proximal mapping and the second-order subdifferential of the regularizer $g$, never those of $\varphi$; these notions state the paper's main result, Theorem 7.8.
--
--   **Formalization Note** The proximal mapping is the argmin set, and a run may select any of its points; the direction may be any solution of (7.18). The stop test is on $\partial\varphi$ (Step 1), not on $v^k=x^k$. The parameter conditions of Step 0 ($\gamma\in(0,r^{-1})$, $I-\gamma A$ nonsingular) are hypotheses of the theorems, not part of the step.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 35, Algorithm 7.6, (7.17)–(7.18)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One step `xᵏ ↦ xᵏ⁺¹` of Algorithm 7.6, p. 35, for `φ = f + g` with `f = quadF A b α`.
With `u = xᵏ − γ(Axᵏ + b)`: stop (`xᵏ⁺¹ = xᵏ`) if `0 ∈ ∂φ(xᵏ)`; otherwise some
`v ∈ Prox_γg(u)` and `dᵏ = xᵏ⁺¹ − xᵏ` satisfy (7.18),
`−γ⁻¹(xᵏ − v) − A dᵏ ∈ ∂²g(v, γ⁻¹(u − v))(xᵏ − v + dᵏ)`. -/
def alg76Step (A : E →L[ℝ] E) (b : E) (α : ℝ) (g : E → EReal) (γ : ℝ) (x x' : E) : Prop :=
  (0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) x ∧ x' = x) ∨
    (0 ∉ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) x ∧
      ∃ v ∈ GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)),
        -(γ⁻¹ • (x - v)) - A (x' - x) ∈
          GenNewtonSubgrad.ProxReg.secondSubdiff g v (γ⁻¹ • ((x - γ • (A x + b)) - v)) (x - v + (x' - x)))

/-- A run of Algorithm 7.6 with parameter `γ`: every consecutive pair is a step. Step 0 takes any
starting point. -/
def IsAlg76Run (A : E →L[ℝ] E) (b : E) (α : ℝ) (g : E → EReal) (γ : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, alg76Step A b α g γ (x k) (x (k + 1))

/-- Algorithm 7.6 is well-defined from `U`: every partial run started in `U` can be continued
(the proximal point exists and (7.18) is solvable, unless the run has stopped). -/
def Alg76WellDefinedOn (A : E →L[ℝ] E) (b : E) (α : ℝ) (g : E → EReal) (γ : ℝ)
    (U : Set E) : Prop :=
  ∀ (N : ℕ) (x : ℕ → E), x 0 ∈ U → (∀ k < N, alg76Step A b α g γ (x k) (x (k + 1))) →
    ∃ x', alg76Step A b α g γ (x N) x'

end GenNewtonSubgrad.Composite


