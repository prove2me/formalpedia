-- Prove2me | Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
-- name    : GenNewtonSubgrad_ProxReg_Alg53
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:59.514362+00:00
-- url     : https://prove2.me/theorems/9825f40c-7a66-4ad8-a9c8-a278f38c69ad
-- title:
--   Algorithm 5.3 — the generalized Newton step for $C^{1,1}$ functions, its runs, and well-definedness
-- statement:
--   Algorithm 5.3 solves $\nabla\varphi(x)=0$ for $\varphi:\mathbb R^n\to\mathbb R$ of class $C^{1,1}$ around a solution. From $x^k$: if $\nabla\varphi(x^k)=0$ it stops; otherwise it chooses any direction $d^k$ with
--   $$-\nabla\varphi(x^k)\in\partial\langle d^k,\nabla\varphi\rangle(x^k)\qquad(5.3)$$
--   and sets $x^{k+1}=x^k+d^k$.
--
--   1. A **step** $x\mapsto x'$ is either the stop ($\nabla\varphi(x)=0$ and $x'=x$) or a Newton step ($\nabla\varphi(x)\neq0$ and $d=x'-x$ satisfies (5.3)).
--   2. A **run** is a sequence $(x^k)$ whose consecutive terms are steps; after a stop the sequence stays constant.
--   3. The algorithm is **well-defined from** $U$ if every finite partial run started in $U$ admits a further step.
--
--   A run is any sequence the algorithm may produce: every choice of the directions is allowed.
--
--   **Formalization Note.** Here $\partial\langle d,\nabla\varphi\rangle(x)$ is the limiting subdifferential of the real function $z\mapsto\langle d,\nabla\varphi(z)\rangle$ (published `LimitingSubdiff`); it is continuous near $\bar x$ when $\varphi$ is $C^{1,1}$ there, so the analytic and geometric subdifferentials agree. The stop of Step 1 is encoded as a constant tail.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 18, Algorithm 5.3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open scoped InnerProductSpace

namespace GenNewtonSubgrad.ProxReg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One step `x ↦ x'` of Algorithm 5.3 for `φ : E → ℝ`: if `∇φ(x) = 0` the algorithm has
stopped and the run stays at `x`; otherwise `d = x' - x` solves the Newton inclusion (5.3)
`-∇φ(x) ∈ ∂⟨d, ∇φ⟩(x)`. -/
def alg53Step (φ : E → ℝ) (x x' : E) : Prop :=
  (gradient φ x = 0 ∧ x' = x) ∨
    (gradient φ x ≠ 0 ∧ -gradient φ x ∈
      NonconvexSplitting.Shared.LimitingSubdiff (fun z => ((⟪x' - x, gradient φ z⟫_ℝ : ℝ) : EReal)) x)

/-- A run of Algorithm 5.3: every consecutive pair of iterates is a step. -/
def IsAlg53Run (φ : E → ℝ) (x : ℕ → E) : Prop :=
  ∀ k, alg53Step φ (x k) (x (k + 1))

/-- Algorithm 5.3 is well-defined from `U`: every partial run started in `U` can be continued. -/
def Alg53WellDefinedOn (φ : E → ℝ) (U : Set E) : Prop :=
  ∀ (N : ℕ) (x : ℕ → E), x 0 ∈ U → (∀ k < N, alg53Step φ (x k) (x (k + 1))) →
    ∃ x', alg53Step φ (x N) x'

end GenNewtonSubgrad.ProxReg


