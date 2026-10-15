-- Prove2me | Definitions.Def_GenNewtonSubgrad_ProxReg_Alg62
-- name    : GenNewtonSubgrad_ProxReg_Alg62
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:51.19423+00:00
-- url     : https://prove2.me/theorems/12048fdb-dd7a-473b-93c2-dee3449e6ee5
-- title:
--   Algorithm 6.2 — the prox-based generalized Newton step for subgradient inclusions, its runs, and well-definedness
-- statement:
--   Algorithm 6.2 solves $0\in\partial\varphi(x)$ for $\varphi:\mathbb R^n\to\overline{\mathbb R}$ with a parameter $\lambda>0$. It starts at $x^0\in U_\lambda=\operatorname{rge}(I+\lambda\partial\varphi)$. From $x^k$: if $0\in\partial\varphi(x^k)$ it stops; otherwise it computes
--   $$v^k=\frac1\lambda\big(x^k-\operatorname{Prox}_\lambda\varphi(x^k)\big)\qquad(6.4)$$
--   chooses any $d^k$ with
--   $$-v^k\in\partial^2\varphi(x^k-\lambda v^k,v^k)(\lambda v^k+d^k)\qquad(6.5)$$
--   and sets $x^{k+1}=x^k+d^k$.
--
--   1. A **step** $x\mapsto x'$ is either the stop ($0\in\partial\varphi(x)$ and $x'=x$) or, when $0\notin\partial\varphi(x)$, a choice of a proximal point $p\in\operatorname{Prox}_\lambda\varphi(x)$, with $v=\lambda^{-1}(x-p)$ (so $x-\lambda v=p$), such that $d=x'-x$ satisfies (6.5).
--   2. A **run** is a sequence starting in $U_\lambda$ whose consecutive terms are steps.
--   3. The algorithm is **well-defined from** $U$ if every finite partial run started in $U$ admits a further step: a proximal point exists and (6.5) is solvable at every iterate reached.
--
--   **Formalization Note.** $\operatorname{Prox}_\lambda\varphi(x)$ is a set and a run may select any of its points, so every statement about runs covers every selection and every direction $d^k$. The stop test is on $\partial\varphi(x^k)$, as printed, not on $v^k$. The base point of $\partial^2\varphi$ is written as the proximal point $p$, which equals $x^k-\lambda v^k$.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 26, Algorithm 6.2 ((6.3)–(6.5))

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope

namespace GenNewtonSubgrad.ProxReg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One step `x ↦ x'` of Algorithm 6.2 with parameter `λ = lam`: if `0 ∈ ∂φ(x)` the algorithm has
stopped and the run stays at `x`; otherwise some proximal point `p ∈ Prox_λφ(x)` gives
`v = λ⁻¹(x - p)` (6.4), and `d = x' - x` solves (6.5) `-v ∈ ∂²φ(p, v)(λv + d)`, where
`p = x - λv`. -/
def alg62Step (φ : E → EReal) (lam : ℝ) (x x' : E) : Prop :=
  (0 ∈ NonconvexSplitting.Shared.LimitingSubdiff φ x ∧ x' = x) ∨
    (0 ∉ NonconvexSplitting.Shared.LimitingSubdiff φ x ∧ ∃ p ∈ prox φ lam x,
      -(lam⁻¹ • (x - p)) ∈
        secondSubdiff φ p (lam⁻¹ • (x - p)) (lam • (lam⁻¹ • (x - p)) + (x' - x)))

/-- A run of Algorithm 6.2: the start lies in `U_λ` (6.3) and every consecutive pair of iterates
is a step. -/
def IsAlg62Run (φ : E → EReal) (lam : ℝ) (x : ℕ → E) : Prop :=
  x 0 ∈ rgeShift φ lam ∧ ∀ k, alg62Step φ lam (x k) (x (k + 1))

/-- Algorithm 6.2 is well-defined from `U`: every partial run started in `U` can be continued
(a proximal point exists and the Newton inclusion (6.5) is solvable at every iterate reached). -/
def Alg62WellDefinedOn (φ : E → EReal) (lam : ℝ) (U : Set E) : Prop :=
  ∀ (N : ℕ) (x : ℕ → E), x 0 ∈ U → (∀ k < N, alg62Step φ lam (x k) (x (k + 1))) →
    ∃ x', alg62Step φ lam (x N) x'

end GenNewtonSubgrad.ProxReg


