-- Prove2me | Definitions.Def_DCAExtrap_IsDCAeRun
-- name    : DCAExtrap_IsDCAeRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:23.686814+00:00
-- url     : https://prove2.me/theorems/3c73bd69-eb18-462c-8027-03fbe63bfc15
-- title:
--   A run of DCAe (Algorithm 1)
-- statement:
--   Let $f,g,h,\varphi,L,l$ be as in problem (1) and $\delta\in(0,1)$. Sequences $(x^k)$, $(\beta_k)$, $(\xi^k)$ in $E$, $\mathbb R$, $E$ form a **run of DCAe** when, for every $k=0,1,\dots$, with $y^k=x^k+\beta_k(x^k-x^{k-1})$ and $x^{-1}=x^0$:
--
--   1. the extrapolation parameter satisfies (8):
--   $$
--   (L+l)\,D_\varphi(x^k,y^k)\le \delta L\,D_\varphi(x^{k-1},x^k);
--   $$
--   2. $\xi^k\in\partial h(x^k)$;
--   3. $x^{k+1}$ solves the convex subproblem (9):
--   $$
--   x^{k+1}\in\operatorname*{argmin}_{x\in E}\Bigl\{G(x)-\bigl\langle L\nabla\varphi(y^k)-\nabla f(y^k)+\xi^k,\,x\bigr\rangle\Bigr\},\qquad G=L\varphi+g.
--   $$
--
--   Every choice of $\beta_k$ satisfying (8), of $\xi^k$ and of a minimizer is a run; the starting point $x^0$ is arbitrary.
--
--   **Formalization Note** The page prints $\langle L\varphi(y^k)-\nabla f(y^k)+\xi^k,x\rangle$ in (9); the text above Algorithm 1 writes $\nabla L\varphi(y^k)$ and the proof of Theorem 3.1 writes $L\nabla\varphi(y^k)$, so the gradient is restored. $\beta_k$ has no constraint other than (8), as in Algorithm 1. The subproblem is `EReal`-valued and minimized over all of $E$. The parameter $\delta\in(0,1)$ is part of the run.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, §3.1 and Algorithm 1, p.5, (8), (9)

import Mathlib
import Definitions.Def_DCAExtrap_bregman
import Definitions.Def_DCAExtrap_convexSubdiff
import Definitions.Def_DCAExtrap_objG
import Definitions.Def_DCAExtrap_prev
import Definitions.Def_DCAExtrap_extrap

open scoped InnerProductSpace

namespace DCAExtrap

/-- **A run of DCAe** (Phan–Le Thi, arXiv:2106.04743v1, Algorithm 1, (8), (9), p.5). Given
`f, g, h, φ`, constants `L, l` and `δ ∈ (0, 1)`, the iterates `x^k`, extrapolation parameters
`β_k` and subgradients `ξ^k` form a run when, for every `k = 0, 1, …`, with
`y^k = x^k + β_k (x^k − x^{k−1})` and `x^{−1} = x^0`:
1. (8) `(L + l) D_φ(x^k, y^k) ≤ δ L D_φ(x^{k−1}, x^k)`;
2. `ξ^k ∈ ∂h(x^k)`;
3. (9) `x^{k+1}` is a minimizer over `E` of the convex subproblem
   `x ↦ G(x) − ⟨L∇φ(y^k) − ∇f(y^k) + ξ^k, x⟩`, where `G = Lφ + g`.

**Formalization Note.** The starting point `x^0` is arbitrary (the paper does not assume
`x^0 ∈ dom g`). `β_k` is any real satisfying (8): Algorithm 1 imposes no other constraint on it.
Every choice of `β_k`, of `ξ^k ∈ ∂h(x^k)` and of a minimizer `x^{k+1}` of (9) is allowed. The
page prints `⟨Lφ(y^k) − ∇f(y^k) + ξ^k, x⟩` in (9); `Lφ(y^k)` is a real number where a vector is
required, and the text above Algorithm 1 and the proof of Theorem 3.1 use `∇Lφ(y^k) = L∇φ(y^k)`,
which is what is encoded. The subproblem is `EReal`-valued (`G` may be `+∞`) and minimised over
all of `E` (`IsMinOn … Set.univ`). -/
structure IsDCAeRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → EReal) (h : E → ℝ) (φ : E → ℝ) (L l δ : ℝ)
    (x : ℕ → E) (β : ℕ → ℝ) (ξ : ℕ → E) : Prop where
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  extrap_cond : ∀ k, (L + l) * bregman φ (x k) (extrap x β k) ≤ δ * L * bregman φ (prev x k) (x k)
  ξ_mem : ∀ k, ξ k ∈ convexSubdiff (fun y => ((h y : ℝ) : EReal)) (x k)
  isMin : ∀ k, IsMinOn
    (fun u => objG φ g L u -
      ((⟪L • gradient φ (extrap x β k) - gradient f (extrap x β k) + ξ k, u⟫_ℝ : ℝ) : EReal))
    Set.univ (x (k + 1))

end DCAExtrap


