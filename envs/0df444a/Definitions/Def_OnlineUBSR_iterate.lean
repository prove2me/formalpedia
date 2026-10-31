-- Prove2me | Definitions.Def_OnlineUBSR_iterate
-- name    : OnlineUBSR_iterate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:00.928908+00:00
-- url     : https://prove2.me/theorems/c028a3a5-0feb-40ae-a620-ad217da1ca5b
-- title:
--   The projected stochastic approximation iterates $t_n$ of (5)
-- statement:
--   Let $\ell$ be a loss, $\lambda$ a risk level, $t_l,t_u$ the projection bounds, $t_0\in\mathbb R$ a starting point, $(a_k)_{k\ge1}$ step sizes and $\xi_1,\xi_2,\dots$ samples. The estimator of shortfall risk is the recursion
--
--   $$
--   t_n=\Gamma\big(t_{n-1}+a_n\,\hat g(t_{n-1})\big),\qquad \hat g(t)=\ell(\xi_n-t)-\lambda,\qquad n\ge1,
--   $$
--
--   where $\Gamma$ is the projection onto $[t_l,t_u]$. Each step uses one fresh sample $\xi_n$ to form an unbiased estimate $\hat g(t_{n-1})$ of $g(t_{n-1})$, so the scheme estimates $SR_\lambda(X)$ online from streaming i.i.d. samples of $-X$.
--
--   **Formalization Note** `iterate ℓ lam tl tu t₀ a ξ n ω` is $t_n$ on the sample path $\omega$, with $t_0$ a deterministic real number and `ξ (n+1)` the sample that forms $t_{n+1}$; `ξ 0` and `a 0` are never read. The step sequence is arbitrary here; Theorem 1 uses $a_k=c/k$.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §4, eq. (5), p.4

import Mathlib
import Definitions.Def_OnlineUBSR_proj

namespace OnlineUBSR

/-- **The projected stochastic approximation recursion (5) for shortfall risk.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §4, (5), p.4: "tn = Γ(tn−1 +
an(ĝ(tn−1))), (5) where ĝ(t) = ℓ(ξn − t) − λ is an estimate of g(t) using an i.i.d. sequence
{ξi} from the distribution of −X, and Γ is a projection operator defined by
Γ(x) = min(max(tl, x), tu)."

`iterate ℓ lam tl tu t₀ a ξ n ω` is `t_n` along the sample path `ω`:
`t_0 = t₀` and `t_{n+1} = Γ(t_n + a_{n+1} (ℓ(ξ_{n+1}(ω) − t_n) − lam))`.

**Formalization Note.** The step sequence `a : ℕ → ℝ` is arbitrary here; Theorem 1 takes
`a k = c / k`. Samples are indexed from `1`, as on the page: `ξ (n+1)` is used to form
`t_{n+1}`, and `ξ 0` and `a 0` are never read. The initial point `t₀` is a deterministic real
number. -/
def iterate {Ω : Type*} (ℓ : ℝ → ℝ) (lam tl tu t₀ : ℝ) (a : ℕ → ℝ) (ξ : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun _ => t₀
  | n + 1 => fun ω =>
      proj tl tu (iterate ℓ lam tl tu t₀ a ξ n ω +
        a (n + 1) * (ℓ (ξ (n + 1) ω - iterate ℓ lam tl tu t₀ a ξ n ω) - lam))

end OnlineUBSR


