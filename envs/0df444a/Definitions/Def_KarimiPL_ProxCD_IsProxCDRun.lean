-- Prove2me | Definitions.Def_KarimiPL_ProxCD_IsProxCDRun
-- name    : KarimiPL_ProxCD_IsProxCDRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:56.412808+00:00
-- url     : https://prove2.me/theorems/5ef2116e-ba81-4f86-9f01-4397ed1fe5f1
-- title:
--   A run of randomized proximal coordinate descent, indexed by coordinate histories
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Let $L \in \mathbb{R}$ and $x_0 \in \mathbb{R}^d$. For each $k \ge 0$ and each history $s = (i_0, \dots, i_{k-1}) \in \{1,\dots,d\}^k$ of chosen coordinates, let $x_k(s) \in \mathbb{R}^d$. The family is a **run of proximal coordinate descent (16) from $x_0$** if $x_0(\emptyset) = x_0$ and, for every $k$ and every history $s = (i_0, \dots, i_k)$ of length $k + 1$,
--   $$x_{k+1}(s) = x_k(i_0, \dots, i_{k-1}) + \alpha^* e_{i_k}, \qquad \alpha^* \in \operatorname*{argmin}_\alpha \Big[\alpha \nabla_{i_k} f(x_k) + \frac L2 \alpha^2 + g_{i_k}(x_{k,i_k} + \alpha) - g_{i_k}(x_{k,i_k})\Big].$$
--   When $i_0, i_1, \dots$ are drawn independently and uniformly, $x_k$ is the random iterate of the method and $x_k(s)$ its value on the history $s$.
--
--   **Formalization Note** The run is required along every one of the $d^k$ histories, because Theorem 6's expectation averages over all of them. Every step uses the same $L$ (step size $1/L$) as the smoothness and proximal-PL inequalities. Existence of each coordinate minimizer is part of the hypothesis, only at points the run visits; no closedness of $g_i$ is assumed. Histories are `Fin k → Fin d`; the last coordinate of a history of length $k+1$ is $i_k$ and its initial segment is $(i_0, \dots, i_{k-1})$.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4.3, eq. (16) and Theorem 6, p. 10

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_IsCoordProxStep

namespace KarimiPL.ProxCD

/-- **A run of randomized proximal coordinate descent (16), indexed by coordinate histories.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §4.3, eq. (16) and Theorem 6, p. 10: "the coordinate-wise proximal-gradient update rule
(16) […] when ik is selected uniformly at random".

`x k s` is the iterate `x_k` produced when the coordinates chosen at steps `0, …, k − 1` are
`s = (s 0, …, s (k − 1)) = (i₀, …, i_{k−1})`. `IsProxCDRun f gc Dc L x0 x` says: `x 0 s = x0`
(the empty history), and for every `k` and every history `s` of length `k + 1`, `x (k + 1) s` is
obtained from `x k (Fin.init s)` by one step (16) in the coordinate `i_k = s (Fin.last k)`.

**Formalization Note.** The randomness of `i_k` is represented by indexing the iterates by every
possible history: `x_k` is a deterministic function of `(i₀, …, i_{k−1})`, and the run is
required along **all** `d^k` histories (the expectation in Theorem 6 averages over all of them).
Each step uses the same `L` as the smoothness inequality and the proximal-PL inequality (step size
`1/L`). Existence of each coordinate minimizer is part of the hypothesis, only at the points the
run visits; no closedness of `gᵢ` is assumed. The initial point is free here; the theorems
require `x0 ∈ dom g`. -/
def IsProxCDRun {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (gc : Fin d → ℝ → ℝ)
    (Dc : Fin d → Set ℝ) (L : ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (x : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ s, x 0 s = x0) ∧
    ∀ (k : ℕ) (s : Fin (k + 1) → Fin d),
      IsCoordProxStep f gc Dc L (s (Fin.last k)) (x k (Fin.init s)) (x (k + 1) s)

end KarimiPL.ProxCD


