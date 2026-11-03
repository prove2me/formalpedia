-- Prove2me | Definitions.Def_PLIAG_Phik
-- name    : PLIAG_Phik
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:24.680703+00:00
-- url     : https://prove2.me/theorems/dd379069-8f0c-4083-873c-e1ea43a2276d
-- title:
--   PLIAG subproblem objective $\Phi_k$ of (3.1)
-- statement:
--   At iteration $k$, with a nonempty block $\mathcal J_k\subseteq\mathcal N$, its complement $\mathcal I_k=\mathcal N\setminus\mathcal J_k$, delays $\tau_k^j$ and step size $\alpha$, the PLIAG subproblem minimizes
--
--   $$
--   \Phi_k(x):=h(x)+\sum_{i\in\mathcal I_k}f_i(x)+\Big\langle\sum_{j\in\mathcal J_k}\nabla f_j\big(x_{k-\tau_k^j}\big),\,x\Big\rangle+\frac1{\alpha}D_w(x,x_k).
--   $$
--
--   The components in $\mathcal J_k$ are linearized at delayed iterates (incremental aggregated gradients), the others are kept exactly, and the Bregman distance to the current iterate is the proximal term.
--
--   **Formalization Note** Components are indexed by `Fin N`, $\mathcal J_k$ is `J k : Finset (Fin N)` and $\mathcal I_k$ its complement; the delays are `τd k j`. The index $k-\tau_k^j$ uses truncated subtraction in $\mathbb N$, which encodes the paper's convention $x_k=x_0$ for $k<0$. Values are in `EReal`; since $D_w(x,x_k)=+\infty$ off $\operatorname{dom}w$, minimizing over $\mathcal Q$ or over $\mathbb R^d$ is the same, as the paper notes.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, (3.1), §3, p.8

import Mathlib
import Definitions.Def_PLIAG_bregman

namespace PLIAG

/-- **The PLIAG subproblem objective `Φ_k`** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, (3.1), p.8):
`Φ_k(y) := h(y) + Σ_{i ∈ I_k} f_i(y) + ⟨Σ_{j ∈ J_k} ∇f_j(x_{k − τ_k^j}), y⟩ + (1/α) D_w(y, x_k)`,
with `I_k` the complement of `J_k` in `{1, …, N}`, delays `τ_k^j` and step size `α`.

**Formalization Note.** Components are indexed by `Fin N`, `J k : Finset (Fin N)` and
`I_k = (J k)ᶜ`; the delays are `τd k j`. The index `k − τ_k^j` is truncated subtraction in `ℕ`,
which encodes the paper's convention `x_k = x_0` for `k < 0`. `∇f_j` is the gradient of the real
function `(f_j ·).toReal`, used at iterates in `int dom w ⊆ dom f_j`. Values are `EReal`;
`D_w(y, x_k) = +∞` off `dom w`, so minimizing over `Q = cl dom w` or over `ℝ^d` is the same, as
the paper notes (p.8). The step `α` is the step used at iteration `k`. -/
noncomputable def Phik {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ) (α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (y : EuclideanSpace ℝ (Fin d)) : EReal :=
  h y + ∑ i ∈ (J k)ᶜ, f i y +
    ((inner ℝ (∑ j ∈ J k, gradient (fun z => (f j z).toReal) (x (k - τd k j))) y : ℝ) : EReal) +
    ((1 / α : ℝ) : EReal) * bregman w y (x k)

end PLIAG


