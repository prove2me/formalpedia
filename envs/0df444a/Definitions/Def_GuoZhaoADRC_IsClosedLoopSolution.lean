-- Prove2me | Definitions.Def_GuoZhaoADRC_IsClosedLoopSolution
-- name    : GuoZhaoADRC_IsClosedLoopSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:45.320981+00:00
-- url     : https://prove2.me/theorems/013ae296-6459-4ac0-9f75-787336c7807c
-- title:
--   Solutions on $[0,\infty)$ of the closed loop (3.3) with gain parameter $\varepsilon$
-- statement:
--   Let $\varepsilon>0$. Trajectories $x(t)\in\mathbb R^n$, $\xi(t)\in\mathbb R^s$ and $\hat x^i(t)\in\mathbb R^{n_i+1}$ form a **solution of the closed loop (3.3)** if at every $t\ge0$, with $e^i_1=(x^i_1-\hat x^i_1)/\varepsilon^{n_i}$, the virtual control $u^*_i$ and the control $u_k=\sum_lb^*_{kl}u^*_l$ of (3.2):
--
--   1. the plant (1.1): $\dot x^i_j=x^i_{j+1}$ ($1\le j<n_i$), $\dot x^i_{n_i}=f_i(x,\xi,w_i)+\sum_ka_{ik}u_k$, $\dot\xi=F_0(x,\xi,w)$;
--   2. the extended state observer (1.5):
--   $$\dot{\hat x}^i_j=\hat x^i_{j+1}+\varepsilon^{n_i-j}g^i_j(e^i_1)\ (1\le j<n_i),\quad \dot{\hat x}^i_{n_i}=\hat x^i_{n_i+1}+g^i_{n_i}(e^i_1)+u^*_i,\quad \dot{\hat x}^i_{n_i+1}=\frac1\varepsilon g^i_{n_i+1}(e^i_1).$$
--
--   The high gain of the observer is $1/\varepsilon$.
--
--   **Formalization Note** 0-based indices: the page's $\varepsilon^{n_i-j}$ is `ε ^ (n i - 1 - j.val)`. Derivatives are taken within $[0,\infty)$ (one-sided at $t=0$), and nothing is required for $t<0$. The initial value is free.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.3), p.1737; plant (1.1), p.1728; ESO (1.5), p.1729; ADRC(G) (3.2), p.1737

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_uStar
import Definitions.Def_GuoZhaoADRC_ctrl

namespace GuoZhaoADRC

/-- **A solution on `[0, ∞)` of the closed loop (3.3) with gain parameter `ε`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.3), p.1737 (plant (1.1), p.1728; ESO (1.5),
p.1729; ADRC(G) (3.2), p.1737).

Trajectories `x(t) ∈ ℝ^n`, `ξ(t) ∈ ℝ^s` and `x̂^i(t) ∈ ℝ^{n_i+1}` such that at every `t ≥ 0`,
with `e^i_1 = (x^i_1 − x̂^i_1)/ε^{n_i}`, `u*_i` and `u_k = ∑_l b*_kl u*_l` as in (3.2):
* `ẋ^i_j = x^i_{j+1}` (`1 ≤ j < n_i`), `ẋ^i_{n_i} = f_i(x, ξ, w_i) + ∑_k a_ik u_k`,
  `ξ̇ = F₀(x, ξ, w)`;
* `x̂^i_j' = x̂^i_{j+1} + ε^{n_i−j} g^i_j(e^i_1)` (`1 ≤ j < n_i`),
  `x̂^i_{n_i}' = x̂^i_{n_i+1} + g^i_{n_i}(e^i_1) + u*_i`,
  `x̂^i_{n_i+1}' = (1/ε) g^i_{n_i+1}(e^i_1)`.

**Formalization Note.** 0-based indices: the page's `j` is `j.val + 1`, so
`ε^{n_i − j}` is `ε ^ (n i - 1 - j.val)`. Derivatives are taken within `[0, ∞)` (one-sided
at `t = 0`); nothing is required for `t < 0`. The initial value is free. -/
def IsClosedLoopSolution {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) (ε : ℝ)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) : Prop :=
  ∀ t, 0 ≤ t →
    (∀ i (j : Fin (n i)) (h : j.val + 1 < n i),
      HasDerivWithinAt (fun τ => x τ ⟨i, j⟩) (x t ⟨i, ⟨j.val + 1, h⟩⟩) (Set.Ici 0) t) ∧
    (∀ i (j : Fin (n i)), j.val + 1 = n i →
      HasDerivWithinAt (fun τ => x τ ⟨i, j⟩)
        (D.f i (x t) (ξ t) (D.w t i) + ∑ k, D.a i k * ctrl D xhat k t) (Set.Ici 0) t) ∧
    HasDerivWithinAt ξ (D.F0 (x t) (ξ t) (D.w t)) (Set.Ici 0) t ∧
    (∀ i (j : Fin (n i + 1)) (h : j.val + 1 < n i),
      HasDerivWithinAt (fun τ => xhat τ i j)
        (xhat t i ⟨j.val + 1, by omega⟩ + ε ^ (n i - 1 - j.val) *
          D.g i j ((x t ⟨i, ⟨0, D.hn i⟩⟩ - xhat t i 0) / ε ^ n i)) (Set.Ici 0) t) ∧
    (∀ i (j : Fin (n i + 1)), j.val + 1 = n i →
      HasDerivWithinAt (fun τ => xhat τ i j)
        (xhat t i (Fin.last (n i)) +
          D.g i j ((x t ⟨i, ⟨0, D.hn i⟩⟩ - xhat t i 0) / ε ^ n i) + uStar D xhat i t)
        (Set.Ici 0) t) ∧
    (∀ i, HasDerivWithinAt (fun τ => xhat τ i (Fin.last (n i)))
        (1 / ε * D.g i (Fin.last (n i)) ((x t ⟨i, ⟨0, D.hn i⟩⟩ - xhat t i 0) / ε ^ n i))
        (Set.Ici 0) t)

end GuoZhaoADRC


