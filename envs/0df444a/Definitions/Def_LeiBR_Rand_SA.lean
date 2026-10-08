-- Prove2me | Definitions.Def_LeiBR_Rand_SA
-- name    : LeiBR_Rand_SA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:38.478895+00:00
-- url     : https://prove2.me/theorems/81cb3a8c-38f7-4015-bfa8-be487c544440
-- title:
--   (SA$_{i,k}$) — projected stochastic gradient steps for the proximal best-response problem
-- statement:
--   At a major iteration $k$, given the profile $y_k$, player $i$ approximates its proximal best response $\widehat x_i(y_k)$ by projected stochastic gradient steps. Starting from $z_{i,1} = x_{i,k}$, for $t = 1, 2, \dots$
--   $$z_{i,t+1} = \Pi_{X_i}\Big[z_{i,t} - \gamma_t\, G_i(z_{i,t}, y_k, \xi^t_{i,k})\Big], \qquad \gamma_t = \frac{1}{\mu(t+1)},$$
--   where $\xi^t_{i,k}$ is the $t$-th sample, $\Pi_{X_i}$ is the Euclidean projection onto $X_i$ and
--   $$G_i(z, y, \xi) = \nabla_{x_i}\psi_i(z, y_{-i}; \xi) + \mu(z - y_i)$$
--   is a sampled gradient of the proximal objective $z \mapsto f_i(z, y_{-i}) + \frac{\mu}{2}\|z - y_i\|^2$.
--
--   After $j_{i,k}$ steps the player reports $z_{i, j_{i,k}}$ as its inexact best response.
--
--   **Formalization Note** `saIter proj dir mu z1 t` is $z_t$, with `dir t` the stochastic direction used at step $t$ (it carries the sample $\xi^t$); index $0$ is unused and equals $z_1$. `saDir` is $G_i$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 10, (SA_{i,k}); p. 15, §4.3

import Mathlib
import Definitions.Def_LeiBR_Rand_Game

namespace LeiBR.Rand

/-- The projected stochastic-gradient iterates of (SA_{i,k}) on `ℝ^m`:
`z_1 = z1` and, for `t ≥ 1`,
`z_{t+1} = Π[z_t − γ_t G_t(z_t)]` with `γ_t = 1/(µ(t+1))`,
where `G_t` is the stochastic direction used at step `t` (it carries the sample `ξ^t`).
The value at index `0` is unused and set to `z1`. -/
noncomputable def saIter {m : ℕ} (proj : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (dir : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (mu : ℝ)
    (z1 : EuclideanSpace ℝ (Fin m)) : ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => z1
  | 1 => z1
  | (t + 2) => proj (saIter proj dir mu z1 (t + 1) -
      (1 / (mu * (((t + 1 : ℕ) : ℝ) + 1))) • dir (t + 1) (saIter proj dir mu z1 (t + 1)))

/-- Player `i`'s stochastic direction in (SA_{i,k}) at the profile `y = y_k` and sample `s`:
`G_i(z, y, s) = ∇_{x_i} ψ_i(z, y_{-i}; s) + µ(z − y_i)`. -/
noncomputable def saDir {N : ℕ} {n : Fin N → ℕ} {d : ℕ}
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (mu : ℝ) (i : Fin N)
    (y : LeiBR.Sync.Profile n) (s : EuclideanSpace ℝ (Fin d)) (z : LeiBR.Sync.Strat n i) : LeiBR.Sync.Strat n i :=
  gψ i (Function.update y i z) s + mu • (z - y i)

end LeiBR.Rand


