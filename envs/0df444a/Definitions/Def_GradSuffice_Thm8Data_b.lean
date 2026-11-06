-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_b
-- name    : GradSuffice_Thm8Data_b
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:52.879204+00:00
-- url     : https://prove2.me/theorems/f617ed7d-17d7-4e96-9a39-e9b25898fa40
-- title:
--   Offsets $b_{t,k}$
-- statement:
--   For $1\le t\le D$ and $1\le k\le\kappa$,
--   $$b_{t,k}:=-r\sum_{k'=1}^{k-1}s^{k'-k}+\frac{\theta}{64D}(D-t+1).$$
--
--   **Formalization Note** 0-based ($t$, $k$ here are the paper's $t-1$, $k-1$): $b_{t,k}=-r\sum_{j<k}s^{j-k}+\frac{\theta}{64D}(D-t)$, with integer powers of $s$. The index $t$ is a natural number so that the paper's $b_{1,k}$ is $b_{0,k}$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data
import Definitions.Def_GradSuffice_thm8R
import Definitions.Def_GradSuffice_thm8S

namespace GradSuffice

/-- **The offsets `b_{t,k}`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19:
`b_{t,k} := −r ∑_{k'=1}^{k−1} s^{k'−k} + (θ/(64D)) (D − t + 1)` for `1 ≤ t ≤ D`, `1 ≤ k ≤ κ`.

**Formalization Note.** 0-based (`t`, `k` here are the paper's `t − 1`, `k − 1`):
`b t k = −r ∑_{j < k} s^{j − k} + (θ/(64D)) (D − t)`, with integer powers of `s`. The index `t` is a
natural number so that `b 0 k` (the paper's `b_{1,k}`) can be written without a proof of `D ≥ 1`. -/
noncomputable def Thm8Data.b {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (t : ℕ) (k : Fin c.κ) : ℝ :=
  -(thm8R c.θ) * ∑ j ∈ Finset.univ.filter (fun j : Fin c.κ => j < k),
      thm8S c.θ ^ ((j : ℤ) - (k : ℤ)) +
    c.θ / (64 * c.D) * ((c.D : ℝ) - t)

end GradSuffice


