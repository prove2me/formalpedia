-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_splitPerturbation
-- name    : RockafellianRelax_Supplement_splitPerturbation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:14:02.485599+00:00
-- url     : https://prove2.me/theorems/8a6e9325-462c-5cd1-872d-f150da309458
-- title:
--   The components $(u,v)$ of a perturbation in $\mathbb R^{s+sm}$
-- statement:
--   A vector $w \in \mathbb R^{s+sm}$ is read as a pair
--
--   $$
--   w = (u, v),\qquad u \in \mathbb R^s,\quad v = (v_1,\dots,v_s),\ v_i \in \mathbb R^m .
--   $$
--
--   The component $u$ perturbs the probabilities and each $v_i$ perturbs the support point $\xi_i$. The map is a bijection, so $w = 0$ exactly when $u = 0$ and $v = 0$.
--
--   **Formalization Note** The perturbation stays one vector indexed by `Fin (s + s * m)`, so that the published exactness definitions apply to the functions of Theorem 4.5.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §4.2, Refinement B, p.16 (the perturbation space)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **The components `(u, v)` of a perturbation in `ℝ^{s+sm}`.**
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §4.2, Refinement B, p.16: "f : ℝ^{s+sm} × ℝⁿ → R̄", with arguments `((u, v), x)`,
`u ∈ ℝˢ` and `v = (v₁, …, v_s) ∈ ℝ^{sm}`.

**Formalization Note.** The perturbation is one vector `w : Fin (s + s * m) → ℝ`, so that the
published exactness definitions apply. Its first `s` coordinates are `u`, and the remaining `s * m`
are the blocks `vᵢ ∈ ℝᵐ`, through `finProdFinEquiv`. The map is a bijection, so `w = 0` exactly
when `u = 0` and `v = 0`. -/
def splitPerturbation {s m : ℕ} (w : Fin (s + s * m) → ℝ) : (Fin s → ℝ) × (Fin s → Fin m → ℝ) :=
  (fun i => w (Fin.castAdd (s * m) i), fun i j => w (Fin.natAdd s (finProdFinEquiv (i, j))))

end RockafellianRelax.Supplement


