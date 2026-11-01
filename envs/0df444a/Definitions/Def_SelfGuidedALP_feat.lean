-- Prove2me | Definitions.Def_SelfGuidedALP_feat
-- name    : SelfGuidedALP_feat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:43.564987+00:00
-- url     : https://prove2.me/theorems/dc167a64-5394-42c2-99b2-fe61b7385cdb
-- title:
--   The basis function $\varphi(s;\theta)=\varphi(\theta^\top(1,s))$
-- statement:
--   For $\theta=(\theta_0,\theta_1,\dots,\theta_d)$ and $s\in\mathbb R^d$, the **basis function** is
--   $$
--   \varphi(s;\theta):=\varphi\bigl(\theta^\top(1,s)\bigr),\qquad \theta^\top(1,s):=\theta_0+\sum_{i=1}^d\theta_i s_i .
--   $$
--
--   It is the feature attached to a sampled parameter vector.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2.2, p.8

import Mathlib

namespace SelfGuidedALP

/-- The basis function `ϕ(s;θ) ≡ ϕ(θᵀ(1,s))`, where `θᵀ(1,s) := θ₀ + ∑ᵢ θᵢ sᵢ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, §2.2, p.8). -/
noncomputable def feat {d : ℕ} (ϕ : ℝ → ℝ) (θ : EuclideanSpace ℝ (Fin (d + 1))) (s : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ϕ (θ 0 + ∑ i : Fin d, θ i.succ * s i)

end SelfGuidedALP


