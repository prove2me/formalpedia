-- Prove2me | Definitions.Def_MarkdownReadjust_rhoD
-- name    : MarkdownReadjust_rhoD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:39.957208+00:00
-- url     : https://prove2.me/theorems/ad3efec3-f3c4-498f-8074-9a9bd5704f99
-- title:
--   Fluid purchase rate $\rho^d=\min\{x_0/(\lambda T),\bar F(v^*)\}$
-- statement:
--   For a problem with initial inventory $x_0$ and horizon $T$, the fluid-optimal purchase rate is
--
--   $$
--   \rho^d=\min\Big\{\frac{x_0}{\lambda T},\ \bar F(v^*)\Big\},
--   $$
--
--   where $\bar F(v^*)=\rho^*$ is the maximizer of the revenue rate. Selling at the constant price $\bar F^{-1}(\rho^d)$ solves the fluid problem (1).
--
--   **Formalization Note** The model's $\rho^*$ is used for $\bar F(v^*)$. For $x_0\ge1$ and $T>0$, $\rho^d\in(0,\rho^*]$.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §4, p.8

import Mathlib
import Definitions.Def_MarkdownReadjust_Model

namespace MarkdownReadjust

/-- The fluid-optimal purchase rate `ρᵈ = min{x₀/(λT), F̄(v*)}` (Chen–Jasin, SSRN 3740871, §4,
p.8) of the problem with initial inventory `x` and horizon `τ`.

**Formalization Note.** `F̄(v*) = ρ*` because `v* = F̄⁻¹(ρ*)`, so the model's `rhoStar` is used.
For `x ≥ 1` and `τ > 0`, `ρᵈ ∈ (0, ρ*] ⊂ (0,1)`. -/
noncomputable def rhoD (M : Model) (x : ℕ) (τ : ℝ) : ℝ :=
  min ((x : ℝ) / (M.lam * τ)) M.rhoStar

end MarkdownReadjust


