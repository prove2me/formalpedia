-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsAnalyticCenter
-- name    : VBSDP_Duality_Supplement_IsAnalyticCenter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:05:57.214574+00:00
-- url     : https://prove2.me/theorems/730b505d-a26d-4fd9-83c3-f509b9679dc7
-- title:
--   (46), p. 71 — the analytic center x⋆ = argmin ϕ(x) of the LMI F(x) ≥ 0
-- statement:
--   With the barrier $\phi$ of (42), the **analytic center** of the linear matrix inequality $F(x)\ge0$ is
--
--   $$x^\star=\operatorname*{argmin}_x\ \phi(x),$$
--
--   that is, $F(x^\star)>0$ and $\phi(x^\star)\le\phi(y)$ for every $y$ with $F(y)>0$. When $\mathbf X=\{x\mid F(x)>0\}$ is nonempty and bounded, $\phi$ is strictly convex and the minimizer exists and is unique.
--
--   **Formalization Note** The predicate states the minimizing property; the minimum is over the points where $\phi$ is finite (outside them the page's $\phi$ is $+\infty$). Existence and uniqueness are not built in.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 71 (PDF p. 23), (46); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_barrier

namespace VBSDP.Duality.Supplement

/-- The analytic center (46), p. 71: `x⋆ = argmin ϕ(x)`, i.e. `F(x⋆) ≻ 0` and
`ϕ(x⋆) ≤ ϕ(y)` for every `y` with `F(y) ≻ 0` (where `ϕ` is finite). -/
def IsAnalyticCenter {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (xs : Fin m → ℝ) : Prop :=
  (VBSDP.Duality.lmi F₀ F xs).PosDef ∧
  ∀ y : Fin m → ℝ, (VBSDP.Duality.lmi F₀ F y).PosDef → barrier F₀ F xs ≤ barrier F₀ F y

end VBSDP.Duality.Supplement


