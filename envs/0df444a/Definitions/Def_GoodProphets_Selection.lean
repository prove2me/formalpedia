-- Prove2me | Definitions.Def_GoodProphets_Selection
-- name    : GoodProphets_Selection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:14.698882+00:00
-- url     : https://prove2.me/theorems/5a4aea78-1367-4d3a-b6bd-3dad57f63cf2
-- title:
--   Assumption 2: a tie-breaking rule $\sigma(\vec N,\vec y)\in\arg\min_{\vec x\ge\vec y}f_{\vec N}$, $\delta$-Lipschitz in $\vec N$
-- statement:
--   A **tie-breaking rule** is a map $\sigma$ that assigns to every right-hand side $\vec N$ and lower bound $\vec y$ a type-action array $\sigma(\vec N,\vec y)$. It satisfies **Assumption 2 with constant $\delta$** if
--
--   1. for all $\vec N\ge0$ and $\vec y\ge0$ whose feasible set $\{\vec x\ge\vec y:\sum_jx_{\theta j}=N_\theta\}$ is non-empty, $\sigma(\vec N,\vec y)\in\arg\min_{\vec x\ge\vec y}f_{\vec N}(\vec x)$;
--   2. for all $\vec N,\vec N'\ge0$ and $\vec y\ge0$ with $\sum_\theta N_\theta=\sum_\theta N'_\theta$ and both feasible sets non-empty,
--   $$
--   |\sigma(\vec N,\vec y)-\sigma(\vec N',\vec y)|_\infty\le\delta\,|\vec N-\vec N'|_\infty .
--   $$
--
--   The rule lets the analysis refer to *the* optimal solution of each of the problems $\mathrm{DLP}=\sigma(\vec p,0)$, $\mathrm{EDLP}(t)=\sigma(\vec N(t)/t,0)$, $\mathrm{OPT}^t=\sigma(\vec N,\vec x^{\mathrm{ALG}}(t-1))$ and $\mathrm{TDLP}(t)=\sigma(\tfrac Tt\vec N(t),\vec x^{\mathrm{ALG}}(t-1))$. The paper obtains it from a lexicographic tie-breaking rule.
--
--   **Formalization Note** The paper writes "maintains $\lambda$-Lipschitz continuity in the right-hand side". This is read with the constant $\delta$ and the norms of Proposition 1 (ii), because the proofs of Lemmas 3.3 and 3.5 bound differences of selected solutions by $\delta|\Delta\vec N|_\infty$. No homogeneity $\sigma(c\vec N,c\vec y)=c\,\sigma(\vec N,\vec y)$ is assumed.
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Assumption 2, p.8

import Mathlib
import Definitions.Def_GoodProphets_StabHyp

namespace GoodProphets

/-- Assumption 2 of Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.8: "For any `N`, `y`, we are
given a tie-breaking rule to select a solution `x` that minimizes `f_N` subject to `x ≥ y` and that
maintains `λ`-Lipschitz continuity in the right-hand side."

`σ N y` is the selected solution. `Selection I σ δ` says:
1. for `N ≥ 0`, `y ≥ 0` with a non-empty feasible set, `σ N y ∈ arg min_{x ≥ y} f_N(x)`;
2. for `N, N′ ≥ 0` with `∑_θ N_θ = ∑_θ N′_θ` and both feasible sets non-empty,
   `|σ(N, y) − σ(N′, y)|_∞ ≤ δ |N − N′|_∞`.

**Formalization Note** The printed constant "`λ`" is read as `δ`, in the norms of Proposition 1
(ii): the proofs of Lemmas 3.3 and 3.5 (pp.11, 27) bound the difference of selected solutions by
`δ · |ΔN|_∞`. The Lipschitz property is required between right-hand sides of equal total, as in
Proposition 1 (ii). No positive homogeneity `σ(cN, cy) = c σ(N, y)` is assumed. -/
def Selection {k ℓ r m : ℕ} (I : Instance k ℓ r m)
    (σ : (Fin k → ℝ) → (Fin k → Fin ℓ → ℝ) → (Fin k → Fin ℓ → ℝ)) (δ : ℝ) : Prop :=
  (∀ N : Fin k → ℝ, ∀ y : Fin k → Fin ℓ → ℝ, (∀ θ, 0 ≤ N θ) → (∀ θ j, 0 ≤ y θ j) →
      (Feas N y).Nonempty → IsOptIn I N y (σ N y)) ∧
  (∀ N N' : Fin k → ℝ, ∀ y : Fin k → Fin ℓ → ℝ, (∀ θ, 0 ≤ N θ) → (∀ θ, 0 ≤ N' θ) →
      (∀ θ j, 0 ≤ y θ j) → ∑ θ, N θ = ∑ θ, N' θ → (Feas N y).Nonempty → (Feas N' y).Nonempty →
      supNorm (fun θ j => σ N y θ j - σ N' y θ j) ≤ δ * supNormK (fun θ => N θ - N' θ))

end GoodProphets


