-- Prove2me | Definitions.Def_GoodProphets_StabHyp
-- name    : GoodProphets_StabHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:23.205348+00:00
-- url     : https://prove2.me/theorems/c1d09ddc-f465-4545-ad35-b7bceedb8835
-- title:
--   Proposition 1 (ii): solution stability $|\vec x-\vec x'|_\infty\le\delta|\vec N-\vec N'|_\infty$
-- statement:
--   An instance satisfies **property (ii) of Proposition 1 with constant $\delta$** if the following holds. Let $\vec y\ge0$, and let $\vec N,\vec N'\ge0$ satisfy $|\vec N|_1=|\vec N'|_1$ and be such that both feasible sets $\{\vec x\ge\vec y:\sum_jx_{\theta j}=N_\theta\}$ and $\{\vec x\ge\vec y:\sum_jx_{\theta j}=N'_\theta\}$ are non-empty. Then for every $\vec x\in\arg\min_{\vec x\ge\vec y}f_{\vec N}$ there is $\vec x'\in\arg\min_{\vec x'\ge\vec y}f_{\vec N'}$ with
--   $$
--   |\vec x-\vec x'|_\infty\le\delta\,|\vec N-\vec N'|_\infty .
--   $$
--   This is the stability property that turns concentration of the arrival counts into concentration of optimal solutions. The paper derives it from a perturbation bound for linear programs (Mangasarian and Shiau 1987), with $\delta$ depending only on $A$ and $D$.
--
--   **Formalization Note** The two feasible sets are required to be non-empty. As printed ("for any $\vec y$, any $\vec N$ and $\vec N'$"), the property cannot hold: with $\vec y$ placing all of $N_\theta$ on type $\theta$ and $N'_\theta<N_\theta$, the second argmin is empty. The cited perturbation theorem also assumes non-empty solution sets. $|\cdot|_\infty$ is a maximum over coordinates, written as an `iSup` over the finite index set.
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Proposition 1 (ii), p.8; Proposition 5, p.25

import Mathlib
import Definitions.Def_GoodProphets_lpObj

namespace GoodProphets

/-- The sup norm `max_θ |N_θ|` of a type vector (`0` when there are no types). -/
noncomputable def supNormK {k : ℕ} (N : Fin k → ℝ) : ℝ :=
  ⨆ θ, |N θ|

/-- The sup norm `max_{θ,j} |x_θj|` of a type-action array (`0` when it is empty). -/
noncomputable def supNorm {k ℓ : ℕ} (x : Fin k → Fin ℓ → ℝ) : ℝ :=
  ⨆ θ, ⨆ j, |x θ j|

/-- Property (ii) of Proposition 1 of Banerjee & Freund, *Good prophets know when the end is near*,
Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.8: "for any `y`, any
`N` and `N′` with `|N|₁ = |N′|₁`, and any `x ∈ arg min_{x≥y} {f_N}`, there exists
`x′ ∈ arg min_{x′≥y} {f_N′}` with `|x − x′|_∞ ≤ δ |N − N′|_∞`".

**Formalization Note** It is required for `y ≥ 0` and `N, N′ ≥ 0` (for which `|N|₁ = ∑_θ N_θ`)
such that **both** feasible sets `{x ≥ y : ∑ⱼ x_θj = N_θ}` and `{x ≥ y : ∑ⱼ x_θj = N′_θ}` are
non-empty. Without that guard the property is unsatisfiable: for `y = N` and `N′` with a smaller
coordinate, `arg min_{x′≥y} f_N′` is empty. The source of (ii), Mangasarian–Shiau (Proposition 5,
p.25), likewise assumes non-empty solution sets. -/
def StabHyp {k ℓ r m : ℕ} (I : Instance k ℓ r m) (δ : ℝ) : Prop :=
  ∀ y : Fin k → Fin ℓ → ℝ, (∀ θ j, 0 ≤ y θ j) →
    ∀ N N' : Fin k → ℝ, (∀ θ, 0 ≤ N θ) → (∀ θ, 0 ≤ N' θ) → ∑ θ, N θ = ∑ θ, N' θ →
      (Feas N y).Nonempty → (Feas N' y).Nonempty →
      ∀ x, IsOptIn I N y x → ∃ x', IsOptIn I N' y x' ∧
        supNorm (fun θ j => x θ j - x' θ j) ≤ δ * supNormK (fun θ => N θ - N' θ)

end GoodProphets


