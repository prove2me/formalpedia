-- Prove2me | Definitions.Def_GoodProphets_LipHyp
-- name    : GoodProphets_LipHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:08.825623+00:00
-- url     : https://prove2.me/theorems/00d998b5-e1ac-44c4-be4c-c62a083e6b69
-- title:
--   Proposition 1 (i): $f_{\vec N}$ is $\lambda$-Lipschitz on $\{\vec x:\sum_jx_{\theta j}=N_\theta\}$
-- statement:
--   An instance satisfies **property (i) of Proposition 1 with constant $\lambda$** if for every $\vec N\ge0$ and all $\vec x,\vec x'$ with $\sum_jx_{\theta j}=\sum_jx'_{\theta j}=N_\theta$ for every $\theta$,
--   $$
--   \big|f_{\vec N}(\vec x)-f_{\vec N}(\vec x')\big|\le\lambda\,\|\vec x-\vec x'\|_1,\qquad \|\vec x\|_1=\sum_{\theta,j}|x_{\theta j}|.
--   $$
--   The paper's bounds on the loss are multiples of $\lambda$: one action changes $\vec x$ by $2$ in $\ell_1$, so a period in which the algorithm deviates from a hindsight-optimal plan costs at most $2\lambda$.
--
--   **Formalization Note** The paper names no norm. The $\ell_1$ norm gives the weakest hypothesis among the standard norms, and it matches the "$2\lambda$ per period" bound of the proof of Theorem 2.2 (p.13).
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Proposition 1 (i), p.8

import Mathlib
import Definitions.Def_GoodProphets_lpObj

namespace GoodProphets

/-- The ℓ1 norm `∑_{θ,j} |x_θj|` of a type-action array. -/
def norm1 {k ℓ : ℕ} (x : Fin k → Fin ℓ → ℝ) : ℝ :=
  ∑ θ, ∑ j, |x θ j|

/-- Property (i) of Proposition 1 of Banerjee & Freund, *Good prophets know when the end is near*,
Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.8:
"`f_N` is `λ`-Lipschitz continuous on the set `{x : ∑ⱼ x_θj = N_θ}`", for every `N ≥ 0`.

**Formalization Note** The paper names no norm; the ℓ1 norm `norm1` is used. It is the weakest
choice among the standard norms (`|·|_∞ ≤ |·|₂ ≤ |·|₁`), so the hypothesis is the weakest, and it
matches the proof's "the loss incurred in any period is bounded by `2λ`" (p.13): one action changes
`x` by `2` in ℓ1. Only `N ≥ 0` is required (the paper's `N` are arrival counts and their
rescalings). -/
def LipHyp {k ℓ r m : ℕ} (I : Instance k ℓ r m) (lam : ℝ) : Prop :=
  ∀ N : Fin k → ℝ, (∀ θ, 0 ≤ N θ) →
    ∀ x ∈ (Dom N : Set (Fin k → Fin ℓ → ℝ)), ∀ x' ∈ (Dom N : Set (Fin k → Fin ℓ → ℝ)),
      |lpObj I N x - lpObj I N x'| ≤ lam * norm1 (fun θ j => x θ j - x' θ j)

end GoodProphets


