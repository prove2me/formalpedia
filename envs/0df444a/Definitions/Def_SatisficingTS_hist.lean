-- Prove2me | Definitions.Def_SatisficingTS_hist
-- name    : SatisficingTS_hist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:28.076573+00:00
-- url     : https://prove2.me/theorems/ee392c74-4e81-4e14-92cb-efca5321c07f
-- title:
--   The history $\mathcal H_{t-1}$
-- statement:
--   The history available when the action $A_t$ is selected is
--   $$
--   \mathcal H_{t-1}=(A_0,Y_0,\dots,A_{t-1},Y_{t-1}),
--   $$
--   the $t$ action–outcome pairs observed before period $t$; $\mathcal H_{-1}$ is empty.
--
--   The history is what the policy acts on and what the conditional mutual information $I(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1})$ conditions on.
--
--   **Formalization Note** 0-based: $\mathcal H_{t-1}$ is $\mathrm{hist}\,t$, a function from $\{0,\dots,t-1\}$ to $\mathcal A\times\mathcal Y$, so $\mathcal H_T=\mathrm{hist}\,(T+1)$.
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, §2, p.5 ("The history available when selecting action At is Ht−1 = (A0, Y0, . . . , At−1, Yt−1)")

import Mathlib
import Definitions.Def_SatisficingTS_obs

namespace SatisficingTS

/-- **The history `H_{t−1}`** (Russo & Van Roy, *Satisficing in Time-Sensitive Bandit Learning*,
arXiv:1803.02855v2, §2, p.5): "The history available when selecting action At is
Ht−1 = (A0, Y0, . . . , At−1, Yt−1)."

`hist ψ g θ W ξ t ω : Fin t → 𝒜 × 𝒴` is the tuple `i ↦ (A_i ω, Y_i ω)`, `i < t`.

**Formalization Note.** 0-based: the paper's `H_{t−1}` is `hist t` (with `t` entries), so
`H_{−1} = hist 0` is the empty tuple and `H_T = hist (T+1)`. -/
def hist {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*}
    (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜) (g : 𝒜 → Θ → 𝒲 → 𝒴)
    (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (t : ℕ) (ω : Ω) : Fin t → 𝒜 × 𝒴 :=
  fun i => obs ψ g θ W ξ (i : ℕ) ω

end SatisficingTS


