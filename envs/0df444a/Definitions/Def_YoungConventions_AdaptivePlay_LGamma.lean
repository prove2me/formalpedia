-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_LGamma
-- name    : YoungConventions_AdaptivePlay_LGamma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:02:36.041989+00:00
-- url     : https://prove2.me/theorems/0334d33f-2bf6-437a-855f-9c23221d5270
-- title:
--   $L_\Gamma = \max_s L(s)$ (§4, p. 64)
-- statement:
--   For a game $\Gamma$ with finite strategy sets,
--   $$L_\Gamma = \max_{s \in \prod_j S_j} L(s),$$
--   the largest, over all strategy tuples, of the length of a shortest best-reply path to a strict Nash equilibrium.
--
--   $L_\Gamma$ measures how many one-player best-reply steps may be needed to reach a strict equilibrium. It sets the memory-to-sample ratio $k \le m/(L_\Gamma + 2)$ of Theorem 1 and the horizon $M = kL_\Gamma + m$ of its proof.
--
--   **Formalization Note** The maximum over the finite set $\prod_j S_j$ is `Finset.univ.sup`.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_shortestPathLength

namespace YoungConventions.AdaptivePlay

/-- **`L_Γ = maxₛ L(s)`** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§4, p. 64, PDF p. 9): "let `L_Γ = maxₛ L(s)`".

`LGamma u` is the maximum, over all strategy tuples `s ∈ ∏ Sᵢ`, of the length `L(s)` of a shortest
best-reply path from `s` to a strict Nash equilibrium.

**Formalization Note.** The maximum over the finite set `∏ Sᵢ` is `Finset.univ.sup` (in `ℕ`, the
supremum of the empty family would be `0`, but `∏ Sᵢ` is nonempty when every `Sᵢ` is). The value is
meaningful for weakly acyclic games; see `shortestPathLength`. -/
noncomputable def LGamma {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] (u : ι → (∀ i, S i) → ℝ) : ℕ :=
  Finset.univ.sup (shortestPathLength u)

end YoungConventions.AdaptivePlay


