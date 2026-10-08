-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_bestReplyRadius
-- name    : YoungConventions_RiskDominance_bestReplyRadius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:02:25.608146+00:00
-- url     : https://prove2.me/theorems/28b2310b-898a-4a99-8298-fb48f9abafa7
-- title:
--   $L_\Gamma=\max_s L(s)$
-- statement:
--   For a finite game $\Gamma$,
--   $$L_\Gamma=\max_{s\in\prod_iS_i}L(s),$$
--   the largest, over all strategy-tuples, of the length of a shortest best-reply path to a strict Nash equilibrium. It sets the sampling condition $k\le m/(L_\Gamma+2)$ of Theorem 1, the Corollary and generic stability.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_shortestPathToNash

namespace YoungConventions.RiskDominance

/-- **`L_Γ = max_s L(s)`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9): "and let `L_Γ = max_s L(s)`." -/
noncomputable def bestReplyRadius {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] (u : ι → ((i : ι) → S i) → ℝ) : ℕ :=
  Finset.univ.sup (shortestPathToNash u)

end YoungConventions.RiskDominance


