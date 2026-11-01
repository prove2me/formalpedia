-- Prove2me | Definitions.Def_BayesBAI_candidates
-- name    : BayesBAI_candidates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:56:07.480559+00:00
-- url     : https://prove2.me/theorems/4bc4041e-26df-45df-b071-3fad1a017323
-- title:
--   The candidate set $\hat{\mathcal J}^*$
-- statement:
--   The set of candidates of Algorithm 1 is
--   $$
--   \hat{\mathcal J}^*=\{i\in[K]:U_i\ge\max_j L_j\}.
--   $$
--
--   **Formalization Note.** The Lean condition $\forall j,\ L_j\le U_i$ is the same as $U_i\ge\max_j L_j$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Algorithm 1, p.6

import Mathlib
import Definitions.Def_BayesBAI_lcb
import Definitions.Def_BayesBAI_ucb

namespace BayesBAI

/-- The candidate set `Ĵ* = {i : U_i ≥ max_j L_j}` of Algorithm 1, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.6.

**Formalization Note.** `∀ j, L_j ≤ U_i` is the same condition as `U_i ≥ max_j L_j`, without a maximum. -/
noncomputable def candidates {K T : ℕ} (q : ℝ) (ω : Tape K T) : Finset (Fin K) :=
  Finset.univ.filter (fun i => ∀ j, lcb q ω j ≤ ucb q ω i)

end BayesBAI


