-- Prove2me | Definitions.Def_FoundationsRL_GeneralDM_LocalizedSubclass
-- name    : FoundationsRL_GeneralDM_LocalizedSubclass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:22:47.222982+00:00
-- url     : https://prove2.me/theorems/d20385e9-06d6-44a5-93cd-f6c7edc16b14
-- title:
--   The localized subclass of models (Eq. 6.28)
-- statement:
--   This definition formalizes the **localized subclass** of models around a reference model
--   $\hat m$, used in Proposition 27 to relate the constrained and offset DEC (Foster & Rakhlin,
--   *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1,
--   Eq. (6.28), p. 105):
--   $$
--   \mathcal{M}_\alpha(\hat m) := \{ m \in \mathcal{M} : f^{\hat m}(\pi_{\hat m}) \ge f^m(\pi_m) - \alpha \},
--   $$
--   the set of models in $\mathcal{M}$ whose optimal value is not more than $\alpha$ above
--   $\hat m$'s optimal value.
--
--   `localizedSubclass 𝓜 rew piStar mhat α` is the literal transcription of $\mathcal{M}_\alpha(\hat
--   m)$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (6.28), p. 105

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol

namespace FoundationsRL.GeneralDM

/-- The localized subclass of models around a reference model `mhat`, at radius `α`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Eq. (6.28), p. 105):

`Mα(M̂) := {M ∈ 𝓜 : f^{M̂}(π_{M̂}) ≥ f^M(π_M) − α}`,

the set of models in `𝓜` whose optimal value is not more than `α` above `M̂`'s. -/
noncomputable def localizedSubclass {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (mhat : S → Y → ℝ) (α : ℝ) : Set (S → Y → ℝ) :=
  {m ∈ 𝓜 | fM rew mhat (piStar mhat) ≥ fM rew m (piStar m) - α}

end FoundationsRL.GeneralDM


