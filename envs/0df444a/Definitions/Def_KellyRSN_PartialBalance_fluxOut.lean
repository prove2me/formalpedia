-- Prove2me | Definitions.Def_KellyRSN_PartialBalance_fluxOut
-- name    : KellyRSN_PartialBalance_fluxOut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:40:32.212455+00:00
-- url     : https://prove2.me/theorems/37a661cd-88c7-4b4e-b0a3-a6c02a16926c
-- title:
--   Probability flux out of $\mathcal A$
-- statement:
--   For rates $q$, a distribution $\pi$ on $\mathcal S$ and $\mathcal A \subseteq \mathcal S$, the **probability flux out of $\mathcal A$** is
--   $$
--   \sum_{j \in \mathcal A} \sum_{k \in \mathcal S - \mathcal A} \pi(j)\, q(j,k) \in [0,\infty].
--   $$
--
--   Its finiteness is the extra hypothesis of Theorem 9.5 (vi).
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 33 (PDF p. 36), Exercise 1.7.8; p. 201 (PDF p. 204), Theorem 9.5

import Mathlib

open scoped ENNReal

namespace KellyRSN.PartialBalance

/-- **Probability flux out of the set `𝒜`.**
Kelly, *Reversibility and Stochastic Networks*, Wiley 1979, Exercise 1.7.8, p. 33 (PDF p. 36) and
Theorem 9.5, p. 201 (PDF p. 204): "the probability flux out of the set `𝒜`
`Σ_{j∈𝒜} Σ_{k∈𝒮−𝒜} π(j) q(j, k)`".

**Formalization Note.** An `ℝ≥0∞`-valued double `tsum`; it may be `∞`. -/
noncomputable def fluxOut {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) (A : Set S) : ℝ≥0∞ :=
  ∑' j : A, ∑' k : ↥Aᶜ, π j * q j k

end KellyRSN.PartialBalance


