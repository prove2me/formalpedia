-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_Up
-- name    : OffPlatformThreats_Leakage_Up
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:05.474283+00:00
-- url     : https://prove2.me/theorems/ffb5035d-3014-4c7c-be29-96a49f6927d0
-- title:
--   On-platform utility rate $U_p(\omega, n)$
-- statement:
--   Suppose $n$ providers of type $j$ are on the platform and the platform pays them the fraction $\omega$ of their fee (the payout ratio). In the symmetric equilibrium of the paper they all charge a fee $Q_p(n)$ that solves
--
--   $$Q_p(n) \in \arg\max_{\zeta \ge 0} \{\omega\,\zeta\,\lambda_p(n, \zeta) - K\} \qquad (9)$$
--
--   and each receives the utility rate $U_p(\omega, n) = \omega\,Q_p(n)\,\lambda_p(n, Q_p(n)) - K$ (10). Here $U_p(\omega, n)$ is defined as the optimal value of (9):
--
--   $$U_p(\omega, n) = \sup_{\zeta \ge 0}\ \big(\omega\,\zeta\,\lambda_p(n, \zeta) - K\big).$$
--
--   It coincides with (10) whenever (9) has a maximizer, which Lemma 2 establishes. With $n = 0$ the demand is $0$ and $U_p(\omega, 0) = -K$.
--
--   **Formalization Note** The supremum is taken in $\mathbb{R}$; the set is nonempty, and its boundedness is part of Lemma 2.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (9) and (10), p. 13

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_onDemand

namespace OffPlatformThreats.Leakage

/-- **On-platform utility rate `U^j_p(ω^j, n^j_p)`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (9) and (10), p. 13: the symmetric
on-platform fee satisfies `Q^j_p ∈ argmax_{ζ ∈ ℝ₊} {ω^j ζ λ^j_p(n^j_p, ζ) − K^j}` (9), and
`U^j_p(ω^j, n^j_p) := ω^j Q^j_p(n^j_p) λ^j_p(n^j_p, Q^j_p(n^j_p)) − K^j` (10).

`Up m ω n` is the optimal value of (9) with `n` providers on the platform: the supremum over
`ζ ≥ 0` of `ω ζ λ_p(n, ζ) − K`.

**Formalization Note.** (10) evaluates the objective of (9) at a maximizer, so it equals the
supremum whenever (9) has a maximizer; Lemma 2 (milestone `lemma_2_optimal_fees`) shows it has
one, and that `U_p(ω, n) = ω g2(n, v) − K` for `n ≥ 1`, `ω ≥ 0`. At `n = 0` the demand is `0`,
so `Up m ω 0 = −K` (reading of Definition 1 at `N^j_p = 0`, where the paper uses
`U^j_p(ω^j, 1)` and `U^j_p(ω^j, 0)` without defining the latter). The supremum is taken in `ℝ`;
the set is nonempty, and Lemma 2 shows it is bounded above. -/
noncomputable def Up (m : Market) (ω : ℝ) (n : ℕ) : ℝ :=
  sSup ((fun ζ : ℝ => ω * ζ * onDemand m n ζ - m.K) '' Set.Ici 0)

end OffPlatformThreats.Leakage


