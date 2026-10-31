-- Prove2me | Definitions.Def_CommitFrontRun_Model_piValue
-- name    : CommitFrontRun_Model_piValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:52.961418+00:00
-- url     : https://prove2.me/theorems/7582fc8c-05b1-4f41-8d5d-5732c452ce3d
-- title:
--   $\pi$, the value of a blind guess
-- statement:
--   The value to $B$ of committing to a guess before seeing $A$'s message:
--   $$
--   \pi\equiv\max_{\sigma_B\in\Sigma}E_s\Big[\max\{q\cdot\tilde P_B(\sigma_B,\sigma^{**}_A(s),s)-f,\,0\}\;\Big|\;\sigma^{**}_A(s)\neq\emptyset\Big].
--   $$
--   The conditional expectation is
--   $$
--   \frac{\sum_{s:\,P_A(s)\ge c}p(s)\max\{q\,\tilde P_B(\sigma_B,\sigma_A(s),s)-f,0\}}{\sum_{s:\,P_A(s)\ge c}p(s)}.
--   $$
--   The maximum over $\sigma_B$ is taken outside the expectation: $B$ commits to one message before learning the state, and then fires only when it pays.
--
--   **Formalization Note** When $\Pr(P_A(s)\ge c)=0$ the paper's $\pi$ is undefined; the formalization gives $\pi=0$ there.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §3.1, p.15

import Mathlib
import Definitions.Def_CommitFrontRun_Model_sends

namespace CommitFrontRun

variable {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype Msg] [DecidableEq Msg] [Nonempty Msg]

open Classical in
/-- **π, B's expected future payoff from a committed guess.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §3.1, p.15:
π ≡ max_{σ_B ∈ Σ} E_s[max{q · P̃_B(σ_B, σ**_A(s), s) − f, 0} | σ**_A(s) ≠ ∅].

The conditional expectation is the ratio of `∑_s p(s) · 1[P_A(s) ≥ c] · max{q·P̃_B(σ, σ_A(s), s) − f, 0}`
to `Pr(P_A(s) ≥ c) = ∑_s p(s) · 1[P_A(s) ≥ c]`; the maximum over σ is taken outside the
expectation.

**Formalization Note** When Pr(σ**_A(s) ≠ ∅) = 0 the paper's π is undefined; Lean's division
gives π = 0 there. -/
noncomputable def Model.piValue (M : Model S Msg) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ : Msg =>
    (∑ s, M.p s * (if M.sends s then max (M.q * M.PtB σ (M.σA s) s - M.f) 0 else 0)) /
      ∑ s, M.p s * (if M.sends s then (1 : ℝ) else 0)

end CommitFrontRun


