-- Prove2me | Definitions.Def_PlatformPrecommit_Commission_AlphaStar
-- name    : PlatformPrecommit_Commission_AlphaStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:19.681887+00:00
-- url     : https://prove2.me/theorems/185e04ff-bfcf-4a9f-81e8-3ea765359234
-- title:
--   Equation (7) — symmetric equilibrium pay-out ratio candidate
-- statement:
--   Equation (7) gives a radical expression $\alpha^*$ in the demand and supply competition intensities $\gamma$ and $\beta$. The expression uses the positive square root and has denominator $2(1-\beta)[3+(1-\gamma)\beta-\beta^2]$.
--
--   The quantity is the candidate symmetric first-stage pay-out ratio whose equilibrium role is asserted in Lemma 4. Defining the printed expression here does not assert that it is an equilibrium.
--
--   **Formalization Note** Lean's `Real.sqrt` is used for the printed positive square root. The standing parameter ranges make the denominator nonzero; this fact is not taken as an extra hypothesis.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 13, (7)

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Setting

namespace PlatformPrecommit.Commission

/-- The displayed radical (7) in Hu and Liu's commission equilibrium formula. -/
noncomputable def alphaStar (M : Model) : ℝ :=
  (M.β * (3 - M.γ ^ 2) - M.β ^ 2 * (M.γ + 1) -
    (1 - M.γ) * (2 + 2 * M.γ + M.β) +
    Real.sqrt ((1 + M.γ) *
      (M.β ^ 4 * (1 + M.γ) - 2 * M.β ^ 3 * M.γ * (3 - M.γ) +
       M.β ^ 2 * M.γ * (12 - 11 * M.γ + M.γ ^ 2) -
       4 * M.β * (1 - M.γ) * (4 + 2 * M.γ - M.γ ^ 2) +
       4 * (4 - 4 * M.γ - M.γ ^ 2 + M.γ ^ 3)))) /
    (2 * (1 - M.β) * (3 + (1 - M.γ) * M.β - M.β ^ 2))

end PlatformPrecommit.Commission


