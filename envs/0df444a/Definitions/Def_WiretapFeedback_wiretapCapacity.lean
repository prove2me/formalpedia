-- Prove2me | Definitions.Def_WiretapFeedback_wiretapCapacity
-- name    : WiretapFeedback_wiretapCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:21.835533+00:00
-- url     : https://prove2.me/theorems/85140a46-d9aa-4cd0-a8c5-5bc4c9774f75
-- title:
--   $(\epsilon,\delta)$-wiretap capacity $C_{\epsilon,\delta}$ with public feedback
-- statement:
--   The **$(\epsilon,\delta)$-wiretap capacity** of $W$ with public feedback is
--   $$
--   C_{\epsilon,\delta}=\sup\{R:\ R\text{ is }(\epsilon,\delta)\text{-achievable}\}.
--   $$
--
--   **Formalization Note** The supremum is taken in the extended reals: it is $+\infty$ if the achievable rates are unbounded and $-\infty$ if there is none (where the usual convention would give $0$; both lie below every non-negative bound, so upper bounds such as Theorem 1 are unaffected).
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, p.2 (definition of C_{ϵ,δ})

import Mathlib
import Definitions.Def_WiretapFeedback_IsAchievableRate

namespace WiretapFeedback

/-- The **`(ϵ, δ)`-wiretap capacity** `C_{ϵ,δ}` with public feedback, Hayashi–Tyagi–Watanabe,
arXiv:1410.0443v1, §II, p. 2: "the supremum of all `(ϵ, δ)`-achievable rates".

**Formalization Note** The supremum is taken in `EReal`, so it is `+∞` if the achievable rates are
unbounded and `⊥` if there is none (where the paper's convention would give `0`; both are below
any non-negative bound). An `ℝ`-valued `sSup` would return the junk value `0` on unbounded sets. -/
noncomputable def wiretapCapacity {X Y Z : Type} [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) (ε δ : ℝ) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, IsAchievableRate W ε δ R ∧ r = (R : EReal)}

end WiretapFeedback


