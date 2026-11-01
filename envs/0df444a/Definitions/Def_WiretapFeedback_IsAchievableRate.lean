-- Prove2me | Definitions.Def_WiretapFeedback_IsAchievableRate
-- name    : WiretapFeedback_IsAchievableRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:31.536091+00:00
-- url     : https://prove2.me/theorems/e8db57f6-0c74-475b-8bd3-4194da70605e
-- title:
--   $(\epsilon,\delta)$-achievable rate
-- statement:
--   A rate $R>0$ is **$(\epsilon,\delta)$-achievable** for the wiretap channel $W$ if there exists an $(\lfloor 2^{nR}\rfloor,n,\epsilon,\delta)$ wiretap code for all $n$ sufficiently large.
--
--   **Formalization Note** "For all $n$ sufficiently large" is an eventually-in-$n$ statement; the code may use any feedback alphabet and any local randomness.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, p.2 (definition of an (ϵ, δ)-achievable rate)

import Mathlib
import Definitions.Def_WiretapFeedback_IsWiretapCode

namespace WiretapFeedback

/-- An **`(ϵ, δ)`-achievable rate**, Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §II, p. 2:
"A rate `R > 0` is `(ϵ, δ)`-achievable if there exists an `(⌊2^{nR}⌋, n, ϵ, δ)` wiretap code for
all `n` sufficiently large."

**Formalization Note** "For all `n` sufficiently large" is `∀ᶠ n in atTop`; the number of
messages is exactly `⌊2^{nR}⌋₊`, which is `≥ 1` for `R > 0`, so the witness of `NeZero` excludes
nothing. The code may use any feedback alphabet and any local randomness (`WiretapCode`). -/
def IsAchievableRate {X Y Z : Type} [Fintype Y] [Fintype Z] (W : WildeQIT.Channel X (Y × Z))
    (ε δ R : ℝ) : Prop :=
  0 < R ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∃ (_ : NeZero ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊) (c : WiretapCode X Y ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ n),
      IsWiretapCode W c ε δ

end WiretapFeedback


