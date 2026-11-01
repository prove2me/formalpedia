-- Prove2me | Definitions.Def_BayesBAI_empMean
-- name    : BayesBAI_empMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:10.142981+00:00
-- url     : https://prove2.me/theorems/8cb9d775-9a56-419d-85eb-de07b43f4b52
-- title:
--   The empirical mean $\hat\mu_{i,n}$ of arm $i$
-- statement:
--   $\hat\mu_{i,n}$ is the empirical mean of arm $i$ with the first $n$ samples:
--   $$
--   \hat\mu_{i,n}=\frac1n\,\#\{t\le n:\omega_{i,t}=1\}.
--   $$
--
--   **Formalization Note.** At $n=0$ Lean returns $0/0=0$; the algorithm reads this quantity with $1\le n\le T$ only.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §D.3, p.20

import Mathlib
import Definitions.Def_BayesBAI_Tape

namespace BayesBAI

/-- `μ̂_{i,n}`, the empirical mean of arm `i` with the first `n` samples, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.20.

**Formalization Note.** At `n = 0` Lean gives `0 / 0 = 0`. The algorithm reads this only with
`1 ≤ n ≤ T`: the statements are for `T` so large that the first stage is nonempty, and `n` never exceeds
`T` (`Solutions/verification/BayesBAI_sanity.lean`). -/
noncomputable def empMean {K T : ℕ} (ω : Tape K T) (i : Fin K) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (fun t : Fin T => t.val < n ∧ ω i t = true)).card : ℝ) / n

end BayesBAI


