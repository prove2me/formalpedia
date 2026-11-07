-- Prove2me | Definitions.Def_CalibeatBandit_HSRof
-- name    : CalibeatBandit_HSRof
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:43.50436+00:00
-- url     : https://prove2.me/theorems/bf25a498-e07b-40e0-a9b6-6baa48cf1321
-- title:
--   The mixing learner's $\mathrm{SR}$ feedback $H^{\mathrm{SR}}_t$
-- statement:
--   For learning rate $\eta$, the post-processing distributions $m^{\mathrm{SR}}_{t,i}$ returned at the beginning of round $t$ (the columns of $M^{\mathrm{SR}}_t$), the mixed strategy $x_t$ and the corrected reward vector $v_t$,
--   $$H^{\mathrm{SR}}_t=\frac1\eta\sum_i\log\Bigl(\sum_j m^{\mathrm{SR}}_{t,i}(j)\exp\bigl(\eta\,x_t(i)\,v_t(j)\bigr)\Bigr).$$
--
--   **Formalization Note** $m^{\mathrm{SR}}_{t,i}(j)$ is the matrix entry `M j i`; $\log$ is `Real.log`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §3.2 item 4, p.11 (PDF 11)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **Feedback `H^SR_t` to the mixing learner.** For learning rate `η`, a post-processing matrix
`M` (column `i` is `m^SR_{t,i}`), the mixed strategy `x` and the corrected reward vector `v`,
`H^SR = (1/η) ∑_i log(∑_j m^SR_{i}(j) exp(η x(i) v(j)))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §3.2 item 4,
p.11 ("Using the post-processing distributions returned at the beginning of round t, compute
H^SR_t = …").

**Formalization Note.** `m^SR_i(j)` is the matrix entry `M j i`; `log` is the natural logarithm
`Real.log`. -/
noncomputable def HSRof {K : ℕ} (η : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (x v : Fin K → ℝ) : ℝ :=
  1 / η * ∑ i, Real.log (∑ j, M j i * Real.exp (η * x i * v j))

end CalibeatBandit


