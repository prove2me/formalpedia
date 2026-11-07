-- Prove2me | Definitions.Def_CalibeatBandit_HRecOf
-- name    : CalibeatBandit_HRecOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:41.743224+00:00
-- url     : https://prove2.me/theorems/12f1aae9-5372-47be-b0e4-ed3c53943a79
-- title:
--   The mixing learner's $\mathrm{Rec}$ feedback $H^{\mathrm{Rec}}_t$
-- statement:
--   For learning rate $\eta$, the post-processing distribution $m^{\mathrm{Rec}}_{t,J_t}$ (column $J_t$ of $M^{\mathrm{Rec}}_t$) and the corrected reward vector $v_t$,
--   $$H^{\mathrm{Rec}}_t=\frac1\eta\log\Bigl(\sum_j m^{\mathrm{Rec}}_{t,J_t}(j)\exp\bigl(\eta\,v_t(j)\bigr)\Bigr).$$
--
--   **Formalization Note** $m^{\mathrm{Rec}}_{t,J}(j)$ is the matrix entry `M j J`; $\log$ is `Real.log`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §3.2 item 4, p.11 (PDF 11)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **Feedback `H^Rec_t` to the mixing learner.** For learning rate `η`, a post-processing matrix
`M` (column `i` is `m^Rec_{t,i}`), the recommended action `J` and the corrected reward vector
`v`,
`H^Rec = (1/η) log(∑_j m^Rec_{J}(j) exp(η v(j)))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §3.2 item 4,
p.11.

**Formalization Note.** `m^Rec_J(j)` is the matrix entry `M j J`; `log` is `Real.log`. -/
noncomputable def HRecOf {K : ℕ} (η : ℝ) (M : Matrix (Fin K) (Fin K) ℝ) (J : Fin K)
    (v : Fin K → ℝ) : ℝ :=
  1 / η * Real.log (∑ j, M j J * Real.exp (η * v j))

end CalibeatBandit


