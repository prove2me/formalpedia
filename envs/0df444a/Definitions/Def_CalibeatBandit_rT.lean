-- Prove2me | Definitions.Def_CalibeatBandit_rT
-- name    : CalibeatBandit_rT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:30.764966+00:00
-- url     : https://prove2.me/theorems/abdc7e8a-1f63-4234-bce6-ce2f79063fef
-- title:
--   The bound $r_T=\mu T+(2K\log K+\log 2)/\eta+5\eta KT/(1-\mu)$
-- statement:
--   For $K$ actions, horizon $T$, learning rate $\eta$ and exploration parameter $\mu$,
--   $$r_T=\mu T+\frac{2K\log K+\log 2}{\eta}+\frac{5\eta KT}{1-\mu}.$$
--   This is the right-hand side of the bandit calibeating bound (Theorem 3.2).
--
--   **Formalization Note** $\log$ is the natural logarithm `Real.log`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Theorem 3.2, p.11 (PDF 11)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **The bound `r_T` of Theorem 3.2**:
`r_T = μT + (2K log K + log 2)/η + 5ηKT/(1 − μ)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Theorem 3.2,
p.11.

**Formalization Note.** `log` is the natural logarithm `Real.log` (p.7: "The constant e is the
base of the natural logarithm"). -/
noncomputable def rT (K T : ℕ) (η μ : ℝ) : ℝ :=
  μ * T + (2 * K * Real.log K + Real.log 2) / η + 5 * η * K * T / (1 - μ)

end CalibeatBandit


