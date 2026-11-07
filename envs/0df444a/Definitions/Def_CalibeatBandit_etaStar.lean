-- Prove2me | Definitions.Def_CalibeatBandit_etaStar
-- name    : CalibeatBandit_etaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:30.351973+00:00
-- url     : https://prove2.me/theorems/0f98eb18-33b0-4814-806d-01867de75a7d
-- title:
--   Tuned parameters $\eta^*=\min\{1/(8K),\sqrt{(2K\log K+\log 2)/(14KT)}\}$ and $\mu^*=4K\eta^*$
-- statement:
--   The parameters chosen at the end of the proof of Theorem 3.2 are
--   $$\eta^*=\min\Bigl\{\frac1{8K},\ \sqrt{\frac{2K\log K+\log 2}{14KT}}\Bigr\},\qquad \mu^*=4K\eta^* .$$
--   With them $r_T=\tilde O(K\sqrt T)$, which gives the $\tilde O(K^2\varepsilon^{-2})$ sample complexity of Theorem 3.2.
--
--   **Formalization Note** $\log$ is `Real.log`. For $T=0$ the square root is $\sqrt{x/0}=0$ in Lean, so $\eta^*=\mu^*=0$; this case is never used with a positive threshold.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2 (proof of Theorem 3.2), p.36 (PDF 36)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **The tuned learning rate** `η* = min{1/(8K), √((2K log K + log 2)/(14KT))}`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, proof of
Theorem 3.2, p.36: "Choosing η = min{1/(8K), √((2K log K + log 2)/(14KT))} and μ = 4Kη yields
r_T = Õ(K√T)".

**Formalization Note.** `log` is `Real.log`; for `T = 0` the square root is `√(·/0) = 0`. -/
noncomputable def etaStar (K T : ℕ) : ℝ :=
  min (1 / (8 * K)) (Real.sqrt ((2 * K * Real.log K + Real.log 2) / (14 * K * T)))

/-- **The tuned exploration parameter** `μ* = 4Kη*` (§C.2, p.36). -/
noncomputable def muStar (K T : ℕ) : ℝ :=
  4 * K * etaStar K T

end CalibeatBandit


