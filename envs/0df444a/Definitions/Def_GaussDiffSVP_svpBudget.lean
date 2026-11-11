-- Prove2me | Definitions.Def_GaussDiffSVP_svpBudget
-- name    : GaussDiffSVP_svpBudget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:30.480446+00:00
-- url     : https://prove2.me/theorems/610a348a-8c03-4b5e-8ff6-9e1dcf055e19
-- title:
--   The default SVP schedule (163)
-- statement:
--   The default schedule for SVP and batches: with $L_{\log} = \lceil\log_2(n+2)\rceil$,
--   $$w_n = L_{\log}^{-4},\qquad h_n = \lceil n/L_{\log}^2\rceil,\qquad b_n = n/\sqrt{L_{\log}},$$
--   and $\ell_n = n w_n + L_{\log}$. These satisfy $\ell_n \ll h_n \ll b_n \ll n$.
--
--   **Formalization Note** $b_n$ is kept as the printed real number: it only enters as an exponent and inside $\Theta(b_n)$ estimates, where rounding up changes nothing.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (163), App. C.1.2, p.80

import Mathlib
import Definitions.Def_GaussDiffSVP_Budget

namespace GaussDiffSVP

/-- The default schedule for SVP and batches (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (163), p.80): with `L_log = ⌈log₂(n + 2)⌉`,
`w_n = L_log^{-4}`, `h_n = ⌈n / L_log²⌉`, `b_n = n / √L_log` (and `ℓ_n = n w_n + L_log`, see
`Budget.ell`).

**Formalization Note.** `h_n` is the printed integer ceiling (`Nat.ceil`, cast to `ℝ`). The
page prints `b_n = n/√L_log` without a ceiling; it is used only as an exponent and inside
`Θ(b_n)`, `O(b_n)` estimates, where rounding up ("Round resource budgets upward to integers")
changes nothing, so it is kept as the printed real number. -/
noncomputable def svpBudget : Budget where
  w n := 1 / ((Llog n : ℝ) ^ 4)
  h n := (⌈(n : ℝ) / (Llog n : ℝ) ^ 2⌉₊ : ℝ)
  b n := (n : ℝ) / Real.sqrt (Llog n)

end GaussDiffSVP


