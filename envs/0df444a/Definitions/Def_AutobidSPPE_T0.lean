-- Prove2me | Definitions.Def_AutobidSPPE_T0
-- name    : AutobidSPPE_T0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:46.63745+00:00
-- url     : https://prove2.me/theorems/7bacf2ca-7064-4a89-a004-8efcb8eb7e1d
-- title:
--   Entry time $T_0=\lceil\log 2/\tau_{\min}\rceil$
-- statement:
--   The certified box-entry time
--   $$
--   T_0=\Big\lceil \frac{\log 2}{\tau_{\min}}\Big\rceil ,
--   $$
--   with the natural logarithm.
--
--   **Formalization Note** The ceiling is the natural-number ceiling; under the step condition $\tau_{\min}>0$, so its argument is positive.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (15), p.12; (24), p.14

import Mathlib
import Definitions.Def_AutobidSPPE_tauMin

namespace AutobidSPPE

/-- The box-entry time `T₀ = ⌈log 2/τ_min⌉` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (15), p.12; (24), p.14).

**Formalization Note** `log` is the natural logarithm and `⌈·⌉` is `Nat.ceil`
(`τ_min > 0` under the step condition, so the argument is positive). -/
noncomputable def T0 {n : ℕ} (τ : Fin n → ℝ) : ℕ := ⌈Real.log 2 / tauMin τ⌉₊

end AutobidSPPE


