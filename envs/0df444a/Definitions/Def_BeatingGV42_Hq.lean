-- Prove2me | Definitions.Def_BeatingGV42_Hq
-- name    : BeatingGV42_Hq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:25.695182+00:00
-- url     : https://prove2.me/theorems/75d0f9f4-6505-4415-9719-cc9db83b4045
-- title:
--   The $q$-ary entropy function $H_q$
-- statement:
--   For an integer $q\ge 2$ and $0<\delta<1$, the **$q$-ary entropy function** is
--   $$
--   H_q(\delta)=\delta\log_q(q-1)-\delta\log_q\delta-(1-\delta)\log_q(1-\delta).
--   $$
--   The Gilbert–Varshamov bound (1.1) asserts that $q$-ary codes of relative distance $\delta$ and rate $1-H_q(\delta)-o(1)$ exist for every $0<\delta<1-1/q$; the mission's goal improves on this bound for $q=42$.
--
--   **Formalization Note** Mathlib's `Real.qaryEntropy q δ` is $\delta\ln(q-1)+h(\delta)$ in nats, with $h(\delta)=-\delta\ln\delta-(1-\delta)\ln(1-\delta)$; $H_q$ is this divided by $\ln q$. At $\delta\in\{0,1\}$ Mathlib's convention $0\ln 0=0$ applies.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §1, eq. (1.1), p.1 (PDF p.3)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

/-- **The `q`-ary entropy function** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §1, eq. (1.1), p.1 (PDF p.3)):
`H_q(δ) = δ log_q(q − 1) − δ log_q δ − (1 − δ) log_q(1 − δ)`.

**Formalization Note** Mathlib's `Real.qaryEntropy q δ = δ ln(q − 1) + h(δ)` is the same quantity
in nats (`h` the natural-log binary entropy), so `H_q` is `qaryEntropy q δ / ln q`. On `(0, 1)`
this is the printed formula; at `δ = 0, 1` Mathlib uses `0 · ln 0 = 0`. -/
noncomputable def Hq (q : ℕ) (δ : ℝ) : ℝ := Real.qaryEntropy q δ / Real.log q

end BeatingGV42


