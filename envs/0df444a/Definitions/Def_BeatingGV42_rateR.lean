-- Prove2me | Definitions.Def_BeatingGV42_rateR
-- name    : BeatingGV42_rateR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:23.119992+00:00
-- url     : https://prove2.me/theorems/4aaaf880-191d-482f-8ffb-159e3ed081af
-- title:
--   The rate $R(a,q)$
-- statement:
--   For a square prime power $Q$, an integer $q\ge 2$ and $a\in\mathbb R$,
--   $$
--   R(a,q)=1-\left(1+\frac{1}{\sqrt Q-1}-a\right)\frac{\ln Q}{\ln q}.
--   $$
--   It is the asymptotic rate that Proposition 4.9 guarantees; for $Q=49$, $q=42$ it is $R(a)=1-(7/6-a)\ln 49/\ln 42$ (§4.5).
--
--   **Formalization Note** `rateR Q q a`, with the dependence on $Q$ explicit.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Proposition 4.9, p.20 (PDF p.22); §4.5, p.23 (PDF p.25)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

/-- **The rate `R(a, q) := 1 − (1 + 1/(√Q − 1) − a) ln Q/ln q`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), Proposition 4.9, p.20
(PDF p.22); with `Q = 49`, `q = 42` it is the `R(a) = 1 − (7/6 − a) ln 49/ln 42` of §4.5, p.23
(PDF p.25), since `1 + 1/(√49 − 1) = 7/6`).

**Formalization Note** `Q, q : ℕ` are cast to `ℝ`; the dependence on `Q` is explicit. -/
noncomputable def rateR (Q q : ℕ) (a : ℝ) : ℝ :=
  1 - (1 + 1 / (Real.sqrt Q - 1) - a) * Real.log Q / Real.log q

end BeatingGV42


