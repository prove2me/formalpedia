-- Prove2me | Definitions.Def_LeGallBrownianMap_cq
-- name    : LeGallBrownianMap_cq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:59.161439+00:00
-- url     : https://prove2.me/theorems/d88ca9ef-4d7f-494c-bf16-77ec19cb719d
-- title:
--   The scaling constant $c_q$
-- statement:
--   For $q$ even,
--
--   $$
--   c_q = \Big(\frac{9}{q(q-2)}\Big)^{1/4},
--   $$
--
--   and $c_3 = 6^{1/4}$. These are the constants by which graph distances in uniform $q$-angulations with $n$ faces are multiplied, together with $n^{-1/4}$, to converge to the Brownian map. For $q=2p$ the constant coincides with $\kappa_p$ of §2.5.
--
--   **Formalization Note** Real powers with exponent $1/4$ (`Real.rpow`).
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Theorem 1.1, pp.2–3

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Theorem 1.1,
pp.2–3: "Set c_q = (9/(q(q − 2)))^{1/4} if q is even, and c_3 = 6^{1/4}."

**Formalization Note.** Real powers are `Real.rpow` with the real exponent `1/4` (not natural
number division). The constant is only used for `q = 3` or `q` even with `q ≥ 4`, where the
base `9/(q(q−2))` is positive. -/
noncomputable def cq (q : ℕ) : ℝ :=
  if q = 3 then (6 : ℝ) ^ (1 / 4 : ℝ) else (9 / ((q : ℝ) * ((q : ℝ) - 2))) ^ (1 / 4 : ℝ)

end LeGallBrownianMap


