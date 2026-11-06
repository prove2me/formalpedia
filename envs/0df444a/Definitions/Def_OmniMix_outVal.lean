-- Prove2me | Definitions.Def_OmniMix_outVal
-- name    : OmniMix_outVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:20.223537+00:00
-- url     : https://prove2.me/theorems/2506b07e-a79d-4f37-b40b-db9490847a81
-- title:
--   Real value of a binary outcome
-- statement:
--   For an outcome $y\in\{0,1\}$, its **real value** is the number $y$ itself ($1$ for the outcome $1$, $0$ for the outcome $0$). It is the $y$ appearing in expressions such as $y-p$.
--
--   **Formalization Note** Outcomes are `Bool`; `outVal true = 1`, `outVal false = 0`.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib

namespace OmniMix

/-- **Real value of a binary outcome.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1: outcomes `y ∈ {0, 1}`.
`outVal y` is `1` for `y = true` and `0` for `y = false`; it is the number `y` in expressions such as
`y − p`. -/
def outVal (y : Bool) : ℝ := if y then 1 else 0

end OmniMix


