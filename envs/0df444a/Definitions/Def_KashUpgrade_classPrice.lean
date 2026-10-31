-- Prove2me | Definitions.Def_KashUpgrade_classPrice
-- name    : KashUpgrade_classPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:28.343883+00:00
-- url     : https://prove2.me/theorems/79e2c4ee-f7ab-4fa1-a6e1-08cc86562019
-- title:
--   The price charged for class $j$ at upgrade experience $m$
-- statement:
--   The price that a customer in class $j$ with upgrade experience $m$ pays per period: $x_{j,m}$ for $j\ge 1$, and $x_0=0$ for class $0$, which encodes opting out.
--
--   **Formalization Note** A price vector is a total function $x:\mathbb N\times\mathbb N\to\mathbb R$. Its values on class $0$ are not decision variables: the model reads prices through this function only.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (1), p.10

import Mathlib

namespace KashUpgrade

/-- **The price actually charged for class `j` at upgrade experience `m`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (1), p.10: class
`0` encodes opting out and costs `x₀ = 0`.

**Formalization Note** A price vector is a total function `x : ℕ → ℕ → ℝ`. The value of `x` on class
`0` is not a decision variable: the model reads prices through this function only. -/
def classPrice (x : ℕ → ℕ → ℝ) (j m : ℕ) : ℝ :=
  if j = 0 then 0 else x j m

end KashUpgrade


