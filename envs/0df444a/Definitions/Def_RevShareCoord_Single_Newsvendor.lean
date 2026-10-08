-- Prove2me | Definitions.Def_RevShareCoord_Single_Newsvendor
-- name    : RevShareCoord_Single_Newsvendor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:20:32.346687+00:00
-- url     : https://prove2.me/theorems/a5474917-00ca-49b8-af5c-ead83331aeb4
-- title:
--   Sec. 2.3 — realized retailer and supplier profits in the fixed-price newsvendor under buy-back and revenue-sharing contracts
-- statement:
--   **Realized profits in the fixed-price newsvendor.** The retail price is fixed at $p$, the retailer orders $q$ units, and demand turns out to be $D$. Sales are $\min(q, D)$ and the leftover stock is $(q-D)^+ = \max(q-D, 0)$; leftover units have zero salvage value.
--
--   Under a **buy-back contract** $\{b, w_b\}$ the supplier charges $w_b$ per unit and buys back leftover units at $b$ per unit. Under a **revenue-sharing contract** $\{\phi, w\}$ the retailer keeps the share $\phi$ of revenue and pays $w$ per unit. With unit production cost $c$, the realized profits are
--
--   $$
--   \begin{aligned}
--   \text{buy-back, retailer:}\quad & p\min(q,D) + b\,(q-D)^+ - w_b q,\\
--   \text{buy-back, supplier:}\quad & w_b q - b\,(q-D)^+ - cq,\\
--   \text{revenue sharing, retailer:}\quad & \phi\, p\min(q,D) - wq,\\
--   \text{revenue sharing, supplier:}\quad & (1-\phi)\, p\min(q,D) + wq - cq.
--   \end{aligned}
--   $$
--
--   Taking expectations over $D$ gives the expected-profit functions of Eq. (2) and (3) of the paper; this definition records the profits pathwise, for one realization of demand, which is the level at which the paper compares the two contracts.
--
--   **Formalization Note.** All arguments are real numbers with no constraints in the definition; the theorem that uses them holds for every real input.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), pp. 8–9 (PDF pp. 9–10), Section 2.3, the buy-back contract {b, w_b} and Eq. (2); salvage normalization p. 5, Section 1

import Mathlib

namespace RevShareCoord.Single

/-- Realized retailer profit in the fixed-price newsvendor of Sec. 2.3 (p. 8–9) under the
buy-back contract `{b, w_b}`: retail price `p`, order `q`, realized demand `D`; the retailer
sells `min(q, D)` units at `p`, returns the `(q − D)⁺` leftover units for `b` each (salvage value
normalized to zero, Sec. 1), and pays `w_b` per unit ordered. -/
def bbRetailerRealized (p b wb q D : ℝ) : ℝ :=
  p * min q D + b * max (q - D) 0 - wb * q

/-- Realized supplier profit under the buy-back contract `{b, w_b}` with unit production cost
`c`: she receives `w_b q`, pays `b` for each of the `(q − D)⁺` returned units, and produces `q`
units at cost `c`. -/
def bbSupplierRealized (b wb c q D : ℝ) : ℝ :=
  wb * q - b * max (q - D) 0 - c * q

/-- Realized retailer profit under the revenue-sharing contract `{φ, w}`: he keeps the share
`φ` of the realized revenue `p · min(q, D)` and pays `w` per unit ordered. -/
def rsRetailerRealized (p φ w q D : ℝ) : ℝ :=
  φ * (p * min q D) - w * q

/-- Realized supplier profit under the revenue-sharing contract `{φ, w}` with unit production
cost `c`: she receives `(1 − φ) p · min(q, D)` and `wq`, and produces `q` units at cost `c`. -/
def rsSupplierRealized (p φ w c q D : ℝ) : ℝ :=
  (1 - φ) * (p * min q D) + w * q - c * q

end RevShareCoord.Single


