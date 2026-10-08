-- Prove2me | Definitions.Def_CachonCoord_Proportional_Game
-- name    : CachonCoord_Proportional_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:19.317766+00:00
-- url     : https://prove2.me/theorems/010be826-64d2-4774-81c0-a005bf3768f5
-- title:
--   §6.5.1, pp. 48–53 — the proportional-allocation ordering game: π_i, Nash equilibrium, L_n of (22), ŵ(q), w_b(b), supplier profit
-- statement:
--   There are $n$ retailers. Retailer $i$ orders $q_i \ge 0$; let $q = \sum_j q_j$ and $q_{-i} = q - q_i$. Total demand $D$ is divided in proportion to stock, $D_i = (q_i/q)D$. Under a **buy-back contract** the retailer pays the wholesale price $w$ per unit ordered and receives $b$ for every unit left over; $b = 0$ is the wholesale-price contract.
--
--   1. **Retailer profit.** Retailer $i$ sells $\min(q_i, D_i)$ units at $p$ and returns $(q_i - D_i)^+$, so
--   $$\pi_i(q_i, q_{-i}) = \mathbb E\big[p\min(q_i, D_i) + b(q_i - D_i)^+\big] - wq_i .$$
--   2. **Nash equilibrium.** A profile $q^*$ is a Nash equilibrium of the decentralized system if every $q^*_i \ge 0$ maximizes $x \mapsto \pi_i(x, q^*_{-i})$ over $x \ge 0$.
--   3. **The left side of (22)**, $L_n(q) = \frac1n F(q) + \frac{n-1}{n}\cdot\frac1q\int_0^q F(x)\,dx$.
--   4. **The wholesale price inducing total stock $q$** (p. 52), $\widehat w(q) = p\big(1 - \tfrac1n F(q) - \tfrac{n-1}{n}\cdot\tfrac1q\int_0^qF(x)\,dx\big)$.
--   5. **The coordinating buy-back wholesale price** (p. 52), at the integrated optimum $q^o$:
--   $$w_b(b) = p - (p-b)\left[\frac1n\cdot\frac{p-c}{p} + \frac{n-1}{n}\cdot\frac{1}{q^o}\int_0^{q^o}F(x)\,dx\right].$$
--   6. **Supplier profit** at total stock $q$: $\pi_s = wq - cq - b\,\mathbb E[(q-D)^+]$, wholesale revenue less production cost less buy-back payments.
--
--   These objects carry every result of §6.5.1.
--
--   **Formalization Note** $\pi_i$ is the expectation of the realized profit with $D_i = (q_i/q)D$; at $q = 0$ (everyone orders $0$) Lean's $0/0 = 0$ gives the correct profit $0$. $\widehat w$ and $w_b$ are the printed formulas, not "the price at which $q^o$ is an equilibrium"; that they induce $q$ and $q^o$ is a theorem. The supplier's profit is computed from the transfers, not as $\Pi$ minus the retailers' profits. $w_b$ takes $q^o$ as an argument; the theorems pin it by (20).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, pp. 48–53 (D_i = (q_i/q)D p. 48; π_i and Nash equilibrium p. 50; (22) p. 51; ŵ(q), π_s, w_b(b) p. 52; π_s(q°, w_b(b), b) p. 53)

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash

namespace CachonCoord.Proportional

open MeasureTheory

namespace Model

variable (M : Model)

/-- Retailer `i`'s expected profit `π_i(q_i, q_{−i})` under a buy-back contract with wholesale
price `w` and buy-back rate `b` (§6.5.1, pp. 48–50), when he stocks `x = q_i` and the other
retailers stock `s = q_{−i}` in total. Total demand `D` is allocated in proportion to stock,
`D_i = (q_i/q) D` with `q = q_i + q_{−i}` (p. 48); the retailer sells `min(q_i, D_i)` at `p`,
returns `(q_i − D_i)⁺` for `b` each, and pays `w` per unit ordered. With `b = 0` this is the
wholesale-price contract. (At `q = 0`, i.e. `x = s = 0`, Lean's `0/0 = 0` gives the profit `0`
of a retailer that orders nothing.) -/
noncomputable def retailerProfit (w b x s : ℝ) : ℝ :=
  ∫ d, (M.p * min x (x / (x + s) * d) + b * max (x - x / (x + s) * d) 0 - w * x) ∂M.law

/-- Total stock `q = ∑_i q_i` of a profile. -/
def total {n : ℕ} (q : Fin n → ℝ) : ℝ := ∑ i, q i

/-- Retailer `i`'s payoff at the profile `q`: `π_i(q_i, q − q_i)`. -/
noncomputable def payoff {n : ℕ} (w b : ℝ) (i : Fin n) (q : Fin n → ℝ) : ℝ :=
  M.retailerProfit w b (q i) (total q - q i)

/-- Nash equilibrium of the `n`-retailer ordering game under the contract `(w, b)` (p. 50):
every retailer's order `q_i ≥ 0` is a best response, over all orders `x ≥ 0`, to the others'. -/
def IsNashEq {n : ℕ} (w b : ℝ) (q : Fin n → ℝ) : Prop :=
  IsNash (M.payoff w b) q

/-- The left-hand side of (22), p. 51:
`L_n(q) = (1/n) F(q) + ((n − 1)/n) (1/q) ∫_0^q F(x) dx`. -/
noncomputable def lhs22 (n : ℕ) (q : ℝ) : ℝ :=
  (1 / (n : ℝ)) * M.F q + (((n : ℝ) - 1) / (n : ℝ)) * M.avgF q

/-- The wholesale price `ŵ(q)` printed on p. 52:
`ŵ(q) = p (1 − (1/n) F(q) − ((n − 1)/n) (1/q) ∫_0^q F(x) dx)`. -/
noncomputable def what (n : ℕ) (q : ℝ) : ℝ :=
  M.p * (1 - (1 / (n : ℝ)) * M.F q - (((n : ℝ) - 1) / (n : ℝ)) * M.avgF q)

/-- The buy-back wholesale price `w_b(b)` printed at the foot of p. 52, at the integrated
optimum `qo` (the book's `q°`):
`w_b(b) = p − (p − b) [(1/n)((p − c)/p) + ((n − 1)/n) (1/q°) ∫_0^{q°} F(x) dx]`. -/
noncomputable def wb (n : ℕ) (b qo : ℝ) : ℝ :=
  M.p - (M.p - b) * ((1 / (n : ℝ)) * ((M.p - M.c) / M.p) +
    (((n : ℝ) - 1) / (n : ℝ)) * M.avgF qo)

/-- The supplier's expected profit when the retailers stock `q` units in total under the
contract `(w, b)`: wholesale revenue `wq`, minus production cost `cq`, minus the buy-back
payment `b` on every unit left over, `b E[(q − D)⁺]` (pp. 50–53). -/
noncomputable def supplierProfit (w b q : ℝ) : ℝ :=
  w * q - M.c * q - b * M.I q

end Model

end CachonCoord.Proportional


