-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_PositionSpp
-- name    : SPPRevenue_SingleUnit_Supplement_PositionSpp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:13:21.013817+00:00
-- url     : https://prove2.me/theorems/34b87d88-2ce9-42a0-adf1-4a52a10d23bf
-- title:
--   Equation (10), p. 23 — the n²-price SPP mechanism for position auctions: expected clicks and revenue
-- statement:
--   The SPP mechanism for position auctions (Equation (10), p. 23).
--
--   For each $j\in[n]$, a $j$-unit SPP mechanism with prices $p^j=(p^j_1,\dots,p^j_n)$ approaches the buyers in decreasing order of $p^j_i$ and offers $\alpha_j-\alpha_{j+1}$ expected clicks at price $p^j_i(\alpha_j-\alpha_{j+1})$, until $j$ buyers have accepted. With $\tilde x^j_i(v)\in\{0,1\}$ the indicator that buyer $i$ accepted in the $j$-th sale,
--   $$\tilde x_i(v)=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})\tilde x^j_i(v),\qquad \mathbb E\Big[\sum_i\tilde\pi_i(v)\Big]=\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})\,\mathrm{SPP}_j(p^j).$$
--
--   When each $j$-unit sale uses the best of the Myersonian and uniform prices of the $j$-unit benchmark $t^j$, the best-of revenue envelope is
--   $$\sum_{j\in[n]}(\alpha_j-\alpha_{j+1})\max(\mathrm{MP}_j,\mathrm{UP}_j).$$
--
--   **Formalization Note** The $j$-unit sale with prices $p^j$ is SPP$_j$ of the multi-unit setting (0-based: index $j$ is the paper's $j+1$ units). MP$_j$ averages over the random Myersonian prices and UP$_j$ is a supremum over uniform prices, so this expression is an envelope and may be unattained. Theorem 4 separately exhibits deterministic prices achieving the weighted approximation guarantee.
--   The definition `paSppPay` records the individual payment sum in (10), and `paSppMech` combines these payments with `paSppClicks`. These formulas describe nonnegative posted prices, as required in Theorem 4.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 23, SPP Mechanisms for Position Auction Settings, Equation (10)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiUnit
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Position

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

/-- The best-of revenue envelope for position auctions (Equation (10), p. 23) when, for
every `j`, the `(j+1)`-unit SPP mechanism uses the best of the Myersonian prices (thresholds
`t j` of the `(j+1)`-unit benchmark, re-sampled) and the uniform price: the `(j+1)`-unit sale of
`α_j − α_{j+1}` clicks has envelope `(α_j − α_{j+1}) · max(MP_{j+1}, UP_{j+1})`.
The uniform-price supremum need not be attained; Theorem 4 separately supplies actual deterministic
prices achieving the stated approximation guarantee. -/
noncomputable def paSppRev {n : ℕ} (α : Fin n → ℝ) (μ : Fin n → Measure ℝ)
    (t : Fin n → Fin n → (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin n, ENNReal.ofReal (ctrGap α j) *
    max (mpHRev ((j : ℕ) + 1) μ (t j)) (upHRev ((j : ℕ) + 1) μ)

/-- Expected clicks `x̃_i(v) = Σ_j (α_j − α_{j+1}) x̃_i^j(v)` of the `n²`-price SPP mechanism for
position auctions (Equation (10), p. 23) with prices `p j i = p_i^j`: for each `j`, buyers are
approached in decreasing order of `p_i^j` and offered `α_j − α_{j+1}` clicks at price
`p_i^j (α_j − α_{j+1})`, until `j` (here `j + 1`, 0-based) buyers have accepted. -/
noncomputable def paSppClicks {n : ℕ} (α : Fin n → ℝ) (p : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ctrGap α j * (if i ∈ sppHWinners ((j : ℕ) + 1) (p j) v then 1 else 0)

/-- The individual payment in Equation (10), p. 23, for deterministic prices `p`. -/
noncomputable def paSppPay {n : ℕ} (α : Fin n → ℝ) (p : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ctrGap α j *
    (if i ∈ sppHWinners ((j : ℕ) + 1) (p j) v then p j i else 0)

/-- The complete direct mechanism of Equation (10), including individual payments. -/
noncomputable def paSppMech {n : ℕ} (α : Fin n → ℝ) (p : Fin n → Fin n → ℝ) : DirectMech n where
  alloc := paSppClicks α p
  pay := paSppPay α p

/-- Expected revenue `E[Σ_i π̃_i(v)] = Σ_j (α_j − α_{j+1}) SPP_j(p^j)` of the `n²`-price SPP mechanism
for position auctions with prices `p j i = p_i^j` (Equation (10), p. 23). -/
noncomputable def paSppRevDet {n : ℕ} (α : Fin n → ℝ) (μ : Fin n → Measure ℝ)
    (p : Fin n → Fin n → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin n, ENNReal.ofReal (ctrGap α j) * sppHRev ((j : ℕ) + 1) μ (p j)

end SPPRevenue.SingleUnit.Supplement


