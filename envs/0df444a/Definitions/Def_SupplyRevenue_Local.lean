-- Prove2me | Definitions.Def_SupplyRevenue_Local
-- name    : SupplyRevenue_Local
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:51.621259+00:00
-- url     : https://prove2.me/theorems/67d17c01-847f-4426-9554-06d4bc921dcd
-- title:
--   Local responses to a stock law, surplus, item-pricing profit and calibration
-- statement:
--   Fix a stock law $\mu$, independent of the arriving type and the offer, whose item indicators may be correlated. It is **good** at level $\eta$ when each item survives with probability at least $1-\eta$. For an offer law $\tau$ this module defines the expected actual payment and the unconditional item allocation against $\mu$. It also defines
--
--   $$U_v(T,q)=\max_{Q\subseteq T}\{v(Q)-q(Q)\},$$
--
--   the profit $\mathrm{IP\ Profit}_c(D_i)$, which is the supremum over offers of $E[p(X)-c(X)]$, and utility/payment optimizers on an assortment. The calibration of §5.1 is $k=\lceil\log_2(1+256m^2/\eta)\rceil$, $\alpha=(1-\eta)/(8(1+\eta k))$, and $\eta_0=\delta/2$ when $\delta K\le 1$, $\eta_0=1/\lceil\sqrt{K/\delta}\rceil$ otherwise.
--
--   These are the objects of the local recovery lemmas and of the stock-law fixed point.
--
--   **Formalization Note** The stock law is a mass function on bundles.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §2, p.6; §4, p.8; §5, pp.10–11; (7)

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer

open scoped ENNReal

namespace SupplyRevenue

/-!
# Local payment responses to a stock law, surplus and item-pricing profit

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§2, p.6, §4, p.8, §5, p.10: "Here remaining stock S is independent of the arriving type and fresh source prices; its item
indicators may be correlated. Write U_v(T, q) = max_{Q⊆T}{v(Q) − q(Q)}."

**Formalization Note** A stock law is a `Lottery` (a mass function on bundles, items may be correlated). The stock, the
type and the offer are independent in these expectations: they are three nested finite sums. `IPProfit` is in `ℝ≥0∞`, and
the empty offer makes the supremum at least zero.
-/

/-- `S ∼ μ` has survival at least `1 − η` for every item (p.8, p.10). -/
def GoodStock {m : ℕ} (μ : Lottery m) (η : ℝ) : Prop := ∀ j, 1 - η ≤ μ.incl j

/-- `E_{S∼μ} E_{o∼τ} E_θ f(o, θ, Q)`, with `Q` the actual demand of type `θ` at `o` with stock `S`, for stock, offer and
type independent. -/
noncomputable def localE {m : ℕ} (tie : Tie m) (b : Buyer m) (τ : Mix (Offer m)) (μ : Lottery m)
    (f : Offer m → Finset (Fin m) → ℝ) : ℝ :=
  μ.E fun S => τ.E fun o => b.E fun θ => f o (demand tie (b.val θ) o S)

/-- The expected actual payment of the offer law `τ` against stock law `μ`. -/
noncomputable def localRev {m : ℕ} (tie : Tie m) (b : Buyer m) (τ : Mix (Offer m))
    (μ : Lottery m) : ℝ :=
  localE tie b τ μ fun o Q => o.pay Q

/-- The unconditional probability that item `j` is allocated by the offer law `τ` against stock law `μ`. -/
noncomputable def localAlloc {m : ℕ} (tie : Tie m) (b : Buyer m) (τ : Mix (Offer m))
    (μ : Lottery m) (j : Fin m) : ℝ :=
  localE tie b τ μ fun _ Q => if j ∈ Q then 1 else 0

/-- `U_v(T, q) = max_{Q ⊆ T} {v(Q) − q(Q)}` (p.8). -/
noncomputable def surplus {m : ℕ} (v : Finset (Fin m) → ℝ) (T : Finset (Fin m)) (q : Fin m → ℝ) : ℝ :=
  T.powerset.sup' ⟨∅, Finset.empty_mem_powerset T⟩ fun Q => v Q - ∑ j ∈ Q, q j

/-- `IP Profit_c(D_i)` (p.6): the supremum over offers of `E[p(X) − c(X)]`, with `X` the tie-ruled full-stock demand. -/
noncomputable def ipProfit {m : ℕ} (tie : Tie m) (b : Buyer m) (c : Fin m → ℝ) : ℝ≥0∞ :=
  ⨆ o : Offer m, ENNReal.ofReal (b.E fun θ =>
    let X := demand tie (b.val θ) o Finset.univ
    o.pay X - ∑ j ∈ X, c j)

/-- `Q` is a utility/payment optimizer on `A` at prices `p`: it maximizes `(v(Q) − p(Q), p(Q))` lexicographically over
subsets of `A` (Lemma 3.2, p.7). -/
def IsUtilPayOpt {m : ℕ} (v : Finset (Fin m) → ℝ) (p : Fin m → ℝ) (A Q : Finset (Fin m)) : Prop :=
  Q ⊆ A ∧ ∀ Q' ⊆ A, (toLex (v Q' - ∑ j ∈ Q', p j, ∑ j ∈ Q', p j) : ℝ ×ₗ ℝ) ≤
    toLex (v Q - ∑ j ∈ Q, p j, ∑ j ∈ Q, p j)

/-- The ladder length of §5.1, p.11: `⌈log₂(1 + 256m²/η)⌉`, which is (7) under the calibration (2). -/
noncomputable def ladderLength (m : ℕ) (η : ℝ) : ℕ :=
  ⌈Real.logb 2 (1 + 256 * (m : ℝ) ^ 2 / η)⌉₊

/-- `α = (1 − η)/(8(1 + ηk))`, display (7), with the ladder length of §5.1. -/
noncomputable def alphaOf (m : ℕ) (η : ℝ) : ℝ :=
  (1 - η) / (8 * (1 + η * (ladderLength m η : ℝ)))

/-- The choice of §5.1, p.11: `η₀ = δ/2` when `δK ≤ 1`, and `η₀ = 1/⌈√(K/δ)⌉` otherwise, with `K` passed as a real. -/
noncomputable def etaZero (K δ : ℝ) : ℝ :=
  if δ * K ≤ 1 then δ / 2 else 1 / (⌈Real.sqrt (K / δ)⌉₊ : ℝ)

end SupplyRevenue


