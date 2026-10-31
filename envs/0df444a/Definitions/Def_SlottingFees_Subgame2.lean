-- Prove2me | Definitions.Def_SlottingFees_Subgame2
-- name    : SlottingFees_Subgame2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:45.843985+00:00
-- url     : https://prove2.me/theorems/93bea094-3256-48a3-8487-0004f64085c3
-- title:
--   The high-variety subgame $|A|=2$: pricing (12), wholesale game (13), fee problem (14)–(16)
-- statement:
--   The subgame in which the retailer has committed to carry both products (§4.2).
--
--   1. **Stage 3.** Given $(w_1,w_2)$ the retailer carries $\{1,2\}$ and solves
--   $$
--   \max_{(p_1,p_2)\ge0}\ (p_1-w_1)z_1(p_1,p_2)+(p_2-w_2)z_2(p_1,p_2)+2S-2K;\qquad(12)
--   $$
--   a pricing strategy is optimal after every $(w_1,w_2)\ge(c_1,c_2)$, and $\tilde z_l(w_1,w_2)$ are the demands at its prices.
--   2. **Stage 2.** The manufacturers play the simultaneous wholesale-price game
--   $$
--   \max_{w_1\ge c_1}(w_1-c_1)\tilde z_1(w_1,w_2)-S,\qquad \max_{w_2\ge c_2}(w_2-c_2)\tilde z_2(w_1,w_2)-S;\qquad(13)
--   $$
--   an outcome is a pure Nash equilibrium in which each manufacturer takes its lowest best response.
--   3. **Stage 1.** With slotting fees, the retailer maximizes its profit (14) over $S\ge0$ subject to the participation constraints $(\tilde w_l-c_l)\tilde z_l(\tilde w_1,\tilde w_2)-S\ge0$, $l=1,2$ ((15)–(16)); in the benchmark the fee is $0$.
--
--   $\Pi^{|2|}_r$ is the retailer's profit on the path of such a subgame equilibrium. Proposition 2 is stated about these objects.
--
--   **Formalization Note** The Nash condition is the published two-player definition `CrossLicensing.ExPost.IsNE` (own action first in each payoff). The lowest-best-response selection is a reading; it is vacuous when both demands are positive. The constant $2S-2K$ is dropped from the pricing objective.
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, §4.2, (12)–(16), pp.14–15

import Mathlib
import Definitions.Def_SlottingFees_Model
import Definitions.Def_CrossLicensing_ExPost_Game

namespace SlottingFees

/-- `p` solves the retailer's stage-3 pricing problem (12), p.14, for `A = {1,2}`:
`max_{(p₁,p₂) ≥ 0} (p₁ − w₁)z₁(p₁,p₂) + (p₂ − w₂)z₂(p₁,p₂) + 2S − 2K`.

**Formalization Note** The constant `2S − 2K` is dropped; it does not change the maximizers. -/
def IsOptPrice2 (ω : Params) (w p : Fin 2 → ℝ) : Prop :=
  (∀ l, 0 ≤ p l) ∧
    ∀ p' : Fin 2 → ℝ, (∀ l, 0 ≤ p' l) →
      grossProfit ω Finset.univ w p' ≤ grossProfit ω Finset.univ w p

/-- A retailer pricing strategy for the `|A| = 2` subgame is optimal in (12) after every pair of
wholesale prices `w ≥ c` (subgame perfection in stage 3). -/
def IsOptPricing2 (ω : Params) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) : Prop :=
  ∀ w : Fin 2 → ℝ, (∀ l, ω.c l ≤ w l) → IsOptPrice2 ω w (σ w)

/-- Manufacturer `l`'s gross profit `(w_l − c_l) z̃_l(w₁, w₂)` when both products are carried and
the retailer prices by `σ` (p.14, after (13)). -/
noncomputable def mfrGross2 (ω : Params) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (w : Fin 2 → ℝ)
    (l : Fin 2) : ℝ :=
  mfrGross ω Finset.univ w (σ w) l

/-- Manufacturer 1's payoff in (13), own wholesale price `x` first: `(x − c₁) z̃₁(x, y) − S`. -/
noncomputable def wholesalePayoff1 (ω : Params) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (S x y : ℝ) :
    ℝ :=
  mfrGross2 ω σ ![x, y] 0 - S

/-- Manufacturer 2's payoff in (13), own wholesale price `x` first: `(x − c₂) z̃₂(y, x) − S`. -/
noncomputable def wholesalePayoff2 (ω : Params) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (S x y : ℝ) :
    ℝ :=
  mfrGross2 ω σ ![y, x] 1 - S

/-- `w` is a stage-2 equilibrium of the `|A| = 2` subgame at fee `S` (13), p.14: a pure Nash
equilibrium of the wholesale-price game with strategy sets `w_l ≥ c_l`, in which, among its best
responses, each manufacturer takes the lowest wholesale price.

**Formalization Note** The selection (lowest best response) is a reading. It only matters when a
manufacturer's best response is not unique, which happens when a product has zero demand (the
corner rows of (18), p.15); a zero-demand rival then prices at cost, the "price pressure" of
p.16. With unique best responses (both demands positive) it is vacuous. -/
def IsSelectedNE2 (ω : Params) (σ : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (S : ℝ) (w : Fin 2 → ℝ) :
    Prop :=
  CrossLicensing.ExPost.IsNE (Set.Ici (ω.c 0)) (Set.Ici (ω.c 1))
      (wholesalePayoff1 ω σ S) (wholesalePayoff2 ω σ S) (w 0, w 1) ∧
    (∀ x, ω.c 0 ≤ x → wholesalePayoff1 ω σ S x (w 1) = wholesalePayoff1 ω σ S (w 0) (w 1) →
      w 0 ≤ x) ∧
    (∀ x, ω.c 1 ≤ x → wholesalePayoff2 ω σ S x (w 0) = wholesalePayoff2 ω σ S (w 1) (w 0) →
      w 1 ≤ x)

/-- A strategy profile of the `|A| = 2` subgame: the retailer's stage-3 pricing `price`, the
manufacturers' wholesale prices `wholesale S` after each announced fee `S`, and the retailer's
fee `fee`. -/
structure Play2 where
  price : (Fin 2 → ℝ) → (Fin 2 → ℝ)
  wholesale : ℝ → Fin 2 → ℝ
  fee : ℝ

/-- The fee `S` is admissible in the stage-1 problem (14)–(16), p.15: `S ≥ 0` and both
participation constraints (15), (16), `(w̃_l − c_l) z̃_l(w̃₁, w̃₂) − S ≥ 0`, hold at the
stage-2 wholesale prices. -/
def Play2.Feasible (ω : Params) (P : Play2) (S : ℝ) : Prop :=
  0 ≤ S ∧ ∀ l, 0 ≤ mfrGross2 ω P.price (P.wholesale S) l - S

/-- The retailer's objective (14), p.15, at fee `S`: its profit (3) from `A = {1,2}` at the
stage-2 wholesale prices and its stage-3 retail prices. -/
noncomputable def Play2.payoff (ω : Params) (P : Play2) (S : ℝ) : ℝ :=
  retailerProfit ω Finset.univ (P.wholesale S) (P.price (P.wholesale S)) S

/-- The retailer's equilibrium profit `Π^{|2|}_r` of the `|A| = 2` subgame under the profile. -/
noncomputable def Play2.value (ω : Params) (P : Play2) : ℝ := P.payoff ω P.fee

/-- `P` is an equilibrium of the `|A| = 2` subgame (§4.2, pp.14–15): the pricing is optimal after
every wholesale-price pair (stage 3), the wholesale prices after every fee `S ≥ 0` are a
stage-2 equilibrium (13), and in stage 1

* with slotting fees (`fees = true`): the fee maximizes (14) subject to (15)–(16);
* in the benchmark (`fees = false`, §5.2, p.20): the fee is `0`. -/
def IsEq2 (fees : Bool) (ω : Params) (P : Play2) : Prop :=
  IsOptPricing2 ω P.price ∧
  (∀ S, 0 ≤ S → IsSelectedNE2 ω P.price S (P.wholesale S)) ∧
  if fees then
    P.Feasible ω P.fee ∧ ∀ S, P.Feasible ω S → P.payoff ω S ≤ P.payoff ω P.fee
  else P.fee = 0

end SlottingFees


