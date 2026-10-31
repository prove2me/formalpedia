-- Prove2me | Definitions.Def_CompetingKS_unitOT
-- name    : CompetingKS_unitOT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:31.663098+00:00
-- url     : https://prove2.me/theorems/c0a1d293-6ae3-498d-abe0-3ae5cf84aeb9
-- title:
--   The channels: profits (4)–(5), disagreement points (7)–(8), the units, the sets (6), simultaneous equilibria, $\Delta_1$, $\Delta_2$, $\Phi$
-- statement:
--   This module assembles the two bargaining games.
--
--   Write $R_i,r_i$ for the trade profits of the retail stage. In the **one-to-two channel** the common supplier earns $\Pi_i(w_i,w_j)=R_i(w_i,w_j)+R_j(w_j,w_i)$ and retailer $i$ earns $\pi_i(w_i,w_j)=r_i(w_i,w_j)$. In the **two-to-one channel** supplier $i$ earns $\Pi_i(w_i,w_j)=R_i(w_i,w_j)$ and the common retailer earns $\pi_i(w_i,w_j)=r_i(w_i,w_j)+r_j(w_j,w_i)$.
--
--   Given the contract $w_j$ of the other unit, unit $i$ bargains over $w_i\in[c,a]$. The common party can still trade with the other partner if this negotiation fails, so its disagreement point is the profit from that trade alone,
--   $$
--   D_i(w_j)=R_j\bigl(w_j,\,a-\tfrac{\eta(a-w_j)}2\bigr)\quad\text{(one-to-two)},\qquad d_i(w_j)=r_j\bigl(w_j,\,a-\eta(a-w_j)\bigr)\quad\text{(two-to-one)},
--   $$
--   and the other party's disagreement point is $0$.
--
--   The feasible contract pairs are
--   $$
--   \hat{\mathcal C}=\Bigl\{\tfrac\eta2\le\tfrac{a-w_i}{a-w_j}\le\tfrac2\eta\Bigr\},\qquad \check{\mathcal C}=\Bigl\{\eta\le\tfrac{a-w_i}{a-w_j}\le\tfrac1\eta\Bigr\}.
--   $$
--   A **simultaneous equilibrium** is a pair $(w_1,w_2)$ in $\hat{\mathcal C}$ (resp. $\check{\mathcal C}$) such that each contract is the solution of its unit given the other contract: the Nash equilibrium of the two bargaining problems. There is one such notion for the Kalai–Smorodinsky solution and one for the Nash solution with power $\theta$, in each channel.
--
--   The module also fixes $\Delta_1,\Delta_2$ of Lemma A.5 and the cubic $\Phi$ of display (42).
--
--   **Formalization Note** `normOT`, `normTO` are the units at $a=b=1$, $c=0$, in which the online appendix works. The sets $\hat{\mathcal C},\check{\mathcal C}$ have cleared denominators: they agree with the printed sets for $w_j<a$, $\eta>0$, and also admit pairs with a coordinate equal to $a$. The channel is symmetric, so the two units of an equilibrium are the same function of the other unit's contract.
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, (4)–(6), p.14; contract space, p.15; (7)–(8), p.17; §5.1.2, p.19; online appendix p.2; Δ₁, Δ₂, online appendix p.10; (42), online appendix p.11

import Mathlib
import Definitions.Def_CompetingKS_BargainingUnit
import Definitions.Def_CompetingKS_qOT

namespace CompetingKS

/-- The common supplier's total profit in the one-to-two channel, display (4) of Feng, Li,
Shanthikumar, *Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution*,
accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, p.14:
`Πᵢ(wᵢ, wⱼ) = Rᵢ(wᵢ, wⱼ) + Rⱼ(wⱼ, wᵢ)`. -/
noncomputable def supplierOT (a b c η wi wj : ℝ) : ℝ := ROT a b c η wi wj + ROT a b c η wj wi

/-- Retailer `i`'s profit in the one-to-two channel, display (4): `πᵢ(wᵢ, wⱼ) = rᵢ(wᵢ, wⱼ)`. -/
noncomputable def retailerOT (a b η wi wj : ℝ) : ℝ := rOT a b η wi wj

/-- Supplier `i`'s profit in the two-to-one channel, display (5) of Feng, Li, Shanthikumar,
SSRN 3447674, p.14: `Πᵢ(wᵢ, wⱼ) = Rᵢ(wᵢ, wⱼ)`. -/
noncomputable def supplierTO (a b c η wi wj : ℝ) : ℝ := RTO a b c η wi wj

/-- The common retailer's total profit in the two-to-one channel, display (5):
`πᵢ(wᵢ, wⱼ) = rᵢ(wᵢ, wⱼ) + rⱼ(wⱼ, wᵢ)`. -/
noncomputable def retailerTO (a b η wi wj : ℝ) : ℝ := rTO a b η wi wj + rTO a b η wj wi

/-- The common supplier's disagreement point in unit `i` of the one-to-two channel, display (7) of
Feng, Li, Shanthikumar, SSRN 3447674, p.17: her profit from trading with retailer `j` alone,
`Dᵢ(wⱼ) = Rⱼ(wⱼ, a - η(a - wⱼ)/2)`. -/
noncomputable def disagreeOT (a b c η wj : ℝ) : ℝ := ROT a b c η wj (a - η * (a - wj) / 2)

/-- The common retailer's disagreement point in unit `i` of the two-to-one channel, display (8) of
Feng, Li, Shanthikumar, SSRN 3447674, p.17: his profit from selling supplier `j`'s product alone,
`dᵢ(wⱼ) = rⱼ(wⱼ, a - η(a - wⱼ))`. -/
noncomputable def disagreeTO (a b η wj : ℝ) : ℝ := rTO a b η wj (a - η * (a - wj))

/-- Bargaining unit `i` of the one-to-two channel given the other unit's contract `wⱼ`
(Feng, Li, Shanthikumar, SSRN 3447674, §5.1.1, pp.16–17): contracts `w ∈ [c, a]`, the common
supplier's total profit against retailer `i`'s profit, disagreement point `(Dᵢ(wⱼ), 0)`.

**Formalization Note** The contract space `[c, a]` is the paper's (p.15). The two units are the
same function of the other unit's contract, because the channel is symmetric. -/
noncomputable def unitOT (a b c η wj : ℝ) : BargainingUnit where
  W := Set.Icc c a
  S := fun w => supplierOT a b c η w wj
  B := fun w => retailerOT a b η w wj
  D := disagreeOT a b c η wj
  d := 0

/-- Bargaining unit `i` of the two-to-one channel given the other unit's contract `wⱼ`
(Feng, Li, Shanthikumar, SSRN 3447674, §5.1.1, pp.16–17): contracts `w ∈ [c, a]`, supplier `i`'s
profit against the common retailer's total profit, disagreement point `(0, dᵢ(wⱼ))`. -/
noncomputable def unitTO (a b c η wj : ℝ) : BargainingUnit where
  W := Set.Icc c a
  S := fun w => supplierTO a b c η w wj
  B := fun w => retailerTO a b η w wj
  D := 0
  d := disagreeTO a b η wj

/-- The normalized one-to-two unit, `a = b = 1`, `c = 0`, in which the online appendix of Feng, Li,
Shanthikumar, SSRN 3447674, works (online appendix p.2). -/
noncomputable abbrev normOT (η wj : ℝ) : BargainingUnit := unitOT 1 1 0 η wj

/-- The normalized two-to-one unit, `a = b = 1`, `c = 0`. -/
noncomputable abbrev normTO (η wj : ℝ) : BargainingUnit := unitTO 1 1 0 η wj

/-- The set `Ĉ` of display (6) of Feng, Li, Shanthikumar, SSRN 3447674, p.14:
`η/2 ≤ (a - wᵢ)/(a - wⱼ) ≤ 2/η`.

**Formalization Note** Written with cleared denominators, it agrees with (6) when `wⱼ < a` and
`η > 0`, and it also admits pairs with a coordinate equal to `a`. -/
def InCHat (a η wi wj : ℝ) : Prop := η * (a - wj) ≤ 2 * (a - wi) ∧ η * (a - wi) ≤ 2 * (a - wj)

/-- The set `Č` of display (6): `η ≤ (a - wᵢ)/(a - wⱼ) ≤ 1/η`, with cleared denominators. -/
def InCCheck (a η wi wj : ℝ) : Prop := η * (a - wj) ≤ a - wi ∧ η * (a - wi) ≤ a - wj

/-- A simultaneous KS equilibrium of the one-to-two channel: "the Nash equilibrium of the two
bargaining problems" (Feng, Li, Shanthikumar, SSRN 3447674, §5.1.2, p.19). The pair lies in `Ĉ` and
each contract is the KS solution of its unit given the other contract. -/
def IsKSEqOT (a b c η w₁ w₂ : ℝ) : Prop :=
  InCHat a η w₁ w₂ ∧ (unitOT a b c η w₂).IsKSResponse w₁ ∧ (unitOT a b c η w₁).IsKSResponse w₂

/-- A simultaneous NB equilibrium of the one-to-two channel with retailer bargaining power `θ`. -/
def IsNBEqOT (a b c η θ w₁ w₂ : ℝ) : Prop :=
  InCHat a η w₁ w₂ ∧ (unitOT a b c η w₂).IsNBResponse θ w₁ ∧ (unitOT a b c η w₁).IsNBResponse θ w₂

/-- A simultaneous KS equilibrium of the two-to-one channel. The pair lies in `Č` and each contract
is the KS solution of its unit given the other contract. -/
def IsKSEqTO (a b c η w₁ w₂ : ℝ) : Prop :=
  InCCheck a η w₁ w₂ ∧ (unitTO a b c η w₂).IsKSResponse w₁ ∧ (unitTO a b c η w₁).IsKSResponse w₂

/-- A simultaneous NB equilibrium of the two-to-one channel with retailer bargaining power `θ`. -/
def IsNBEqTO (a b c η θ w₁ w₂ : ℝ) : Prop :=
  InCCheck a η w₁ w₂ ∧ (unitTO a b c η w₂).IsNBResponse θ w₁ ∧ (unitTO a b c η w₁).IsNBResponse θ w₂

/-- The discriminant `Δ₁` of Lemma A.5, Feng, Li, Shanthikumar, SSRN 3447674, online appendix
p.10. -/
def Delta1 (η w : ℝ) : ℝ :=
  (1 - η) ^ 4 + 2 * (1 - η) ^ 3 * (3 + 7 * η) * w - (1 - η) ^ 2 * (3 - 38 * η - 67 * η ^ 2) * w ^ 2
    - 4 * η * (17 - 14 * η - 28 * η ^ 2 + 25 * η ^ 3) * w ^ 3
    + η * (40 - 54 * η - 60 * η ^ 2 + 75 * η ^ 3) * w ^ 4
    - 2 * η * (4 - 12 * η - 6 * η ^ 2 + 15 * η ^ 3) * w ^ 5 - η ^ 2 * (4 - 5 * η ^ 2) * w ^ 6

/-- The discriminant `Δ₂` of Lemma A.5, Feng, Li, Shanthikumar, SSRN 3447674, online appendix
p.10. -/
def Delta2 (η w : ℝ) : ℝ :=
  4 * (1 - η) ^ 2 - 8 * (3 - 5 * η + 3 * η ^ 2 - η ^ 3) * w
    + 4 * (15 - 20 * η + 15 * η ^ 2 - 7 * η ^ 3 + η ^ 4) * w ^ 2
    - 4 * (20 - 20 * η + 20 * η ^ 2 - 9 * η ^ 3 + η ^ 4) * w ^ 3
    + (60 - 40 * η + 60 * η ^ 2 - 20 * η ^ 3 + η ^ 4) * w ^ 4
    - 4 * (6 - 2 * η + 6 * η ^ 2 - η ^ 3) * w ^ 5 + 4 * (1 + η ^ 2) * w ^ 6

/-- The cubic `Φ` of display (42), Feng, Li, Shanthikumar, SSRN 3447674, online appendix p.11:
`Φ(wᵢ, wⱼ) = -2wᵢ³ + (5 - θ)wᵢ² - 2(1 + (1 - θ)(2wⱼ - wⱼ²))wᵢ + (1 - θ)(2wⱼ - wⱼ²)`. -/
def Phi (θ wi wj : ℝ) : ℝ :=
  -2 * wi ^ 3 + (5 - θ) * wi ^ 2 - 2 * (1 + (1 - θ) * (2 * wj - wj ^ 2)) * wi
    + (1 - θ) * (2 * wj - wj ^ 2)

end CompetingKS


