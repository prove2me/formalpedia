-- Prove2me | Definitions.Def_DarkKnights_ActiveSellerModel
-- name    : DarkKnights_ActiveSellerModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:34.891792+00:00
-- url     : https://prove2.me/theorems/1c9a8d9b-66c8-4d60-afae-f91e29a8f978
-- title:
--   Active-CDS-seller model: dealer offers, acceptance, Table 3 payoffs, fair premium, debt value and firm value (14)
-- statement:
--   The model of §2, in which the CDS dealer (the protection seller) can also intervene.
--
--   Fix $k,b\ge0$ and a hedge ratio $h\ge0$ (p.14). After $z$ is drawn, the dealer makes a take-it-or-leave-it offer $(b_n,\theta)\in[0,b]\times[0,1]$: inject $b-b_n$, paid to the lender, so that the face value falls to $b_n$, in exchange for an equity stake $\theta$.
--
--   1. The owner **accepts** iff $(1-\theta)\cdot e(b_n)\ge e(b)$, where $e(d)$ is the equity payoff of the default decision with face value $d$ and protection $hb$ (she accepts when indifferent).
--   2. With $D$ the face value in force ($b_n$ if accepted, $b$ if rejected), and $\theta=0$, no injection if rejected, the **ex-post payoffs** (Table 3) are: owner $(1-\theta)\,e(D)$; dealer $\theta\,e(D)-(b-b_n)-hb\,\mathbf 1\{\text{liquidation}\}$; lender $(b-b_n)+(\text{debt payoff under }D)+hb\,\mathbf 1\{\text{liquidation}\}$.
--   3. A dealer strategy $\sigma:z\mapsto(b_n,\theta)$ is **optimal** if at every $z\in[0,Z]$ the offer $\sigma(z)$ is feasible and maximizes the dealer's ex-post payoff over all feasible offers (the upfront premium is sunk, p.17).
--   4. The fair **CDS premium** is zero NPV for the dealer: $\text{premium}=-\mathbb E[\text{dealer's ex-post payoff}]$.
--   5. The **value of debt** is $M=\mathbb E[\text{lender's ex-post payoff}]-\text{premium}$, the owner's **firm value** is $V=M-k+(1-\tau)\,\mathbb E[\text{owner's ex-post payoff}]$ (14), and the **probability of liquidation** is $\frac1Z\,\mathrm{Leb}\{z\in[0,Z]:\text{liquidation}\}$.
--
--   These objects carry Lemmas 2–4, eqs. (13)–(19) and the second model of Proposition 1.
--
--   **Formalization Note** The premium is read from p.18 ("the CDS spread is set so that the protection seller breaks even including the contingent equity injection") and p.8 ("zero–NPV for the protection seller"); on the equilibrium path it equals the bracket of Lemma 4. Integrals are Bochner integrals; a dealer strategy is an arbitrary function, and its payoffs are determined up to the dealer's indifference points.
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, pp.14–18 (PDF 16–20); acceptance and θ, p.16 (PDF 18); dealer objective, p.17 (PDF 19); premium, p.18 (PDF 20) and p.8 (PDF 10); eq. (14), p.20 (PDF 22); Table 3, p.35 (PDF 37)

import Mathlib
import Definitions.Def_DarkKnights_Primitives

open MeasureTheory

namespace DarkKnights

/-- Model 2 (active CDS seller): the dealer's feasible offers `(b_n, θ) ∈ [0, b] × [0, 1]`.
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, p.14 (PDF p.16): after `z` is drawn the dealer offers to reduce
the face value of debt to `b_n ≤ b` by injecting equity `b − b_n`, for an equity stake
`θ ∈ [0, 1]`. -/
def offerSet (b : ℝ) : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) b ×ˢ Set.Icc (0 : ℝ) 1

/-- The owner accepts the offer `o = (b_n, θ)` iff her payoff after acceptance,
`(1 − θ) · (equity payoff with face value b_n)`, is at least her payoff after rejection, the
equity payoff with face value `b` (§2, p.16, PDF p.18; Appendix C, pp.42–43). The lender's
protection is `h b` in both cases.

**Formalization Note** The owner accepts when indifferent: Lemma 2's `θ` is "the equity stake
θ … that makes the owner indifferent between accepting and rejecting" (p.16). -/
def accepts (a b h : ℝ) (o : ℝ × ℝ) : Prop :=
  equityPayoff a b (h * b) ≤ (1 - o.2) * equityPayoff a o.1 (h * b)

open Classical in
/-- The face value of debt in force after the dealer's offer: `b_n` if accepted, `b` if
rejected. -/
noncomputable def faceValue (a b h : ℝ) (o : ℝ × ℝ) : ℝ :=
  if accepts a b h o then o.1 else b

open Classical in
/-- The dealer's equity stake after the offer: `θ` if accepted, `0` if rejected. -/
noncomputable def stake (a b h : ℝ) (o : ℝ × ℝ) : ℝ :=
  if accepts a b h o then o.2 else 0

open Classical in
/-- The dealer's equity injection, paid to the lender to reduce the face value: `b − b_n` if
accepted, `0` if rejected (p.14; Lemma 4's "recapitalization", p.19). -/
noncomputable def injection (a b h : ℝ) (o : ℝ × ℝ) : ℝ :=
  if accepts a b h o then b - o.1 else 0

/-- The owner's ex-post payoff (Table 3, p.35, PDF p.37): `(1 − θ)` times the equity payoff of
the default decision taken with the face value in force. -/
noncomputable def ownerPayoff (a b h : ℝ) (o : ℝ × ℝ) : ℝ :=
  (1 - stake a b h o) * equityPayoff a (faceValue a b h o) (h * b)

/-- The dealer's ex-post payoff, the premium excluded (Table 3, p.35; p.17, PDF p.19: "the
algebraic sum of … his (negative) CDS payoff in liquidation, of his (positive) payoff as a future
equity holder, and his (negative) payoff from injecting equity capital in the amount of b − b_n";
"We do not include his cash inflow from the upfront insurance premium because that is sunk"):
`θ · equity − (b − b_n) − h b · 1{liquidation}`. -/
noncomputable def dealerPayoff (a b h : ℝ) (o : ℝ × ℝ) : ℝ :=
  stake a b h o * equityPayoff a (faceValue a b h o) (h * b) - injection a b h o
    - h * b * liqInd a (faceValue a b h o) (h * b)

/-- The lender's ex-post payoff, the premium excluded (Table 3, p.35; Lemma 4, p.19): the
injection `b − b_n`, plus the payoff from the firm (`b_n` repaid, `b_r = h b` renegotiated,
`0` liquidated), plus the CDS payment `h b` in liquidation. -/
noncomputable def lenderPayoff (a b h : ℝ) (o : ℝ × ℝ) : ℝ :=
  injection a b h o + debtPayoff a (faceValue a b h o) (h * b)
    + h * b * liqInd a (faceValue a b h o) (h * b)

/-- A dealer strategy `σ : z ↦ (b_n, θ)` is optimal for given `(k, b, h)` if at every state
`z ∈ [0, Z]` the offer `σ z` is feasible and maximizes the dealer's ex-post payoff over all
feasible offers (p.17, PDF p.19; Lemma 3 and Appendix D). -/
def IsDealerOptimal (α Z k b h : ℝ) (σ : ℝ → ℝ × ℝ) : Prop :=
  ∀ z ∈ Set.Icc (0 : ℝ) Z, σ z ∈ offerSet b ∧
    ∀ o ∈ offerSet b, dealerPayoff (assetValue α z k) b h o ≤ dealerPayoff (assetValue α z k) b h (σ z)

/-- The fair CDS premium in model 2: zero NPV for the protection seller, including the contingent
equity injection (p.18, PDF p.20: "the CDS spread is set so that the protection seller breaks
even including the contingent equity injection of b − b_n"; p.8: "zero–NPV for the protection
seller"): `premium = −E[dealer's ex-post payoff]`. -/
noncomputable def premium2 (α Z k b h : ℝ) (σ : ℝ → ℝ × ℝ) : ℝ :=
  -expect Z (fun z => dealerPayoff (assetValue α z k) b h (σ z))

/-- Model 2, the value of debt: the lender's expected ex-post payoff net of the premium
(Lemma 4, p.19, PDF p.21: `M(k, b, h)`). -/
noncomputable def debtValue2 (α Z k b h : ℝ) (σ : ℝ → ℝ × ℝ) : ℝ :=
  expect Z (fun z => lenderPayoff (assetValue α z k) b h (σ z)) - premium2 α Z k b h σ

/-- Model 2, the owner's firm value for given `(k, b, h)` and dealer strategy, the objective of
eq. (14), p.20 (PDF p.22): `V = M − k + (1 − τ) E[owner's ex-post payoff]`. -/
noncomputable def firmValue2 (α Z τ k b h : ℝ) (σ : ℝ → ℝ × ℝ) : ℝ :=
  debtValue2 α Z k b h σ - k + (1 - τ) * expect Z (fun z => ownerPayoff (assetValue α z k) b h (σ z))

/-- Model 2, the probability of liquidation (the credit event, p.11) under the dealer strategy
`σ`: `(1/Z) · Leb{z ∈ [0, Z] : the firm is liquidated}`. -/
noncomputable def liqProb2 (α Z k b h : ℝ) (σ : ℝ → ℝ × ℝ) : ℝ :=
  (1 / Z) * (volume {z : ℝ | z ∈ Set.Icc (0 : ℝ) Z ∧
    defaultAction (assetValue α z k) (faceValue (assetValue α z k) b h (σ z)) (h * b)
      = Action.liquidate}).toReal

end DarkKnights


