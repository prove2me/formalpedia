-- Prove2me | Definitions.Def_DarkKnights_ActiveBuyerModel
-- name    : DarkKnights_ActiveBuyerModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:44.66699+00:00
-- url     : https://prove2.me/theorems/bb738a3e-4efe-4bfb-884d-0d9a263b6da8
-- title:
--   Active-CDS-buyer model: CDS price (4), debt value (5)–(6), firm value (2), its subgame-perfect equilibria
-- statement:
--   The model of §1, in which only the CDS buyer (the lender) intervenes.
--
--   The owner picks capital $k\ge0$ and face value of debt $b\ge0$; the lender then picks a hedge ratio $h\in[0,1]$ (p.9); nature draws $z\sim U[0,Z]$; the equity holders take the default decision with face value $b$ and protection $hb$.
--
--   1. The fair **CDS price** (4) is $C(k,b,h)=\mathbb E[hb\,\mathbf 1\{\text{liquidation}\}]$.
--   2. The lender's payoff before the premium (5) is $\psi(k,b,h)=\mathbb E[\text{debt payoff}+hb\,\mathbf 1\{\text{liquidation}\}]$, and the **value of debt** is $M(k,b,h)=\psi(k,b,h)-C(k,b,h)$ (6).
--   3. The owner's **firm value** for given $(k,b,h)$, the objective of (2), is
--   $$
--   V(k,b,h)=M(k,b,h)-k+(1-\tau)\,\mathbb E[\text{equity payoff}],
--   $$
--   with tax rate $\tau$.
--   4. A lender **best response** (3) is an $h\in[0,1]$ maximizing $M(k,b,\cdot)$ over $[0,1]$.
--   5. A **subgame-perfect equilibrium** is a lender strategy $h(k,b)$ that is a best response after every $k,b\ge0$, together with $(k^*,b^*)$, $k^*,b^*\ge0$, maximizing $V(k,b,h(k,b))$. Its **value** is $V(k^*,b^*,h(k^*,b^*))$.
--
--   These are the objects of eqs. (2)–(9) and of the first model compared in Proposition 1.
--
--   **Formalization Note** The equilibrium is defined by the optimality conditions only, never by the closed forms (7)–(9). The hedge ratio is restricted to $[0,1]$ as in §1 (p.9).
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §1, eqs. (2)–(6), pp.11–12 (PDF 13–14); hedge ratio in [0,1], p.9 (PDF 11); timeline Figure 1, p.32

import Mathlib
import Definitions.Def_DarkKnights_Primitives

open MeasureTheory

namespace DarkKnights

/-- Model 1 (active CDS buyer), fair CDS price, eq. (4).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §1, eq. (4), p.11 (PDF p.13):
`C(k, b, h) = E[h b · 1{liquidation}]`, the expected CDS payment, the face value in force being
`b` and the lender's protection `h b`. -/
noncomputable def cdsPrice1 (α Z k b h : ℝ) : ℝ :=
  expect Z (fun z => h * b * liqInd (assetValue α z k) b (h * b))

/-- Model 1, the lender's expected payoff before the premium, eq. (5), p.11 (PDF p.13):
`ψ(k, b, h) = E[debt payoff from the firm + h b · 1{liquidation}]`. -/
noncomputable def lenderGross1 (α Z k b h : ℝ) : ℝ :=
  expect Z (fun z => debtPayoff (assetValue α z k) b (h * b)
    + h * b * liqInd (assetValue α z k) b (h * b))

/-- Model 1, the value of debt net of the CDS premium, `M(k, b, h) = ψ(k, b, h) − C(k, b, h)`,
p.12 (PDF p.14), eqs. (5)–(6). -/
noncomputable def debtValue1 (α Z k b h : ℝ) : ℝ :=
  lenderGross1 α Z k b h - cdsPrice1 α Z k b h

/-- Model 1, the owner's (cum-dividend) firm value for given `(k, b, h)`, the objective of
eq. (2), p.11 (PDF p.13): `V(k, b, h) = M(k, b, h) − k + (1 − τ) E[equity payoff]`. -/
noncomputable def firmValue1 (α Z τ k b h : ℝ) : ℝ :=
  debtValue1 α Z k b h - k + (1 - τ) * expect Z (fun z => equityPayoff (assetValue α z k) b (h * b))

/-- Model 1, the lender's best response, eq. (3), p.11 (PDF p.13), with the §1 restriction
`h ∈ [0, 1]` (p.9, PDF p.11: "we assume that the optimal hedge ratio is h∗ ∈ [0, 1]"). -/
def IsLenderBR1 (α Z k b h : ℝ) : Prop :=
  h ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ h' ∈ Set.Icc (0 : ℝ) 1, debtValue1 α Z k b h' ≤ debtValue1 α Z k b h

/-- A subgame-perfect equilibrium of model 1 (§1, timeline Figure 1, p.32; eqs. (2)–(3),
p.11): a lender strategy `hfun` that is a best response (3) after every `(k, b)` with
`k, b ≥ 0`, and an owner choice `(k, b)`, `k, b ≥ 0`, maximizing `V(k, b, hfun k b)` (2). -/
structure Equilibrium1 (α Z τ : ℝ) where
  /-- The lender's hedge ratio after the owner's choice `(k, b)`. -/
  hfun : ℝ → ℝ → ℝ
  /-- The owner's capital. -/
  k : ℝ
  /-- The owner's face value of debt. -/
  b : ℝ
  hfun_br : ∀ k' b' : ℝ, 0 ≤ k' → 0 ≤ b' → IsLenderBR1 α Z k' b' (hfun k' b')
  k_nonneg : 0 ≤ k
  b_nonneg : 0 ≤ b
  opt : ∀ k' b' : ℝ, 0 ≤ k' → 0 ≤ b' →
    firmValue1 α Z τ k' b' (hfun k' b') ≤ firmValue1 α Z τ k b (hfun k b)

/-- The ex ante firm value of a model-1 equilibrium, `V(k*, b*, h(k*, b*))`, eq. (2). -/
noncomputable def Equilibrium1.value {α Z τ : ℝ} (E : Equilibrium1 α Z τ) : ℝ :=
  firmValue1 α Z τ E.k E.b (E.hfun E.k E.b)

end DarkKnights


