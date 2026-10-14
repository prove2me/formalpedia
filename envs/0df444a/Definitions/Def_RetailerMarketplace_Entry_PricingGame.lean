-- Prove2me | Definitions.Def_RetailerMarketplace_Entry_PricingGame
-- name    : RetailerMarketplace_Entry_PricingGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:55.368984+00:00
-- url     : https://prove2.me/theorems/693f628b-91fd-4a0b-94d3-d13378e3376b
-- title:
--   §3 and proof of Proposition 1, pp. 4–5, 13 — the Stage-3 pricing games SBM, SBT and SBMT with consumer steering, and their subgame perfect equilibria
-- statement:
--   This file defines the Stage-3 pricing games of one product market $v$ (§2–§3 and the proof of Proposition 1).
--
--   Consumers in the market have unit demand and valuation $v$. A share $\lambda$ is inattentive: they buy from the seller $M$ steers them to, $S\in\{M,T\}$, provided that seller's price does not exceed $v$. The remaining $1-\lambda$ are attentive: they buy from the cheapest seller whose price is at most $v$, with ties broken in favour of $M$. Both firms have unit cost $c$, and $T$ pays the fee $f$ on her sales revenue to $M$.
--
--   1. **SBM** (only $M$ supplies): $M$ chooses a price $p_M$ and steering $S$; his demand is $\lambda[S=M,\ p_M\le v]+(1-\lambda)[p_M\le v]$ and his profit is $(p_M-c)$ times it. $(p_M,S)$ is optimal if no other choice yields more.
--   2. **SBT** (only $T$ supplies): $T$ quotes $p_T$, then $M$ chooses $S$. $T$'s demand is $\lambda[S=T,\ p_T\le v]+(1-\lambda)[p_T\le v]$; $M$ earns $f p_T$ times it and $T$ earns $((1-f)p_T-c)$ times it. A subgame perfect equilibrium is a price $p_T$ and a steering strategy $\sigma(\cdot)$ of $M$ that is a best response to **every** price of $T$, such that $p_T$ maximizes $T$'s profit given $\sigma$.
--   3. **SBMT** (both supply): $T$ quotes $p_T$; then $M$ quotes $p_M$ and chooses $S$. Demands are
--   $$q_M=\lambda[S=M,\ p_M\le v]+(1-\lambda)[p_M\le v,\ (p_T>v \text{ or } p_M\le p_T)],$$
--   $$q_T=\lambda[S=T,\ p_T\le v]+(1-\lambda)[p_T\le v,\ (p_M>v \text{ or } p_T<p_M)],$$
--   with profits $u_M=(p_M-c)q_M+f p_T q_T$ and $u_T=((1-f)p_T-c)q_T$. A subgame perfect equilibrium is a price $p_T$ of $T$ and a strategy $\sigma:p\mapsto(p_M,S)$ of $M$ that is a best response at every price $p$ of $T$ (on and off the equilibrium path), such that $p_T$ maximizes $u_T(p,\sigma(p))$ over all $p$.
--
--   These games are the building blocks whose equilibrium payoffs (Proposition 1) drive the entry stage.
--
--   **Formalization Note** $M$'s strategy is a function of $T$'s price, so the equilibrium notion is subgame perfection, not Nash equilibrium. Prices range over all reals.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, pp. 4–5 and 13 (PDF pp. 6–7, 15), §2 (demand, steering), §3 (sequential pricing game), proof of Proposition 1

import Mathlib

namespace RetailerMarketplace.Entry

/-- M's steering choice for inattentive consumers: to himself (`M`) or to the third party (`T`). -/
inductive Steer
  | M
  | T
  deriving DecidableEq

/-! ### SBM: only M supplies product `v` -/

/-- M's demand when he alone supplies `v` at price `pM` with steering `S`: the inattentive share
`λ` buys if steered to M and `pM ≤ v`; the attentive share `1 - λ` buys if `pM ≤ v`. -/
noncomputable def qM_SBM (lam v pM : ℝ) (S : Steer) : ℝ :=
  (if S = Steer.M ∧ pM ≤ v then lam else 0) + (if pM ≤ v then 1 - lam else 0)

/-- M's profit as the sole supplier. -/
noncomputable def uM_SBM (c lam v pM : ℝ) (S : Steer) : ℝ := (pM - c) * qM_SBM lam v pM S

/-- `(pM, S)` maximizes M's profit as the sole supplier. -/
def IsOptSBM (c lam v pM : ℝ) (S : Steer) : Prop :=
  ∀ p S', uM_SBM c lam v p S' ≤ uM_SBM c lam v pM S

/-! ### SBT: only T supplies product `v`; M chooses steering after observing T's price -/

/-- T's demand when she alone supplies `v` at price `pT` and M steers with `S`. -/
noncomputable def qT_SBT (lam v pT : ℝ) (S : Steer) : ℝ :=
  (if S = Steer.T ∧ pT ≤ v then lam else 0) + (if pT ≤ v then 1 - lam else 0)

/-- M's fee revenue in SBT. -/
noncomputable def uM_SBT (f lam v pT : ℝ) (S : Steer) : ℝ := f * pT * qT_SBT lam v pT S

/-- T's profit in SBT. -/
noncomputable def uT_SBT (c f lam v pT : ℝ) (S : Steer) : ℝ := ((1 - f) * pT - c) * qT_SBT lam v pT S

/-- Subgame perfect equilibrium of the SBT game: T quotes `pT`; M's steering strategy `σ` is a
best response to every price of T, and `pT` maximizes T's profit given `σ`. -/
def IsSPNE_SBT (c f lam v pT : ℝ) (σ : ℝ → Steer) : Prop :=
  (∀ p S, uM_SBT f lam v p S ≤ uM_SBT f lam v p (σ p)) ∧
    ∀ p, uT_SBT c f lam v p (σ p) ≤ uT_SBT c f lam v pT (σ pT)

/-! ### SBMT: both firms supply product `v`; T quotes first, then M quotes and steers -/

/-- M's demand: the inattentive share `λ` if steered to M and `pM ≤ v`; the attentive share
`1 - λ` if `pM ≤ v` and M is the cheapest seller at a price `≤ v` (ties go to M). -/
noncomputable def qM (lam v pT pM : ℝ) (S : Steer) : ℝ :=
  (if S = Steer.M ∧ pM ≤ v then lam else 0) +
    (if pM ≤ v ∧ (v < pT ∨ pM ≤ pT) then 1 - lam else 0)

/-- T's demand: the inattentive share `λ` if steered to T and `pT ≤ v`; the attentive share
`1 - λ` if `pT ≤ v` and T is strictly the cheapest seller at a price `≤ v`. -/
noncomputable def qT (lam v pT pM : ℝ) (S : Steer) : ℝ :=
  (if S = Steer.T ∧ pT ≤ v then lam else 0) +
    (if pT ≤ v ∧ (v < pM ∨ pT < pM) then 1 - lam else 0)

/-- M's profit in SBMT: margin on his own sales plus the fee `f` on T's sales revenue. -/
noncomputable def uM (c f lam v pT pM : ℝ) (S : Steer) : ℝ :=
  (pM - c) * qM lam v pT pM S + f * pT * qT lam v pT pM S

/-- T's profit in SBMT: her sales revenue net of the fee, minus cost. -/
noncomputable def uT (c f lam v pT pM : ℝ) (S : Steer) : ℝ :=
  ((1 - f) * pT - c) * qT lam v pT pM S

/-- Subgame perfect equilibrium of the sequential SBMT pricing game: M's strategy `σ` maps every
price of T to a price and a steering choice that is a best response to it, and `pT` maximizes
T's profit given `σ`. -/
def IsSPNE_SBMT (c f lam v pT : ℝ) (σ : ℝ → ℝ × Steer) : Prop :=
  (∀ p pM S, uM c f lam v p pM S ≤ uM c f lam v p (σ p).1 (σ p).2) ∧
    ∀ p, uT c f lam v p (σ p).1 (σ p).2 ≤ uT c f lam v pT (σ pT).1 (σ pT).2

end RetailerMarketplace.Entry


