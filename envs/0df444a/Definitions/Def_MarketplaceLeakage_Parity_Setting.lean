-- Prove2me | Definitions.Def_MarketplaceLeakage_Parity_Setting
-- name    : MarketplaceLeakage_Parity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:48.817923+00:00
-- url     : https://prove2.me/theorems/d2e94a8d-81e3-47a8-91c6-ffddcaacc114
-- title:
--   §3.1, §4, §5.4, pp. 5–9, 22–23 — the leakage game with a price-parity clause: uniform G, the seller's profit (1), acceptance under a PPC, Π*_PPC and Π* as attained maxima
-- statement:
--   This file sets up the price-parity-clause (PPC) version of the marketplace-leakage game of Hagiu and Wright.
--
--   **Primitives.** A marketplace $M$ and a seller $S$ face a unit mass of buyers who all value $S$'s product at $v$; $S$'s marginal cost is $c$ (the theorems assume $c<v$). A buyer who buys directly from $S$ rather than on $M$ bears a switching cost $s$. In the baseline state the switching costs are uniformly distributed on $[0,\mu]$ ($\mu>0$), with cumulative distribution function
--   $$G(s)=\min\Big\{\max\Big\{\frac{s}{\mu},0\Big\},1\Big\},$$
--   that is $G(s)=s/\mu$ on $[0,\mu]$, $G(s)=0$ for $s<0$ and $G(s)=1$ for $s>\mu$.
--
--   **The seller's problem without a PPC.** At fee $f$ (per transaction on $M$), with marketplace price $p_m=v$, the seller choosing direct price $p_d\le v$ earns
--   $$\pi(f,p_d)=(p_d-c)\,G(v-p_d)+(v-c-f)\,\big(1-G(v-p_d)\big).$$
--   A direct price $p_d$ is *seller-optimal at $f$* if $p_d\le v$ and $\pi(f,p)\le\pi(f,p_d)$ for every $p\le v$.
--
--   **States.** With probability $q$ switching costs follow $G$ (baseline state); with probability $1-q$ they are infinite, so no buyer ever buys directly (no-switching state). $S$ knows the state when it decides; $M$ does not when it sets its fee.
--
--   **With a PPC.** If $S$ lists it must set $p_d=p_m=v$ and earns $v-c-f$. If it delists it earns $(p_d-c)G(v-p_d)$ at its chosen $c\le p_d\le v$ in the baseline state, and $0$ in the no-switching state. $S$ accepts $M$'s offer in the baseline state iff
--   $$(p_d-c)\,G(v-p_d)\le v-c-f\quad\text{for every } c\le p_d\le v,$$
--   and in the no-switching state iff $0\le v-c-f$ (ties accept). $M$'s expected revenue at a fee $f\in\mathbb R$ is
--   $$R_{PPC}(f)=f\,\big(q\,\mathbf 1[\text{accept in the baseline state}]+(1-q)\,\mathbf 1[\text{accept in the no-switching state}]\big),$$
--   and $V$ is *the PPC value* $\Pi^*_{PPC}$ if $V$ is the greatest value of $R_{PPC}$ over $f\in\mathbb R$ (attained).
--
--   **Without a PPC.** $S$ always lists; in the baseline state it sets a seller-optimal $p_d$, in the no-switching state every buyer buys on $M$. $M$'s expected revenue at fee $f$ and direct price $p_d$ is
--   $$R(f,p_d)=f\big(q(1-G(v-p_d))+(1-q)\big)=f\,\big(1-q\,G(v-p_d)\big),$$
--   and $W$ is *the no-PPC value* $\Pi^*$ if $W$ is the greatest value of $R(f,p_d)$ over fees $f\le v-c$ and seller-optimal $p_d$ at $f$ (attained).
--
--   These objects are the vocabulary of Proposition 4, which compares $\Pi^*_{PPC}$ with $\Pi^*$.
--
--   **Formalization Note.** Both values are defined as attained maxima (`IsGreatest`) over the game's choices, never by the paper's closed-form expressions, so the closed forms are theorems. The seller's delisting maximum $\max_{c\le p_d\le v}(p_d-c)G(v-p_d)$ is not defined either: acceptance quantifies over every delisting price. Acceptance is weak (ties accept), as in the paper's second bullet on p. 23 where $S$ "always accepts" at $f=v-c-\max\{\cdot\}$. Without a PPC, if several seller-optimal prices existed $M$'s value would be computed at the best of them; under the uniform $G$ the seller-optimal price is unique, so this choice is immaterial. The baseline objects $G$, $\pi$ and seller-optimality are not redeclared here: they are `G`, `sProfit` and `IsSOpt` of the shared definition `MarketplaceLeakage.Baseline.Setting`, which this file imports.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 5–9 (§3.1, §4, (1), uniform G on p. 9) and pp. 22–23 (§5.4, price-parity clauses, Π*_PPC and Π*)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Parity

/-- The seller's payoff from delisting in the baseline state at direct price `pd`
(p. 23): `(pd - c) MarketplaceLeakage.Baseline.G(v - pd)`. -/
noncomputable def delistPayoff (v c μ pd : ℝ) : ℝ := (pd - c) * MarketplaceLeakage.Baseline.G μ (v - pd)

/-- Under a PPC, in the baseline state (probability `q`) the seller accepts M's offer at fee `f`
iff listing, which earns `v - c - f`, is at least every delisting payoff
`(pd - c) MarketplaceLeakage.Baseline.G(v - pd)`, `c ≤ pd ≤ v` (ties accept). -/
def AcceptsB (v c μ f : ℝ) : Prop :=
  ∀ pd, c ≤ pd → pd ≤ v → delistPayoff v c μ pd ≤ v - c - f

/-- Under a PPC, in the no-switching state (probability `1 - q`) delisting earns `0`, so the
seller accepts iff listing earns `v - c - f ≥ 0` (ties accept). -/
def AcceptsN (v c f : ℝ) : Prop := 0 ≤ v - c - f

open Classical in
/-- M's expected revenue under a PPC at fee `f ∈ ℝ`: `f` times the probability that the seller
accepts, `q · 1[accepts in the baseline state] + (1 - q) · 1[accepts in the no-switching state]`. -/
noncomputable def ppcRev (v c μ q f : ℝ) : ℝ :=
  f * (q * (if AcceptsB v c μ f then 1 else 0) + (1 - q) * (if AcceptsN v c f then 1 else 0))

/-- `V` is M's optimal profit under a PPC, `Π*_PPC`: the greatest value of `ppcRev` over all
fees `f ∈ ℝ` (attained). -/
def IsPPCValue (v c μ q V : ℝ) : Prop := IsGreatest (Set.range (ppcRev v c μ q)) V

/-- M's expected revenue without a PPC (p. 23) at fee `f` when, in the baseline state, the seller
sets the direct price `pd`: `f (q (1 - MarketplaceLeakage.Baseline.G(v - pd)) + (1 - q)) = f (1 - q MarketplaceLeakage.Baseline.G(v - pd))`. -/
noncomputable def noRev (v μ q f pd : ℝ) : ℝ := f * (1 - q * MarketplaceLeakage.Baseline.G μ (v - pd))

/-- `W` is M's optimal profit without a PPC, `Π*`: the greatest value of `noRev v μ q f pd`
over fees `f ≤ v - c` and seller-optimal direct prices `pd` at `f` (attained). -/
def IsNoPPCValue (v c μ q W : ℝ) : Prop :=
  IsGreatest {w | ∃ f pd, f ≤ v - c ∧ MarketplaceLeakage.Baseline.IsSOpt v c μ f pd ∧ w = noRev v μ q f pd} W

end MarketplaceLeakage.Parity


