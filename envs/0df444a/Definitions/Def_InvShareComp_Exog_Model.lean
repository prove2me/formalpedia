-- Prove2me | Definitions.Def_InvShareComp_Exog_Model
-- name    : InvShareComp_Exog_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:18.030979+00:00
-- url     : https://prove2.me/theorems/42773856-0252-4b3b-9a11-5eb98e4947a7
-- title:
--   §3.1, §4, pp. 7–13; (A.1) — two retailers competing on service, sharing inventory at transfer price t: profits (1), (3), symmetric equilibria, ŝᴺ, ŝ, centralized profit
-- statement:
--   This file sets up the exogenous-inventory model of Guo and Jiang's *Inventory Sharing under Service Competition*.
--
--   **Parameters.** Two retailers sell one product at price $p$. Pre-season inventory costs $c$ per unit, a quick-response order from the manufacturer costs $\bar c$ per unit, a unit of inventory shipped between the retailers costs $\delta$, providing service level $s_i$ costs $k s_i^2$, and $\beta$ measures how strongly demand reacts to the service gap. The standing assumptions of §3.1 are
--   $$0\le c<\bar c\le p,\qquad k>0,\qquad \beta\ge 0,\qquad 0\le\delta<\bar c .$$
--
--   **Demand.** Retailer $i$'s demand is $D_i=\varepsilon_i\,d_i(s_i,s_j)$ with deterministic part
--   $$d_i(s_i,s_j)=\tfrac12+\beta(s_i-s_j).$$
--   The demand factors $(\varepsilon_1,\varepsilon_2)$ have a joint law $\nu$ which is a probability measure on $[0,1]^2$, is exchangeable ($(\varepsilon_1,\varepsilon_2)$ and $(\varepsilon_2,\varepsilon_1)$ have the same law) and has a density. The mean is $\mu=E[\varepsilon_1]$.
--
--   **Profits.** Without sharing, retailer $i$ with inventory $I_i$ earns, as in (1),
--   $$\pi_i^N(s_i,I_i\mid s_j)=p\,E[\varepsilon_i d_i]-\bar c\,E[(\varepsilon_i d_i-I_i)^+]-k s_i^2-cI_i .$$
--   With sharing at transfer price $t$, it earns, as in (3),
--   $$\pi_i(s_i,I_i\mid s_j,I_j)=p\,E[\varepsilon_i d_i]+t\,E[(\min\{I_i-\varepsilon_i d_i,\varepsilon_j d_j-I_j\})^+]-(t+\delta)\,E[(\min\{\varepsilon_i d_i-I_i,I_j-\varepsilon_j d_j\})^+]-\bar c\,E[((\varepsilon_i d_i-I_i)^+-(I_j-\varepsilon_j d_j)^+)^+]-ks_i^2-cI_i .$$
--
--   **Equilibria.** A deviation $s'$ against $s$ is feasible when both deterministic demands stay non-negative. A profile $(s,s)$ is a *symmetric equilibrium* of the sharing subgame at $t$ (resp. the no-sharing subgame) with $I_1=I_2=I$ when neither retailer gains from any feasible unilateral deviation.
--
--   **Closed forms.** With $A$ and $B$ the region integrals of Lemma 3(a),
--   $$\hat s^N(I)=\frac{\beta\bigl(p\mu-\bar c\int_{2I}^1\varepsilon g(\varepsilon)\,d\varepsilon\bigr)}{2k},\qquad \hat s(t,I)=\frac{\beta(p\mu-A-B)}{2k},$$
--   and $\hat\pi_i(t,I)$, $\hat\pi^N_i(I)$ are the profits at the profiles $(\hat s,\hat s)$ and $(\hat s^N,\hat s^N)$. The quantity $W(I)=E[\varepsilon_1;\ \varepsilon_2<2I\le\varepsilon_1<4I-\varepsilon_2]+E[\varepsilon_2;\ \varepsilon_2<2I,\ \varepsilon_1\ge 4I-\varepsilon_2]$ is the expected shared mass appearing in the proof of Proposition 1(a).
--
--   **Centralized benchmark.** At zero service, a centralized firm earns, as in (A.1),
--   $$\pi^c(I_1,I_2)=p\,E\bigl[\tfrac{\varepsilon_1}2+\tfrac{\varepsilon_2}2\bigr]-\bar c\,E\bigl[(\tfrac{\varepsilon_1}2+\tfrac{\varepsilon_2}2-I_1-I_2)^+\bigr]-\delta\,E\bigl[(\min\{I_1-\tfrac{\varepsilon_1}2,\tfrac{\varepsilon_2}2-I_2\})^++(\min\{I_2-\tfrac{\varepsilon_2}2,\tfrac{\varepsilon_1}2-I_1\})^+\bigr]-c(I_1+I_2).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's iterated integrals against the density $g_{12}$ are written as expectations under $\nu$ of region indicators; open versus closed region boundaries differ by null sets because $\nu$ has a density, and inner integrals with reversed limits (e.g. $\int_0^{4I-\varepsilon_2}$ when $\varepsilon_2>4I$) vanish because $\nu$ lives on $[0,1]^2$. Exchangeability is the Online Appendix's $g_{12}(x,y)=g_{12}(y,x)$, added to the main text's "same distribution". Service levels are real numbers with no sign restriction; the paper imposes none. The upper bound $\beta\le\bar\beta$ of (A.7) is not part of the model: it is not used by the results formalized here. $p$ is kept as a parameter, not normalised to 1.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), pp. 7–13 (PDF 7–13), §3.1, §4.1–4.2, equations (1)–(4); Online Appendix pp. 2–3 (PDF 34–35), Lemma A.1 preamble and (A.1); Online Appendix p. 9 (PDF 41), proof of Proposition 1(a)

import Mathlib

namespace InvShareComp.Exog

open MeasureTheory Classical

/-- Model parameters (§3.1, pp. 7–8): retail price `p`, pre-season unit cost `c`,
quick-response unit cost `cbar` (c̄), service cost factor `k`, service sensitivity `β`,
unit shipping cost `δ` of shared inventory. -/
structure Params where
  p : ℝ
  c : ℝ
  cbar : ℝ
  k : ℝ
  β : ℝ
  δ : ℝ

/-- Standing assumptions of §3.1 (pp. 7–8): `0 ≤ c < c̄ ≤ p`, `k > 0`, `β ≥ 0`, `0 ≤ δ < c̄`. -/
def Params.Standing (P : Params) : Prop :=
  0 ≤ P.c ∧ P.c < P.cbar ∧ P.cbar ≤ P.p ∧ 0 < P.k ∧ 0 ≤ P.β ∧ 0 ≤ P.δ ∧ P.δ < P.cbar

/-- The law `ν` of the demand factors `(ε₁, ε₂)`: a probability measure concentrated on
`[0,1]²`, exchangeable (`g₁₂(x,y) = g₁₂(y,x)`, Online Appendix p. 2) and with a density
(p. 7). -/
structure IsDemandLaw (ν : Measure (ℝ × ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  support : ν (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)ᶜ = 0
  exch : ν.map Prod.swap = ν
  density : ν ≪ volume

/-- Deterministic demand term `dᵢ(sᵢ, sⱼ) = 1/2 + β (sᵢ − sⱼ)` (p. 11). -/
noncomputable def dDet (β si sj : ℝ) : ℝ := 1 / 2 + β * (si - sj)

/-- Per-realization payoff inside the expectation of (3), p. 13, for a retailer with
inventory `Ii`, deterministic demand `di` and demand factor `e`, facing a rival with
inventory `Ij`, deterministic demand `dj` and demand factor `e'`, at transfer price `t`. -/
noncomputable def payShare (P : Params) (t Ii Ij di dj e e' : ℝ) : ℝ :=
  P.p * (e * di) + t * max (min (Ii - e * di) (e' * dj - Ij)) 0
    - (t + P.δ) * max (min (e * di - Ii) (Ij - e' * dj)) 0
    - P.cbar * max (max (e * di - Ii) 0 - max (Ij - e' * dj) 0) 0

/-- Per-realization payoff inside the expectation of (1), p. 11 (no sharing). -/
noncomputable def payNo (P : Params) (Ii di e : ℝ) : ℝ :=
  P.p * (e * di) - P.cbar * max (e * di - Ii) 0

/-- Retailer 1's expected profit (3) under sharing at transfer price `t`. -/
noncomputable def profitShare1 (P : Params) (ν : Measure (ℝ × ℝ)) (t I1 I2 s1 s2 : ℝ) : ℝ :=
  (∫ ω, payShare P t I1 I2 (dDet P.β s1 s2) (dDet P.β s2 s1) ω.1 ω.2 ∂ν)
    - P.k * s1 ^ 2 - P.c * I1

/-- Retailer 2's expected profit (3) under sharing at transfer price `t`. -/
noncomputable def profitShare2 (P : Params) (ν : Measure (ℝ × ℝ)) (t I1 I2 s1 s2 : ℝ) : ℝ :=
  (∫ ω, payShare P t I2 I1 (dDet P.β s2 s1) (dDet P.β s1 s2) ω.2 ω.1 ∂ν)
    - P.k * s2 ^ 2 - P.c * I2

/-- Retailer 1's expected profit (1) without sharing. -/
noncomputable def profitNo1 (P : Params) (ν : Measure (ℝ × ℝ)) (I1 _I2 s1 s2 : ℝ) : ℝ :=
  (∫ ω, payNo P I1 (dDet P.β s1 s2) ω.1 ∂ν) - P.k * s1 ^ 2 - P.c * I1

/-- Retailer 2's expected profit (1) without sharing. -/
noncomputable def profitNo2 (P : Params) (ν : Measure (ℝ × ℝ)) (_I1 I2 s1 s2 : ℝ) : ℝ :=
  (∫ ω, payNo P I2 (dDet P.β s2 s1) ω.2 ∂ν) - P.k * s2 ^ 2 - P.c * I2

/-- A unilateral deviation `si` against `sj` is feasible when both deterministic demands
stay non-negative (p. 7: `dᵢ(sᵢ, sⱼ) ≥ 0`). -/
def Feasible (β si sj : ℝ) : Prop := 0 ≤ dDet β si sj ∧ 0 ≤ dDet β sj si

/-- `(s, s)` is a symmetric equilibrium of the sharing subgame at transfer price `t`
with inventories `I₁ = I₂ = I`. -/
def IsSymEqShare (P : Params) (ν : Measure (ℝ × ℝ)) (t I s : ℝ) : Prop :=
  (∀ s', Feasible P.β s' s → profitShare1 P ν t I I s' s ≤ profitShare1 P ν t I I s s) ∧
  (∀ s', Feasible P.β s' s → profitShare2 P ν t I I s s' ≤ profitShare2 P ν t I I s s)

/-- `(s, s)` is a symmetric equilibrium of the no-sharing subgame with `I₁ = I₂ = I`. -/
def IsSymEqNoShare (P : Params) (ν : Measure (ℝ × ℝ)) (I s : ℝ) : Prop :=
  (∀ s', Feasible P.β s' s → profitNo1 P ν I I s' s ≤ profitNo1 P ν I I s s) ∧
  (∀ s', Feasible P.β s' s → profitNo2 P ν I I s s' ≤ profitNo2 P ν I I s s)

/-- Mean demand factor `μ = E[ε₁]`. -/
noncomputable def mean (ν : Measure (ℝ × ℝ)) : ℝ := ∫ ω, ω.1 ∂ν

/-- The quantity `A` of Lemma 3(a), p. 13, as an expectation over regions. -/
noncomputable def Aval (P : Params) (ν : Measure (ℝ × ℝ)) (t I : ℝ) : ℝ :=
  ∫ ω, ((if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then (t + P.δ) * ω.1 else 0)
    + (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1
        then P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2 else 0)) ∂ν

/-- The quantity `B` of Lemma 3(a), p. 13, as an expectation over regions. -/
noncomputable def Bval (P : Params) (ν : Measure (ℝ × ℝ)) (t I : ℝ) : ℝ :=
  ∫ ω, ((if 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2 then t * ω.2 else 0)
    + (if 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I then t * ω.1 else 0)
    + (if 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1 then P.cbar * ω.1 else 0)) ∂ν

/-- `pμ − A − B`, the numerator of (4) divided by `β`. -/
noncomputable def SVal (P : Params) (ν : Measure (ℝ × ℝ)) (t I : ℝ) : ℝ :=
  P.p * mean ν - Aval P ν t I - Bval P ν t I

/-- `ŝ(t, I) = β (pμ − A − B) / (2k)`, equation (4), p. 13. -/
noncomputable def sHat (P : Params) (ν : Measure (ℝ × ℝ)) (t I : ℝ) : ℝ :=
  P.β * SVal P ν t I / (2 * P.k)

/-- `ŝᴺ(I) = β (pμ − c̄ ∫_{2I}^1 ε g(ε) dε) / (2k)`, equation (2), p. 12. -/
noncomputable def sHatN (P : Params) (ν : Measure (ℝ × ℝ)) (I : ℝ) : ℝ :=
  P.β * (P.p * mean ν - P.cbar * ∫ ω, (if 2 * I ≤ ω.1 then ω.1 else 0) ∂ν) / (2 * P.k)

/-- `π̂ᵢ(t, I) = πᵢ(ŝ(t, I), I | ŝ(t, I), I)`, Lemma 3(c), p. 13. -/
noncomputable def piHat (P : Params) (ν : Measure (ℝ × ℝ)) (t I : ℝ) : ℝ :=
  profitShare1 P ν t I I (sHat P ν t I) (sHat P ν t I)

/-- `π̂ᵢᴺ(I) = πᵢᴺ(ŝᴺ(I), I | ŝᴺ(I))`, Lemma 2(c), p. 12. -/
noncomputable def piHatN (P : Params) (ν : Measure (ℝ × ℝ)) (I : ℝ) : ℝ :=
  profitNo1 P ν I I (sHatN P ν I) (sHatN P ν I)

/-- The expected shared mass `W` in the proof of Proposition 1(a), Online Appendix p. 9:
`∫₀^{2I} (∫_{2I}^{4I−ε₂} ε₁ g₁₂ dε₁ + ∫_{4I−ε₂}^1 ε₂ g₁₂ dε₁) dε₂`. -/
noncomputable def Wval (ν : Measure (ℝ × ℝ)) (I : ℝ) : ℝ :=
  ∫ ω, ((if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then ω.1 else 0)
    + (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then ω.2 else 0)) ∂ν

/-- Centralized profit `πᶜ(I₁, I₂)` of (A.1), Online Appendix p. 3, at service levels
`s₁ᶜ = s₂ᶜ = 0`. -/
noncomputable def centralProfit (P : Params) (ν : Measure (ℝ × ℝ)) (I1 I2 : ℝ) : ℝ :=
  (∫ ω, (P.p * (ω.1 / 2 + ω.2 / 2) - P.cbar * max (ω.1 / 2 + ω.2 / 2 - I1 - I2) 0
      - P.δ * (max (min (I1 - ω.1 / 2) (ω.2 / 2 - I2)) 0
        + max (min (I2 - ω.2 / 2) (ω.1 / 2 - I1)) 0)) ∂ν)
    - P.c * (I1 + I2)

end InvShareComp.Exog


