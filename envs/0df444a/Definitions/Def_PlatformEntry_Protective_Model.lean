-- Prove2me | Definitions.Def_PlatformEntry_Protective_Model
-- name    : PlatformEntry_Protective_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:49.453729+00:00
-- url     : https://prove2.me/theorems/3a750b83-84bb-4b98-92fa-30f926f22e82
-- title:
--   §3–§4, (5)–(10), PDF pp. 7–18, 33–36 — parameters, condition (5), H, the profits (6)–(7), Δ, the benchmarks (9)–(10) and the seller's piecewise profit Π^S
-- statement:
--   This module fixes the closed-form model of the seller's first-stage effort problem in Qi, Song and Xiao's model of a retail platform that may enter a third-party seller's product space.
--
--   The parameters are real numbers: the degree of spillover $\delta$, the referral rate $f$, the competition intensity $\beta$, the seller's effort-cost coefficient $c_S$ and the platform's fixed entry cost $K$; the platform's effort-cost coefficient is normalized to $c_P=1/2$. The standing ranges of §3 are $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ (the predicate `InBox`) and $c_S>1/2$. The seller's product has base value $a$ and she chooses an effort $e_S$, so the second-stage product value is $a+e_S$. The module defines:
--
--   1. **Condition (5)**: $N_5(\delta,f,\beta)=4(1+\delta)-2\beta(2-\delta+\delta^2)+\beta^3(1+f)-\beta^2(2+f+\delta f)>0$.
--   2. **The denominator** $D=8-8\delta^2f+8\beta\delta(1+f)-2\beta^3\delta f(1+f)+\beta^4(1+f)^2+2\beta^2(-4-3f+\delta^2(-1+f^2))$ and **(8)**: $H=N_5^2/D^2$ if (5) holds, $H=0$ otherwise.
--   3. **The seller's two-stage profits (6)–(7)**:
--   $$\Pi^S_N(e_S)=\frac{(1-f)(a+e_S)^2}{2}-c_Se_S^2,\qquad \Pi^S_E(e_S)=\Big(\frac14+H\Big)(1-f)(a+e_S)^2-c_Se_S^2 .$$
--   4. **The platform's entry gain** (proof of Proposition 1), with $E_N$ the bracketed polynomial printed there:
--   $$\Pi^P_{E-N}=-\frac{(a+e_S)^2E_N}{4D}-K,\qquad \Delta=\sqrt{-\frac{4KD}{E_N}} .$$
--   5. **The benchmarks (9)–(10)**: $e^B_N(a)=\frac{(1-f)a}{f+2c_S-1}$ and $e^B_E(a)=\frac{a(1-f)(1+4H)}{4c_S-(1-f)(1+4H)}$.
--   6. **The seller's total profit** $\Pi^S(e_S)=\Pi^S_N(e_S)$ if $e_S+a\le\Delta$ and $\Pi^S_E(e_S)$ if $e_S+a>\Delta$ (p. 15), and the notion of an **optimal effort**: a global maximizer of $\Pi^S$ over all real $e_S$, ties allowed.
--   7. The seller's **stage-1 profit** $q_1(a+e_S-q_1)(1-f)-c_Se_S^2$ and the auxiliary function of the proof of Proposition 3, $M(a)=\Pi^S_N(\Delta-a)-\Pi^S_E(e^B_E(a))$.
--
--   These are the objects of Proposition 3 and of every step of its proof.
--
--   **Formalization Note** Every polynomial is written term for term as printed. $\Delta$ and $\Pi^P_{E-N}$ are the paper's formulas for the case where (5) holds; the formulas for the other case are not defined, because every theorem of this mission assumes (5). The closed forms (6), (7) and $\Pi^P_{E-N}$ are taken as definitions here; their derivation from the second-stage game (Lemmas 1–2) is the subject of a companion mission. Real division and `Real.sqrt` are total in Lean ($x/0=0$, $\sqrt{x}=0$ for $x<0$), so the theorems carry (5), the box and $K>0$, under which $D>0$, $E_N<0$ and the radicand is positive.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF pp. 7–10 (§3), p. 12 (5), p. 15 (6)–(8) and Π^S, pp. 17–18 (9)–(10), PDF pp. 33–34 (proof of Proposition 1: Π^P_{E−N}, Δ), PDF p. 36 (proof of Proposition 3: Π^S, M(a))

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Protective

/-- The bracketed polynomial in the numerator of Π^P_{E−N} and in the denominator of Δ
(proof of Proposition 1, Online Supplement, PDF pp. 33–34). -/
def EN (δ f β : ℝ) : ℝ :=
  β ^ 4 * f * (1 + f) ^ 2 + 8 * β * (1 + f) * (2 + δ * f) - 2 * β ^ 3 * f * (1 + f) * (2 + δ * f)
    - 8 * (2 + 2 * δ * f + δ ^ 2 * (-1 + f) * f)
    + 2 * β ^ 2 * (-2 - (2 + δ ^ 2) * f - (2 - 2 * δ + δ ^ 2) * f ^ 2 + δ ^ 2 * f ^ 3)

/-- Π^P_{E−N}(e_S) = Π^P_{2,E} − Π^P_{2,N} when (5) holds (proof of Proposition 1, PDF p. 33):
the platform's stage-2 gain from entering, as a function of the inferred value A = a + e_S,
with fixed entry cost K. -/
noncomputable def entryGain (δ f β K A : ℝ) : ℝ := -(A ^ 2 * EN δ f β) / (4 * PlatformEntry.Regimes.D δ f β) - K

/-- The entry threshold Δ when (5) holds (proof of Proposition 1, PDF p. 34):
Δ = √(−K·4D / EN). -/
noncomputable def Delta (δ f β K : ℝ) : ℝ := Real.sqrt (-(K * (4 * PlatformEntry.Regimes.D δ f β)) / EN δ f β)

/-- (9), p. 17: the first-best effort e^B_N(a) assuming the platform never enters. -/
noncomputable def eBN (f cS a : ℝ) : ℝ := (1 - f) * a / (f + 2 * cS - 1)

/-- (10), p. 18: the first-best effort e^B_E(a) assuming the platform always enters. -/
noncomputable def eBE (δ f β cS a : ℝ) : ℝ :=
  a * (1 - f) * (1 + 4 * PlatformEntry.Regimes.H δ f β) / (4 * cS - (1 - f) * (1 + 4 * PlatformEntry.Regimes.H δ f β))

/-- The seller's total profit Π^S(e_S), p. 15 and p. 36: the non-entry profit (6) if
e_S + a ≤ Δ, the entry profit (7) if e_S + a > Δ. -/
noncomputable def sellerTotal (δ f β cS K a e : ℝ) : ℝ := by
  classical exact if e + a ≤ Delta δ f β K then PlatformEntry.Regimes.profitN δ f β cS a e else PlatformEntry.Regimes.profitE δ f β cS a e

/-- `e` is an optimal first-stage effort for base value `a`: a global maximizer of Π^S over all
real efforts (ties allowed). -/
def IsOptimalEffort (δ f β cS K a e : ℝ) : Prop :=
  ∀ e' : ℝ, sellerTotal δ f β cS K a e' ≤ sellerTotal δ f β cS K a e

/-- M(a) = Π^S_N(Δ − a) − Π^S_E(e^B_E(a)) of the proof of Proposition 3 (PDF p. 36). -/
noncomputable def Mfun (δ f β cS K a : ℝ) : ℝ :=
  PlatformEntry.Regimes.profitN δ f β cS a (Delta δ f β K - a) - PlatformEntry.Regimes.profitE δ f β cS a (eBE δ f β cS a)

end PlatformEntry.Protective


