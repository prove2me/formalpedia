-- Prove2me | Definitions.Def_CarbonPolicy_TaxVsCap_Setting
-- name    : CarbonPolicy_TaxVsCap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:31.11501+00:00
-- url     : https://prove2.me/theorems/3741c4a7-11f7-4b85-9527-22d814bfc49b
-- title:
--   §§3–5: two-stage monopoly, policy profits, welfare, and correlation thresholds
-- statement:
--   A monopolist faces uncertain market potential $a$ and permit price $k$ on a probability space. Their means are $\bar a$ and $\bar k$, standard deviations $\sigma_D$ and $\sigma$, and correlation $\rho=\operatorname{Cov}(a,k)/(\sigma_D\sigma)$. The firm first chooses emission intensity $\gamma\in[0,\gamma^+]$, paying $\beta(\gamma^+-\gamma)^2$, then chooses production $q$ after uncertainty is resolved. With demand price $a-bq$ and quota $w$, its operating profit and optimal production rule are
--
--   $$\pi(q;\gamma,a,k)=(a-bq)q-(\gamma q-w)k,\qquad q^*(\gamma,a,k)=\frac{a-\gamma k}{2b}.$$
--
--   Under the tax, the carbon price is fixed at $\bar k$ and the same quota term gives the lump-sum subsidy $w\bar k$. Under cap-and-trade, the price is the random $k$. The first-stage objectives $\Pi_T$ and $\Pi_C$, expected consumer surpluses $CS_T,CS_C$, and expected emissions $S_T,S_C$ are defined as expectations of these production outcomes. An optimal intensity maximizes its regime's expected profit on $[0,\gamma^+]$.
--
--   Assumption 1 is $4b\beta>\bar k^2+\sigma^2$, $4b\beta\gamma^+>\max\{\bar a\bar k,\bar a\bar k+\rho\sigma_D\sigma\}$, and $a>\gamma^+k$ almost surely. The setting also defines the paper's closed-form intensities and the thresholds $R_0,\rho_0,\rho_1,R$ used in its policy comparisons.
--
--   **Formalization Note** $\gamma^+$ is named `γp` in Lean. Demand and permit price are in $L^2$; both variances and $\bar k$ are positive. The real-valued integrals use these assumptions to avoid the nonintegrable default value. The smaller root of the quadratic determines $\rho_0$; outside the root-existence condition its defining function returns zero.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), pp. 8–19, §3, Assumption 1, equations (1)–(6), (8)–(9), Propositions 1–2

import Mathlib

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

noncomputable section

def abar {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → ℝ) : ℝ :=
  ∫ ω, a ω ∂P

def kbar {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (k : Ω → ℝ) : ℝ :=
  ∫ ω, k ω ∂P

def sigmaD {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → ℝ) : ℝ :=
  Real.sqrt (Var[a; P])

def sigma {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (k : Ω → ℝ) : ℝ :=
  Real.sqrt (Var[k; P])

def rho {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a k : Ω → ℝ) : ℝ :=
  cov[a, k; P] / (sigmaD P a * sigma P k)

structure Model (Ω : Type) [MeasurableSpace Ω] where
  P : Measure Ω
  prob : IsProbabilityMeasure P
  a : Ω → ℝ
  k : Ω → ℝ
  a_L2 : MemLp a 2 P
  k_L2 : MemLp k 2 P
  var_a_pos : 0 < Var[a; P]
  var_k_pos : 0 < Var[k; P]
  kbar_pos : 0 < kbar P k

def Assumption1 {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp : ℝ) : Prop :=
  4 * b * β > (kbar M.P M.k) ^ 2 + (sigma M.P M.k) ^ 2 ∧
  4 * b * β * γp > max ((abar M.P M.a) * (kbar M.P M.k))
    ((abar M.P M.a) * (kbar M.P M.k) +
      rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k) ∧
  ∀ᵐ ω ∂M.P, γp * M.k ω < M.a ω

def profit (b w γ a k q : ℝ) : ℝ :=
  (a - b * q) * q - (γ * q - w) * k

def qStar (b γ a k : ℝ) : ℝ :=
  (a - γ * k) / (2 * b)

def PiT {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w γ : ℝ) : ℝ :=
  (∫ ω, profit b w γ (M.a ω) (kbar M.P M.k)
    (qStar b γ (M.a ω) (kbar M.P M.k)) ∂M.P) - β * (γp - γ) ^ 2

def PiC {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w γ : ℝ) : ℝ :=
  (∫ ω, profit b w γ (M.a ω) (M.k ω)
    (qStar b γ (M.a ω) (M.k ω)) ∂M.P) - β * (γp - γ) ^ 2

def OptimalTax {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w γ : ℝ) : Prop :=
  γ ∈ Set.Icc (0 : ℝ) γp ∧ IsMaxOn (PiT M b β γp w) (Set.Icc 0 γp) γ

def OptimalCap {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w γ : ℝ) : Prop :=
  γ ∈ Set.Icc (0 : ℝ) γp ∧ IsMaxOn (PiC M b β γp w) (Set.Icc 0 γp) γ

def CST {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b γT : ℝ) : ℝ :=
  ∫ ω, b * (qStar b γT (M.a ω) (kbar M.P M.k)) ^ 2 / 2 ∂M.P

def CSC {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b γC : ℝ) : ℝ :=
  ∫ ω, b * (qStar b γC (M.a ω) (M.k ω)) ^ 2 / 2 ∂M.P

def ST {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b γT : ℝ) : ℝ :=
  ∫ ω, γT * qStar b γT (M.a ω) (kbar M.P M.k) ∂M.P

def SC {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b γC : ℝ) : ℝ :=
  ∫ ω, γC * qStar b γC (M.a ω) (M.k ω) ∂M.P

def PiDet (b β γp w abar kbar γ : ℝ) : ℝ :=
  (abar - γ * kbar) ^ 2 / (4 * b) + w * kbar - β * (γp - γ) ^ 2

def gammaT0 (b β γp abar kbar : ℝ) : ℝ :=
  (4 * b * β * γp - abar * kbar) / (4 * b * β - kbar ^ 2)

def gammaC0 (b β γp abar kbar sD s r : ℝ) : ℝ :=
  if abar * kbar + r * sD * s > (kbar ^ 2 + s ^ 2) * γp then
    (4 * b * β * γp - abar * kbar - r * sD * s) /
      (4 * b * β - kbar ^ 2 - s ^ 2)
  else γp

def R0 (b β γp abar kbar sD s : ℝ) : ℝ :=
  s / sD * gammaT0 b β γp abar kbar

def rhoC (γp abar kbar sD s : ℝ) : ℝ :=
  ((kbar ^ 2 + s ^ 2) * γp - abar * kbar) / (sD * s)

noncomputable def rho0 (b β γp abar kbar sD s : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ r : ℝ,
        r < (4 * b * β * γp - abar * kbar) / (sD * s) ∧
        R0 b β γp abar kbar sD s +
          sD * s * r ^ 2 / (4 * b * β * γp - abar * kbar) - 2 * r = 0
      then Classical.choose h else 0

def rho1 (b β γp abar kbar sD s : ℝ) : ℝ :=
  (abar * kbar ^ 2 * (2 * kbar * γp - abar) +
    (4 * b * β * s ^ 2 - s ^ 2 * kbar ^ 2 - kbar ^ 4) * γp ^ 2) /
    (2 * sD * s * (4 * b * β - kbar ^ 2) * γp)

noncomputable def R (b β γp abar kbar sD s : ℝ) : ℝ :=
  if rho0 b β γp abar kbar sD s > rhoC γp abar kbar sD s then
    rho0 b β γp abar kbar sD s
  else rho1 b β γp abar kbar sD s

end

end CarbonPolicy.TaxVsCap


