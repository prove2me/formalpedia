-- Prove2me | Definitions.Def_ChenChaoShiSALA_Regret_Parameters
-- name    : ChenChaoShiSALA_Regret_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:17:31.800994+00:00
-- url     : https://prove2.me/theorems/d968bf54-2bc4-4cb4-a5d6-302e33a85553
-- title:
--   Algorithm 1 — horizon parameters and finite-order smoothness
-- statement:
--   For horizon $T$, set $m=\max\{3,\lceil\sqrt{\log T}\rceil\}$, $L=\lceil T^{1/2+1/(\log T)^{1/3}}\rceil$, $l=\lceil(\log T)^{3/2}T^{1/(4\sqrt{\log T})}\rceil$, $N=L(m+l)m$, $\Delta=T^{-1/4}$ and $B=\lceil\log L\log\log L\rceil$. The spline uses these $m,l$ and the market endpoints. The grid consists of $p^l+k\Delta\le p^h$ for natural $k$, together with $p^h$ explicitly. The extension knots are retained. At a given $T$, demand derivatives of orders $0,\ldots,m$ must exist on $[p^l-A,p^h+A]$ and have absolute value at most the same fixed $M$. Derivative existence is expressed by differentiability of each iterated derivative of order below $m$. Construction-domain conditions are $T\ge3$, $L>1$, $l\ge1$, $N\le T$ and every knot in that extended interval; none is a learning-success event. The real ceiling for $B$ uses integers, so small-horizon negative values are not truncated. Define $\varepsilon(T)=(\log T)^{-1/3}+1/(4\sqrt{\log T})$ and the exact product constant from Remark 1:
--   $$\widetilde K=\frac1a\left(2M+2\sigma+p^h\left(2M+\frac\sigma{p^h-p^l}\right)+\frac1r\right)\left(M+\frac1{r(b+p^l+h)^2}\right).$$
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, p. 9, Assumption 1(ii); p. 12, (7)–(8); p. 15, Remark 1

import Definitions.Def_ChenChaoShiSALA_Regret_Model
import Definitions.Def_ChenChaoShiSALA_Regret_Spline

noncomputable section

namespace ChenChaoShiSALA.Regret

def order (T : ℕ) : ℕ := max 3 ⌈Real.sqrt (Real.log T)⌉₊
def blockLength (T : ℕ) : ℕ := ⌈(T : ℝ) ^ ((1 / 2 : ℝ) + 1 / (Real.log T) ^ (1 / 3 : ℝ))⌉₊
def interiorKnots (T : ℕ) : ℕ :=
  ⌈(Real.log T) ^ (3 / 2 : ℝ) * (T : ℝ) ^ (1 / (4 * Real.sqrt (Real.log T)))⌉₊
def sampleSize (T : ℕ) : ℕ := blockLength T * (order T + interiorKnots T) * order T
def mesh (T : ℕ) : ℝ := (T : ℝ) ^ (-(1 / 4 : ℝ))
def explorationLevel (T : ℕ) : ℝ := (⌈Real.log (blockLength T) * Real.log (Real.log (blockLength T))⌉ : ℤ)
def spline (e : Market) (T : ℕ) : Spline := ⟨e.low, e.high, order T, interiorKnots T⟩

def priceGrid (e : Market) (T : ℕ) : Set ℝ :=
  {p | (∃ k : ℕ, p = e.low + k * mesh T ∧ p ≤ e.high) ∨ p = e.high}

/-- Exactly the derivative orders required at this horizon, including order zero. -/
def HorizonSmooth (e : Market) (c : Constants) (T : ℕ) : Prop :=
  (∀ j ≤ order T, ∀ p ∈ Set.Icc (e.low - c.A) (e.high + c.A),
    |iteratedDeriv j e.demand p| ≤ c.M) ∧
  (∀ j < order T, ∀ p ∈ Set.Icc (e.low - c.A) (e.high + c.A),
    DifferentiableAt ℝ (iteratedDeriv j e.demand) p)

/-- Only deterministic construction-domain conditions, never statistical accuracy. -/
def ConstructionDomain (e : Market) (c : Constants) (T : ℕ) : Prop :=
  3 ≤ T ∧ 1 < blockLength T ∧ 1 ≤ interiorKnots T ∧ sampleSize T ≤ T ∧
    ∀ i ∈ Finset.Icc 1 (2 * order T + interiorKnots T),
      (spline e T).knot i ∈ Set.Icc (e.low - c.A) (e.high + c.A)

def epsilon (T : ℕ) : ℝ :=
  1 / (Real.log T) ^ (1 / 3 : ℝ) + 1 / (4 * Real.sqrt (Real.log T))

def decisionConstant (e : Market) (c : Constants) : ℝ :=
  (1 / c.a) * (2 * c.M + 2 * e.sigma + e.high *
    (2 * c.M + e.sigma / (e.high - e.low)) + 1 / c.r) *
      (c.M + 1 / (c.r * (e.b + e.low + e.h) ^ 2))

end ChenChaoShiSALA.Regret


