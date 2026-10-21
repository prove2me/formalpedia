-- Prove2me | Definitions.Def_BuybackSignal_ReturnsRisk_Model
-- name    : BuybackSignal_ReturnsRisk_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:01.661907+00:00
-- url     : https://prove2.me/theorems/f0c139b3-0f6c-4687-b285-f6a5d50bfab1
-- title:
--   §3–§4.2 and Appendix B — returns-risk buyback signaling model
-- statement:
--   A manufacturer offers a buyback contract $(w,r)$, with wholesale price $w$ and returns price $r$. Baseline demand is $\alpha_h$ with probability $\lambda$ and $\alpha_l$ with probability $\lambda^c=1-\lambda$; demand falls by $\beta p$ when the retailer charges price $p$. The manufacturer honors returns with probability $\theta$, either $\bar\theta$ or $\underline\theta<\bar\theta$. The retailer forms a belief $\hat\theta$ from the contract, orders stock, then chooses a retail price after demand's baseline realizes.
--
--   The retailer order response and manufacturer profit are equations (1) and (2):
--   $$
--   s^R=\frac{\hat\lambda\alpha_h+(1-\hat\lambda)\alpha_l-\beta w}{2}
--   +\frac{1-\hat\lambda}{2}\left[\Delta\alpha-\frac{\beta}{\hat\lambda}(w-\hat\theta r)\right]^+,
--   \qquad
--   \Pi=w s^R-\lambda^c\theta r\frac{\left[\Delta\alpha-(\beta/\lambda)(w-\hat\theta r)\right]^+}{2}.
--   $$
--
--   The model separately defines the retailer's price-stage and ex ante objectives, the realized leftover $s-\min\{\alpha_i-\beta p,s\}$ at a retail price $p$ and the optimal retail prices of (A.1), the symmetric-information benchmark, feasible and maximizing contracts of problem (4), the separating PBE with both types' deviations, and the transformed Appendix B optimization. These definitions are shared by all the theorem statements.
--
--   **Formalization Note** Strict positivity of $\alpha_l$ and $\underline\theta$ is added for the printed benchmark. The prior $\mu$ has no role in the returns-risk claims and is omitted. The real supremum for the price-stage profit ranges over $[0,\alpha_i/\beta]$, a nonempty compact interval under the standing assumptions.
-- source:
--   Wang, Gurnani & Subramanian, The Informational Role of Buyback Contracts, SSRN 3166462 (author's revised version; Management Science 2020), pp. 7–13 (PDF 7–13), §3, §4.1–4.2, (1)–(4); EC pp. 1–10 (PDF 33–42), (A.1), (A.4), (B.4)–(B.7), (B.24)

import Mathlib

namespace BuybackSignal.ReturnsRisk

structure Params where
  αh : ℝ
  αl : ℝ
  β : ℝ
  lam : ℝ
  θbar : ℝ
  θlow : ℝ

namespace Params
noncomputable section

def Standing (P : Params) : Prop :=
  0 < P.αl ∧ P.αl < P.αh ∧ 0 < P.β ∧
  0 < P.lam ∧ P.lam < 1 ∧ 0 < P.θlow ∧ P.θlow < P.θbar ∧ P.θbar ≤ 1
def lamC (P : Params) : ℝ := 1 - P.lam
def dAlpha (P : Params) : ℝ := P.αh - P.αl
def dTheta (P : Params) : ℝ := P.θbar - P.θlow
def alpha (P : Params) : ℝ := P.lam * P.αh + P.lamC * P.αl

/-- Contract action set w ≥ θr ≥ 0, from problems (3) and (4). -/
def actionSet (P : Params) (θ : ℝ) : Set (ℝ × ℝ) :=
  {c | 0 ≤ c.2 ∧ θ * c.2 ≤ c.1}

/-- Retailer's price-stage objective (A.1). -/
def postObj (P : Params) (αi s w r θhat p : ℝ) : ℝ :=
  p * min (αi - P.β * p) s + θhat * r * (s - min (αi - P.β * p) s) - w * s

/-- Optimal posterior profit (A.1) on the compact price interval. -/
noncomputable def postProfit (P : Params) (αi s w r θhat : ℝ) : ℝ :=
  sSup (postObj P αi s w r θhat '' Set.Icc 0 (αi / P.β))

/-- Units of stock s left unsold at retail price p, s − min{dᵢ, s}, as in (A.1). -/
def leftover (P : Params) (αi s p : ℝ) : ℝ := s - min (αi - P.β * p) s

/-- p is an optimal retail price of (A.1) for baseline αi and stock s. -/
def IsOptimalPrice (P : Params) (αi s w r θhat p : ℝ) : Prop :=
  p ∈ Set.Icc 0 (αi / P.β) ∧
    IsMaxOn (P.postObj αi s w r θhat) (Set.Icc 0 (αi / P.β)) p

/-- Retailer's ex ante objective (A.4). -/
noncomputable def exAnteProfit (P : Params) (s w r θhat probHat : ℝ) : ℝ :=
  probHat * P.postProfit P.αh s w r θhat +
  (1 - probHat) * P.postProfit P.αl s w r θhat

/-- Retailer's order formula (1), including the positive part. -/
def sR (P : Params) (w r θhat probHat : ℝ) : ℝ :=
  (probHat * P.αh + (1 - probHat) * P.αl - P.β * w) / 2 +
  ((1 - probHat) / 2) * max (P.dAlpha - (P.β / probHat) * (w - θhat * r)) 0
def unsoldLow (P : Params) (w r θhat probHat : ℝ) : ℝ :=
  max (P.dAlpha - (P.β / probHat) * (w - θhat * r)) 0 / 2
def unsoldHigh (P : Params) (s r θhat : ℝ) : ℝ :=
  max (s - (P.αh - P.β * θhat * r) / 2) 0

/-- Manufacturer's expected profit (2), using response (1). -/
def Pi (P : Params) (w r θhat θ : ℝ) : ℝ :=
  w * P.sR w r θhat P.lam - P.lamC * θ * r * P.unsoldLow w r θhat P.lam

def w0 (P : Params) : ℝ := P.alpha / (2 * P.β)
def r0 (P : Params) (θ : ℝ) : ℝ := P.αl / (2 * P.β * θ)
def pi0 (P : Params) : ℝ :=
  (P.lamC * P.lam * P.dAlpha ^ 2 + P.alpha ^ 2) / (8 * P.β)
def s0 (P : Params) : ℝ := P.αh / 4
def q0 (P : Params) : ℝ := P.dAlpha / 4

/-- Problem (4), including both incentive constraints. -/
def Feasible4 (P : Params) (c : ℝ × ℝ) : Prop :=
  c ∈ P.actionSet P.θbar ∧
  P.Pi c.1 c.2 P.θbar P.θlow ≤ P.pi0 ∧
  P.Pi P.w0 (P.r0 P.θlow) P.θlow P.θbar ≤ P.Pi c.1 c.2 P.θbar P.θbar

/-- A maximizing contract for (4); existence is not assumed. -/
def IsSolution4 (P : Params) (c : ℝ × ℝ) : Prop :=
  P.Feasible4 c ∧ ∀ d : ℝ × ℝ, P.Feasible4 d →
    P.Pi d.1 d.2 P.θbar P.θbar ≤ P.Pi c.1 c.2 P.θbar P.θbar

/-- Pessimistic off-path belief on p. 13. -/
noncomputable def pessimistic (P : Params) (cstar : ℝ × ℝ) : ℝ × ℝ → ℝ :=
  fun c => if c = cstar then P.θbar else P.θlow

/-- Separating PBE under the admissible-deviation convention on p. 10. -/
def IsSeparatingPBE (P : Params) (cBar cLow : ℝ × ℝ)
    (belief : ℝ × ℝ → ℝ) : Prop :=
  cBar ≠ cLow ∧
  (∀ c, P.θlow ≤ belief c ∧ belief c ≤ P.θbar) ∧
  belief cBar = P.θbar ∧ belief cLow = P.θlow ∧
  cBar ∈ P.actionSet P.θbar ∧ cLow ∈ P.actionSet P.θlow ∧
  (∀ c ∈ P.actionSet P.θbar, 0 ≤ c.1 - belief c * c.2 →
    P.Pi c.1 c.2 (belief c) P.θbar ≤ P.Pi cBar.1 cBar.2 P.θbar P.θbar) ∧
  (∀ c ∈ P.actionSet P.θlow, 0 ≤ c.1 - belief c * c.2 →
    P.Pi c.1 c.2 (belief c) P.θlow ≤ P.Pi cLow.1 cLow.2 P.θlow P.θlow)

def wTilde (P : Params) (c : ℝ × ℝ) : ℝ := c.1 - P.w0
def uTilde (P : Params) (c : ℝ × ℝ) : ℝ :=
  c.1 - P.θbar * c.2 - P.lam * P.dAlpha / (2 * P.β)
def quad (P : Params) (w u : ℝ) : ℝ := P.lam * w ^ 2 + P.lamC * u ^ 2
def b6 (P : Params) (w u : ℝ) : ℝ :=
  P.quad w u + (P.lamC * P.dTheta / P.θbar) *
    (w - u + P.αl / (2 * P.β)) * (u - P.lam * P.dAlpha / (2 * P.β))
def b7Bound (P : Params) : ℝ :=
  P.lamC * P.dTheta * P.αl * P.lam * P.dAlpha /
    (4 * P.β ^ 2 * P.θlow)

/-- Domain (B.4), (B.6), and (B.7) for the transformed problem. -/
def TransformedFeasible (P : Params) (z : ℝ × ℝ) : Prop :=
  z.2 ≤ z.1 + P.αl / (2 * P.β) ∧
  -P.lam * P.dAlpha / (2 * P.β) ≤ z.2 ∧
  z.2 ≤ P.lam * P.dAlpha / (2 * P.β) ∧
  0 ≤ P.b6 z.1 z.2 ∧ P.quad z.1 z.2 ≤ P.b7Bound
def IsTransformedSolution (P : Params) (z : ℝ × ℝ) : Prop :=
  P.TransformedFeasible z ∧
  ∀ y : ℝ × ℝ, P.TransformedFeasible y → P.quad z.1 z.2 ≤ P.quad y.1 y.2

/-- Positive root (B.24) of the returns-price-only problem. -/
noncomputable def uDag (P : Params) : ℝ :=
  (-P.alpha * P.dTheta +
    Real.sqrt ((P.alpha * P.dTheta) ^ 2 +
      4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta)) /
    (4 * P.β * P.θlow)

end
end Params
end BuybackSignal.ReturnsRisk


