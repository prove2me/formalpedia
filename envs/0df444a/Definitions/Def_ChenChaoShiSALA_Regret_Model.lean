-- Prove2me | Definitions.Def_ChenChaoShiSALA_Regret_Model
-- name    : ChenChaoShiSALA_Regret_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:16:48.261996+00:00
-- url     : https://prove2.me/theorems/b7902d07-d70d-4a0c-98ba-94bfc104096d
-- title:
--   Sections 2.1–2.5 — market, noise law, benchmark and standing assumptions
-- statement:
--   A market consists of real prices $p^l,p^h$, shortage and holding costs $b,h$, a demand-price function $\lambda:\mathbb R\to\mathbb R$, and a real noise measure $\nu$. The price set is $P=[p^l,p^h]$, $F(x)=\nu(( -\infty,x])$, $f=F'$, $q(p)=(b+p)/(b+p+h)$ and $z^*(p)=\inf\{x:q(p)\le F(x)\}$. Write $\sigma=(\int x^2\,d\nu)^{1/2}$, with zero mean required below. Period profit is $p\min(d,y)-h(y-d)^+-b(d-y)^+$. Its expectation is $Q(p,y)=p\lambda(p)-(b+p)\int(\lambda(p)+x-y)^+d\nu-h\int(y-\lambda(p)-x)^+d\nu$. Define $G(p)=Q(p,\lambda(p)+z^*(p))$, the least maximizer $p^*$ of $G$ over $P$, and $y^*=\lambda(p^*)+z^*(p^*)$. Inventory optimization is over all real levels.
--
--   Fixed constants $A,M,\theta_1,\theta_2,\theta_3,\kappa,r,a$ are positive. Standing assumptions require $p^l<p^h$, $h>0$, $b\ge0$, $b+p>0$ on $P$, nonincreasing demand on $[p^l-A,p^h+A]$, a probability noise law with zero mean and finite second moment, and an everywhere differentiable CDF. The defined $p^*$ must attain the continuous-price maximum and lie in the interior. The density satisfies $f(x)\le\theta_1e^{-\theta_2x}$ for $x\ge\theta_3$, and $f(x)\ge r$ for $|x-z^*(p)|\le\kappa$, $p\in P$. The inventory-optimized profit has two derivatives on $P$ and $G''\le-a$. Horizon-dependent demand smoothness is separately specified. An error sequence on any probability space consists of independent measurable variables, each with law $\nu$; the sample support may be all of $\mathbb R$.
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, pp. 6–9, (1)–(3), Assumption 1; p. 16, safety stock

import Mathlib
import Definitions.Def_InventoryBounds_Primitives
import Definitions.Def_DataDrivenNV_LRS_Setting

open MeasureTheory ProbabilityTheory
noncomputable section

namespace ChenChaoShiSALA.Regret

structure Market where
  low : ℝ
  high : ℝ
  b : ℝ
  h : ℝ
  demand : ℝ → ℝ
  noise : Measure ℝ

def Market.prices (e : Market) : Set ℝ := Set.Icc e.low e.high

def Market.cdf (e : Market) (x : ℝ) : ℝ := (e.noise (Set.Iic x)).toReal

def Market.density (e : Market) : ℝ → ℝ := deriv e.cdf

def Market.quantileLevel (e : Market) (p : ℝ) : ℝ := (e.b + p) / (e.b + p + e.h)

def Market.stock (e : Market) (p : ℝ) : ℝ := DataDrivenNV.LRS.critQuantile e.noise (e.b + p) e.h

def Market.sigma (e : Market) : ℝ := Real.sqrt (∫ x : ℝ, x ^ 2 ∂e.noise)

def Market.profit (e : Market) (p y d : ℝ) : ℝ :=
  p * InventoryBounds.sales y d - InventoryBounds.stageCost e.h e.b y d

def Market.Q (e : Market) (p y : ℝ) : ℝ :=
  p * e.demand p - (e.b + p) * (∫ x : ℝ, max (e.demand p + x - y) 0 ∂e.noise) -
    e.h * (∫ x : ℝ, max (y - e.demand p - x) 0 ∂e.noise)

/-- The inventory-optimized profit and its continuous-price maximizer. -/
def Market.G (e : Market) (p : ℝ) : ℝ := e.Q p (e.demand p + e.stock p)

def Market.optimalPrices (e : Market) : Set ℝ :=
  {p | p ∈ e.prices ∧ ∀ q ∈ e.prices, e.G q ≤ e.G p}

def Market.pStar (e : Market) : ℝ := sInf e.optimalPrices

def Market.yStar (e : Market) : ℝ := e.demand e.pStar + e.stock e.pStar

structure Constants where
  A : ℝ
  M : ℝ
  theta1 : ℝ
  theta2 : ℝ
  theta3 : ℝ
  kappa : ℝ
  r : ℝ
  a : ℝ

/-- The horizon-independent standing assumptions, §2 and Assumption 1(i),(iii)-(v). -/
structure Standing (e : Market) (c : Constants) : Prop where
  price_order : e.low < e.high
  holding_pos : 0 < e.h
  shortage_nonneg : 0 ≤ e.b
  critical_pos : ∀ p ∈ e.prices, 0 < e.b + p
  A_pos : 0 < c.A
  M_pos : 0 < c.M
  theta1_pos : 0 < c.theta1
  theta2_pos : 0 < c.theta2
  theta3_pos : 0 < c.theta3
  kappa_pos : 0 < c.kappa
  r_pos : 0 < c.r
  a_pos : 0 < c.a
  demand_antitone : AntitoneOn e.demand (Set.Icc (e.low - c.A) (e.high + c.A))
  noise_probability : IsProbabilityMeasure e.noise
  noise_integrable : Integrable (fun x : ℝ => x) e.noise
  noise_square_integrable : Integrable (fun x : ℝ => x ^ 2) e.noise
  noise_centered : (∫ x : ℝ, x ∂e.noise) = 0
  cdf_differentiable : Differentiable ℝ e.cdf
  interior : e.pStar ∈ Set.Ioo e.low e.high
  optimal : e.pStar ∈ e.optimalPrices
  right_tail : ∀ x : ℝ, c.theta3 ≤ x → e.density x ≤ c.theta1 * Real.exp (-c.theta2 * x)
  density_lower : ∀ p ∈ e.prices, ∀ x ∈ Set.Icc (e.stock p - c.kappa) (e.stock p + c.kappa),
    c.r ≤ e.density x
  G_differentiable : ∀ p ∈ e.prices, DifferentiableAt ℝ e.G p
  G_twice_differentiable : ∀ p ∈ e.prices, DifferentiableAt ℝ (deriv e.G) p
  strong_concavity : ∀ p ∈ e.prices, deriv (deriv e.G) p ≤ -c.a

/-- Independent measurable errors with the specified common law; no residual independence. -/
def NoiseSequence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Market) (err : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Measurable (err t)) ∧ iIndepFun err μ ∧
    ∀ t, Measure.map (err t) μ = e.noise

end ChenChaoShiSALA.Regret


