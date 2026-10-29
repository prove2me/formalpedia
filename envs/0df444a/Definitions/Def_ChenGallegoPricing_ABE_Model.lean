-- Prove2me | Definitions.Def_ChenGallegoPricing_ABE_Model
-- name    : ChenGallegoPricing_ABE_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:33:05.364134+00:00
-- url     : https://prove2.me/theorems/56c9af1b-6574-4790-ab20-34e7cc96e19e
-- title:
--   Demand, bin conditioning, clairvoyant prices and Assumptions 2–3
-- statement:
--   A demand is a function $D:[0,1)^d\times[0,1]\to[0,1]$, with revenue $f(x,p)=pD(x,p)$. The theorem requires $D$ to be measurable. The optimizer operation chooses an actual maximum over the closed price interval whenever it exists, with zero only as an off-domain fallback. Personalized optimal prices and revenues are computed from $f$, not supplied independently.
--
--   Given a probability law $\mu$, a bin-law family $\nu_B$ is a probability measure supported on each nonempty rectangle $B$, equal to $\mu(B)^{-1}\mu|_B$ when $\mu(B)>0$, and equal to $\delta_x$ on $\{x\}$. Set $f_B(p)=\int f(x,p)\,d\nu_B(x)$ and construct its maximizing price $p^*(B)$ by the same optimizer.
--
--   Assumption 2 bounds both $|f(x,p)-f(y,p)|$ by $M_1\|x-y\|_2$ and $|f(x,p)-f(x,q)|$ by $M_1|p-q|$. Assumption 3 requires, for every rectangle, a unique maximizing price, both inequalities
--   $$M_2(p^*(B)-p)^2\le f_B(p^*(B))-f_B(p)\le M_3(p^*(B)-p)^2,$$
--   containment of $p^*(B)$ between the infimum and supremum of personalized optimal prices on $B$, and a bound of $M_4\operatorname{diam}(B)$ on that supremum minus infimum. All four constants are required positive in the goal. There is no density or full-support condition. Lipschitz continuity and compactness give actual maximizers; bounded measurable revenue makes all displayed bin integrals genuine finite expectations.
--
--   Differences from the source:
--   - reading: conditional bin revenue on every rectangle, including singletons → all supported probability-law versions on null rectangles, normalized restriction on positive-mass rectangles, and Dirac laws on singletons; reason: conditioning on a null event has no canonical law; this retains arbitrary covariate laws and the stated singleton revenues
-- source:
--   Chen and Gallego, Nonparametric Pricing Analytics with Customer Covariates, arXiv:1805.01136v3 (16 February 2020), https://arxiv.org/abs/1805.01136v3; §2, Assumptions 2–3, printed/PDF pp. 7–10

import Mathlib
import Definitions.Def_ChenGallegoPricing_ABE_Geometry

open MeasureTheory ProbabilityTheory

namespace ChenGallegoPricing.ABE

abbrev Demand (d : ℕ) := Ctx d × Price → Price

noncomputable def revenue {d : ℕ} (D : Demand d) (x : Ctx d) (p : Price) : ℝ :=
  (p : ℝ) * (D (x, p) : ℝ)

/-- Choose an actual maximizer when one exists; zero is only an off-domain fallback. -/
noncomputable def optimizer (g : Price → ℝ) : Price := by
  classical
  exact if h : ∃ p, ∀ q, g q ≤ g p then h.choose else ⟨0, by norm_num⟩

noncomputable def optimalPrice {d : ℕ} (D : Demand d) (x : Ctx d) : Price :=
  optimizer (revenue D x)

noncomputable def optimalRevenue {d : ℕ} (D : Demand d) (x : Ctx d) : ℝ :=
  revenue D x (optimalPrice D x)

/-- Bin laws express conditional versions, not an independent revenue oracle. -/
def IsBinLaw {d : ℕ} (μ : Measure (Ctx d)) (ν : Set (Ctx d) → Measure (Ctx d)) : Prop :=
  (∀ B, IsRectangle B → IsProbabilityMeasure (ν B) ∧ ν B Bᶜ = 0 ∧
    (μ B ≠ 0 → ν B = (μ B)⁻¹ • μ.restrict B)) ∧
  ∀ x, ν {x} = Measure.dirac x

noncomputable def binRevenue {d : ℕ} (D : Demand d)
    (ν : Set (Ctx d) → Measure (Ctx d)) (B : Set (Ctx d)) (p : Price) : ℝ :=
  ∫ x, revenue D x p ∂ν B

noncomputable def binOptimalPrice {d : ℕ} (D : Demand d)
    (ν : Set (Ctx d) → Measure (Ctx d)) (B : Set (Ctx d)) : Price :=
  optimizer (binRevenue D ν B)

/-- The two separate Euclidean/price Lipschitz bounds of Assumption 2. -/
def Assumption2 {d : ℕ} (D : Demand d) (M₁ : ℝ) : Prop :=
  (∀ x y p, |revenue D x p - revenue D y p| ≤ M₁ * ‖x.val - y.val‖) ∧
  ∀ x p q, |revenue D x p - revenue D x q| ≤ M₁ * |(p : ℝ) - q|

/-- All three clauses of Assumption 3, on every rectangle, not just dyadic cells. -/
def Assumption3 {d : ℕ} (D : Demand d)
    (ν : Set (Ctx d) → Measure (Ctx d)) (M₂ M₃ M₄ : ℝ) : Prop :=
  ∀ B, IsRectangle B →
    (∃! p : Price, ∀ q, binRevenue D ν B q ≤ binRevenue D ν B p) ∧
    (∀ p : Price,
      M₂ * ((binOptimalPrice D ν B : ℝ) - p) ^ 2 ≤
        binRevenue D ν B (binOptimalPrice D ν B) - binRevenue D ν B p ∧
      binRevenue D ν B (binOptimalPrice D ν B) - binRevenue D ν B p ≤
        M₃ * ((binOptimalPrice D ν B : ℝ) - p) ^ 2) ∧
    (sInf ((fun x => (optimalPrice D x : ℝ)) '' B) ≤ (binOptimalPrice D ν B : ℝ) ∧
      (binOptimalPrice D ν B : ℝ) ≤ sSup ((fun x => (optimalPrice D x : ℝ)) '' B)) ∧
    sSup ((fun x => (optimalPrice D x : ℝ)) '' B) -
      sInf ((fun x => (optimalPrice D x : ℝ)) '' B) ≤ M₄ * diameter B

end ChenGallegoPricing.ABE


