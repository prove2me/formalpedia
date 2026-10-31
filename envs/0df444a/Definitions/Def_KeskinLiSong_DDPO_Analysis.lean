-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_Analysis
-- name    : KeskinLiSong_DDPO_Analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:46:54.3512+00:00
-- url     : https://prove2.me/theorems/c75e7ae1-e0ad-4d47-a75e-7a7d4a50828e
-- title:
--   Profit proxies, detection intervals and sample-cost deviations
-- statement:
--   Optimal profit values are suprema over the nonempty compact stock interval. Detection endpoints use a finite sentinel when no detection occurs. The three regret contributions sum the actual unconstrained-profit gaps over the printed estimation, delay and false-alarm intervals, excluding experimental periods and clipping to T. The false-alarm lower endpoint uses the ec19 intended reading n*tau_minus+1. The one-sided slopes use the ordinary cdf and its left limit; sign infima and suprema use extended reals. Omega retains the exact two expected-loss differences. J uses signed subtraction n-2m and the printed denominator m.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 21–25; ec1, ec8 and ec17–ec19

import Definitions.Def_KeskinLiSong_DDPO_Estimation

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
noncomputable section

namespace KeskinLiSong.DDPO

/-- The supremum is over the nonempty compact stock interval. Under the model's
moment assumptions its continuous objective is bounded and attains its maximum. -/
def G (A : Model) (μ : Measure ℝ) (theta xi : Vector 2) (p : ℝ) : ℝ :=
  sSup ((fun y => Q A μ theta xi p y) '' A.Y)

def Gemp (A : Model) (xi theta : Vector 2) (S : Finset ℕ)
    (M : ℕ) (e : ℕ → ℝ) (p : ℝ) : ℝ :=
  sSup ((fun y => empiricalProfit A xi theta S M e p y) '' A.Y)

def changeCycle (A : Model) (u : Tuning A) (v : Version) {T : ℕ}
    (E : Environment A T) (j : ℕ) : ℕ := (E.changeTime j - 1) / n u v T

/-- A finite endpoint is included in the search, so absence of a detection
never invokes an empty natural-number infimum. -/
def firstDetection {A : Model} (u : Tuning A) (v : Version) (T : ℕ)
    (D : ℕ → ℝ) (after endpoint : ℕ) : ℕ :=
  sInf {τ : ℕ | τ = endpoint ∨
    (after < τ ∧ τ < endpoint ∧ lastReset u v T D τ = τ)}

def detectionPlus (A : Model) (u : Tuning A) (v : Version) {T : ℕ}
    (E : Environment A T) (D : ℕ → ℝ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else firstDetection u v T D (changeCycle A u v E j)
    (changeCycle A u v E (j + 1))

def detectionMinus (A : Model) (u : Tuning A) (v : Version) {T : ℕ}
    (E : Environment A T) (D : ℕ → ℝ) (j : ℕ) : ℕ :=
  firstDetection u v T D (detectionPlus A u v E D j) (changeCycle A u v E (j + 1))

inductive Contribution | estimation | delay | falseAlarm

def contributionRange (part : Contribution) (A : Model) (u : Tuning A)
    (v : Version) {T : ℕ} (E : Environment A T) (D : ℕ → ℝ) (j : ℕ) : Finset ℕ :=
  let start := match part with
    | .estimation => n u v T * detectionPlus A u v E D j + 1
    | .delay => n u v T * changeCycle A u v E j + 1
    | .falseAlarm => n u v T * detectionMinus A u v E D j + 1
  let finish := match part with
    | .estimation => n u v T * detectionMinus A u v E D j
    | .delay => n u v T * detectionPlus A u v E D j
    | .falseAlarm => n u v T * changeCycle A u v E (j + 1)
  (Finset.Icc start finish) ∩ Finset.Icc 1 T

def contributionSample (part : Contribution) (mode : NoiseMode) (A : Model)
    (u : Tuning A) {T : ℕ} (E : Environment A T) (L : Learner mode)
    (opt : ℕ → Action) (z : Paths T) : ℝ :=
  ∑ j ∈ Finset.range (A.changes + 1),
    ∑ t ∈ contributionRange part A u mode.version E (demandPath A E L.policy z) j,
      if t ∉ experimental u mode.version T then
        Q A A.noise.law (E.theta t) E.xi (opt t).1 (opt t).2 -
        Q A A.noise.law (E.theta t) E.xi (actionAt A E L.policy z t).1
          (evaluate A E L.policy L.optimum z t).2
      else 0

def contribution (part : Contribution) (mode : NoiseMode) (A : Model)
    (u : Tuning A) {T : ℕ} (E : Environment A T) (L : Learner mode)
    (opt : ℕ → Action) : ℝ :=
  ∫ z, contributionSample part mode A u E L opt z ∂primitiveLaw A E

def rate (v : Version) (T : ℕ) : ℝ :=
  if v = .N then (T : ℝ) ^ (2 / 3 : ℝ) * Real.sqrt (Real.log T)
  else Real.sqrt T * Real.log T

def cdf (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Iic x)).toReal

def leftCdf (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Iio x)).toReal

def slope (right : Bool) (A : Model) (theta xi : Vector 2) (p y : ℝ) : ℝ :=
  (A.h - A.c + A.b + p) *
    (∫ q, (1 - q) * (if right then cdf A.noise.law else leftCdf A.noise.law)
      ((1 - q) * y - meanDemand A theta p) ∂perishLaw xi) -
    (A.b + p) * (1 - ∫ q, q ∂perishLaw xi) +
    (A.w * (∫ q, q ∂perishLaw xi) + A.c)

/-- The source's two sign sets are interpreted in the extended reals. Empty
sets have infimum +infinity and supremum -infinity, never the real default zero. -/
def rightSignInf (A : Model) (theta xi : Vector 2) (p : ℝ) : EReal :=
  sInf ((fun y : ℝ => (y : EReal)) '' {y ∈ A.Y | 0 ≤ slope true A theta xi p y})

def leftSignSup (A : Model) (theta xi : Vector 2) (p : ℝ) : EReal :=
  sSup ((fun y : ℝ => (y : EReal)) '' {y ∈ A.Y | slope false A theta xi p y < 0})

def omega (A : Model) (theta xi : Vector 2) (p y e : ℝ) : ℝ :=
  (A.h - A.c) *
    ((∫ eps, ∫ q, max ((1 - q) * y - meanDemand A theta p - eps) 0 ∂perishLaw xi ∂A.noise.law) -
      ∫ q, max ((1 - q) * y - meanDemand A theta p - e) 0 ∂perishLaw xi) +
  (A.b + p) *
    ((∫ eps, ∫ q, max (eps - ((1 - q) * y - meanDemand A theta p)) 0 ∂perishLaw xi ∂A.noise.law) -
      ∫ q, max (e - ((1 - q) * y - meanDemand A theta p)) 0 ∂perishLaw xi)

/-- Literal signed index; no truncation of n-2m. -/
def Jindex {A : Model} (u : Tuning A) (v : Version) (T : ℕ)
    (D : ℕ → ℝ) (τ ell : ℕ) : ℤ :=
  (n u v T : ℤ) * lastReset u v T D τ +
    ((n u v T : ℤ) - 2 * m u v T) * ((ell - 1) / m u v T : ℕ) + ell

end KeskinLiSong.DDPO


