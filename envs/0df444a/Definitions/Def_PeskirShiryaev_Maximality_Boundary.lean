-- Prove2me | Definitions.Def_PeskirShiryaev_Maximality_Boundary
-- name    : PeskirShiryaev_Maximality_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:24:38.967194+00:00
-- url     : https://prove2.me/theorems/1b6f175c-acb2-4fb3-81b4-47685b45b0fa
-- title:
--   Scale, speed, and admissible free boundaries
-- statement:
--   Normalize the diffusion scale at zero. Write
--
--   $$L'(y)=\exp\!\left(-\int_0^y\frac{2\rho(z)}{\sigma(z)^2}\,dz\right),\quad L(x)=\int_0^xL'(y)\,dy,\quad m(dy)=\frac{2\,dy}{L'(y)\sigma(y)^2}.$$
--
--   The Green kernel on $[a,b]$, for $a<b$, is $(L(b)-L(x))(L(y)-L(a))/(L(b)-L(a))$ when $y\le x$, and $(L(b)-L(y))(L(x)-L(a))/(L(b)-L(a))$ otherwise. An admissible boundary is a globally defined continuously differentiable function $g$ with $g(s)<s$ and
--
--   $$g'(s)=\frac{\sigma(g(s))^2L'(g(s))}{2c(g(s))[L(s)-L(g(s))]}.$$
--
--   A maximal boundary dominates every admissible boundary pointwise. Its associated analytic candidate is $s+\int_{g(s)}^x[L(x)-L(y)]c(y)m(dy)$ in the continuation region, and $s$ for $x\le g(s)$. The free-boundary system comprises the generator equation, inward normal reflection at $x=s$, instantaneous stopping at $x=g(s)$, and inward smooth fit there. A diagonal-contact boundary solves the same equation below a finite contact level and is extended by $g(s)=s$ above it.
--
--   These definitions distinguish ODE solutions from optimal boundaries: no comparison with the stopping value is included.
--
--   **Formalization Note** The analytic integrals use the speed density with Lebesgue measure. The unpatched integral candidate is defined for every real $x,s$ to express inward derivatives. The Green formula is total off its intended domain, but no result uses it at $a=b$ or outside $a\le x,y\le b$.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 200, 204–207, 209–210 (PDF 219, 223–226, 228–229), Eqs. (13.1.6), (13.1.10)–(13.1.11), (13.2.9)–(13.2.12), (13.2.21)–(13.2.22), (13.2.25), (13.2.41)

import Definitions.Def_PeskirShiryaev_Maximality_Diffusion

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

/- Imported declaration context (verbatim, for a self-contained blind code audit):

structure Coefficients where
  drift : ℝ → ℝ
  volatility : ℝ → ℝ
  cost : ℝ → ℝ
  drift_continuous : Continuous drift
  volatility_continuous : Continuous volatility
  volatility_pos : ∀ x, 0 < volatility x
  cost_continuous : Continuous cost
  cost_pos : ∀ x, 0 < cost x

noncomputable def itoSum {Ω : Type*} (σ : ℝ → ℝ)
    (X B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n),
    σ (X (t * (k : ℝ≥0) / (2 ^ n : ℝ≥0)) ω) *
      (B (t * ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℝ≥0)) ω -
       B (t * (k : ℝ≥0) / (2 ^ n : ℝ≥0)) ω)

/-- A nonexplosive weak solution on R. The stochastic integral is specified by
its defining left dyadic sums in probability, not by an unconstrained integral oracle. -/
structure Diffusion {Ω : Type*} [MeasurableSpace Ω] (p : Coefficients)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (x : ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ t, Measurable (X t)
  continuous : ∀ ω, Continuous (fun t => X t ω)
  initial : ∀ᵐ ω ∂P, X 0 ω = x
  weak_solution : ∃ (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ),
    Adapted ℱ X ∧ Adapted ℱ B ∧ IsBrownianReal B P ∧
    (∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (ℱ s) P) ∧
    ∀ t : ℝ≥0, TendstoInMeasure P (itoSum p.volatility X B t) atTop
      (fun ω => X t ω - x -
        ∫ r in (0 : ℝ)..(t : ℝ), p.drift (X r.toNNReal ω))

/-- Right-continuous natural past, augmented by ambient measurable null sets. -/
noncomputable def naturalPast {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨅ u : ℝ≥0, ⨅ (_ : t < u),
    ((⨆ r : ℝ≥0, ⨆ (_ : r ≤ u), MeasurableSpace.comap (X r) inferInstance) ⊔
      MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ P N = 0})

/-- The book's Markov times; a stopping time must additionally be finite a.s. -/
def IsMarkovTime {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞) : Prop :=
  Measurable τ ∧ ∀ t : ℝ≥0, MeasurableSet[naturalPast P X t] {ω | τ ω ≤ (t : ℝ≥0∞)}


-/

namespace PeskirShiryaev.Maximality

noncomputable def scaleDensity (p : Coefficients) (y : ℝ) : ℝ :=
  Real.exp (- ∫ z in (0 : ℝ)..y, 2 * p.drift z / p.volatility z ^ 2)

noncomputable def scale (p : Coefficients) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, scaleDensity p y

noncomputable def speedDensity (p : Coefficients) (x : ℝ) : ℝ :=
  2 / (scaleDensity p x * p.volatility x ^ 2)

noncomputable def speed (p : Coefficients) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (speedDensity p y))

noncomputable def green (p : Coefficients) (a b x y : ℝ) : ℝ :=
  if y ≤ x then (scale p b - scale p x) * (scale p y - scale p a) /
      (scale p b - scale p a)
  else (scale p b - scale p y) * (scale p x - scale p a) /
      (scale p b - scale p a)

noncomputable def odeRhs (p : Coefficients) (s y : ℝ) : ℝ :=
  p.volatility y ^ 2 * scaleDensity p y /
    (2 * p.cost y * (scale p s - scale p y))

/-- Global C1 solutions strictly below the diagonal; no optimality is assumed. -/
def AdmissibleBoundary (p : Coefficients) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ ∀ s, g s < s ∧ HasDerivAt g (odeRhs p s (g s)) s

def MaximalBoundary (p : Coefficients) (g : ℝ → ℝ) : Prop :=
  AdmissibleBoundary p g ∧ ∀ h, AdmissibleBoundary p h → ∀ s, h s ≤ g s

/-- The analytic expression, extended to either side of its lower integration limit. -/
noncomputable def integralCandidate (p : Coefficients) (g : ℝ → ℝ) (x s : ℝ) : ℝ :=
  s + ∫ y in g s..x, (scale p x - scale p y) * p.cost y * speedDensity p y

noncomputable def candidate (p : Coefficients) (g : ℝ → ℝ) (x s : ℝ) : ℝ :=
  if x ≤ g s then s else integralCandidate p g x s

/-- Equations (13.2.9)--(13.2.12), with inward derivatives at the two boundaries. -/
def FreeBoundarySystem (p : Coefficients) (g : ℝ → ℝ) : Prop :=
  (∀ s x, g s < x → x < s →
    p.drift x * deriv (fun z => integralCandidate p g z s) x +
    p.volatility x ^ 2 / 2 * deriv (deriv (fun z => integralCandidate p g z s)) x =
      p.cost x) ∧
  (∀ s, HasDerivWithinAt (fun u => integralCandidate p g s u) 0 (Set.Ici s) s) ∧
  (∀ s, integralCandidate p g (g s) s = s) ∧
  (∀ s, HasDerivWithinAt (fun x => integralCandidate p g x s) 0 (Set.Ici (g s)) (g s))

/-- A solution up to its first diagonal contact, extended by the diagonal afterwards. -/
def DiagonalBoundary (p : Coefficients) (g : ℝ → ℝ) (d : ℝ) : Prop :=
  Continuous g ∧
  (∀ s, s < d → g s < s ∧ HasDerivAt g (odeRhs p s (g s)) s) ∧
  ∀ s, d ≤ s → g s = s

end PeskirShiryaev.Maximality


