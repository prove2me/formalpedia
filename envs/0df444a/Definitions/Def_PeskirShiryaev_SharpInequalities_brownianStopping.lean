-- Prove2me | Definitions.Def_PeskirShiryaev_SharpInequalities_brownianStopping
-- name    : PeskirShiryaev_SharpInequalities_brownianStopping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:40.058542+00:00
-- url     : https://prove2.me/theorems/58c57ea2-3a69-4735-9fa8-67c6f59e6d7a
-- title:
--   Brownian stopping class, running maximum, and equality rules
-- statement:
--   Let $B$ be standard real Brownian motion started at zero on a probability space, with measurable evaluations and continuous paths. For $x\ge0$, put $X_t=|B_t+x|$ and $S_t=\sup_{0\le r\le t}X_r$. An admissible time is a stopping time of the natural filtration of $B$ that is almost surely finite and satisfies
--   $$\mathbb E[\tau^r]<\infty\quad\text{for some }r>1/2.$$
--   For $c>1$, with $\alpha,v_*,u_*$ defined in the logarithmic-cost item, define
--   $$\sigma_* = \inf\{t>0:S_t\ge v_*,\ X_t=\alpha S_t\},\qquad
--   \tau_* = \inf\{t>0:S_t\ge u_*,\ X_t=1\vee\alpha S_t\}.$$
--   The two rules are selected by the plain and positive-logarithm costs, respectively. The stopped absolute value is $|B_\tau+x|$ and the expected maximum is $\mathbb E\sup_{0\le t\le\tau}|B_t+x|$.
--
--   These objects specify the admissible class and the explicit times whose equality properties are theorem conclusions.
--
--   **Formalization Note** Time is nonnegative real; random times and maxima take values in $[0,\infty]$. An empty hitting set has infimum $+\infty$. At finite times, continuity makes the maximum finite, so its conversion to a real boundary value is exact. Evaluation at an infinite time is assigned the time-zero value, used only on null sets under admissibility. Everywhere continuous paths with $B_0=0$ choose the standard continuous version of Brownian motion.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 272–274, 278–282 (PDF pp. 290–292, 296–300), Section 19.1 and Eqs. (19.2.2), (19.2.30)

import Definitions.Def_PeskirShiryaev_SharpInequalities_logarithmicCosts
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace PeskirShiryaev.SharpInequalities

/-- A standard Brownian process with a measurable, continuous version, started at zero.
Its stopping times below use its natural filtration. -/
structure BrownianData (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  B : ℝ≥0 → Ω → ℝ
  brownian : IsBrownianReal B P
  measurable : ∀ t, StronglyMeasurable (B t)
  continuous : ∀ ω, Continuous (fun t => B t ω)
  zero : ∀ ω, B 0 ω = 0

/-- Nonnegative extended running maximum, including time zero and the stopping endpoint. -/
def stoppedMaximum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ⨆ (_ : (t : ℝ≥0∞) ≤ τ ω), ENNReal.ofReal |B t ω + x|

/-- Evaluated only at a.s. finite times in the theorems; the value at infinity is a null-set convention. -/
def stoppedAbsolute {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ := |B (τ ω).toNNReal ω + x|

/-- The source's admissibility restriction, with its existential exponent. -/
def Admissible {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : BrownianData Ω P) (τ : Ω → ℝ≥0∞) : Prop :=
  IsStoppingTime (Filtration.natural D.B D.measurable) τ ∧
  (∀ᵐ ω ∂P, τ ω < ⊤) ∧ ∃ r : ℝ, 1 / 2 < r ∧ (∫⁻ ω, (τ ω) ^ r ∂P) < ⊤

/-- Eq. (19.2.2) for plain, Eq. (19.2.30) for plus. The infimum is in [0,∞],
so failure ever to hit gives infinity. The real maximum used in the boundary is finite
for a continuous path on a finite interval. -/
def optimalTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (k : LogCost)
    (x c : ℝ) (ω : Ω) : ℝ≥0∞ :=
  sInf {z | ∃ t : ℝ≥0, z = (t : ℝ≥0∞) ∧ 0 < t ∧
    let S := (stoppedMaximum B x (fun _ => (t : ℝ≥0∞)) ω).toReal
    (match k with
    | .plain => vStar c ≤ S ∧ |B t ω + x| = alpha c * S
    | .plus => uStar c ≤ S ∧ |B t ω + x| = max 1 (alpha c * S))}

def maximumExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (x : ℝ) (τ : Ω → ℝ≥0∞) : EReal :=
  ((∫⁻ ω, stoppedMaximum B x τ ω ∂P) : EReal)

end PeskirShiryaev.SharpInequalities


