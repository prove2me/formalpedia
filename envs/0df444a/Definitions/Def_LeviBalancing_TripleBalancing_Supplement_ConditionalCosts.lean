-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_Supplement_ConditionalCosts
-- name    : LeviBalancing_TripleBalancing_Supplement_ConditionalCosts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:19:46.402828+00:00
-- url     : https://prove2.me/theorems/93e9aebd-e5a8-4649-bc61-47e0b43fc0f0
-- title:
--   Conditional marginal costs and interpolation at integer orders
-- statement:
--   Fix a finite-horizon periodic-review instance with integer lead time $L$, nonnegative holding and backlog rates $h_t,p_t$, real initial stock, and a nonnegative given pipeline. At period $s$, let $x$ be inventory position before ordering, $q$ the new order, and $d$ a future demand path. The conditional marginal holding and backlog costs under the supplied conditional demand law $\nu$ are
--
--   $$
--   \ell_s(x,q)=E_\nu\!\left[\sum_{j=s+L}^T h_j\bigl(q-(D_{[s,j]}-x)^+\bigr)^+\right],\qquad
--   \pi_s(x,q)=E_\nu[p_{s+L}(D_{[s,s+L]}-x-q)^+].
--   $$
--
--   For a nonnegative integer-cost function $f$ and $n=\lfloor q\rfloor$, its affine interpolation is $(n+1-q)f(n)+(q-n)f(n+1)$. The full expected transformed cost is also recorded, including the initial costs omitted in Equation (4).
--
--   These wrappers use the published marginal costs by shifting the initial-stock coordinate to evaluate one decision at $(s,x)$. The empty pipeline in that coordinate chart does not restrict the actual controlled instance. Nonnegative expectations take values in $[0,\infty]$; no nonintegrable cost is assigned the real number zero.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, pp. 291–292, 295 (PDF 8–9, 12), Eqs. (1), (2), (4), §4.3

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Policy

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LeviBalancing.TripleBalancing.Supplement
open LeviBalancing.DualBalancing

/-- Evaluate the published marginal costs at a specified pre-order position. Shifting the
initial stock cancels past demand; the empty pipeline is only a coordinate chart for this
single decision, not a restriction on the instance being controlled. -/
def decisionInstance (I : Instance) (d : ℤ → ℝ) (s : ℤ) (x : ℝ) : Instance :=
  { I with ni0 := x + cumDemand d 1 (s - 1), q := fun _ => 0,
           q_nonneg := by intros; exact le_rfl }

def holdingAt (I : Instance) (d : ℤ → ℝ) (s : ℤ) (x q : ℝ) : ℝ :=
  marginalHolding (decisionInstance I d s x) d (fun j => if j = s then q else 0) s

def backlogAt (I : Instance) (d : ℤ → ℝ) (s : ℤ) (x q : ℝ) : ℝ :=
  marginalBacklog (decisionInstance I d s x) d (fun j => if j = s then q else 0) s

/-- Nonnegative expectations under a supplied conditional demand law. No totalized real
conditional expectation is used. -/
def conditionalHolding (I : Instance) (ν : Measure (ℤ → ℝ)) (s : ℤ) (x q : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (holdingAt I d s x q) ∂ν

def conditionalBacklog (I : Instance) (ν : Measure (ℤ → ℝ)) (s : ℤ) (x q : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (backlogAt I d s x q) ∂ν

/-- Affine interpolation of INTEGER cost values; at an integer its weight on that integer is 1. -/
def integerInterpolation (f : ℝ → ℝ≥0∞) (q : ℝ) : ℝ≥0∞ :=
  let n : ℤ := ⌊q⌋
  ENNReal.ofReal ((n : ℝ) + 1 - q) * f n +
    ENNReal.ofReal (q - (n : ℝ)) * f ((n : ℝ) + 1)

/-- The full transformed cost, including the policy-independent initial costs omitted in (4). -/
def expectedFullCost {Ω : Type*} [MeasurableSpace Ω] (I : Instance) (μ : Measure Ω)
    (D Q : ℤ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (∑ t ∈ Icc (1 : ℤ) (I.T : ℤ),
    periodCost I (fun j => D j ω) (fun j => Q j ω) t) ∂μ

end LeviBalancing.TripleBalancing.Supplement


