-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_GroundLearner
-- name    : GibbsTransition_SizeCopies_Supplement_GroundLearner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:35:43.429199+00:00
-- url     : https://prove2.me/theorems/b2159047-41d1-49cf-95af-fb305a8a7f8a
-- title:
--   The specified Appendix A local-measurement ground learner
-- statement:
--   The learner starts with $[1/4,3/4]$, uses the published overlapping updates, and stops after $K=\lceil\log(1/(4\epsilon))/\log(8/5)\rceil$ rounds. At round $k$, its interval width is $w_k=\frac12(5/8)^k$, its margin is $\gamma_k=w_k/8$, and
--   $$L_k=\left\lceil\frac{16C}{d\gamma_k}\right\rceil,\quad C=\max(1,3J+J_b),\quad d=b-a,\quad \delta_k=\delta2^{k-K}.$$
--   It takes an integer number of samples in $[2(d/4)^{-2}\log(2/\delta_k),2(d/4)^{-2}\log(2/\delta_k)+2)$. Each sample measures the two-outcome POVM $\{P,I-P\}$ at an independent uniformly selected site on a fresh ground-state copy. The empirical mean is compared with $(a+b)/2$, and the final midpoint is returned.
--
--   The module specifies the actual finite product Born laws and resource sums. Sample counts use a finite rational logarithm series and the stopping count uses a finite rational search, so neither exact comparisons nor the unknown transition are supplied to the algorithm.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Section A.2, (16),(72)–(75), printed pp. 6,22–23 (PDF pp. 8,24–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Interval
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Access
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

/-- Finite rational atanh series with range reduction. All choices here are
rational/integer arithmetic; no exact logarithm oracle chooses a sample count. -/
def logSeries (x : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, ((x-1)/(x+1))^(2*i+1) / (2*i+1 : ℚ)

def logUpper (x eta : ℚ) : ℚ :=
  let B := x.num.natAbs.log2 + 2
  let m := ((List.range (B+1)).filter (fun k => (2 : ℚ)^k ≤ x)).foldl max 0
  let n := eta.den * (B+1) + 16
  (m : ℚ) * logSeries 2 n + logSeries (x/(2:ℚ)^m) n + eta/2

/-- Least contraction count, computed by a finite rational search. For valid
accuracy inputs epsilon.den is more than sufficient search fuel. -/
def groundRounds (epsilon : ℚ) : ℕ :=
  (((List.range (epsilon.den+1)).filter
    (fun k => (1/2 : ℚ)*(5/8 : ℚ)^k ≤ 2*epsilon)).head?).getD 0

def roundMargin (k : ℕ) : ℚ := (1/16 : ℚ)*(5/8 : ℚ)^k

def roundFailure (epsilon delta : ℚ) (k : ℕ) : ℚ :=
  delta / (2 : ℚ)^(groundRounds epsilon-k)

def groundSide {q : ℕ} (p : FieldData q) (k : ℕ) : ℕ :=
  ⌈16*surfaceC p / (gap p * roundMargin k)⌉₊

def groundCount {q : ℕ} (p : FieldData q) (epsilon delta : ℚ) (k : ℕ) : ℕ :=
  let g := gap p / 4
  ⌈2/g^2 * logUpper (2/roundFailure epsilon delta k) (g^2/128)⌉₊

def historyBits (h : List Bool) (k : ℕ) : Bool := h[k]?.getD false

def historyField (h : List Bool) (k : ℕ) : ℚ := searchField (historyBits h) k

/-- The average over the uniformly selected site of the Born probability for
{P,I-P}. This allows every positive contraction P, including nonprojectors. -/
def localGroundMean {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (L : ℕ) (phi : ℚ) : ℝ :=
  (L : ℝ)⁻¹^3 * ∑ x : Site L,
    (Matrix.trace (fieldGround p u L phi * embedSite p.P x)).re

def sampleBitWeight (p : ℝ) (b : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (if b then p else 1-p)

def comparison (threshold : ℚ) {n : ℕ} (y : Fin n → Bool) : Bool :=
  decide (threshold ≤ (∑ i : Fin n, if y i then (1 : ℚ) else 0) / n)

/-- A fresh independent state is used for every factor of this product Born
law. Quantum memory is unnecessary for this specified upper learner. -/
def groundRoundStep {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (epsilon delta : ℚ) (h : List Bool) : Measure (List Bool) :=
  let k := h.length
  let n := groundCount p epsilon delta k
  let m := localGroundMean p u (groundSide p k) (historyField h k)
  ∑ y : Fin n → Bool, (∏ i : Fin n, sampleBitWeight m (y i)) •
    Measure.dirac (h ++ [comparison ((p.a+p.b)/2) y])

def groundRun {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (epsilon delta : ℚ) : ℕ → Measure (List Bool)
  | 0 => Measure.dirac []
  | k+1 => (groundRun p u epsilon delta k).bind (groundRoundStep p u epsilon delta)

def groundOutput (h : List Bool) : ℚ := searchOutput (historyBits h) h.length

def groundFinal {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (epsilon delta : ℚ) : Measure ℚ :=
  Measure.map groundOutput (groundRun p u epsilon delta (groundRounds epsilon))

def groundCopies {q : ℕ} (p : FieldData q) (epsilon delta : ℚ) : ℕ :=
  ∑ k ∈ Finset.range (groundRounds epsilon), groundCount p epsilon delta k

def groundSpins {q : ℕ} (p : FieldData q) (epsilon delta : ℚ) : ℕ :=
  ∑ k ∈ Finset.range (groundRounds epsilon), groundCount p epsilon delta k * (groundSide p k)^3

def GroundLearns {q : ℕ} (p : FieldData q) (epsilon delta : ℚ) : Prop :=
  ∀ u, InFieldClass p u →
    groundFinal p u epsilon delta Set.univ = 1 ∧
    groundFinal p u epsilon delta {x | |(x : ℝ)-fieldTheta p u| > epsilon} ≤
      ENNReal.ofReal delta ∧
    groundFinal p u epsilon delta (Set.Icc (1/4 : ℚ) (3/4)) = 1

end GibbsTransition.SizeCopies.Supplement


