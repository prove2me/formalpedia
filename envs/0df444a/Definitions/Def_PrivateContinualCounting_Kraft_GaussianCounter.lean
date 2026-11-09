-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_GaussianCounter
-- name    : PrivateContinualCounting_Kraft_GaussianCounter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:17.582192+00:00
-- url     : https://prove2.me/theorems/cb96b526-29be-4b96-95ab-4714a7885786
-- title:
--   Infinite causal Gaussian factorisation counters
-- statement:
--   A stream is a sequence in $[0,1]$; neighboring streams may differ at one coordinate, and $S_t$ is the sum of the first $t$ entries, with $S_0=0$. Let $I$ be countable. A factorisation consists of real matrices $L,R$ with square-summable decoder rows and strategy columns, exact product
--   $$\sum_{i\in I}L_{t,i}R_{i,j}=\mathbf1_{j\le t},\qquad
--   \Delta^2=\sup_{j\ge1}\sum_{i\in I}R_{i,j}^2<\infty.$$
--   A counter includes the Gaussian L² realization $W_t=\sum_iL_{t,i}Z_i$. At a positive parameter $\mu$ its releases and normalized variance are
--   $$Y_t=S_t+(\Delta/\mu)W_t,\qquad v_t=\Delta^2\sum_iL_{t,i}^2.$$
--   The seed is independent of the stream and shared by every time. Finite transcript laws are defined from these releases. Causality follows from the deterministic prefix plus stream-independent noise. The divergence predicate means $v_t/(\ln t)^2\to+\infty$ along every integer time. This interface provides the paper's exact coefficient definition of normalized variance, not an arbitrary sequence of accuracy values.
--
--   **Formalization Note** Matrix indices are zero-based: row $t$ and column $j$ stand for source times $t+1,j+1$. Release time $t$ itself is not shifted. The sensitivity is a bounded, nonempty real supremum of squared column norms. Gaussian privacy calibration is described in the source; this item does not introduce an opaque privacy predicate or a new testing-law theorem.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 6, PDF p. 8, §2.1 and Definition 2.1

import Definitions.Def_PrivateContinualCounting_Kraft_GaussianSeries

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Coordinate zero represents the source's first stream element. -/
abbrev Stream := ℕ → Set.Icc (0 : ℝ) 1

def Adjacent (x y : Stream) : Prop :=
  ∃ j : ℕ, ∀ i : ℕ, i ≠ j → x i = y i

noncomputable def prefixSum (x : Stream) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, (x j : ℝ)

/-- Definition 2.1. Row t and column j represent positive source times t+1 and j+1. -/
structure Factorization (I : Type) [Countable I] where
  L : ℕ → I → ℝ
  R : I → ℕ → ℝ
  rows_l2 : ∀ t, Memℓp (L t) 2
  cols_l2 : ∀ j, Memℓp (fun i => R i j) 2
  product : ∀ t j, (∑' i, L t i * R i j) = if j ≤ t then 1 else 0
  bounded_sensitivity : BddAbove (Set.range (fun j => ∑' i, (R i j) ^ 2))

/-- Squared factor sensitivity, a bounded nonempty supremum on Factorization. -/
noncomputable def Factorization.deltaSq {I : Type} [Countable I] (F : Factorization I) : ℝ :=
  sSup (Set.range (fun j => ∑' i, (F.R i j) ^ 2))

/-- One infinite counter, with actual Gaussian laws and L² decoder sums. -/
structure GaussianCounter (I : Type) [Countable I] where
  factors : Factorization I
  noise : GaussianSeries I factors.L

/-- The coefficient definition of normalized variance (Definition 2.1). -/
noncomputable def GaussianCounter.variance {I : Type} [Countable I] (M : GaussianCounter I) (t : ℕ) : ℝ :=
  if t = 0 then 0 else M.factors.deltaSq * ∑' i, (M.factors.L (t - 1) i) ^ 2

/-- At any μ>0, all releases use the same seed ω with law gaussianSeed I. -/
noncomputable def GaussianCounter.release {I : Type} [Countable I] (M : GaussianCounter I)
    (μ : Set.Ioi (0 : ℝ)) (x : Stream) (t : ℕ) (ω : I → ℝ) : ℝ :=
  prefixSum x t + Real.sqrt M.factors.deltaSq / (μ : ℝ) *
    (if t = 0 then 0 else M.noise.value (t - 1) ω)

noncomputable def GaussianCounter.transcriptLaw {I : Type} [Countable I] (M : GaussianCounter I)
    (μ : Set.Ioi (0 : ℝ)) (x : Stream) (n : ℕ) : Measure (Fin n → ℝ) :=
  (gaussianSeed I).map (fun ω k => M.release μ x (k.val + 1) ω)

/-- Divergence to +∞ over all natural times, rather than a subsequence or running maximum. -/
def LogSqDiverges (v : ℕ → ℝ) : Prop :=
  Tendsto (fun t : ℕ => v t / (Real.log (t : ℝ)) ^ 2) atTop atTop

end PrivateContinualCounting.Kraft


