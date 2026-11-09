-- Prove2me | Definitions.Def_PersuasionByParts_Known_Pooling
-- name    : PersuasionByParts_Known_Pooling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:22.914752+00:00
-- url     : https://prove2.me/theorems/ecbf703a-1c88-4b8d-8770-480de82c94b1
-- title:
--   Fractional top pools, pooling capacities and the sparse experiment
-- statement:
--   For a real probability law $\mu$ with finite absolute mean, let $F^{-1}$ be its generalized inverse CDF. For $0<s<1$, put $a=F^{-1}(1-s)$. The top-mass selector $w_s$ equals one above $a$, zero below $a$, and
--
--   $$w_s(a)=\frac{s-\mu((a,\infty))}{\mu(\{a\})}$$
--
--   when the denominator is positive; it is zero at a boundary atom of zero mass. Set $w_0\equiv0$ and $w_1\equiv1$. Its mean is
--
--   $$m_\mu(s)=\frac1s\int_{1-s}^1F^{-1}(u)\,du\qquad(0<s\le1).$$
--
--   The pool/reveal kernel draws a fresh uniform $U\in[0,1]$, sends a distinguished pool tag when $U<w_s(z)$, and otherwise reveals $z$. A joint pool applies this kernel to $X=\sum_iX_i$. Its reveal signal carries $X$; it need not reveal the entire vector.
--
--   For a product prior and $q\in(0,1]$, define $X_{-i}=\sum_{j\ne i}X_j$ and
--
--   $$h_i=t-F_{X_{-i}}^{-1}(1-q/3),\quad b_i=\max\{s\in(0,1]:m_{P_i}(s)\ge h_i\},\quad B=\sum_i b_i,\quad p=P(X\ge t),$$
--
--   with empty maximum zero. If $B\ge q/6$, source $i$ pools mass $s_i=(q/6)b_i/B$; otherwise $s_i=0$ and it reveals. The sparse experiment uses these actual coordinate kernels. The random variable $N$ counts pool tags.
--
--   These definitions supply the concrete objects in the joint-value and capacity statements; no capacities or posterior means are supplied as free parameters.
--
--   **Formalization Note** The quantile and upper integral are imported from the published quantile definition at state space $\mathbb R$. The capacity is a bounded-set supremum with an explicit empty branch. Positive-mass attainment is a theorem conclusion. The signal type is `Unit ⊕ ℝ`; independent uniforms implement the fractional selector. The real count embeds the integer count. The unused zero-mass mean is zero by total division. No endpoint quantile is evaluated to decide whether to pool at mass zero or one.
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed pp. 3, 7–8 / PDF pp. 4, 8–9, §1.1 top-mass pool definition and §2.1 construction

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model
import Definitions.Def_PersuasionNetworks_Quantile

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace PersuasionByParts.Known
attribute [local instance] Classical.propDecidable

/-- Only strict interior quantiles are evaluated as real thresholds in the experiment. -/
def quantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  (PersuasionNetworks.stateQuantile μ Set.univ u).toReal

/-- The published upper quantile integral divided by positive pool mass. At zero, the value is unused. -/
def poolMean (μ : Measure ℝ) (s : ℝ) : ℝ := PersuasionNetworks.g μ Set.univ s / s

/-- Fraction of a boundary atom, with zero used if that atom has zero probability. -/
def atomFraction (μ : Measure ℝ) (s : ℝ) : ℝ :=
  let a := quantile μ (1 - s)
  if μ.real {a} = 0 then 0 else (s - μ.real (Ioi a)) / μ.real {a}

/-- Top mass, including fractional atoms. The endpoint branches avoid quantiles at 0 and 1. -/
def topSelector (μ : Measure ℝ) (s z : ℝ) : ℝ :=
  if s ≤ 0 then 0 else if 1 ≤ s then 1 else
  if quantile μ (1 - s) < z then 1 else
  if z = quantile μ (1 - s) then atomFraction μ s else 0

/-- A structural fact: the selector is a finite combination of Borel half-lines and a singleton. -/
theorem measurable_topSelector (μ : Measure ℝ) (s : ℝ) : Measurable (topSelector μ s) := by
  unfold topSelector
  split_ifs with h0 h1
  · exact measurable_const
  · exact measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      (Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
        measurable_const measurable_const)

/-- Empty-capacity convention is explicit; every nonempty capacity set is bounded by one. -/
def capacitySet (μ : Measure ℝ) (h : ℝ) : Set ℝ :=
  {s | 0 < s ∧ s ≤ 1 ∧ h ≤ poolMean μ s}

def capacity (μ : Measure ℝ) (h : ℝ) : ℝ :=
  if (capacitySet μ h).Nonempty then sSup (capacitySet μ h) else 0

/-- One fresh independent uniform random seed per invocation of a coordinate kernel. -/
def privateUniform : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure privateUniform := by
  constructor
  simp [privateUniform]

/-- inl () is the pool tag; inr z reveals the real value z. -/
def poolReport (μ : Measure ℝ) (s : ℝ) (z : ℝ × ℝ) : Unit ⊕ ℝ :=
  if z.2 < topSelector μ s z.1 then Sum.inl () else Sum.inr z.1

theorem measurable_poolReport (μ : Measure ℝ) (s : ℝ) : Measurable (poolReport μ s) := by
  unfold poolReport
  exact Measurable.ite
    (measurableSet_lt measurable_snd ((measurable_topSelector μ s).comp measurable_fst))
    measurable_const (measurable_inr.comp measurable_fst)

/-- Actual Markov kernel: draw U uniformly and pool iff U < w_s(z), otherwise reveal z. -/
def poolKernel (μ : Measure ℝ) (s : ℝ) : Kernel ℝ (Unit ⊕ ℝ) :=
  (Kernel.deterministic (poolReport μ s) (measurable_poolReport μ s)) ∘ₖ
    ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ privateUniform)

instance (μ : Measure ℝ) (s : ℝ) : IsMarkovKernel (poolKernel μ s) := by
  unfold poolKernel
  infer_instance

/-- Joint top-mass pooling of the sum; the reveal branch reports the sum itself. -/
def jointPool {n : ℕ} (P : Prior n) (s : ℝ) : JointExperiment n where
  Signal := Unit ⊕ ℝ
  signalSpace := inferInstance
  kernel := (poolKernel (sumLaw P) s).comap total (by unfold total; fun_prop)
  markov := inferInstance

def target {n : ℕ} (P : Prior n) (q t : ℝ) (i : Fin n) : ℝ :=
  t - quantile (othersLaw P i) (1 - q / 3)

def coordinateCapacity {n : ℕ} (P : Prior n) (q t : ℝ) (i : Fin n) : ℝ :=
  capacity (P.marginal i) (target P q t i)

def totalCapacity {n : ℕ} (P : Prior n) (q t : ℝ) : ℝ :=
  ∑ i, coordinateCapacity P q t i

def revelationProbability {n : ℕ} (P : Prior n) (t : ℝ) : ℝ :=
  (priorLaw P).real {x | t ≤ total x}

/-- The low-capacity branch makes every pooling mass zero, hence reveals every coordinate. -/
def sparseMass {n : ℕ} (P : Prior n) (q t : ℝ) (i : Fin n) : ℝ :=
  if q / 6 ≤ totalCapacity P q t then
    (q / 6) * coordinateCapacity P q t i / totalCapacity P q t else 0

def sparseExperiment {n : ℕ} (P : Prior n) (q t : ℝ) : ProductExperiment n where
  Signal := fun _ => Unit ⊕ ℝ
  signalSpace := fun _ => inferInstance
  kernel := fun i => poolKernel (P.marginal i) (sparseMass P q t i)
  markov := fun _ => inferInstance

/-- Counts tags rather than posterior values: a reveal equal to a pool mean is still a reveal. -/
def poolCount {n : ℕ} (s : Fin n → Unit ⊕ ℝ) : ℝ :=
  ∑ i, match s i with | .inl _ => 1 | .inr _ => 0

end PersuasionByParts.Known


