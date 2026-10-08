-- Prove2me | Definitions.Def_PrivateRelease_Continuous_Queries
-- name    : PrivateRelease_Continuous_Queries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:28.569497+00:00
-- url     : https://prove2.me/theorems/1b83de6e-04d6-4773-be8d-1d2b57af56c6
-- title:
--   Interval queries, percentile sets, useful median answers and (α, δ)-usefulness for intervals (§5, Definition 2.10)
-- statement:
--   Throughout, a **real-valued database** of size $n$ is an $n$-tuple $z = (z_1, \dots, z_n) \in \mathbb R^n$.
--
--   1. **Interval queries** (§4, p. 12; §5, p. 14). For real numbers $a \le b$, the interval query $Q_{[a,b]}$ returns the fraction of database entries lying in the closed interval $[a,b]$:
--   $$
--   Q_{[a,b]}(z) = \frac{\#\{\, i : a \le z_i \le b \,\}}{n}.
--   $$
--
--   2. **Percentile set** (p. 14). The paper says that a real number $r$ "falls within the $50-\delta, 50+\delta$ percentile of points in database $D$", with $\delta$ measured in percent. Writing $\theta = \delta/100$, a real number $r$ is a $\theta$-percentile point of $z$ when at least a $(1/2 - \theta)$ fraction of the entries lies on each side of $r$, entries equal to $r$ counting on both sides:
--   $$
--   \#\{\, i : z_i \le r \,\} \ \ge\ \Big(\tfrac12 - \theta\Big) n \qquad\text{and}\qquad \#\{\, i : z_i \ge r \,\} \ \ge\ \Big(\tfrac12 - \theta\Big) n .
--   $$
--   For $0 \le \theta < 1/2$ and $n \ge 1$ this set always contains a sample median, and for a constant database $(c, \dots, c)$ it is exactly $\{c\}$.
--
--   3. **Useful median answers** (p. 14, Theorem 5.1). A mechanism $A$ that maps each database $z$ to a probability distribution $A(z)$ on $\mathbb R$ *answers median queries usefully with positive probability on every database* if, for every $z \in \mathbb R^n$, its output is a $\theta$-percentile point of $z$ with positive probability.
--
--   4. **$(\alpha,\delta)$-usefulness for interval queries** (Definition 2.10, p. 7). A mechanism $A$ with outputs in a measurable space $O$, together with a readout $\mathrm{ans} : O \times \mathbb R \times \mathbb R \to \mathbb R$ giving the output's answer $\mathrm{ans}(o, a, b)$ to the query $Q_{[a,b]}$, is $(\alpha,\delta)$-useful for interval queries if for every database $z \in \mathbb R^n$
--   $$
--   \Pr_{o \sim A(z)}\Big[\ \forall\, a \le b:\ \big|\mathrm{ans}(o,a,b) - Q_{[a,b]}(z)\big| \le \alpha\ \Big] \ \ge\ 1 - \delta .
--   $$
--   When the output is synthetic data $\hat D$ (the paper's setting), $\mathrm{ans}(\hat D, a, b) = Q_{[a,b]}(\hat D)$.
--
--   These objects are the vocabulary of the paper's lower bound for non-discretized domains: they make precise what it would mean for a private mechanism to release real-valued data that is accurate for every interval.
--
--   **Formalization Note.** Databases are `Fin n → ℝ`, so neighbouring databases and ε-differential privacy come from the published definitions `PrivLearn.Generic.Neighbors` (replace one entry) and `PrivLearn.Generic.IsDP`. The usefulness event is an intersection over uncountably many queries and need not be measurable; Lean's `A z` of a non-measurable set is its outer measure. A general readout `ans` replaces synthetic data, which makes the class of mechanisms larger. At $n = 0$, Lean's division gives $Q_{[a,b]} = 0$; every theorem using these definitions assumes $n \ge 1$.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 7, Definition 2.10; p. 12, interval indicator I_{a1,a2}; p. 14, definition of answering a median query usefully

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PrivateRelease.Continuous

open MeasureTheory

/-- Interval query (§4, p. 12, and §5, p. 14): for real `a ≤ b`, `Q_{[a,b]}(z)` is the fraction
of the `n` entries of the real-valued database `z` that lie in the closed interval `[a, b]`. -/
noncomputable def intervalQuery {n : ℕ} (a b : ℝ) (z : Fin n → ℝ) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun i => a ≤ z i ∧ z i ≤ b).card : ℝ) / n

/-- The `50 − δ, 50 + δ` percentile (p. 14), with `θ = δ/100`: the real number `r` has at least a
`1/2 − θ` fraction of the entries of `z` on each side of it, counting entries equal to `r` on both
sides. -/
noncomputable def IsPercentile {n : ℕ} (z : Fin n → ℝ) (θ r : ℝ) : Prop :=
  open Classical in
  ((Finset.univ.filter fun i => z i ≤ r).card : ℝ) ≥ (1 / 2 - θ) * n ∧
    ((Finset.univ.filter fun i => r ≤ z i).card : ℝ) ≥ (1 / 2 - θ) * n

/-- A mechanism with real outputs answers median queries usefully with positive probability on
every database (p. 14, Theorem 5.1): on every real-valued database `z` its output lies in the
`θ`-percentile set of `z` with positive probability. -/
def AnswersMedianUsefully {n : ℕ} (A : (Fin n → ℝ) → Measure ℝ) (θ : ℝ) : Prop :=
  ∀ z : Fin n → ℝ, 0 < A z {r | IsPercentile z θ r}

/-- Definition 2.10 (p. 7) for the class of interval queries: on every real-valued database `z`,
with probability at least `1 − δ` the output `o` answers every interval query `[a, b]`, `a ≤ b`,
through the readout `ans o a b` to within `α` of its true value on `z`. The event is an
uncountable intersection; `A z` of it is the outer measure when it is not measurable. -/
def UsefulIntervals {n : ℕ} {O : Type} [MeasurableSpace O] (A : (Fin n → ℝ) → Measure O)
    (ans : O → ℝ → ℝ → ℝ) (α δ : ℝ) : Prop :=
  ∀ z : Fin n → ℝ,
    ENNReal.ofReal (1 - δ) ≤ A z {o | ∀ a b : ℝ, a ≤ b → |ans o a b - intervalQuery a b z| ≤ α}

end PrivateRelease.Continuous


