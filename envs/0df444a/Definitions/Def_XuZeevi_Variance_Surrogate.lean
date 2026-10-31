-- Prove2me | Definitions.Def_XuZeevi_Variance_Surrogate
-- name    : XuZeevi_Variance_Surrogate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:08:22.643983+00:00
-- url     : https://prove2.me/theorems/9d38b5d8-02ff-4128-9744-5e5a0e912dc9
-- title:
--   Meaningful surrogates, sub-root condition and literal fixed-point graph
-- statement:
--   A meaningful surrogate $\psi(r;\delta)$ is nonnegative, nondecreasing and bounded in $r\in[0,\infty)$ for every $\delta\in(0,1)$. Values outside this domain are unused. The sub-root predicate on $[0,4B^2]$ is
--   $$\psi(t;\delta)\sqrt r\le\psi(r;\delta)\sqrt t\qquad(0\le r\le t\le4B^2).$$
--   At positive radii this is exactly monotonic decrease of $\psi(r;\delta)/\sqrt r$; the zero endpoint uses no division by zero.
--
--   The printed fixed-point graph asserts that $r^*$ is a real least upper bound of $\{r>0:\phi(r)\le r\}$. For a bounded $\phi$ this set is unbounded: the graph has no value, rather than assigning zero to its supremum. This preserves source finding I1.
--
--   For $F$ the excess-loss class, the Strategy 2 expression is
--   $$4R_n\{f\in F:P_n f^2\le2r\}+\sqrt{2r\log(8/\delta)/n}+9B\log(8/\delta)/n.$$
--   A Strategy 2 surrogate can depend on the primary sample $S$. It is meaningful for each $S$, its fixed-radius values and the displayed expression are measurable in $S$, and for every fixed $\delta\in(0,1)$ and $r>0$ it dominates the expression on a measurable event of probability at least $1-\delta$. These events may differ with $r$. No simultaneous event, monotonicity in confidence, or sub-root property beyond $4B^2$ is assumed.
--
--   The combination of boundedness and domination for all $r>0$ is inconsistent even for measurable sample-dependent surrogates (finding I2). This is retained literally; these assumptions do not describe a nonvacuous class of generalization guarantees.
-- source:
--   Xu and Zeevi, arXiv:2011.06186v4, Definitions 1-3 p. 9, Strategy 2 and Theorem 2 p. 12, sample dependence pp. 5-6 (PDF pages equal printed pages)

import Definitions.Def_XuZeevi_Variance_Model
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalRademacherComplexity_v2

open MeasureTheory FoundationsML.RademacherVC

namespace XuZeevi.Variance

/-- Definition 1, including boundedness on the entire nonnegative half-line. -/
def Meaningful (ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ δ, 0 < δ → δ < 1 →
    (∀ r, 0 ≤ r → 0 ≤ ψ r δ) ∧
    MonotoneOn (fun r => ψ r δ) (Set.Ici 0) ∧
    ∃ M : ℝ, ∀ r, 0 ≤ r → ψ r δ ≤ M

/-- Theorem 2's sub-root condition, only on [0,4 B²].
Cross multiplication avoids assigning a meaning to ψ(0)/sqrt(0). -/
def SubRootOn (B : ℝ) (ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ δ, 0 < δ → δ < 1 → ∀ r t, 0 ≤ r → r ≤ t → t ≤ 4 * B ^ 2 →
    ψ t δ * Real.sqrt r ≤ ψ r δ * Real.sqrt t

/-- Literal Definition 2: graph of sup {r>0 : φ(r)≤r}.
It has no real value for bounded φ; no real sSup default is used. -/
def PrintedFixedPoint (φ : ℝ → ℝ) (rstar : ℝ) : Prop :=
  IsLUB {r : ℝ | 0 < r ∧ φ r ≤ r} rstar

/-- Strategy 2's empirical localization expression at radius r. -/
noncomputable def strategyLower {H Z : Type*} {n : ℕ}
    (loss : H → Z → ℝ) (hstar : H) (B : ℝ) (s : Fin n → Z) (r δ : ℝ) : ℝ :=
  4 * EmpiricalRademacherComplexity
    {f ∈ excessClass loss hstar | empiricalMean s (fun z => f z ^ 2) ≤ 2 * r} s +
    Real.sqrt (2 * r * Real.log (8 / δ) / n) + 9 * B * Real.log (8 / δ) / n

/-- The literal all-r Strategy 2 assumption; ψ can depend on the primary sample.
Meaningfulness is pointwise in the sample, not a deterministic uniform bound.
The boundedness/all-r incompatibility is intentionally preserved (insight I2). -/
def Strategy2Surrogate {H Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (P : Measure Z) (loss : H → Z → ℝ) (hstar : H) (B : ℝ)
    (ψ : (Fin n → Z) → ℝ → ℝ → ℝ) : Prop :=
  (∀ s, Meaningful (ψ s)) ∧
  (∀ r δ, 0 ≤ r → 0 < δ → δ < 1 → Measurable (fun s => ψ s r δ)) ∧
  (∀ r δ, 0 < r → 0 < δ → δ < 1 →
    Measurable (fun s : Fin n → Z => strategyLower loss hstar B s r δ)) ∧
  ∀ δ, 0 < δ → δ < 1 → ∀ r, 0 < r →
    HighProbability (sampleLaw P n) (1 - δ)
      (fun s => strategyLower loss hstar B s r δ ≤ ψ s r δ)

end XuZeevi.Variance


