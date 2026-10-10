-- Prove2me | Definitions.Def_BenfordLaw_Defs
-- name    : BenfordLaw_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:25:42.194804+00:00
-- url     : https://prove2.me/theorems/dae67b61-fbe2-474d-b4d8-ba3575ac297f
-- title:
--   Benford's law: leading digits, Benford probabilities, Benford sequences
-- statement:
--   Core definitions for Benford's law in an integer base $b$ (in the theorems $b \ge 2$, usually $b = 10$). Write $\{t\} = t - \lfloor t\rfloor$ for the fractional part.
--
--   1. **Leading digit.** $D_b(x) = \left\lfloor b^{\{\log_b |x|\}}\right\rfloor$. For $x \ne 0$, writing $|x| = m\,b^e$ with $1 \le m < b$, $e\in\mathbb Z$, this is $\lfloor m\rfloor\in\{1,\dots,b-1\}$.
--   2. **First $k$ digits.** $D_b^{(k)}(x) = \left\lfloor b^{\{\log_b |x|\} + k - 1}\right\rfloor$, the integer formed by the first $k$ significant digits (leading zeros discarded).
--   3. **$n$-th digit.** $\mathrm{dig}_b^{(n)}(x) = D_b^{(n)}(x) \bmod b$.
--   4. **Benford probability.** $P_b(d) = \log_b\!\left(1 + \frac1d\right) = \log_b(d+1) - \log_b d$.
--   5. **Digit frequency.** For a real sequence $(a_n)_{n\ge0}$, $\mathrm{freq}_{b,d}(a, N) = \frac{1}{N}\#\{0\le n<N : D_b(a_n)=d\}$.
--   6. **Benford sequence.** $(a_n)$ satisfies Benford's law in base $b$ if $\mathrm{freq}_{b,d}(a,N) \to P_b(d)$ as $N\to\infty$ for every $1 \le d < b$.
--   7. **Strong form (uniform log-significand).** A random variable $X$ on $(\Omega,\mathbb P)$ has a uniform log-significand in base $b$ if $X$ is measurable, $X>0$ almost surely, and the law of $\{\log_b X\}$ is the uniform (Lebesgue) distribution on $[0,1)$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note.** `Real.logb` uses $\log|x|$, so $D_b(-x) = D_b(x)$, and $D_b(0) = 1$ (junk value). For $N = 0$ the frequency is $0/0 = 0$. The strong-form predicate is a `Prop`-valued definition `HasUniformLogMantissa b P X`; it forces $\mathbb P(\Omega)=1$.
-- source:
--   Wikipedia, "Benford's law" (https://en.wikipedia.org/wiki/Benford%27s_law), snapshot uploaded by the proposer, sections "Definition", "In other bases", "Generalization to digits beyond the first", "Distributions known to obey Benford's law".

import Mathlib

/-!
# Benford's law — core definitions

Shared definitions for the Benford's-law mission (source: Wikipedia, "Benford's law").
-/

namespace BenfordLaw

/-- The leading (most significant) digit of `x` in base `b`: writing `|x| = m · b^e` with
`1 ≤ m < b` and `e ∈ ℤ`, this is `⌊m⌋`. It is computed as `⌊b ^ frac(log_b |x|)⌋`.
(Junk value: for `x = 0` this returns `1`.) -/
noncomputable def leadingDigit (b : ℕ) (x : ℝ) : ℕ :=
  ⌊(b : ℝ) ^ Int.fract (Real.logb b x)⌋₊

/-- The integer formed by the first `k` significant digits of `x` in base `b`
(leading zeros discarded): `⌊m · b^(k-1)⌋` where `|x| = m · b^e`, `1 ≤ m < b`. -/
noncomputable def leadingDigits (b k : ℕ) (x : ℝ) : ℕ :=
  ⌊(b : ℝ) ^ (Int.fract (Real.logb b x) + ((k : ℝ) - 1))⌋₊

/-- The `n`-th significant digit of `x` in base `b` (`n = 1` is the leading digit). -/
noncomputable def digitAt (b n : ℕ) (x : ℝ) : ℕ :=
  leadingDigits b n x % b

/-- The Benford probability of leading digit `d` in base `b`:
`log_b (d + 1) - log_b d = log_b (1 + 1/d)`. -/
noncomputable def benfordProb (b d : ℕ) : ℝ :=
  Real.logb b (1 + 1 / (d : ℝ))

/-- Relative frequency of leading digit `d` (base `b`) among the first `N` terms
`a 0, …, a (N-1)` of a sequence. -/
noncomputable def digitFreq (b d : ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter (fun n => leadingDigit b (a n) = d)).card : ℝ) / N

/-- A real sequence satisfies Benford's law (exactly, in the asymptotic limit) in base `b`
if for every digit `1 ≤ d < b` the relative frequency of leading digit `d` among the first
`N` terms tends to `log_b (1 + 1/d)` as `N → ∞`. -/
def IsBenfordSeq (b : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d < b →
    Filter.Tendsto (digitFreq b d a) Filter.atTop (nhds (benfordProb b d))

/-- Strong form of Benford's law for a random variable: `X` is measurable, almost surely
positive, and the fractional part of `log_b X` is uniformly distributed on `[0, 1)`. -/
def HasUniformLogMantissa {Ω : Type*} [MeasurableSpace Ω] (b : ℕ)
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ (∀ᵐ ω ∂P, 0 < X ω) ∧
    P.map (fun ω => Int.fract (Real.logb b (X ω))) =
      MeasureTheory.volume.restrict (Set.Ico (0 : ℝ) 1)

end BenfordLaw


