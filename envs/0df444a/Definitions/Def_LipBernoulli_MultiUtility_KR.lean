-- Prove2me | Definitions.Def_LipBernoulli_MultiUtility_KR
-- name    : LipBernoulli_MultiUtility_KR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:19.214544+00:00
-- url     : https://prove2.me/theorems/23d02f8a-0f7e-4406-822e-ae2da523052f
-- title:
--   (5), (6), (7), Lemma 4.5, pp. 5–15 — the Kantorovich–Rubinstein space KR(X), its norm, and the cone C
-- statement:
--   Let $X = (X,d)$ be a metric space with its Borel $\sigma$-algebra, and let $\Delta_1(X)$, $W_1$ be as in `LipBernoulli.MultiUtility.Setting`.
--
--   1. **The Kantorovich–Rubinstein space** ((5), p. 5). $\mathrm{KR}(X)$ is the set of finite signed Borel measures $\mu$ on $X$ with $\mu(X) = 0$ and
--   $$
--   \int_{X\times X} d\,\mathrm d(|\mu|\times|\mu|) < \infty,
--   $$
--   where $|\mu| = \mu^+ + \mu^-$ is the total variation of $\mu$ and $\mu = \mu^+ - \mu^-$ its Jordan decomposition.
--   2. **Integral against a signed measure.** $\int_X f\,\mathrm d\mu := \int_X f\,\mathrm d\mu^+ - \int_X f\,\mathrm d\mu^-$.
--   3. **The KR norm** ((6), p. 6).
--   $$
--   \|\mu\|_{\mathrm{KR}} := \sup\Big|\int_X f\,\mathrm d\mu\Big|,
--   $$
--   the supremum over all 1-Lipschitz functions $f$ on $X$, valued in $[0,\infty]$.
--   4. **Differences of lotteries.** For finite measures $p, q$, $p - q$ is the signed measure $A \mapsto p(A) - q(A)$.
--   5. **Finitely supported measures.** A signed measure is finitely supported if it equals $\sum_{x \in F} c_x\,\delta_x$ for a finite set $F \subseteq X$ and reals $c_x$.
--   6. **The cone of a preorder** (Lemma 4.5, p. 15). For a relation $\succsim$, $C := \{\alpha(p-q) : \alpha \ge 0,\ p, q \in \Delta_1(X),\ p \succsim q\}$.
--
--   $\mathrm{KR}(X)$ is the predual-type space in which the paper's separation argument for Theorem 4.6 takes place: a Lipschitz affine preorder is encoded by its cone $C$, and Lipschitz utilities arise as bounded linear functionals on $\mathrm{KR}(X)$.
--
--   **Formalization Note** Signed measures are Mathlib's `SignedMeasure X`, a real vector space, so $\alpha\mu$, $\mu+\nu$ and $\mu-\nu$ are its operations. The integral is taken through the Jordan decomposition, exactly as the paper's proofs use $\mu^+$ and $\mu^-$ (p. 6). The norm is valued in $[0,\infty]$, so it is never a junk real supremum; Proposition 2.2 states that it is finite on $\mathrm{KR}(X)$. `toSM p` is $p$ as a signed measure when $p$ is finite (and $0$ otherwise; it is only ever applied to probability measures), and `diff p q = toSM p - toSM q`. No normed-space structure is put on $\mathrm{KR}(X)$; statements use $\|\sigma-\mu\|_{\mathrm{KR}}$ directly.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, (5) p. 5, (6) p. 6, Proposition 2.2 p. 6, Lemma 4.5 p. 15

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- The Kantorovich–Rubinstein space `KR(X)` ((5), p. 5): the finite signed Borel measures `μ` on
`X` with `μ(X) = 0` and `∫_{X×X} d d(|μ| × |μ|) < ∞`, where `|μ|` is the total variation. -/
def KR (X : Type*) [MetricSpace X] [MeasurableSpace X] : Set (SignedMeasure X) :=
  {μ | μ Set.univ = 0 ∧
    ∫⁻ z, edist z.1 z.2 ∂(μ.totalVariation.prod μ.totalVariation) < ∞}

/-- `∫_X f dμ` for a finite signed measure `μ`: `∫ f dμ⁺ − ∫ f dμ⁻` through the Jordan
decomposition `μ = μ⁺ − μ⁻`. -/
noncomputable def krIntegral {X : Type*} [MeasurableSpace X] (μ : SignedMeasure X)
    (f : X → ℝ) : ℝ :=
  ∫ x, f x ∂μ.toJordanDecomposition.posPart - ∫ x, f x ∂μ.toJordanDecomposition.negPart

/-- The Kantorovich–Rubinstein norm (6), p. 6: `‖μ‖_KR := sup |∫_X f dμ|` over all 1-Lipschitz
functions `f` on `X`, valued in `[0, ∞]`. -/
noncomputable def krNorm {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : SignedMeasure X) : ℝ≥0∞ :=
  ⨆ (f : X → ℝ) (_ : LipschitzWith 1 f), ENNReal.ofReal |krIntegral μ f|

/-- A finite measure viewed as a signed measure (`0` for a measure that is not finite; only applied
to probability measures). -/
noncomputable def toSM {X : Type*} [MeasurableSpace X] (p : Measure X) : SignedMeasure X := by
  classical
  exact if h : IsFiniteMeasure p then @Measure.toSignedMeasure X _ p h else 0

/-- The signed measure `p − q`, for finite measures `p, q`. -/
noncomputable def diff {X : Type*} [MeasurableSpace X] (p q : Measure X) : SignedMeasure X :=
  toSM p - toSM q

/-- A finitely supported signed measure: `∑_{x ∈ s} c(x) δ_x` for a finite set `s ⊆ X`. -/
def IsFinitelySupported {X : Type*} [MeasurableSpace X] (μ : SignedMeasure X) : Prop :=
  ∃ s : Finset X, ∃ c : X → ℝ, μ = ∑ x ∈ s, c x • (Measure.dirac x).toSignedMeasure

/-- The cone of Lemma 4.5, p. 15: `C := {α(p − q) : α ≥ 0 and p ≿ q}`, with `p, q ∈ Δ₁(X)`. -/
def coneC {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (R : Measure X → Measure X → Prop) : Set (SignedMeasure X) :=
  {σ | ∃ α : ℝ, 0 ≤ α ∧ ∃ p ∈ Delta1 X, ∃ q ∈ Delta1 X, R p q ∧ σ = α • diff p q}

end LipBernoulli.MultiUtility


