-- Prove2me | Definitions.Def_TalagrandConc_TwoPoint_Basic
-- name    : TalagrandConc_TwoPoint_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:34.286933+00:00
-- url     : https://prove2.me/theorems/099d12e5-d765-42bc-acba-7f934f993560
-- title:
--   The two-point space $\{0,1\}^N$, the Hamming and one-sided distances to a set, and the constants $b(\alpha,t,p)$, $a(\alpha,t)$ of §2.3
-- statement:
--   This module fixes the objects of Section 2.3 of Talagrand's paper, the case of the two-point space.
--
--   Let $\Omega=\{0,1\}$ and, for $p\in[0,1]$, let $\mu$ be the probability on $\Omega$ with $\mu(\{1\})=p$ and $\mu(\{0\})=1-p$. For an integer $N\ge 0$ write points of $\Omega^N$ as $x=(x_1,\dots,x_N)$ and let $P=\mu^N$ be the product probability. For a subset $A\subseteq\Omega^N$ and $x\in\Omega^N$:
--
--   1. **Hamming distance to $A$** (Eq. (2.1.1)):
--   $$f(A,x)=\min\big\{\operatorname{card}\{i\le N:\ x_i\neq y_i\}\ :\ y\in A\big\}.$$
--
--   2. **One-sided distance to $A$** (Theorem 2.3.4): only the coordinates where $x$ has a $1$ and the point of $A$ has a $0$ are counted,
--   $$f^{+}(A,x)=\min\big\{\operatorname{card}\{i\le N:\ x_i=1,\ y_i=0\}\ :\ y\in A\big\}.$$
--
--   Both distances equal $+\infty$ when $A=\emptyset$.
--
--   3. **The constant of Proposition 2.3.1** (Eqs. (2.3.2)–(2.3.3)): for $\alpha>0$, $t\ge 0$,
--   $$b(\alpha,t,p)=\begin{cases}((1-p)e^{t}+p)\,(p+(1-p)e^{-t/\alpha})^{\alpha}, & p\ge 1/2,\\ ((1-p)e^{-t}+p)\,(p+(1-p)e^{t/\alpha})^{\alpha}, & p< 1/2.\end{cases}$$
--   The two expressions agree at $p=1/2$, and the second equals $b(\alpha,t,1-p)$ computed with the first.
--
--   4. **The constant of Theorem 2.3.4**: for a second parameter $p_1\in[0,1]$,
--   $$a(\alpha,t)=\max\Big(1,\ (1-p+pe^{t})\,(p_1e^{-t/\alpha}+1-p_1)^{\alpha}\Big).$$
--
--   5. **Exponential moment integrand**: $e^{tz}$ for $t\in\mathbb R$ and $z\in[0,+\infty]$, with $e^{t\cdot\infty}=+\infty$ for $t>0$ and $e^{0\cdot\infty}=1$.
--
--   These are the objects in which the two-point inequalities of Section 2.3 are stated: the exponential moments of $f$ and $f^{+}$ under $P$ are bounded by the $N$-th power of $b(\alpha,t,p)$ or $a(\alpha,t)$, divided by a power of the measure of $A$.
--
--   **Formalization Note** $\Omega$ is `Bool` with $1$ = `true`. The product measure reuses the published `TalagrandCore.bernPi`, with `p : unitInterval` converted to its nonnegative-real parameter. Coordinates are indexed by `Fin N`. Distances take values in $[0,\infty]$ (`ℝ≥0∞`), so the empty set gives $+\infty$ rather than a junk $0$; the integrand $e^{tz}$ is computed through `EReal.exp`. Every subset of the finite set $\{0,1\}^N$ is measurable, so no measurability hypotheses are needed.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 81, Eq. (2.1.1); p. 87, Section 2.3, Eqs. (2.3.2)–(2.3.3); p. 90, Theorem 2.3.4

import Mathlib
import Definitions.Def_talagrand_finite_bool_core
import Definitions.Def_TalagrandConc_OnePoint_Basic

namespace TalagrandConc.TwoPoint

open MeasureTheory
open scoped ENNReal NNReal Classical

/-- Talagrand (1995), §2.1, p. 81 and §2.3, p. 87: the product probability `P = μ^N` on
`Ω^N = {0,1}^N` (coordinates indexed by `Fin N`), where `μ({1}) = p`.
This is the published Boolean product Bernoulli measure `TalagrandCore.bernPi`. -/
noncomputable def productMeasure (N : ℕ) (p : unitInterval) : Measure (Fin N → Bool) :=
  TalagrandCore.bernPi (Fin N) (unitInterval.toNNReal p) (by
    exact_mod_cast p.property.2)

/-- Talagrand (1995), Eq. (2.1.1), p. 81: the Hamming distance from `x ∈ Ω^N` to `A ⊆ Ω^N`,
`f(A, x) = min { card {i ≤ N ; x_i ≠ y_i} ; y ∈ A }`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def hammingDistToSet {N : ℕ} (A : Set (Fin N → Bool)) (x : Fin N → Bool) : ℝ≥0∞ :=
  ⨅ y ∈ A, ((Finset.univ.filter (fun i => x i ≠ y i)).card : ℝ≥0∞)

/-- Talagrand (1995), Theorem 2.3.4, p. 90: the one-sided distance
`f(A, x) = min { card {i ≤ N ; x_i = 1, y_i = 0} ; y ∈ A }`, which counts only the coordinates
where `x` has a `1` and the point `y ∈ A` has a `0`.
It takes values in `ℝ≥0∞`; for `A = ∅` the infimum is `⊤ = +∞`. -/
noncomputable def oneSidedDistToSet {N : ℕ} (A : Set (Fin N → Bool)) (x : Fin N → Bool) : ℝ≥0∞ :=
  ⨅ y ∈ A, ((Finset.univ.filter (fun i => x i = true ∧ y i = false)).card : ℝ≥0∞)

/-- Talagrand (1995), Eqs. (2.3.2)–(2.3.3), p. 87: for `p ≥ 1/2`,
`b(α, t, p) = ((1 - p) e^t + p) (p + (1 - p) e^{-t/α})^α`, and for `p ≤ 1/2`,
`b(α, t, p) = ((1 - p) e^{-t} + p) (p + (1 - p) e^{t/α})^α`.
(The two formulas agree at `p = 1/2`; the second equals `b(α, t, 1 - p)` computed by the first.) -/
noncomputable def bConst (α t p : ℝ) : ℝ :=
  if 1 / 2 ≤ p then
    ((1 - p) * Real.exp t + p) * (p + (1 - p) * Real.exp (-t / α)) ^ α
  else
    ((1 - p) * Real.exp (-t) + p) * (p + (1 - p) * Real.exp (t / α)) ^ α

/-- Talagrand (1995), Theorem 2.3.4, p. 90:
`a(α, t) = max(1, (1 - p + p e^t) (p₁ e^{-t/α} + 1 - p₁)^α)`, where `p = μ({1})` and
`p₁ = μ₁({1})`. -/
noncomputable def aConst (α t p p₁ : ℝ) : ℝ :=
  max 1 ((1 - p + p * Real.exp t) * (p₁ * Real.exp (-t / α) + 1 - p₁) ^ α)

end TalagrandConc.TwoPoint


