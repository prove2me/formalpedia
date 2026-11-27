-- Prove2me | Definitions.Def_LearningBasedRO_Supplement_Reconstruction
-- name    : LearningBasedRO_Supplement_Reconstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:15:27.821808+00:00
-- url     : https://prove2.me/theorems/d8d640da-81a9-403e-9557-b973584eac67
-- title:
--   The reconstruction quantile $\rho(\hat x_0)$ and the reconstructed robust program (9)
-- statement:
--   Let $P$ be a probability measure on the data space $E$, $X$ a set of decisions, $g:X\times E\to\mathbb R^l$, $b\in\mathbb R^l$, $k\in\mathbb R^l$ a positive vector, $\epsilon$ a tolerance level and $\hat x_0\in X$ a given solution (not necessarily feasible).
--
--   1. **Reconstruction quantile.** With $Z(\xi)=\max_{j=1,\dots,l}(g_j(\hat x_0;\xi)-b_j)/k_j$, $\rho=\rho(\hat x_0)$ is the $(1-\epsilon)$-quantile of $Z$ under $P$,
--   $$\rho=\inf\{q\in\mathbb R:\ P(Z\le q)\ge 1-\epsilon\}.$$
--   2. **Uncertainty set of (9).** $\{\xi:\ g(\hat x_0;\xi)\le b+\rho k\}$ (componentwise).
--   3. **Feasibility for (9).** $x$ is feasible for the reconstructed robust program
--   $$\text{minimize } f(x)\ \text{ subject to }\ g(x;\xi)\le b\quad\forall\,\xi:\ g(\hat x_0;\xi)\le b+\rho k \tag{9}$$
--   if $g(x;\xi)\le b$ for every $\xi$ in that set.
--   4. **Optimality for (9).** $\hat x$ is an optimal solution of (9) if it is feasible for (9) and $f(\hat x)\le f(x)$ for every $x$ feasible for (9).
--
--   These are the objects of the self-improving reconstruction of §2.4.2, about which Theorems 3 and 4 are stated.
--
--   **Formalization Note** $Z\le q$ is written as $(g_j(\hat x_0;\xi)-b_j)/k_j\le q$ for all $j$, which equals $\max_j(\cdot)\le q$ for $l\ge1$ and avoids an empty maximum for $l=0$. "The $(1-\epsilon)$-quantile" is the lower quantile (an infimum); in degenerate cases where the set is empty or unbounded below Lean's `sInf` returns $0$. Feasibility for (9) is the base mission's robust feasibility `ROFeasible` with safety set $\{y: y\le b\}$. Probabilities are (outer) measures, $1-\epsilon$ enters through `ENNReal.ofReal`.
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, §2.4.2, (8), (9) and the text after (9), p.13

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO.Supplement

/-- The reconstruction quantile `ρ = ρ(x̂₀)` of (9): the `(1 - ϵ)`-quantile of
`Z(ξ) = max_{j=1,…,l} (gⱼ(x̂₀; ξ) - bⱼ) / kⱼ` under `P`, taken as the lower quantile
`ρ = inf {q ∈ ℝ : P(Z ≤ q) ≥ 1 - ϵ}`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.4.2, text after (9), p.13.

**Formalization Note** The event `Z ≤ q` is written `∀ j, (gⱼ(x̂₀; ξ) - bⱼ) / kⱼ ≤ q`, which equals
`max_j (…) ≤ q` for `l ≥ 1` and avoids an empty maximum for `l = 0`. "The `(1 - ϵ)`-quantile" is
read as the lower quantile (`sInf`); for a probability measure `P`, `0 < ϵ < 1` and measurable
`ξ ↦ gⱼ(x̂₀; ξ)` the set is nonempty, bounded below and closed, so the infimum is attained. In the
degenerate cases (empty or unbounded set, e.g. `l = 0`) Lean's `sInf` returns the junk value `0`.
`P` of a set is its (outer) measure; `1 - ϵ` enters through `ENNReal.ofReal`. -/
noncomputable def reconQuantile {X E : Type*} [MeasurableSpace E] (P : Measure E) {l : ℕ}
    (g : X → E → (Fin l → ℝ)) (b k : Fin l → ℝ) (ϵ : ℝ) (x₀ : X) : ℝ :=
  sInf {q : ℝ | ENNReal.ofReal (1 - ϵ) ≤ P {ξ | ∀ j, (g x₀ ξ j - b j) / k j ≤ q}}

/-- The uncertainty set of the reconstructed robust program (9):
`{ξ : g(x̂₀; ξ) ≤ b + ρ k}` (componentwise), with `ρ = ρ(x̂₀)` the reconstruction quantile.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.4.2, (9), p.13. -/
noncomputable def reconSet {X E : Type*} [MeasurableSpace E] (P : Measure E) {l : ℕ}
    (g : X → E → (Fin l → ℝ)) (b k : Fin l → ℝ) (ϵ : ℝ) (x₀ : X) : Set E :=
  {ξ | g x₀ ξ ≤ b + reconQuantile P g b k ϵ x₀ • k}

/-- Feasibility for the reconstructed robust program (9): `g(x; ξ) ≤ b` for every `ξ` with
`g(x̂₀; ξ) ≤ b + ρ k`, i.e. feasibility for the base robust program (2) with the inequality safety
set `{y : y ≤ b}` and uncertainty set `reconSet`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.4.2, (9), p.13. -/
def ReconFeasible {X E : Type*} [MeasurableSpace E] (P : Measure E) {l : ℕ}
    (g : X → E → (Fin l → ℝ)) (b k : Fin l → ℝ) (ϵ : ℝ) (x₀ x : X) : Prop :=
  ROFeasible g (Set.Iic b) (reconSet P g b k ϵ x₀) x

/-- `x̂` is an optimal solution of the reconstructed robust program (9) with objective `f`: it is
feasible for (9) and `f(x̂) ≤ f(x)` for every `x` feasible for (9).
Hong–Huang–Lam, arXiv:1704.04342v2, §2.4.2, (9) and Theorem 4, p.13. -/
def IsReconOptimal {X E : Type*} [MeasurableSpace E] (P : Measure E) {l : ℕ}
    (g : X → E → (Fin l → ℝ)) (b k : Fin l → ℝ) (ϵ : ℝ) (x₀ : X) (f : X → ℝ) (xhat : X) : Prop :=
  ReconFeasible P g b k ϵ x₀ xhat ∧ ∀ x, ReconFeasible P g b k ϵ x₀ x → f xhat ≤ f x

end LearningBasedRO.Supplement


