-- Prove2me | Definitions.Def_MHSpectralGap_RWM_L2Gap
-- name    : MHSpectralGap_RWM_L2Gap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:54.845496+00:00
-- url     : https://prove2.me/theorems/3273e700-9d8b-4b6e-853b-815e7e26a295
-- title:
--   Definition 2.7, p. 10 — the Markov operator Pf and β = ‖P‖_{L²₀→L²₀}, the L²_µ-spectral gap being 1 − β
-- statement:
--   Let $P$ be a Markov kernel on a measurable space $X$ and $\mu$ a probability measure on $X$. The **Markov operator** of $P$ acts on functions by $(Pf)(x)=\int_X f(y)\,P(x,dy)$. Write $\mu(f)=\int f\,d\mu$ and $\|\cdot\|_2$ for the norm of $L^2_\mu$. Define
--
--   $$
--   \beta \;=\; \|P\|_{L^2_0\to L^2_0} \;=\; \sup_{f\in L^2_\mu,\ \|f-\mu(f)\|_2\neq 0}\ \frac{\|Pf-\mu(f)\|_2}{\|f-\mu(f)\|_2}.
--   $$
--
--   Following Definition 2.7 of the paper, if $\mu$ is invariant for $P$ and $\beta<1$, then $P$ has an **$L^2_\mu$-spectral gap** $1-\beta$; the quantity $1-\beta$ is what Theorem 2.17 bounds.
--
--   For a $\mu$-invariant Markov kernel the ratios are at most $1$, by Jensen's inequality and invariance, so the supremum is over a set bounded by $1$; the set is nonempty as soon as $L^2_\mu$ contains a non-constant function.
--
--   **Formalization Note** The supremum ranges over measurable functions $f$ in $L^2_\mu$ (every $L^2_\mu$ class has a measurable representative). Norms are Mathlib's `eLpNorm` with exponent 2, converted to real numbers; $(Pf)(x)$ is a Bochner integral, which is finite for $\mu$-almost every $x$ when $\mu$ is invariant. $\beta$ is the real `sSup` of the set of ratios; on an empty set (every $f$ almost surely constant, e.g. a Dirac $\mu$) it takes the value $0$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 10, Definition 2.7

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The Markov operator of a kernel: `(P f)(x) = ∫ f(y) P(x, dy)`. -/
noncomputable def markovOp {X : Type*} [MeasurableSpace X] (P : ProbabilityTheory.Kernel X X)
    (f : X → ℝ) (x : X) : ℝ :=
  ∫ y, f y ∂(P x)

/-- The set of ratios `‖P f − μ(f)‖₂ / ‖f − μ(f)‖₂` over (measurable representatives of)
`f ∈ L²_μ` with `‖f − μ(f)‖₂ ≠ 0` (Definition 2.7, p. 10). -/
def l2RatioSet {X : Type*} [MeasurableSpace X] (P : ProbabilityTheory.Kernel X X)
    (μ : Measure X) : Set ℝ :=
  {r | ∃ f : X → ℝ, Measurable f ∧ MemLp f 2 μ ∧
    eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ ≠ 0 ∧
    r = (eLpNorm (fun x => markovOp P f x - ∫ y, f y ∂μ) 2 μ).toReal /
      (eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ).toReal}

/-- `β = ‖P‖_{L²_0 → L²_0} = sup_{f ∈ L²_μ} ‖P f − μ(f)‖₂ / ‖f − μ(f)‖₂` (Definition 2.7,
p. 10); the `L²_μ`-spectral gap is `1 − β`. For a `μ`-invariant Markov kernel and a
probability measure `μ` the ratio set is bounded above by `1`; it is nonempty unless every
`f ∈ L²_μ` is `μ`-a.e. constant (then `β = 0` by the `sSup ∅` convention). -/
noncomputable def l2Beta {X : Type*} [MeasurableSpace X] (P : ProbabilityTheory.Kernel X X)
    (μ : Measure X) : ℝ :=
  sSup (l2RatioSet P μ)

end MHSpectralGap.RWM


