-- Prove2me | Definitions.Def_CompetitionComplexity_Distribution
-- name    : CompetitionComplexity_Distribution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:54.800902+00:00
-- url     : https://prove2.me/theorems/ee74c258-60fa-46ed-9dfc-fa32ed3628c5
-- title:
--   Distributions on $[0,\infty)$ with finite mean, the expected maximum $M_n(F)$, and the support endpoints $\omega_0(F),\omega_1(F)$
-- statement:
--   Throughout the paper a **distribution** $F$ is a probability law on the non-negative reals with finite expectation. In Lean it is a measure $\mu$ on $\mathbb R$ with
--
--   1. $\mu$ a probability measure,
--   2. $\mu((-\infty,0))=0$, and
--   3. $\int |x|\,d\mu(x)<\infty$.
--
--   Nothing else is assumed: no density, no continuity, no bounded support.
--
--   For such $F$ and $n\in\mathbb N$, the **expected maximum** is $M_0(F)=0$ and, for $n\ge1$,
--   $$
--   M_n(F)=\mathbb E\bigl[\max\{X_1,\dots,X_n\}\bigr],
--   $$
--   where $X_1,\dots,X_n$ are i.i.d. with law $F$. It is the welfare of the optimal auction with $n$ buyers (the "prophet").
--
--   Writing $F(y)=\mu((-\infty,y])$ for the distribution function, the **endpoints of the support** are
--   $$
--   \omega_0(F)=\inf\{y\in\mathbb R: F(y)>0\},\qquad \omega_1(F)=\sup\{y\in\mathbb R: F(y)<1\}.
--   $$
--   $\omega_1(F)=+\infty$ exactly when the support is unbounded.
--
--   The value $A_n(F)$ of the optimal dynamic pricing policy with $n$ buyers is the recursion $A_0(F)=0$, $A_{n+1}(F)=\mathbb E\max\{X,A_n(F)\}$. It is the published definition `CorreaThreshold.Adaptive.dpW`, which this mission reuses.
--
--   **Formalization Note** $M_n(F)$ for $n\ge1$ is the published `SamuelCahnProphet.IID.Emax`, the lower integral of $\max(x_1,\dots,x_n)$ against the product law, valued in $[0,\infty]$; for a distribution on $[0,\infty)$ the maximum is a.s. non-negative, so this is the expectation. The endpoints are valued in the extended reals so that $\omega_1(F)=+\infty$ is representable.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §2, p.6 (distributions, M_n(F), A_n(F)); §3, p.8 (ω_0(F), ω_1(F))

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory ProbabilityTheory

namespace CompetitionComplexity

/-- **Distribution** (the standing class).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §2, p.6: "We consider
distributions F over the non-negative reals with finite expectation."

**Formalization Note.** A distribution `F` is a probability measure `μ` on `ℝ` with
`μ (Set.Iio 0) = 0` (support in `[0, ∞)`) and `∫ |x| dμ < ∞` (finite expectation). Nothing else
(no density, no continuity, no bounded support) is assumed. -/
def IsDist (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ Integrable (fun x : ℝ => x) μ

/-- **`Mₙ(F)`**, the expected maximum of `n` i.i.d. draws (§2, p.6): `M₀(F) = 0` and, for
`n ≥ 1`, `Mₙ(F) = E(max{X₁, …, Xₙ})`.

**Formalization Note.** For `n ≥ 1` this is the published `SamuelCahnProphet.IID.Emax μ n`, the
lower integral of `max(x₁, …, xₙ)` against the product measure `μ^{⊗n}`, valued in `[0, ∞]`.
For a distribution supported on `[0, ∞)` the maximum is a.s. nonnegative, so this is the
expectation of the maximum (finite, since it is at most `n E X`). -/
noncomputable def Mval (μ : Measure ℝ) (n : ℕ) : ENNReal :=
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    SamuelCahnProphet.IID.Emax μ n

/-- **`ω₀(F) = inf{y ∈ ℝ : F(y) > 0}`**, the left endpoint of the support (§3, p.8), where `F` is
the distribution function `ProbabilityTheory.cdf μ`.

**Formalization Note.** Valued in `EReal`, like `ω₁`, so that the two endpoints can be compared;
for a distribution on `[0, ∞)` it is a real number `≥ 0`. -/
noncomputable def omega0 (μ : Measure ℝ) : EReal :=
  ⨅ (y : ℝ) (_ : 0 < cdf μ y), (y : EReal)

/-- **`ω₁(F) = sup{y ∈ ℝ : F(y) < 1}`**, the right endpoint of the support (§3, p.8).

**Formalization Note.** Valued in `EReal`: `ω₁(F) = +∞` exactly when the support is unbounded.
The set is never empty for a distribution on `[0, ∞)` (it contains every `y < 0`). -/
noncomputable def omega1 (μ : Measure ℝ) : EReal :=
  ⨆ (y : ℝ) (_ : cdf μ y < 1), (y : EReal)

end CompetitionComplexity


