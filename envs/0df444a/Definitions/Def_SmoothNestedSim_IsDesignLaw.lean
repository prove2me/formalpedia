-- Prove2me | Definitions.Def_SmoothNestedSim_IsDesignLaw
-- name    : SmoothNestedSim_IsDesignLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:18.562029+00:00
-- url     : https://prove2.me/theorems/b8419fed-e00c-41a9-8cd5-c9ff09223177
-- title:
--   Assumption 2: bounded convex support, density bounded above and below
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ and let $\mu_X$ be the law of the conditioning variable $X$. **Assumption 2** holds if
--
--   1. $\Omega$ is bounded and convex, and
--   2. $\mu_X$ has a density $\rho$ with respect to Lebesgue measure on $\Omega$ (and gives no mass outside $\Omega$) with $c\le\rho(\mathbf x)\le C$ for all $\mathbf x\in\Omega$, for some constants $0<c\le C$.
--
--   Boundedness and convexity of the support make the Sobolev-space description of the Matérn RKHS available on $\Omega$, and the two-sided density bound lets empirical and population norms be compared.
--
--   **Formalization Note** That $\mu_X$ is a probability measure is a separate hypothesis of every statement. No openness, closedness, boundary regularity or continuity of $\rho$ is assumed.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §4.1, Assumption 2, p.15

import Mathlib

open MeasureTheory

namespace SmoothNestedSim

/-- **Assumption 2** (Wang, Wang, Zhang, *Smooth Nested Simulation*, arXiv:2201.02958v6, §4.1,
p.15): "The support of `X` is a bounded convex set `Ω ⊂ ℝ^d`. Moreover, `X` has a probability
density function that is bounded above and below away from zero."

`IsDesignLaw Ω μX` says: `Ω` is bounded and convex, and the law `μX` of `X` has a density `ρ`
with respect to Lebesgue measure restricted to `Ω` with `c ≤ ρ ≤ C` on `Ω` for some constants
`0 < c` and `C`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`.
"Support `Ω`" is encoded by the density living on `Ω` (so `μX(Ωᶜ) = 0`) and being bounded
below by `c > 0` on `Ω`. That `μX` is a probability measure is a separate instance argument of
every statement. No openness, closedness, regularity of the boundary, or continuity of the
density is assumed. -/
def IsDesignLaw {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (μX : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  Bornology.IsBounded Ω ∧ Convex ℝ Ω ∧
    ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, Measurable ρ ∧
      μX = (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (ρ x)) ∧
      ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ Ω, c ≤ ρ x ∧ ρ x ≤ C

end SmoothNestedSim


