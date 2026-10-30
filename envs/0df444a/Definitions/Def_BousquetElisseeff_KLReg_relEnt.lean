-- Prove2me | Definitions.Def_BousquetElisseeff_KLReg_relEnt
-- name    : BousquetElisseeff_KLReg_relEnt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:32.752629+00:00
-- url     : https://prove2.me/theorems/119e91e5-5339-4b5b-8e61-bcf2c3838c03
-- title:
--   Relative entropy $K(g, g')$ of two densities
-- statement:
--   For two densities $g, g'$ with respect to a reference measure $\mu$ on $\Theta$, the **relative entropy** (Kullback–Leibler divergence) is
--   $$K(g, g') = \int_\Theta g(\theta) \ln \frac{g(\theta)}{g'(\theta)}\,d\mu(\theta) \in [0, \infty],$$
--   with the value $+\infty$ when $g\cdot\mu$ is not absolutely continuous with respect to $g'\cdot\mu$ or the integral diverges. With $g' = f_0$ a fixed prior density, $K(\cdot, f_0)$ is the regularizer $N$ of §5.2.3.
--
--   **Formalization Note** $K(g,g')$ is Mathlib's `InformationTheory.klDiv` of the two measures $g\cdot\mu$ and $g'\cdot\mu$ (`Measure.withDensity`). For probability measures this equals $\int g \ln(g/g')\,d\mu$ when finite and $+\infty$ otherwise (the mass-correction term of `klDiv` vanishes), so it is exactly the paper's $K$, values in $[0,\infty]$.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, §5.2.3, p. 517 (unnumbered): N(g) = K(g, f0); p. 518: K(g, g′)

import Mathlib

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **The relative entropy (Kullback–Leibler divergence) K(g, g′) of two densities** (§5.2.3).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, §5.2.3, p. 517
(unnumbered): "We choose some fixed density f0 and define the regularizer as
N(g) = K(g, f0) = ∫_Θ g(θ) ln (g(θ)/f0(θ)) dθ, K being the Kullback-Leibler divergence or the
relative entropy." p. 518 uses K(g, g′) for any two densities g, g′.

`relEnt μ g g'` is Mathlib's `InformationTheory.klDiv` of the two measures `g · μ` and `g' · μ`
(`Measure.withDensity` of `ENNReal.ofReal ∘ g` and `ENNReal.ofReal ∘ g'`), a value in `[0, ∞]`.

**Formalization Note.** For two probability measures `P = g · μ`, `Q = g' · μ`, `klDiv P Q` is
`∫ ln (dP/dQ) dP = ∫ g ln (g/g′) dμ` when `P ≪ Q` and the log-likelihood ratio is
`P`-integrable, and `+∞` otherwise, which is exactly when the paper's integral is `+∞` (its
mass-correction term `Q(Θ) − P(Θ)` vanishes for probability measures). It is therefore the
paper's K, with value `+∞` allowed, and adds no condition. No `Real.log` integral is used, so
the Bochner junk value `0` and `Real.log 0 = 0` cannot make an infinite divergence finite. The
definition is used only for densities (`IsDensity`); its value on other functions is irrelevant
to the mission. -/
noncomputable def relEnt {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (g g' : Θ → ℝ) :
    ENNReal :=
  InformationTheory.klDiv (μ.withDensity fun θ => ENNReal.ofReal (g θ))
    (μ.withDensity fun θ => ENNReal.ofReal (g' θ))

end BousquetElisseeff.KLReg


