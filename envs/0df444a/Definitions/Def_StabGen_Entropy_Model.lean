-- Prove2me | Definitions.Def_StabGen_Entropy_Model
-- name    : StabGen_Entropy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:47:50.007917+00:00
-- url     : https://prove2.me/theorems/47c010d2-86f6-4321-99f7-ee76f57fd998
-- title:
--   Mixtures over a parameter space: densities, the averaged loss (28), the relative entropy $K$ and the objective (29)
-- statement:
--   This file fixes the objects of §5.2.3 of Bousquet and Elisseeff, *Stability and Generalization*, in which a learning algorithm outputs a mixture of base hypotheses.
--
--   Let $\Theta$ be a measurable space carrying a reference measure $\nu$, and write $d\theta$ for integration against $\nu$. A base class $\mathcal H=\{h_\theta:\theta\in\Theta\}$ is indexed by $\Theta$, and $r(h_\theta,z)$ is a loss of the base hypothesis $h_\theta$ at an example $z\in Z$; only the function $(\theta,z)\mapsto r(h_\theta,z)$ enters, so it is written $r(\theta,z)$.
--
--   1. **Densities.** A function $g:\Theta\to\mathbb R$ is a *probability density* with respect to $\nu$ if it is measurable, nonnegative, integrable and $\int_\Theta g(\theta)\,d\theta=1$. The class $F$ of the paper is the set of all such densities.
--   2. **Averaged loss (28).** For a density $g$ and an example $z$,
--   $$\ell(g,z)=\int_\Theta r(h_\theta,z)\,g(\theta)\,d\theta .$$
--   3. **Relative entropy.** For densities $g,g'$, $K(g,g')$ is the Kullback–Leibler divergence of the probability measure $g\,\nu$ from $g'\,\nu$, with values in $[0,\infty]$:
--   $$K(g,g')=\int_\Theta g(\theta)\ln\frac{g(\theta)}{g'(\theta)}\,d\theta$$
--   when $g\,\nu\ll g'\,\nu$ and the log-likelihood ratio is integrable, and $K(g,g')=+\infty$ otherwise.
--   4. **Objective (29).** For a fixed density $f_0$ (the prior), a regularization parameter $\lambda$ and a training set $S=(z_1,\dots,z_m)$,
--   $$R_r(g)=\frac1m\sum_{j=1}^m\ell(g,z_j)+\lambda K(g,f_0),$$
--   and its truncated version, the analogue of (20) with the factor $1/m$ kept,
--   $$R_r^{\setminus i}(g)=\frac1m\sum_{j\ne i}\ell(g,z_j)+\lambda K(g,f_0).$$
--
--   The algorithm of Theorem 24 returns a minimizer of $R_r$ over all densities; its stability is measured by comparing it with a minimizer of $R_r^{\setminus i}$.
--
--   **Formalization Note** $K$ is Mathlib's `InformationTheory.klDiv` of the measures $\nu$ with densities $g$ and $g'$; for probability densities its correction term $\nu'(\Theta)-\mu(\Theta)$ vanishes. Both objectives take values in $[0,\infty]$ (`ENNReal`): the empirical part is entered through `ENNReal.ofReal`, which is exact on densities because $r\ge0$ makes it nonnegative, and $\lambda K$ is kept extended so that a density with $K(g,f_0)=\infty$ has infinite objective. The sample is `S : Fin m → Z`.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), pp. 517–518, §5.2.3, Eq. (28), the regularizer N(g) = K(g, f0), Eq. (29); p. 512, Eq. (20) (truncated objective)

import Mathlib

namespace StabGen.Entropy

open MeasureTheory InformationTheory

/-- `g` is a probability density with respect to the reference measure `ν` on the parameter space
`Θ` (§5.2.3, p. 517): measurable, nonnegative, integrable, with total mass one. The class `F` of
Theorem 24 is the set of all such densities. -/
def IsDensity {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (g : Θ → ℝ) : Prop :=
  Measurable g ∧ (∀ θ, 0 ≤ g θ) ∧ Integrable g ν ∧ ∫ θ, g θ ∂ν = 1

/-- The averaged loss (28), p. 517: `ℓ(g, z) = ∫_Θ r(h_θ, z) g(θ) dθ`, where `r θ z` stands for
`r(h_θ, z)` and `dθ` is integration against the reference measure `ν`. -/
noncomputable def avgLoss {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (r : Θ → Z → ℝ)
    (g : Θ → ℝ) (z : Z) : ℝ :=
  ∫ θ, r θ z * g θ ∂ν

/-- The relative entropy (Kullback–Leibler divergence) `K(g, g')` of two densities with respect
to `ν` (p. 517–518), valued in `[0, ∞]`: Mathlib's `klDiv` of the measures `g · ν` and `g' · ν`.
For probability densities it equals `∫ g ln (g / g') dν` when `g · ν ≪ g' · ν` and the
log-likelihood ratio is integrable, and `+∞` otherwise. -/
noncomputable def relEntropy {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (g g' : Θ → ℝ) :
    ENNReal :=
  klDiv (ν.withDensity (fun θ => ENNReal.ofReal (g θ)))
    (ν.withDensity (fun θ => ENNReal.ofReal (g' θ)))

/-- The objective (29), p. 518: `(1/m) ∑_{j=1}^m ℓ(g, z_j) + λ K(g, f0)`, valued in `[0, ∞]`
so that a density with infinite relative entropy to `f0` has infinite objective. -/
noncomputable def entropyRegRisk {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (r : Θ → Z → ℝ) (f0 : Θ → ℝ) (lam : ℝ) {m : ℕ} (S : Fin m → Z) (g : Θ → ℝ) : ENNReal :=
  ENNReal.ofReal ((1 / (m : ℝ)) * ∑ j, avgLoss ν r g (S j)) +
    ENNReal.ofReal lam * relEntropy ν g f0

/-- The truncated objective, the analogue of (20), p. 512, for (29):
`(1/m) ∑_{j ≠ i} ℓ(g, z_j) + λ K(g, f0)`, with the factor `1/m` kept. -/
noncomputable def truncEntropyRegRisk {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (r : Θ → Z → ℝ) (f0 : Θ → ℝ) (lam : ℝ) {m : ℕ} (S : Fin m → Z) (i : Fin m)
    (g : Θ → ℝ) : ENNReal :=
  ENNReal.ofReal ((1 / (m : ℝ)) * ∑ j ∈ Finset.univ.erase i, avgLoss ν r g (S j)) +
    ENNReal.ofReal lam * relEntropy ν g f0

end StabGen.Entropy


