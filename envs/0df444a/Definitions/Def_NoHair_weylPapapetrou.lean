-- Prove2me | Definitions.Def_NoHair_weylPapapetrou
-- name    : NoHair_weylPapapetrou
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T20:52:39.65411+00:00
-- url     : https://prove2.me/theorems/86e0c08d-a046-416d-846b-13c546a065b8
-- title:
--   Reconstructing the vacuum Weyl–Papapetrou metric from its axial norm and twist
-- statement:
--   In local Weyl coordinates $(t,\varphi,\rho,z)$, let $X$ be the squared norm of the axial field and $Y$ its twist potential. The stationary vacuum metric takes the form
--
--   $$
--   g=-\frac{\rho^2}{X}\,dt^2+X(d\varphi+w\,dt)^2+\frac{e^{2h}}{X}(d\rho^2+dz^2).
--   $$
--
--   The radial quadratures determine $w$ and $h$ from $(X,Y)$ along each ray with fixed $z$. The normalization is $w\to0$ and $h-\log\rho\to0$ as $\rho\to\infty$. The twist sign is chosen so that $\partial_\rho w=\rho\,\partial_zY/X^2$.
--
--   Two continuous metric matrices on a common exterior admit common Weyl charts when these integrals converge absolutely for each pair of potentials and the displayed formula gives the respective matrices in the same local charts on a dense subset. Local angular charts allow for the periodicity of $\varphi$.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, eqs. (6.13)–(6.18), (6.45)–(6.47) and Cor. 6.3, https://arxiv.org/abs/0806.0016. For the degenerate end see Amsel et al., pp. 3–5, eqs. (6)–(16), https://arxiv.org/abs/0906.2367. For the global regularity hypotheses see Chruściel, Costa and Heusler, Def. 2.1 and Thm. 3.2, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_spacetime
import Definitions.Def_NoHair_vacuumErnst

noncomputable section

open Set MeasureTheory

namespace NoHair.Weyl

/-- The radial equation for the angular shift, with twist sign chosen so that
`∂ρ w = ρ (∂z Y) / X²`. The derivative here is with respect to `s = log ρ`. -/
def shiftRate (u : ErnstPotentials) (p : OrbitPoint) : ℝ :=
  Real.exp (2 * p.1) * dz u.twist p / u.normSq p ^ 2

/-- The radial equation for `h - log ρ`, with orbit metric `exp(2h)/X · (dρ² + dz²)`. -/
def conformalRate (u : ErnstPotentials) (p : OrbitPoint) : ℝ :=
  (ds u.normSq p ^ 2 + ds u.twist p ^ 2 -
    Real.exp (2 * p.1) * (dz u.normSq p ^ 2 + dz u.twist p ^ 2)) /
      (4 * u.normSq p ^ 2) - 1

/-- Absolute convergence of the two quadratures along rays of constant Weyl height. -/
def HasRadialQuadratures (u : ErnstPotentials) : Prop :=
  ∀ p : OrbitPoint,
    IntegrableOn (fun t : ℝ => shiftRate u (t, p.2)) (Ioi p.1) ∧
    IntegrableOn (fun t : ℝ => conformalRate u (t, p.2)) (Ioi p.1)

/-- The angular shift normalized to zero at infinity. -/
def angularShift (u : ErnstPotentials) (p : OrbitPoint) : ℝ :=
  -(∫ t in Ioi p.1, shiftRate u (t, p.2))

/-- The conformal exponent normalized by `h - log ρ → 0` along each radial ray. -/
def conformalExponent (u : ErnstPotentials) (p : OrbitPoint) : ℝ :=
  p.1 - ∫ t in Ioi p.1, conformalRate u (t, p.2)

/-- The Weyl–Papapetrou metric in a local coordinate map `c = (t, φ, ρ, z)`, pulled
back to the original four coordinates. The chart is used only where `ρ > 0`. -/
def metricInChart (u : ErnstPotentials) (c : E4 → E4) (y : E4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let ρ := (c y) 2
  let p : OrbitPoint := (Real.log ρ, (c y) 3)
  let b := fun (i j : Fin 4) => (fderiv ℝ c y (coordBasis j)) i
  let w := angularShift u p
  fun i j =>
    -(ρ ^ 2 / u.normSq p) * b 0 i * b 0 j +
    u.normSq p * (b 1 i + w * b 0 i) * (b 1 j + w * b 0 j) +
    Real.exp (2 * conformalExponent u p) / u.normSq p *
      (b 2 i * b 2 j + b 3 i * b 3 j)

/-- Two continuous tensor matrices on the same exterior admit local Weyl charts on
a dense subset. In each such chart their respective potentials specify all coefficients. -/
def HaveCommonCharts (D : Set E4) (G₁ G₂ : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : ErnstPotentials) : Prop :=
  HasRadialQuadratures u ∧ HasRadialQuadratures v ∧
  ContinuousOn G₁ D ∧ ContinuousOn G₂ D ∧
  ∃ S : Set E4, S ⊆ D ∧ D ⊆ closure S ∧
    ∀ y ∈ S, ∃ (V : Set E4) (c : E4 → E4),
      IsOpen V ∧ y ∈ V ∧ V ⊆ S ∧ IsOpen (c '' V) ∧ IsDiffeoOnto c V (c '' V) ∧
        ∀ x ∈ V, 0 < (c x) 2 ∧
          G₁ x = metricInChart u c x ∧ G₂ x = metricInChart v c x

end NoHair.Weyl


