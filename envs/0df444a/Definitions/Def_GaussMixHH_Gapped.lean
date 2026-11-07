-- Prove2me | Definitions.Def_GaussMixHH_Gapped
-- name    : GaussMixHH_Gapped
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:54.647382+00:00
-- url     : https://prove2.me/theorems/150bc585-d384-46e1-94ca-72476886a4e9
-- title:
--   Definition 16: $(R/2,R)$-gapped radial distributions and near mass
-- statement:
--   Let $R>0$. A probability distribution $\rho$ on $[0,\infty)$ (a law of radii) is **$(R/2,R)$-gapped** if it is supported on $[0,R/2]\cup[R,\infty)$, that is,
--
--   $$\rho\big(([0,R/2]\cup[R,\infty))^{\mathrm c}\big)=0 .$$
--
--   Its **near mass** is
--
--   $$\operatorname{near-mass}_R(\rho)=\rho([0,R/2]).$$
--
--   In the paper, $\rho$ is the law of $\|\mu-z\|$ for a center $\mu\sim D$, and the near mass is the weight of centers within $R/2$ of the query point $z$. Gapped distributions are the class on which the near mass can be estimated from noisy samples.
--
--   **Formalization Note** A radial distribution is a measure on $\mathbb R$; "supported on" is the measure-zero condition above (not the topological support), which also forces $\rho$ to live on $[0,\infty)$. Being a probability measure is a separate hypothesis where the definition is used. The near mass is the real number $\rho([0,R/2])$.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Definition 16, p.23 (PDF p.25)

import Mathlib

open MeasureTheory

namespace GaussMixHH

/-!
# Gapped radial distributions and near mass (Definition 16)

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Definition 16, p.23 (PDF p.25).

"A probability distribution ρ on [0, ∞) is (R/2, R)-gapped if it is supported on
[0, R/2] ∪ [R, ∞). Its near mass is near-mass_R(ρ) := ρ([0, R/2])."

**Formalization Note.** A radial distribution is a measure on `ℝ`; "supported on" is read as the
measure-zero condition `ρ(([0, R/2] ∪ [R, ∞))ᶜ) = 0`, not the topological support. This forces
`ρ` to live on `[0, ∞)`. Being a probability measure is a separate hypothesis wherever the
definition is used. The near mass is the real number `ρ([0, R/2])` (finite for a probability
measure).
-/

/-- `ρ` is `(R/2, R)`-gapped: it gives no mass outside `[0, R/2] ∪ [R, ∞)`. -/
def IsGapped (R : ℝ) (ρ : Measure ℝ) : Prop :=
  ρ ((Set.Icc 0 (R / 2) ∪ Set.Ici R)ᶜ) = 0

/-- The near mass `near-mass_R(ρ) = ρ([0, R/2])`. -/
noncomputable def nearMass (R : ℝ) (ρ : Measure ℝ) : ℝ :=
  (ρ (Set.Icc 0 (R / 2))).toReal

end GaussMixHH


