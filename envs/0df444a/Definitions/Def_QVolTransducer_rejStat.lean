-- Prove2me | Definitions.Def_QVolTransducer_rejStat
-- name    : QVolTransducer_rejStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:25:16.026664+00:00
-- url     : https://prove2.me/theorems/01e00ceb-853d-4846-aee9-a44081be43e2
-- title:
--   Rejection-sampled distribution $\tilde\pi_{\beta,r,\zeta/\gamma}$, discretized Gibbs distribution $\pi_{\beta,r,\zeta/\gamma}$ and total variation
-- statement:
--   Let $\gamma:=1-\frac1{2d}$. For $x\in K\cap rB_d$ the **acceptance weight** is
--
--   $$
--   a(x):=\frac{\exp(-\frac{\beta}{\gamma^2}\|x\|^2)}{\exp(-\beta\|x\|^2)}\,\mathbb 1_{x/\gamma\in K\cap rB_d},
--   $$
--
--   and the **rejection-sampled distribution** on $(K\cap rB_d)_{\zeta/\gamma}$ is
--
--   $$
--   \tilde\pi_{\beta,r,\zeta/\gamma}(x):=\frac{\pi_{\beta,\delta,r,\zeta}(\gamma x)\,a(\gamma x)}{A_\zeta},
--   \qquad
--   A_\zeta:=\mathbb E_{x\sim\pi_{\beta,\delta,r,\zeta}}[a(x)] .
--   $$
--
--   The **discretization** of the Gibbs distribution on a body $S$ to the grid $S_\zeta$ is $\pi_{f,\zeta}(x)=f(x)/\sum_{y\in S_\zeta}f(y)$ with $f(x)=e^{-\beta\|x\|^2}$; with $S=K\cap rB_d$ and spacing $\zeta/\gamma$ it is $\pi_{\beta,r,\zeta/\gamma}$. The **total variation distance** of two distributions on a finite set is $\frac12\sum_z|p(z)-q(z)|$.
--
--   Rejection sampling turns the speedy-walk distribution, whose density carries the local conductance, into an approximation of the clipped Gibbs distribution.
--
--   **Formalization Note** The grid point $x=(\zeta/\gamma)z$ and the point $\gamma x=\zeta z$ of the finer grid share the index $z\in\mathbb Z^d$. All distributions are functions on $\mathbb Z^d$, zero off their support.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.16, p.61; Definition 7.4, p.43 (PDF pp.63, 45)

import Mathlib
import Definitions.Def_QVolTransducer_speedyStat

namespace QVolTransducer

/-- The shrinking factor `γ := 1 − 1/(2d)` of the rejection-sampling step (Cornelissen, Apers,
Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 9.16, p.61). -/
noncomputable def shrink (d : ℕ) : ℝ := 1 - 1 / (2 * (d : ℝ))

open Classical in
/-- The acceptance weight of Theorem 9.16 (arXiv:2609.40217, p.61): for `x ∈ K ∩ rB_d`,
`a(x) := exp(−(β/γ²)‖x‖²) / exp(−β‖x‖²) · 1_{x/γ ∈ K ∩ rB_d}` with `γ = 1 − 1/(2d)`. -/
noncomputable def acceptWeight {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-(β / shrink d ^ 2) * ‖x‖ ^ 2) / Real.exp (-β * ‖x‖ ^ 2) *
    (if (shrink d)⁻¹ • x ∈ K ∩ Metric.closedBall 0 r then 1 else 0)

/-- The normalizer `A_ζ := E_{x∼π_{β,δ,r,ζ}}[a(x)]` of Theorem 9.16 (arXiv:2609.40217, p.61), the
expectation of the acceptance weight under the clipped speedy-walk distribution `π_{β,δ,r,ζ}` on
`(K ∩ rB_d)_ζ`. -/
noncomputable def rejNormalizer {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ r ζ R : ℝ) :
    ℝ :=
  ∑ z ∈ gridIdx d ζ R,
    speedyStat (K ∩ Metric.closedBall 0 r) β δ ζ R z * acceptWeight K β r (latticePt ζ z)

/-- The rejection-sampled distribution `π̃_{β,r,ζ/γ}` on `(K ∩ rB_d)_{ζ/γ}` (arXiv:2609.40217,
Theorem 9.16, p.61): `π̃_{β,r,ζ/γ}(x) := π_{β,δ,r,ζ}(γx) a(γx) / A_ζ`.

**Formalization Note** The argument `z ∈ ℤ^d` stands for the point `x = (ζ/γ) z` of the grid
`ζ/γ ℤ^d`, so that `γx = ζ z` is the point of the grid `ζℤ^d` at which `π_{β,δ,r,ζ}` and `a` are
evaluated. The indicator in `a(γx)` is `1_{x ∈ K ∩ rB_d}`, so the value is `0` off
`(K ∩ rB_d)_{ζ/γ}` (the zero extension of p.53). -/
noncomputable def rejStat {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ r ζ R : ℝ)
    (z : Fin d → ℤ) : ℝ :=
  speedyStat (K ∩ Metric.closedBall 0 r) β δ ζ R z * acceptWeight K β r (latticePt ζ z) /
    rejNormalizer K β δ r ζ R

open Classical in
/-- The discretization `π_{f,ζ}` of the Gibbs distribution `π_β` on a body `S` to the grid
`S_ζ = ζℤ^d ∩ S` (arXiv:2609.40217, Definition 7.4, p.43: "(π_{f,ζ})_x = f(x)/N_{f,ζ} where
N_{f,ζ} = Σ_{x∈Ω_ζ} f(x)"), with `f(x) = exp(−β‖x‖²)`; `0` off `S_ζ`. With `S = K ∩ rB_d` and
spacing `ζ/γ` it is the distribution `π_{β,r,ζ/γ}` of Theorem 9.16 (p.61).

**Formalization Note** The argument `z ∈ ℤ^d` stands for the grid point `ζ z`; the grid of `S` is
taken inside `(RB_d)_ζ`, which is all of `S_ζ` when `S ⊆ RB_d`. -/
noncomputable def gibbsGrid {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (β ζ R : ℝ)
    (z : Fin d → ℤ) : ℝ :=
  if z ∈ gridIdx d ζ R ∧ latticePt ζ z ∈ S then
    Real.exp (-β * ‖latticePt ζ z‖ ^ 2) /
      ∑ y ∈ (gridIdx d ζ R).filter (fun y => latticePt ζ y ∈ S),
        Real.exp (-β * ‖latticePt ζ y‖ ^ 2)
  else 0

/-- The total variation distance `‖p − q‖_TV = ½ Σ_{z ∈ s} |p(z) − q(z)|` of two distributions
supported on the finite set `s` (arXiv:2609.40217, Theorem 9.16, p.61). -/
noncomputable def tvGrid {d : ℕ} (s : Finset (Fin d → ℤ)) (p q : (Fin d → ℤ) → ℝ) : ℝ :=
  (1 / 2) * ∑ z ∈ s, |p z - q z|

end QVolTransducer


