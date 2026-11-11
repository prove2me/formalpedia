-- Prove2me | Definitions.Def_SumReLU_thetaPM
-- name    : SumReLU_thetaPM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:23.499095+00:00
-- url     : https://prove2.me/theorems/6bcd60bd-1625-47b4-8d1d-25df21c29b3f
-- title:
--   Projective angle $\theta_\pm$, orthogonal component $u^{\perp v}$ and normalization $\hat u$
-- statement:
--   For nonzero $x,y\in\mathbb R^d$ let $\theta(x,y)=\arccos\big(x\cdot y/(\|x\|_2\|y\|_2)\big)$ and
--   $$
--   \theta_\pm(x,y)=\min\{\theta(x,y),\ \pi-\theta(x,y)\}.
--   $$
--   For a unit vector $v$, $u^{\perp v}=(I-vv^\top)u=u-(v\cdot u)v$ is the component of $u$ orthogonal to $v$, and for $u\ne0$, $\hat u=u/\|u\|_2$ is its normalization (also written $\mathrm{proj}_{S^{d-1}}u$). For unit vectors, $\cos\theta_\pm(x,y)=|x\cdot y|$.
--
--   **Formalization Note** $\theta$ is Mathlib's `InnerProductGeometry.angle`. The normalization of $0$ is $0$; the paper uses $\hat u$ only for $u\ne0$, and every statement either assumes or asserts $u\ne0$.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, p.9 (PDF p.11)

import Mathlib

namespace SumReLU

/-- The projective angle `θ±(x, y) = min{θ(x, y), π − θ(x, y)}`, with
`θ(x, y) = arccos(x · y/(‖x‖₂‖y‖₂))` (`InnerProductGeometry.angle`).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, p.9 (PDF p.11): "θ(x, y) := arccos(x · y/(‖x‖₂ ‖y‖₂)) when x ≠ 0 and y ≠ 0. We denote
θ±(x, y) := min{θ(x, y), π − θ(x, y)}."

**Formalization Note.** Every use is on unit vectors; for a zero argument Mathlib's angle is
`π/2`, a value the paper leaves undefined and no statement uses. For unit `x, y`,
`cos θ±(x, y) = |x · y|`. -/
noncomputable def thetaPM {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  min (InnerProductGeometry.angle x y) (Real.pi - InnerProductGeometry.angle x y)

/-- The component of `u` orthogonal to `v`, `u^{⊥v} = (I − vvᵀ)u = u − (v · u)v` (§2, p.9, PDF p.11;
used for unit `v` only). -/
noncomputable def perp {d : ℕ} (v u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  u - (inner ℝ v u) • v

/-- The normalization `û = u/‖u‖₂` of a vector (§2, p.9, PDF p.11: "For any vector u ≠ 0, we use û
to denote its normalization to unit ℓ2 norm"); it is also `proj_{S^{d−1}}`.

**Formalization Note.** `normalize 0 = 0`; the paper uses `û` only for `u ≠ 0`, and every
statement here either has `u ≠ 0` or asserts it. -/
noncomputable def normalize {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ‖u‖⁻¹ • u

end SumReLU


