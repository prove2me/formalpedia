-- Prove2me | Definitions.Def_HeilmanMax3Cut_Theta
-- name    : HeilmanMax3Cut_Theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:03.121243+00:00
-- url     : https://prove2.me/theorems/4429355d-23e9-430a-84f4-4f0d565d8e46
-- title:
--   The standard simplex partition $\Theta$ of $\mathbb R^2$
-- statement:
--   $\Theta=(\Theta_1,\Theta_2,\Theta_3)$ is the partition of $\mathbb R^2$ into three sectors of angle $2\pi/3$ with vertex at the origin. Here $\Theta_1$ is the sector of angles $[-\pi/3,\pi/3]$, $\Theta_2$ that of angles $[\pi/3,\pi]$ and $\Theta_3$ that of angles $[\pi,5\pi/3]$.
--
--   It is the conjectured (and, by Theorem 7.1 for $\rho\in[-1/2,0)$, actual) minimizer of noise stability among three-set partitions.
--
--   **Formalization Note** The sectors are the published closed propeller sectors; neighbours share a boundary ray, which has Gaussian measure zero, so $\Theta$ is a partition up to a null set. The orientation is immaterial by rotation invariance.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 7, p.21

import Mathlib
import Definitions.Def_GaussianPropeller
open OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **The standard simplex partition `Θ` of `ℝ²`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 7, p.21: "Let `Θ = (Θ₁, Θ₂, Θ₃)`
be the standard simplex partition of `ℝ²`, consisting of three sectors of angle `2π/3` with vertex
at the origin."

**Formalization Note.** `Θ` is the published `OAI.GaussianPropeller.propeller 2 3`: the closed
sectors `{|x₁| ≤ √3 x₀}` (angles in `[−π/3, π/3]`), `{x₁ ≥ 0, √3 x₀ ≤ x₁}` (angles in
`[π/3, π]`) and `{x₁ ≤ 0, √3 x₀ ≤ −x₁}` (angles in `[π, 5π/3]`). Adjacent closed sectors share a
boundary ray, a Gaussian-null set, so `Θ` is a partition up to measure zero (`IsPartition`); the
orientation is immaterial since the Gaussian measure is rotation invariant. -/
noncomputable def Theta : Fin 3 → Set (Space 2) :=
  propeller 2 3

end HeilmanMax3Cut


