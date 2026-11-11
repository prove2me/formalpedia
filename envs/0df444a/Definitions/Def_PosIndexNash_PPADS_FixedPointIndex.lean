-- Prove2me | Definitions.Def_PosIndexNash_PPADS_FixedPointIndex
-- name    : PosIndexNash_PPADS_FixedPointIndex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:28.441257+00:00
-- url     : https://prove2.me/theorems/10ca026a-4050-4ef9-9db8-916b115d195a
-- title:
--   Regular fixed points and the fixed point index sign det(I − DΦ(p)) (eq. (5))
-- statement:
--   For a map $\Phi : \mathbb{R}^d \to \mathbb{R}^d$ and a point $p$, let $D\Phi(p)$ be its Jacobian. An interior fixed point $p \in (0,1)^d$ of $\Phi$ is **regular** if $\det(I_d - D\Phi(p)) \ne 0$, and its **fixed point index** is
--   $$\mathrm{ind}_\Phi(p) := \mathrm{sign}\det\big(I_d - D\Phi(p)\big) \in \{-1, +1\}.$$
--
--   **Formalization Note** $D\Phi(p)$ is the Fréchet derivative `fderiv ℝ Φ p`. At a point where the circuit computing $\Phi$ is strict, $\Phi$ agrees with its active affine piece on a neighbourhood, so this is the Jacobian of that piece (p. 13). The index is an integer, with $\mathrm{sign}(0) = 0$ off regular points.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), pp. 13–14, eq. (5)

import Mathlib

namespace PosIndexNash.PPADS

/-- **Determinant `det(I_d − DΦ(p))`** of a map `Φ : ℝ^d → ℝ^d` at `p` (Kontogiannis, Panageas,
Pollatos, Yan, *Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879,
p. 13–14, eq. (5)).

**Formalization Note** `DΦ(p)` is the Fréchet derivative `fderiv ℝ Φ p`. At a point where the
circuit computing `Φ` is strict, `Φ` agrees with its active affine piece on a neighbourhood of `p`
(p. 13), so `fderiv` is the Jacobian of that piece; elsewhere the value may be junk and no item
uses it there. -/
noncomputable def detIdSubD {d : ℕ} (Φ : (Fin d → ℝ) → (Fin d → ℝ)) (p : Fin d → ℝ) : ℝ :=
  LinearMap.det ((ContinuousLinearMap.id ℝ (Fin d → ℝ) - fderiv ℝ Φ p :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))

/-- **Regular interior fixed point** (arXiv:2609.23879, p. 13: "An interior fixed point
p ∈ (0, 1)^d is regular if det(I_d − DΦ(p)) ≠ 0"). -/
def IsRegularFixedPoint {d : ℕ} (Φ : (Fin d → ℝ) → (Fin d → ℝ)) (p : Fin d → ℝ) : Prop :=
  Φ p = p ∧ (∀ i, 0 < p i ∧ p i < 1) ∧ detIdSubD Φ p ≠ 0

/-- **Fixed point index** (arXiv:2609.23879, p. 14, eq. (5)):
`ind_Φ(p) := sign det(I_d − DΦ(p)) ∈ {−1, +1}` at a regular fixed point.

**Formalization Note** An integer; `sign 0 = 0` off regular points. -/
noncomputable def fixedPointIndex {d : ℕ} (Φ : (Fin d → ℝ) → (Fin d → ℝ)) (p : Fin d → ℝ) : ℤ :=
  ((SignType.sign (detIdSubD Φ p) : SignType) : ℤ)

end PosIndexNash.PPADS


