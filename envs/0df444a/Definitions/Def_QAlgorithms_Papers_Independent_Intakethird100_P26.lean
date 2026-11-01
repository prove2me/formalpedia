-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P26
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P26
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:02:17.232685+00:00
-- url     : https://prove2.me/theorems/066f173e-a281-4af5-828a-e174f2175347
-- title:
--   Definitions for Proof of the Holographic Formula for Entanglement Entropy
-- statement:
--   The objects the formalized statements of *Proof of the Holographic Formula for Entanglement Entropy* (arXiv:hep-th/0606184) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `btzSliceEnergy`: PDF pp.8–9, (2.13): kinetic energy of the actual constant-tau BTZ slice, in lifted coordinates q=(rho,phi). The metric is `d rho^2 + rplus^2 * cosh(rho/l)^2 * d phi^2`. The angular coordinate is projected modulo `2*pi` at the endpoints.
--   - `IsBTZSliceGeodesic`: PDF pp.8–9, (2.13): affine geodesics of the BTZ slice, defined by the Euler–Lagrange equation of its kinetic energy, rather than by an assumed turning property. Only interior derivatives are used; the curve is C^2 up to the endpoints.
--   - `extrinsicQuadratic`: PDF p.13, the combination following (4.5): sum over both orthonormal normal directions of squared mean curvature minus twice squared second fundamental form. `sigma` and `k i` are the covariant 2-by-2 component matrices in any tangent coordinate basis; `sigma` is required positive definite by the theorem. Matrix inverse raises one tangent index.
--   - `extrinsicDensity`: PDF pp.12–13: the coordinate area density multiplying the conformal extrinsic invariant. The square root is of the determinant of the induced positive definite metric, not of an arbitrary signed tensor.
--   - `weylSurfaceMetric`: PDF p.12: the induced metric under `h -> exp(-2*omega) h`.
--   - `weylSecondForms`: PDF p.13, displayed second fundamental form transformation: `v i` is the old unit-normal derivative `n_i(omega)`. Both normal covariant forms transform, with the source's plus sign.
-- source:
--   Proof of the Holographic Formula for Entanglement Entropy, arXiv:hep-th/0606184v2, https://arxiv.org/abs/hep-th/0606184v2

import Mathlib

/-!
Fursaev, arXiv:hep-th/0606184v2. This module states the BTZ turning result
and the algebraic conformal density identity. Physical entropy identifications
and the unconstructed global geometric interfaces are deferred in the unit.
Complementary pure-state entropy equality is reused through metadata only.
-/

noncomputable section

open Set

namespace QAlgorithms.Papers.Independent.Intakethird100.P26

/-- PDF pp.8–9, (2.13): kinetic energy of the actual constant-tau BTZ slice,
in lifted coordinates q=(rho,phi). The metric is
`d rho^2 + rplus^2 * cosh(rho/l)^2 * d phi^2`.
The angular coordinate is projected modulo `2*pi` at the endpoints. -/
def btzSliceEnergy (l rplus : ℝ) (q v : Fin 2 → ℝ) : ℝ :=
  (v 0 ^ 2 + rplus ^ 2 * Real.cosh (q 0 / l) ^ 2 * v 1 ^ 2) / 2

/-- PDF pp.8–9, (2.13): affine geodesics of the BTZ slice, defined by the
Euler–Lagrange equation of its kinetic energy, rather than by an assumed
turning property. Only interior derivatives are used; the curve is C^2 up
to the endpoints. -/
def IsBTZSliceGeodesic (l rplus a b : ℝ) (x : ℝ → (Fin 2 → ℝ)) : Prop :=
  ContDiffOn ℝ 2 x (Icc a b) ∧
    ∀ t ∈ Ioo a b, ∀ j : Fin 2,
      deriv (fun s =>
        (fderiv ℝ (fun v => btzSliceEnergy l rplus (x s) v) (deriv x s))
          (Pi.single j 1)) t =
      (fderiv ℝ (fun q => btzSliceEnergy l rplus q (deriv x t)) (x t))
        (Pi.single j 1)

example (l rplus : ℝ) (q : Fin 2 → ℝ) :
    btzSliceEnergy l rplus q 0 = 0 := by
  simp [btzSliceEnergy]

example (l rplus : ℝ) (v : Fin 2 → ℝ) :
    btzSliceEnergy l rplus 0 v = (v 0 ^ 2 + rplus ^ 2 * v 1 ^ 2) / 2 := by
  simp [btzSliceEnergy]

/-- PDF p.13, the combination following (4.5): sum over both orthonormal
normal directions of squared mean curvature minus twice squared second
fundamental form. `sigma` and `k i` are the covariant 2-by-2 component
matrices in any tangent coordinate basis; `sigma` is required positive
definite by the theorem. Matrix inverse raises one tangent index. -/
def extrinsicQuadratic (sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (k : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ∑ i : Fin 2,
    ((Matrix.trace (sigma⁻¹ * k i)) ^ 2 -
      2 * Matrix.trace ((sigma⁻¹ * k i) * (sigma⁻¹ * k i)))

/-- PDF pp.12–13: the coordinate area density multiplying the conformal
extrinsic invariant. The square root is of the determinant of the induced
positive definite metric, not of an arbitrary signed tensor. -/
def extrinsicDensity (sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (k : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt sigma.det * extrinsicQuadratic sigma k

/-- PDF p.12: the induced metric under `h -> exp(-2*omega) h`. -/
def weylSurfaceMetric (omega : ℝ)
    (sigma : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.exp (-2 * omega) • sigma

/-- PDF p.13, displayed second fundamental form transformation:
`v i` is the old unit-normal derivative `n_i(omega)`. Both normal
covariant forms transform, with the source's plus sign. -/
def weylSecondForms (omega : ℝ) (v : Fin 2 → ℝ)
    (sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (k : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun i => Real.exp (-omega) • (k i + v i • sigma)

example (sigma : Matrix (Fin 2) (Fin 2) ℝ) :
    extrinsicDensity sigma (fun _ => 0) = 0 := by
  simp [extrinsicDensity, extrinsicQuadratic]

example (v : Fin 2 → ℝ) (sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (k : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    weylSecondForms 0 v sigma k = fun i => k i + v i • sigma := by
  funext i
  change Real.exp (-(0 : ℝ)) • (k i + v i • sigma) = k i + v i • sigma
  rw [neg_zero, Real.exp_zero, one_smul]

end QAlgorithms.Papers.Independent.Intakethird100.P26


