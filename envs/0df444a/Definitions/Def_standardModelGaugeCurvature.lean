-- Prove2me | Definitions.Def_standardModelGaugeCurvature
-- name    : standardModelGaugeCurvature
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T03:43:32.769171+00:00
-- url     : https://prove2.me/theorems/88fb1722-a7ea-4a5b-b242-c63b3cf5347e
-- title:
--   Non-Abelian Curvature and Constant-Gauge Kinetic Data
-- statement:
--   For each natural number $n$, let $A_\mu$ be a four-component connection with values in the complex $n\times n$ matrices, and let $dA_{\mu\nu}$ be its derivative data. The curvature is defined by
--
--   $$
--   F_{\mu\nu}=dA_{\mu\nu}-dA_{\nu\mu}+c(A_\mu A_\nu-A_\nu A_\mu),
--   $$
--
--   where $c$ is a complex coupling and matrix products are used. The interface also defines constant conjugation of the connection and derivative data, together with the finite weighted trace density built from these curvature matrices. These are algebraic definitions; they do not model spacetime dependence or local gauge transformations.
-- source:
--   J. A. Shifflett, “Standard Model Lagrangian (including neutrino mass terms),” equations (6) and (28)–(30), updated 2 February 2015; https://perma.cc/QDL7-VQZZ; original PDF https://einstein-schrodinger.com/Standard_Model.pdf.

import Mathlib

/-- Matrix-valued curvature for a gauge connection, in the convention
`F_{μν} = ∂_μ A_ν - ∂_ν A_μ + c [A_μ, A_ν]`.
The coefficient `coupling` packages the source's `i g` normalization. -/
def standardModelGaugeCurvature (n : ℕ)
    (A : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (coupling : ℂ) (μ ν : Fin 4) : Matrix (Fin n) (Fin n) ℂ :=
  dA μ ν - dA ν μ + coupling • (A μ * A ν - A ν * A μ)

/-- The action of a spacetime-constant gauge transformation on a connection.
`V` represents the inverse of `U` when the hypotheses of the covariance theorem hold. -/
def standardModelConstantGaugeTransform (n : ℕ)
    (U V : Matrix (Fin n) (Fin n) ℂ)
    (A : Fin 4 → Matrix (Fin n) (Fin n) ℂ) : Fin 4 → Matrix (Fin n) (Fin n) ℂ :=
  fun μ => U * A μ * V

/-- Under a constant gauge transformation, connection derivative data transforms
by the same conjugation. This excludes the derivative-of-gauge term present for
local transformations. -/
def standardModelConstantGaugeTransformDerivative (n : ℕ)
    (U V : Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) ℂ) :
    Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) ℂ :=
  fun μ ν => U * dA μ ν * V

/-- A weighted sum of the Yang–Mills kinetic densities. The weight can encode
index raising, Lorentz-signature signs, and the overall normalization. -/
def standardModelGaugeKineticDensity (n : ℕ)
    (A : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) ℂ)
    (coupling : ℂ) (weight : Fin 4 → Fin 4 → ℂ) : ℂ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    weight μ ν * Matrix.trace
      (standardModelGaugeCurvature n A dA coupling μ ν *
        standardModelGaugeCurvature n A dA coupling μ ν)


