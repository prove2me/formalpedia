-- Prove2me | Definitions.Def_BirkhoffGlobalSection_AmbientRotation
-- name    : BirkhoffGlobalSection_AmbientRotation
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-28T03:00:30.656373+00:00
-- url     : https://prove2.me/theorems/46c9bb9b-4d03-4206-9e4c-47afb72c9e59
-- title:
--   Ambient determinant rotation of Hamiltonian variational flows
-- statement:
--   Identify phase space with $\mathbb C^2$ using $z=q-ip$. For a real linear map with two-by-two blocks $A,B,C,D$, define its complex-linear part and ambient determinant by
--
--   $$
--   P(M)=\tfrac12(A+D+i(B-C)),\qquad d(M)=\det_{\mathbb C}P(M).
--   $$
--
--   A continuous real function $\alpha$ is an ambient rotation angle along a matrix path $Y$ when, for every real time, there is a positive radius with
--
--   $$
--   d(Y(t))=\rho(t)(\cos\alpha(t)+i\sin\alpha(t)),\qquad \rho(t)>0.
--   $$
--
--   The module also names the identity-normalized Hamiltonian variational equation along a trajectory. These definitions provide a concrete interface between local variational growth, global rotation estimates, and transverse winding. The determinant is defined for every real linear map; nonvanishing on symplectic maps and existence of angle lifts are separate theorem obligations.
--
--   **Formalization Note** The sign convention makes the Hamiltonian complex structure act as multiplication by $i$. The determinant is left unnormalized because a positive polar radius removes the normalization without changing the angle.
-- source:
--   Jean Gutt, Generalized Conley–Zehnder index, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3), normalized determinant of the complex-linear part. Coordinates use z=q-ip to match the Hamiltonian complex structure in Joung–van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3. The variational equation is the one in Liu–Salomão, https://arxiv.org/html/2506.17867v2#S7, Section 7.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Mathlib.Data.Complex.Basic

namespace BirkhoffGlobalSection

noncomputable section

/-- The complex-linear part of a real linear map in the convention
`(q,p) ↦ q - i p`. For real blocks `A,B,C,D`, this is
`(A + D + i (B - C)) / 2`. The Hamiltonian complex structure `qI`
acts as multiplication by `i` in this convention. -/
def ambientComplexLinearPart (M : Phase →L[ℝ] Phase) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  Complex.mk
    ((M (coordinateVector (j.castAdd 2)) (i.castAdd 2) +
      M (coordinateVector (j.natAdd 2)) (i.natAdd 2)) / 2)
    ((M (coordinateVector (j.natAdd 2)) (i.castAdd 2) -
      M (coordinateVector (j.castAdd 2)) (i.natAdd 2)) / 2)

/-- The unnormalized determinant whose phase is the complex-linear-part
rotation map on the symplectic group. It is nonzero for symplectic maps;
nonvanishing is a theorem, not an assumption in this definition. -/
def ambientRotationDet (M : Phase →L[ℝ] Phase) : ℂ :=
  (ambientComplexLinearPart M).det

/-- A continuous real lift of the argument of the ambient determinant.
The positive radius avoids any convention for the argument at zero. -/
def IsAmbientRotationAngle (Y : ℝ → (Phase →L[ℝ] Phase))
    (α : ℝ → ℝ) : Prop :=
  Continuous α ∧ ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
    ambientRotationDet (Y t) =
      Complex.mk (ρ * Real.cos (α t)) (ρ * Real.sin (α t))

/-- The identity-normalized fundamental solution of the Hamiltonian
variational equation along `x`. -/
def IsHamiltonianVariationalSolution (F : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) : Prop :=
  Y 0 = ContinuousLinearMap.id ℝ Phase ∧
    ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x t)).comp (Y t)) t

end

end BirkhoffGlobalSection


