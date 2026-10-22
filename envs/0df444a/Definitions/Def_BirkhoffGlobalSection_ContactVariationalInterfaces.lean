-- Prove2me | Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
-- name    : BirkhoffGlobalSection_ContactVariationalInterfaces
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-02T12:06:20.01637+00:00
-- url     : https://prove2.me/theorems/b58647b4-ded0-4fee-b2b5-125f49ca53ee
-- title:
--   Concrete Reeb extensions and normalized contact variational interfaces
-- statement:
--   Ten lightweight definitions for the contact-variational interface of a convex regularization model: the raw weighted Reeb formula and its radial extension, the concrete model sphere Reeb field, characteristic projection, Hamiltonian and sphere contact pairs, their gradient radius and square-root normalization, normalized coefficient coordinates, and the coefficient action of a supplied linear-map path.
--
--   The sphere weight is $f=\operatorname{gauge}_M^{-2}$; the normalized basis is $s_i=e_i/\sqrt n$; and the coefficient action is
--   $$A(t)p=C_{q(t)}\big(Z(t)(p_0s_0(q(0))+p_1s_1(q(0)))\big).$$
--   These are definitions only. Positivity, tangency, basis properties, preservation and regularity are proved in separate theorem bundles. Inverses in these ambient definitions are total real inverses; validity statements impose the required positivity and sphere hypotheses.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem.

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.SpecialFunctions.Sqrt
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology

noncomputable def weightedReebField (f : Phase → ℝ) (x : Phase) : Phase :=
  let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
  let g : Phase := fun i => fderiv ℝ f x (coordinateVector i)
  ((f x)^2)⁻¹ • ((2 * f x + fderiv ℝ f x x) • J x - J g -
    (fderiv ℝ f x (J x)) • x)

noncomputable def sphereReebExtension (f : Phase → ℝ) (x : Phase) : Phase :=
  weightedReebField f (radialNormalize x)

noncomputable def convexModelSphereReebField {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) : Phase → Phase :=
  sphereReebExtension (fun x => ((gauge M.body x)⁻¹)^2)

noncomputable def characteristicContactProjection (F : Phase → ℝ) (y v : Phase) : Phase :=
  v - (phaseRadialContact y v) •
    ((phaseRadialContact y (hamiltonianVectorField F y))⁻¹ • hamiltonianVectorField F y)

noncomputable def hamiltonianContactFrame (F : Phase → ℝ) (y : Phase) : Fin 2 → Phase :=
  ![characteristicContactProjection F y (TangentialHessian.frame (TangentialHessian.grad F y) 1),
    characteristicContactProjection F y (TangentialHessian.frame (TangentialHessian.grad F y) 2)]

noncomputable def convexModelSphereContactFrame {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (i : Fin 2) : Phase :=
  let y := (gauge M.body u)⁻¹ • u
  fderiv ℝ radialNormalize y (hamiltonianContactFrame M.modelHamiltonian y i)

noncomputable def convexModelFrameRadius {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (u : Phase) : ℝ :=
  let g := TangentialHessian.grad M.modelHamiltonian ((gauge M.body u)⁻¹ • u)
  zNormSq g + wNormSq g

noncomputable def convexModelSymplecticContactFrame {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (u : Phase) (i : Fin 2) : Phase :=
  (Real.sqrt (convexModelFrameRadius M u))⁻¹ • convexModelSphereContactFrame M u i

noncomputable def convexModelContactCoordinates {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) : Plane :=
  let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
  (Real.sqrt (convexModelFrameRadius M u))⁻¹ •
    transverseFrameCoordinates (TangentialHessian.grad M.modelHamiltonian (G u)) (fderiv ℝ G u v)

noncomputable def convexModelContactVariationPath {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) (p : Plane) : Plane :=
  convexModelContactCoordinates M (q t)
    (Z t (p 0 • convexModelSymplecticContactFrame M (q 0) 0 +
      p 1 • convexModelSymplecticContactFrame M (q 0) 1))


