-- Prove2me | Definitions.Def_BirkhoffGlobalSection_EllipticRationalDisk
-- name    : BirkhoffGlobalSection_EllipticRationalDisk
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-27T04:52:55.734327+00:00
-- url     : https://prove2.me/theorems/e965c936-af1e-46e3-98e1-951279100056
-- title:
--   A lifted rational disk with one positive elliptic characteristic singularity
-- statement:
--   Let $K\subset S^3$ and let $\alpha_y(v)=-\omega(y,v)/2$ be the standard radial contact form. A positive elliptic rational disk for $K$ is a smooth embedded immersed disk $f:\overline{D}\to S^3$ with boundary $K$. Its only antipodal identifications occur at opposite boundary parameters, and its boundary is positively transverse to $\ker\alpha$. Write $f^*\alpha=A\,dx+B\,dy$ and define the characteristic vector field by
--
--   $$W=(B,-A),\qquad \iota_W(dx\wedge dy)=f^*\alpha.$$
--
--   The characteristic field has exactly one zero in the open disk, at the origin, with
--
--   $$DW(0)=\kappa\,\operatorname{id},\qquad \kappa>0.$$
--
--   Thus the disk has one positive elliptic singularity in a specified local linear normal form. The antipodal quotient is a rational two-disk. This certificate contains no contactomorphism, isotopy, Reeb transversality of the interior, or return-time assumption.
--
--   **Formalization Note.** Smoothness is expressed through an ambient extension near the closed disk, and immersion means injectivity of the Frechet derivative. `diskCharacteristic` is defined from the explicit coordinate basis. The scalar linearization is a normal-form condition, stronger than merely calling a singularity elliptic.
-- source:
--   Hryniewicz–Licata–Salomão, A dynamical characterization of universally tight lens spaces, arXiv:1306.6617, https://arxiv.org/pdf/1306.6617, Section 6.1, Lemma 6.1 and Definition 6.3(a), pp. 36–37. In the displayed Darboux form lambda=dz+xdy, disk z=-xy/2, the pullback is (x dy-y dx)/2. Only the one-positive-elliptic condition is represented here, not Definition 6.3(b) robustness. Rational disk convention: same paper Section 3.1.

import Definitions.Def_BirkhoffGlobalSection_SphereContact

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- Coordinate basis vector in the disk parameter plane. -/
def planeCoordinateVector (i : Fin 2) : Plane :=
  fun j => if j = i then 1 else 0

/-- If the disk pulls the radial contact form back to `A dx + B dy`, this
field is `(B,-A)`, characterized by contraction with `dx ∧ dy`. -/
noncomputable def diskCharacteristic (f : Plane → Phase) (u : Plane) : Plane :=
  ![phaseRadialContact (f u) (fderiv ℝ f u (planeCoordinateVector 1)),
    -phaseRadialContact (f u) (fderiv ℝ f u (planeCoordinateVector 0))]

/-- A concrete lifted rational two-disk with one positive elliptic
characteristic singularity. Its quotient has embedded interior and a boundary
covering of degree two. There are no contactomorphism, isotopy, Reeb-return,
or global-section clauses in this certificate. -/
structure PositiveEllipticRationalDisk (K : Set Phase) where
  disk : Plane → Phase
  sphere : ∀ u ∈ closedUnitDisk, disk u ∈ unitThreeSphere
  smooth : ∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ disk u
  injective : Set.InjOn disk closedUnitDisk
  immersion : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ disk u)
  boundary : disk '' unitCircle = K
  antipodal_fibers : ∀ u ∈ closedUnitDisk, ∀ v ∈ closedUnitDisk,
    (disk u = -disk v ↔ u ∈ unitCircle ∧ v ∈ unitCircle ∧ v = -u)
  positive_boundary : ∀ u ∈ unitCircle,
    0 < phaseRadialContact (disk u) (fderiv ℝ disk u (circleTangent u))
  characteristic_zero : ∀ u ∈ openUnitDisk,
    diskCharacteristic disk u = 0 ↔ u = 0
  elliptic : ∃ κ : ℝ, 0 < κ ∧ ∀ v : Plane,
    fderiv ℝ (diskCharacteristic disk) 0 v = κ • v

end BirkhoffGlobalSection


