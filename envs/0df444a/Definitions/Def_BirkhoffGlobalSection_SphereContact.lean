-- Prove2me | Definitions.Def_BirkhoffGlobalSection_SphereContact
-- name    : BirkhoffGlobalSection_SphereContact
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-27T04:35:45.954419+00:00
-- url     : https://prove2.me/theorems/b4850348-3308-44f9-98a6-bd847ac09e4e
-- title:
--   Equivariant contactomorphisms and contact isotopies of the standard sphere
-- statement:
--   Write $S^3\subset\mathbb R^4$ for the Euclidean unit sphere and $\alpha_y(v)=-\omega(y,v)/2$ for its standard radial contact form. An equivariant sphere contactomorphism is a smooth diffeomorphism $F:S^3\to S^3$ satisfying $F(-y)=-F(y)$ and
--
--   $$F^*\alpha=a\alpha,\qquad a(y)>0.$$
--
--   The equality is imposed on tangent vectors to the sphere. An equivariant sphere contact isotopy to $F$ is a jointly smooth family of such maps on the closed time interval, starting at the identity and ending at $F$. There is no distinguished knot, orbit, or spanning surface in these definitions.
--
--   **Formalization Note.** Maps and inverse maps are represented by ambient functions smooth at every sphere point. Joint smoothness is required at points of $[0,1]\times S^3$, and endpoint equalities only on the sphere. The pairing `phaseDot` is Euclidean, independently of the norm instance on the coordinate function space.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/pdf/2207.03590, Section 1.1, p. 2 (coorientation-preserving contactomorphisms and contact isotopy). Standard lift from RP^3=L(2,1) to its antipodal sphere cover.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- Coordinate Euclidean pairing, independent of the sup norm on `Phase`. -/
def phaseDot (y v : Phase) : ℝ :=
  y 0 * v 0 + y 1 * v 1 + y 2 * v 2 + y 3 * v 3

/-- A coorientation-preserving contact diffeomorphism of the standard sphere
which commutes with the antipodal involution. Ambient extensions are required
to be smooth only at sphere points. The contact identity concerns tangent
vectors to the sphere, not arbitrary ambient vectors. -/
structure EquivariantSphereContactomorphism where
  toFun : Phase → Phase
  invFun : Phase → Phase
  smooth : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ toFun y
  inv_smooth : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ invFun y
  maps_sphere : Set.MapsTo toFun unitThreeSphere unitThreeSphere
  inv_maps_sphere : Set.MapsTo invFun unitThreeSphere unitThreeSphere
  left_inv : ∀ y ∈ unitThreeSphere, invFun (toFun y) = y
  right_inv : ∀ y ∈ unitThreeSphere, toFun (invFun y) = y
  antipodal : ∀ y ∈ unitThreeSphere, toFun (-y) = -toFun y
  contact : ∀ y ∈ unitThreeSphere, ∃ a : ℝ, 0 < a ∧
    ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (toFun y) (fderiv ℝ toFun y v) =
        a * phaseRadialContact y v

/-- A smooth equivariant contact isotopy from the identity to `F`. Its slices
outside the unit time interval are irrelevant; endpoint equalities are imposed
only on the sphere. No distinguished knot is part of this structure. -/
structure EquivariantSphereContactIsotopy
    (F : EquivariantSphereContactomorphism) where
  slice : ℝ → EquivariantSphereContactomorphism
  smooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
    ContDiffAt ℝ ∞ (fun p : ℝ × Phase => (slice p.1).toFun p.2) (t, y)
  start : ∀ y ∈ unitThreeSphere, (slice 0).toFun y = y
  finish : ∀ y ∈ unitThreeSphere, (slice 1).toFun y = F.toFun y

end BirkhoffGlobalSection


