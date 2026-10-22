-- Prove2me | Definitions.Def_BirkhoffGlobalSection_SphereDiffeoIsotopy
-- name    : BirkhoffGlobalSection_SphereDiffeoIsotopy
-- status  : Definition
-- author  : @caleb
-- created : 2026-10-02T21:31:33.826613+00:00
-- url     : https://prove2.me/theorems/ea95f9dc-f215-4380-a1dd-cbaa62f30cdc
-- title:
--   Equivariant sphere diffeomorphisms and diffeomorphism isotopies
-- statement:
--   An antipodally symmetric diffeomorphism of the round three-sphere $S^3 \subset \mathbb{R}^4$ is a pair of mutually inverse maps, smooth with smooth inverse at every sphere point, preserving the sphere and commuting with the antipodal involution:
--
--   $$F(-y) = -F(y), \qquad F^{-1}(F(y)) = y \qquad (y \in S^3).$$
--
--   No contact condition is imposed. A diffeomorphism isotopy from the identity to an equivariant contactomorphism $F$ is a one-parameter family of such diffeomorphisms, jointly smooth in $(t, y)$ in both directions on $[0,1] \times S^3$, starting at the identity and ending at $F$ on the sphere.
--
--   This packages the smooth (non-contact) isotopy data produced by the Smale picture: unlike a bare family of sphere maps, every slice is a genuine diffeomorphism with smoothly varying inverse, which is exactly what Gray stability needs as input. It is the companion to the contactomorphism/isotopy structures, with the contact condition removed.
--
--   **Formalization Note** Smoothness is required only at sphere points, and endpoint equalities only on the sphere, matching the contact-side conventions.
-- source:
--   Companion to BirkhoffGlobalSection_SphereContact (equivariant contactomorphisms and contact isotopies of the standard sphere), with the contact condition removed; the diffeomorphism-isotopy half is produced by the Smale picture, Hatcher, Ann. of Math. 117 (1983).

import Definitions.Def_BirkhoffGlobalSection_SphereContact

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- An antipodally symmetric diffeomorphism of the round three-sphere:
smooth with smooth inverse on the sphere, with no contact condition.
Ambient extensions are required to be smooth only at sphere points. -/
structure EquivariantSphereDiffeomorphism where
  toFun : Phase → Phase
  invFun : Phase → Phase
  smooth : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ toFun y
  inv_smooth : ∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ invFun y
  maps_sphere : Set.MapsTo toFun unitThreeSphere unitThreeSphere
  inv_maps_sphere : Set.MapsTo invFun unitThreeSphere unitThreeSphere
  left_inv : ∀ y ∈ unitThreeSphere, invFun (toFun y) = y
  right_inv : ∀ y ∈ unitThreeSphere, toFun (invFun y) = y
  antipodal : ∀ y ∈ unitThreeSphere, toFun (-y) = -toFun y

/-- A smooth equivariant diffeomorphism isotopy from the identity to `F`.
Both directions are jointly smooth in `(t, y)` on the unit time slab;
endpoint equalities are imposed only on the sphere. This records a smooth
isotopy through genuine diffeomorphisms, as produced by the Smale picture,
rather than through mere sphere maps. -/
structure EquivariantSphereDiffeoIsotopy
    (F : EquivariantSphereContactomorphism) where
  slice : ℝ → EquivariantSphereDiffeomorphism
  smooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
    ContDiffAt ℝ ∞ (fun p : ℝ × Phase => (slice p.1).toFun p.2) (t, y)
  inv_smooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
    ContDiffAt ℝ ∞ (fun p : ℝ × Phase => (slice p.1).invFun p.2) (t, y)
  start : ∀ y ∈ unitThreeSphere, (slice 0).toFun y = y
  finish : ∀ y ∈ unitThreeSphere, (slice 1).toFun y = F.toFun y

end BirkhoffGlobalSection


