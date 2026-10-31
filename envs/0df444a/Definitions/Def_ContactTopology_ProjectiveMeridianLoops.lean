-- Prove2me | Definitions.Def_ContactTopology_ProjectiveMeridianLoops
-- name    : ContactTopology_ProjectiveMeridianLoops
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:54:27.505977+00:00
-- url     : https://prove2.me/theorems/0a87257b-1b98-45f2-ac40-231a2deb6af7
-- title:
--   Product-boundary meridians for the actual projective solid torus
-- statement:
--   For the complex closed disk $D^2$ and unit circle $S^1$, define the inclusion $v\mapsto v\in D^2$, the boundary-coordinate inclusion $S^1\times S^1\hookrightarrow D^2\times S^1$, and the continuous product meridians $\mu_z(v)=(v,z)$ with distinguished meridian $\mu_1$. These are explicit maps only. No homotopy, intersection count, geometric embedding or classification conclusion is included in the interface.
-- source:
--   Derived projective meridian minimality preparation for Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of the proof. Builds on the accepted actual projective solid-torus boundary/core/dividing-coordinate theorem and the accepted sphere-model meridian construction. This auxiliary theorem proves the sharp intersection bound for the explicit boundary-meridian homotopy class in the actual RP3 model. It does not assert classification of all essential disks, a quotient contact atlas, bypass existence, tightness, or the full Legendrian core classification.

import Definitions.Def_ContactTopology_ProjectiveSolidCoordinates
import Mathlib.Topology.Homotopy.Basic

namespace ContactTopology.ProjectiveMeridian
open ContactTopology.SolidTorusQuotient
noncomputable section
def unitDisk (v : Circle) : ClosedDisk := ⟨(v:ℂ),(Circle.norm_coe v).le⟩
def boundaryCoordinates (p : Circle × Circle) : DiskCircle := (unitDisk p.1,p.2)
def meridianAt (z : Circle) : C(Circle,Circle × Circle) where
  toFun v := (v,z)
  continuous_toFun := continuous_id.prodMk continuous_const
def meridian : C(Circle,Circle × Circle) := meridianAt 1

end
end ContactTopology.ProjectiveMeridian


