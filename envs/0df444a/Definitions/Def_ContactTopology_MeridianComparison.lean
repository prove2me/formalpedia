-- Prove2me | Definitions.Def_ContactTopology_MeridianComparison
-- name    : ContactTopology_MeridianComparison
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:00:10.489191+00:00
-- url     : https://prove2.me/theorems/92c86ed8-3039-43fd-8c14-cbfbdf461f90
-- title:
--   Rotation of the explicit convex meridian and the two actual comparison core curves
-- statement:
--   Define simultaneous rotation $R_s(q,p)=(e^{sJ}q,e^{sJ}p)$, the explicit family $D_{F,r,s}=F\circ R_s\circ D_r$, its diameter $t\mapsto D_{F,r,s}(t,0)$ and the restriction of that diameter to $[-1,1]$. The two actual core curves are
--   $$C_F(t)=F(0,0,\cos t,\sin t),\qquad \gamma_G(t)=G(\cos(2\pi t),\sin(2\pi t),0,0).$$
--   Here $D_r$ is the imported normalized polynomial disk. This interface contains only these formulas, the interval parameter type and the elementary linear-map constructor proof. The existence of an arbitrarily small rotation with convexity, same-solid-torus placement, unique reference-core intersection and finite transverse comparison intersections is proved in the accompanying theorem.
-- source:
--   Derived explicit sphere-model comparison geometry for the first paragraph of the proof of Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3. This auxiliary construction uses the previously proved explicit convex meridian and its actual transverse rotation field. It proves a small rotation transverse to the other actual core, same-solid-torus placement, exact single dividing arc, unique transverse intersection with the reference core, and finite intersections with the other core. It does not assert Proposition 3.3, generic convex perturbation of arbitrary disks, projective differential descent, dividing-slope minimality, bypass existence, tightness, or core classification. The regular-value input reuses Mathlib.MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero.

import Definitions.Def_ContactTopology_ConvexMeridian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ContactTopology.ConvexMeridian
open BirkhoffGlobalSection Set Function
noncomputable section

def spin (t : ℝ) : Phase →L[ℝ] Phase := LinearMap.toContinuousLinearMap
  { toFun := fun y => ![Real.cos t*y 0-Real.sin t*y 1,Real.sin t*y 0+Real.cos t*y 1,
      Real.cos t*y 2-Real.sin t*y 3,Real.sin t*y 2+Real.cos t*y 3]
    map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
    map_smul' := by intro a y; ext i; fin_cases i <;> simp <;> ring }
def spunDisk (F : EquivariantSphereContactomorphism) (r : ℝ) (p : ℝ × Plane) : Phase :=
  F.toFun (spin p.1 (disk r p.2))
def spunDividingArc (F : EquivariantSphereContactomorphism) (r s t : ℝ) : Phase := spunDisk F r (s,![t,0])
def spunDividingArcMap (F : EquivariantSphereContactomorphism) (r s : ℝ) (t : Icc (-1:ℝ) 1) : Phase :=
  spunDividingArc F r s t.val
def referenceCore (F : EquivariantSphereContactomorphism) (t : ℝ) : Phase :=
  F.toFun ![0,0,Real.cos t,Real.sin t]
def comparisonCore (G : EquivariantSphereContactomorphism) (t : ℝ) : Phase :=
  G.toFun ![Real.cos (2*Real.pi*t),Real.sin (2*Real.pi*t),0,0]

end
end ContactTopology.ConvexMeridian


