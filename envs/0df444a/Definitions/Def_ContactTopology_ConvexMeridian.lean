-- Prove2me | Definitions.Def_ContactTopology_ConvexMeridian
-- name    : ContactTopology_ConvexMeridian
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T03:20:52.430288+00:00
-- url     : https://prove2.me/theorems/25460e7d-3e5f-4f3c-b910-f2850a8626d9
-- title:
--   An explicit convex meridian, its two contact fields and contactomorphic images
-- statement:
--   For $r>0$, the explicit normalized polynomial disk and simultaneous rotation field are
--   $$D_r(u,v)=N\bigl(u,v,r(1-v^2/2),ruv/2\bigr),\qquad X(q,p)=(Jq,Jp).$$
--   Here $N$ is radial normalization and $J$ is the positive plane quarter-turn. The Euler field is
--   $$E(q,p)=(0,p)-|p|^2(q,p).$$
--   For an actual equivariant sphere contactomorphism $F$, define the image disk, torus and arc by composition with $F$, and define the pushed fields by
--   $$F_*X(y)=dF_{F^{-1}(y)}X(F^{-1}(y)),\qquad F_*E(y)=dF_{F^{-1}(y)}E(F^{-1}(y)).$$
--   The dividing-arc parameter is $t\mapsto F(D_r(t,0))$, with compact parameter interval $[-1,1]$. The torus formulas and standard complementary product region come from the imported meridian-torus interface.
--
--   These are explicit formulas and parameter types. Embeddings, proper placement in an actual solid torus, Legendrian boundary, transversality, contact identities and the exact single dividing arc are established by the accompanying theorem, not assumed in this interface.
-- source:
--   Derived explicit sphere-model convex meridian for the geometric preparation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of its proof. The explicit polynomial disk and arbitrary-contactomorphism transport are auxiliary constructions supplied here. This is not the generic relative convex-perturbation theorem, the bypass argument, or a formalization of Proposition 3.3. The contact-factor/exterior-pairing calculus reuses the earlier sphere-core framing proof.

import Definitions.Def_ContactTopology_MeridianTorus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ContactTopology.ConvexCore
open BirkhoffGlobalSection
noncomputable section
def vertical (y : Phase) : Phase := ![0,0,y 2,y 3]

def fiberEuler (y : Phase) : Phase := vertical y-wNormSq y • y

end
end ContactTopology.ConvexCore

namespace ContactTopology.ContactFieldTransport
open BirkhoffGlobalSection
noncomputable section
def pushedField (F : EquivariantSphereContactomorphism) (X : Phase → Phase) (y : Phase) : Phase :=
  fderiv ℝ F.toFun (F.invFun y) (X (F.invFun y))

end
end ContactTopology.ContactFieldTransport

namespace ContactTopology.ConvexMeridian
open BirkhoffGlobalSection ContactTopology.ConvexCore ContactTopology.ContactFieldTransport Set Function
open scoped ContDiff Topology
noncomputable section

def raw (r : ℝ) (u : Plane) : Phase := ![u 0,u 1,r*(1-u 1^2/2),r*u 0*u 1/2]

def disk (r : ℝ) : Plane → Phase := radialNormalize ∘ raw r

def rotation : Phase →L[ℝ] Phase := LinearMap.toContinuousLinearMap
  { toFun := fun y => ![-y 1,y 0,-y 3,y 2]
    map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
    map_smul' := by intro a y; ext i; fin_cases i <;> simp }

def dividingArc (r : ℝ) (t : ℝ) : Phase := disk r ![t,0]

def dividingArcMap (r : ℝ) (t : Icc (-1:ℝ) 1) : Phase := dividingArc r t.val

def imageDisk (F : EquivariantSphereContactomorphism) (r : ℝ) : Plane → Phase := F.toFun ∘ disk r
def imageField (F : EquivariantSphereContactomorphism) : Phase → Phase :=
  pushedField F (rotation : Phase → Phase)
def imageTorusMap (F : EquivariantSphereContactomorphism) (r : ℝ) :
    MeridianTorus.UnitPlaneCircle × MeridianTorus.UnitPlaneCircle → Phase := F.toFun ∘ MeridianTorus.torusMap r (1/2)
def imageSurface (F : EquivariantSphereContactomorphism) (r k : ℝ) : Plane × Plane → Phase :=
  F.toFun ∘ MeridianTorus.surface r k
def imageDividingArc (F : EquivariantSphereContactomorphism) (r : ℝ) : ℝ → Phase := F.toFun ∘ dividingArc r
def imageDividingArcMap (F : EquivariantSphereContactomorphism) (r : ℝ) (t : Icc (-1:ℝ) 1) : Phase :=
  imageDividingArc F r t.val

def imageEuler (F : EquivariantSphereContactomorphism) : Phase → Phase := pushedField F fiberEuler

end
end ContactTopology.ConvexMeridian


