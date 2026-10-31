-- Prove2me | Definitions.Def_ContactTopology_ProjectiveSolidCoordinates
-- name    : ContactTopology_ProjectiveSolidCoordinates
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:41:18.146238+00:00
-- url     : https://prove2.me/theorems/db052dde-3089-46ee-928a-7457fc0fac29
-- title:
--   Explicit projective solid-torus, boundary, core and Euler zero-set formulas
-- statement:
--   Use the complex closed disk $D^2=\{u\in\mathbb C:|u|\le1\}$ and the unit circle $S^1$. The explicit invariant parameter map and sphere model are
--   $$U(u,v)=(u/v,v^2),\qquad K(u,v)=F\!\left(\Phi_1\!\left(N(\Re u/r,\Im u/r,\Re v,\Im v)\right)\right).$$
--   The interface defines the conversion to the existing real-plane solid-torus parameters, this model map and its sphere projection. It also defines the actual projected boundary set, projected reference core, and the projection of the sphere zero set of $\lambda(F_*E)$, where $E(q,p)=(0,p)-|p|^2(q,p)$.
--
--   These are formulas and parameter types, with only elementary subtype-membership proofs. An accompanying theorem constructs the actual quotient product homeomorphism, its boundary/core compatibility and the two dividing longitudes; those geometric conclusions are not inputs to this interface.
-- source:
--   Derived explicit projective solid-torus and dividing-coordinate preparation for Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of its proof, and the solid-torus input to Proposition 3.5. The actual sphere solid torus, its ambient inverse families and transverse fields are from the previously proved explicit meridian construction. The diagonal-antipodal untwist (u,v) -> (u/v,v^2), the concrete quotient homeomorphism, boundary/core compatibility and the continuous descended Euler pairing are auxiliary constructions supplied here. This is a topological product theorem with actual dividing-locus data, not a contactomorphism/diffeomorphism, quotient contact tangent-bundle theorem, bypass or tightness theorem, Proposition 3.3 itself, or the Legendrian core classification.

import Definitions.Def_ContactTopology_ConvexMeridian
import Definitions.Def_ContactTopology_AntipodalSphereQuotients
import Definitions.Def_ContactTopology_MeridianBoundaryLoops
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith

namespace ContactTopology.SolidTorusQuotient
open BirkhoffGlobalSection ContactTopology.Projective ContactTopology.ConvexMeridian ContactTopology.TorusMeridian Set Function Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev ClosedDisk := {z : ℂ // ‖z‖ ≤ 1}
abbrev DiskCircle := ClosedDisk × Circle

def untwist (p : DiskCircle) : DiskCircle :=
  (⟨p.1.val/(p.2:ℂ),by simpa only [norm_div,Circle.norm_coe,div_one] using p.1.property⟩,p.2^2)

def diskPlane (u : ClosedDisk) : MeridianTorus.DiskPoint := ⟨![(u:ℂ).re,(u:ℂ).im],by
  have hn : ‖(u:ℂ)‖ ≤ 1 := u.property
  have hs := Complex.sq_norm (u:ℂ)
  change (u:ℂ).re^2+(u:ℂ).im^2 ≤ 1
  rw [Complex.normSq_apply] at hs
  nlinarith [norm_nonneg (u:ℂ)]⟩

def parameterMap (p : DiskCircle) : MeridianTorus.DiskPoint × MeridianTorus.UnitPlaneCircle :=
  (diskPlane p.1,planeUnit p.2)

def modelSolid (r : ℝ) (p : DiskCircle) : Phase := MeridianTorus.solidMap r (parameterMap p)

def actualSolid (F : EquivariantSphereContactomorphism) (r : ℝ) (Φ : ℝ → Phase → Phase) (p : DiskCircle) : Phase :=
  F.toFun (Φ 1 (modelSolid r p))


def modelCore (v : Circle) : Phase := ![0,0,(v:ℂ).re,(v:ℂ).im]

def sphereModel (K : DiskCircle → Phase) (hS : ∀ p, K p ∈ unitThreeSphere) (p : DiskCircle) : RoundSphere 4 :=
  ⟨K p,by
    simpa [sphereSet,Fin.sum_univ_four,unitThreeSphere,zNormSq,wNormSq,add_assoc] using hS p⟩
def projectedModel (K : DiskCircle → Phase) (hS : ∀ p, K p ∈ unitThreeSphere) : DiskCircle → ProjectiveSphere 4 :=
  project 4 ∘ sphereModel K hS

def projectedBoundarySet (F : EquivariantSphereContactomorphism) (r : ℝ) : Set (ProjectiveSphere 4) :=
  project 4 '' {y : RoundSphere 4 | y.val ∈ range (imageTorusMap F r)}
def projectedCoreSet (F : EquivariantSphereContactomorphism) : Set (ProjectiveSphere 4) :=
  project 4 '' {y : RoundSphere 4 | y.val ∈ range (fun v : Circle => F.toFun (modelCore v))}
def projectedEulerZero (F : EquivariantSphereContactomorphism) : Set (ProjectiveSphere 4) :=
  project 4 '' {y : RoundSphere 4 | phaseRadialContact y.val (imageEuler F y.val)=0}


end
end ContactTopology.SolidTorusQuotient


