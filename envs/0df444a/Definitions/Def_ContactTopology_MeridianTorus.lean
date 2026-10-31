-- Prove2me | Definitions.Def_ContactTopology_MeridianTorus
-- name    : ContactTopology_MeridianTorus
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T02:50:35.138713+00:00
-- url     : https://prove2.me/theorems/36c0c975-c8f5-4b0b-90ad-c779f7f859b0
-- title:
--   Explicit deformed tori, complementary solid torus and meridian in the contact sphere
-- statement:
--   Write a point of real four-space as $(q,p)$, with both blocks in $\mathbb R^2$, and write $N$ for radial normalization. For plane vectors $U,V$, put $d=U\cdot V$, $c=\det(U,V)$, and let $J$ be the positive quarter-turn. The deformed torus parametrization is
--   $$S_{r,k}(U,V)=N\bigl(U,r(dU+kcJU)\bigr).$$
--   The torus map restricts both parameters to unit circles. The standard complementary solid-torus parametrization and its meridian slice are
--   $$B_r(u,V)=N(u/r,V),\qquad M_r(u)=B_r(u,(1,0)).$$
--   The solid map restricts $u$ to the closed unit disk and $V$ to the unit circle. Its intended region is the subset of the unit sphere satisfying $r^2|q|^2\le |p|^2$. For an ambient family $\Phi_t$, the moved product, solid torus and disk are the compositions with $\Phi_1$.
--
--   These are explicit formulas and parameter types. The accompanying theorem establishes smoothness, embeddings, tangent ranks, exact images, actual ambient deformation, Legendrian boundary and a transverse contact field. Those geometric assertions are not built into the definitions.
-- source:
--   Derived explicit sphere-model meridian construction supporting the meridian preparation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first geometric step of its proof. This is an explicit auxiliary construction, not a formalization of Proposition 3.3 or its subsequent convex perturbation and bypass argument. The formulas and complete proof are specified in the associated definition and solution.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Tactic.NormNum

namespace ContactTopology.MeridianTorus
open BirkhoffGlobalSection Set Function
open scoped ContDiff Topology
noncomputable section

def dot2 (u v : Plane) : ℝ := u 0*v 0+u 1*v 1
def cross2 (u v : Plane) : ℝ := u 0*v 1-u 1*v 0
def raw (r k : ℝ) (p : Plane × Plane) : Phase :=
  ![p.1 0,p.1 1,r*(p.1 0*dot2 p.1 p.2-k*(p.1 1*cross2 p.1 p.2)),
    r*(p.1 1*dot2 p.1 p.2+k*(p.1 0*cross2 p.1 p.2))]

def surface (r k : ℝ) : Plane × Plane → Phase := radialNormalize ∘ raw r k

abbrev UnitPlaneCircle := {u : Plane // u ∈ unitCircle}
def torusMap (r k : ℝ) (p : UnitPlaneCircle × UnitPlaneCircle) : Phase :=
  surface r k (p.1.val,p.2.val)

def solidRaw (r : ℝ) (p : Plane × Plane) : Phase := ![p.1 0/r,p.1 1/r,p.2 0,p.2 1]
def solid (r : ℝ) : Plane × Plane → Phase := radialNormalize ∘ solidRaw r

abbrev DiskPoint := {u : Plane // planeNormSq u ≤ 1}

def solidMap (r : ℝ) (p : DiskPoint × UnitPlaneCircle) : Phase := solid r (p.1.val,p.2.val)

def solidRegion (r : ℝ) : Set Phase := {y | y ∈ unitThreeSphere ∧ r^2*zNormSq y ≤ wNormSq y}

def pole : Plane := ![1,0]
lemma pole_unit : pole ∈ unitCircle := by norm_num [pole,unitCircle,planeNormSq]
def standardDisk (r : ℝ) (u : Plane) : Phase := solid r (u,pole)

def movedDisk (r : ℝ) (Φ : ℝ → Phase → Phase) : Plane → Phase := Φ 1 ∘ standardDisk r
def movedSolid (r : ℝ) (Φ : ℝ → Phase → Phase) : DiskPoint × UnitPlaneCircle → Phase := Φ 1 ∘ solidMap r
def movedProduct (r : ℝ) (Φ : ℝ → Phase → Phase) : Plane × Plane → Phase := Φ 1 ∘ solid r

end
end ContactTopology.MeridianTorus


