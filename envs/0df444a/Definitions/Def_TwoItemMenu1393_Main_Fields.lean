-- Prove2me | Definitions.Def_TwoItemMenu1393_Main_Fields
-- name    : TwoItemMenu1393_Main_Fields
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:14.221197+00:00
-- url     : https://prove2.me/theorems/202530ce-b5f7-41bd-b654-b2062dbc279d
-- title:
--   Allocation interpolation, defects and weak derivatives
-- statement:
--   Sample the selected allocation at the upper-left vertex of every full cell, place it at the center, and interpolate on elementary equilateral triangles of full centers. The derivative $D\Gamma_h$ is the actual affine interpolation matrix on triangle interiors; it is assigned zero on boundaries and outside its domain. Define
--   $$\mathcal T(J)=(J_{12},J_{21},J_{11}-J_{22}).$$
--   All matrix norms are Euclidean operator norms. A rhombus has $(m+1)^2$ centers with $m\ge1$, spacing $\sqrt3h$, and directions $(1,0)$ and $(1/2,\sqrt3/2)$. Its total defect sums the six-vertex supporting-plane gaps. Separately, $W^{1,2}$ is represented by square-integrable fields and Jacobians satisfying integration by parts against every compactly supported smooth scalar test function. The field itself need not be smooth. This makes the weak estimate a statement about actual weak derivatives and provides reusable analytical interfaces.
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), §4.2, p. 12; D.3–D.4, pp. 28–33, equations (22)–(27). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf

import Definitions.Def_TwoItemMenu1393_Main_Distribution
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-! Chan–Guo–Thach, submission #1393 (October 2026), §4.2 p. 12,
Appendix D.3–D.4 pp. 28–33, equations (22)–(27). -/
abbrev Mat := Vec →L[ℝ] Vec
def basisVector (j : Fin 2) : Vec := WithLp.toLp 2 (Pi.single j 1)
def scalarDeviation (J : Mat) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(J (basisVector 1)) 0, (J (basisVector 0)) 1,
    (J (basisVector 0)) 0 - (J (basisVector 1)) 1]

abbrev Triangle := Fin 3 → Vec
def triangleRegion (T : Triangle) : Set Vec := convexHull ℝ (Set.range T)
def equilateral (T : Triangle) (ℓ : ℝ) : Prop :=
  0 < ℓ ∧ ∀ i j : Fin 3, i ≠ j → dist (T i) (T j) = ℓ

/-- The actual affine interpolation derivative. Nondegenerate triangles are required
where this is used. The determinant is not a differentiability test. -/
def interpolationJ (T G : Triangle) : Mat :=
  let x := T 1 - T 0
  let y := T 2 - T 0
  let s := G 1 - G 0
  let t := G 2 - G 0
  let D := x 0 * y 1 - x 1 * y 0
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if j = 0 then (y 1 * s i - x 1 * t i) / D else (x 0 * t i - y 0 * s i) / D
  (Matrix.toEuclideanLin A).toContinuousLinearMap
def interpolation (T G : Triangle) (v : Vec) : Vec := G 0 + interpolationJ T G (v - T 0)

/-- All permutations are harmless: the same elementary triangle gives the same
affine map. Only nearest-neighbor equilateral center triangles are used. -/
def centerTriangles (h : ℝ) : Finset Triangle := by
  classical
  let C := fullCenters h
  exact (((C.product C).product C).image (fun t => ![t.1.1,t.1.2,t.2])).filter
    (fun T => equilateral T (Real.sqrt 3 * h))
def fieldDomain (h : ℝ) : Set Vec := ⋃ T ∈ centerTriangles h, triangleRegion T
def sampled (h : ℝ) (M : Mechanism) (T : Triangle) : Triangle :=
  fun i => M.g (vertex h (T i) 0)
def allocationField (h : ℝ) (M : Mechanism) (v : Vec) : Vec := by
  classical
  exact if H : ∃ T ∈ centerTriangles h, v ∈ triangleRegion T then
    let T := Classical.choose H
    interpolation T (sampled h M T) v
  else 0

/-- Interior triangle Jacobian, with zero assigned on all triangle boundaries and
outside the field domain. This boundary convention changes no area statement. -/
def fieldDerivative (h : ℝ) (M : Mechanism) (v : Vec) : Mat := by
  classical
  exact if H : ∃ T ∈ centerTriangles h, v ∈ interior (triangleRegion T) then
    let T := Classical.choose H
    interpolationJ T (sampled h M T)
  else 0

def rhombusCenter (h : ℝ) (z : Vec) (i j : ℕ) : Vec :=
  z + (Real.sqrt 3 * h) • ((i : ℝ) • vec 1 0 + (j : ℝ) • vec (1/2) (Real.sqrt 3/2))
def rhombusCenters (h : ℝ) (z : Vec) (m : ℕ) : Finset Vec := by
  classical
  exact ((Finset.range (m+1)).product (Finset.range (m+1))).image
    (fun ij => rhombusCenter h z ij.1 ij.2)
def rhombusRegion (h : ℝ) (z : Vec) (m : ℕ) : Set Vec :=
  convexHull ℝ {z, rhombusCenter h z m 0, rhombusCenter h z 0 m, rhombusCenter h z m m}
def FullRhombus (h : ℝ) (z : Vec) (m : ℕ) : Prop :=
  0 < h ∧ 1 ≤ m ∧ ∀ w ∈ rhombusCenters h z m, Full h w
def totalDefect (h : ℝ) (M : Mechanism) (z : Vec) (m : ℕ) : ℝ :=
  ∑ w ∈ rhombusCenters h z m, defect h M w

/-- Actual distributional first derivatives, tested against every compactly supported
smooth scalar function. fderiv is applied only to a test function known to be smooth. -/
def WeakJacobian (Φ : Vec → Vec) (J : Vec → Mat) : Prop :=
  ∀ i j : Fin 2, ∀ φ : Vec → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ v, Φ v i * (fderiv ℝ φ v (basisVector j))) =
      -(∫ v, (J v (basisVector j)) i * φ v)
def Sobolev12 (Φ : Vec → Vec) (J : Vec → Mat) : Prop :=
  MemLp Φ 2 volume ∧ MemLp J 2 volume ∧ WeakJacobian Φ J

end TwoItemMenu1393.Main


