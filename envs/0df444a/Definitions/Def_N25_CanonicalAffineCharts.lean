-- Prove2me | Definitions.Def_N25_CanonicalAffineCharts
-- name    : N25_CanonicalAffineCharts
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:57.602094+00:00
-- url     : https://prove2.me/theorems/6ee44747-9743-4de4-ae99-d37b57db4abb
-- title:
--   The four affine charts and five rational cusps of the canonical curve
-- statement:
--   For each pivot $i∈\{0,1,2,3\}$, the file defines the chart ring cut out by $(Q,C,x_i-1)$, its point carrier, evaluation map, point ideal, and residue quotient. It records the five rational cusp representatives, defines normalization of a homogeneous point at a nonzero pivot, and defines every two-column Jacobian minor. These literal charts support point enumeration, cusp calculations, and the local smoothness criterion.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
/-! All four affine charts of the canonical curve and the five rational cusp points. -/
noncomputable section

namespace N25

open MvPolynomial

/-- Four homogeneous coordinates before fixing an affine chart. -/
abbrev CanonicalChartPolynomial25 (k : Type*) [CommRing k] := MvPolynomial (Fin 4) k

/-- The canonical equations together with the equation setting one coordinate equal to one. -/
def canonicalChartIdeal25 (k : Type*) [CommRing k] (i : Fin 4) :
    Ideal (CanonicalChartPolynomial25 k) :=
  Ideal.span {canonicalQuadric (X 0) (X 1) (X 2) (X 3),
    canonicalCubic (X 0) (X 1) (X 2) (X 3), X i - 1}

/-- The literal affine chart in which the i-th homogeneous coordinate is one. -/
abbrev CanonicalChartRing25 (k : Type*) [CommRing k] (i : Fin 4) :=
  CanonicalChartPolynomial25 k ⧸ canonicalChartIdeal25 k i

/-- A point in a specified affine chart. Its pivot condition ensures nonzero coordinates. -/
structure CanonicalChartPoint25 (k : Type*) [CommRing k] (i : Fin 4) where
  coordinates : Fin 4 → k
  quadric : canonicalQuadric (coordinates 0) (coordinates 1) (coordinates 2) (coordinates 3) = 0
  cubic : canonicalCubic (coordinates 0) (coordinates 1) (coordinates 2) (coordinates 3) = 0
  pivot : coordinates i = 1

/-- Evaluate regular functions at a point in the chosen affine chart. -/
noncomputable def canonicalChartEvaluation25 {k : Type*} [CommRing k] {i : Fin 4}
    (p : CanonicalChartPoint25 k i) : CanonicalChartRing25 k i →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval p.coordinates) (by
    intro f hf
    have hle : canonicalChartIdeal25 k i ≤ RingHom.ker (aeval p.coordinates :
        CanonicalChartPolynomial25 k →ₐ[k] k).toRingHom := by
      apply Ideal.span_le.mpr
      intro g hg
      rcases hg with rfl | hg
      · simpa [RingHom.mem_ker, canonicalQuadric] using p.quadric
      · rcases hg with rfl | hg
        · simpa [RingHom.mem_ker, canonicalCubic] using p.cubic
        · rcases hg with rfl | hg
          · simp [RingHom.mem_ker, p.pivot]
    exact hle hf)

/-- The ideal of the point in its affine coordinate ring. -/
noncomputable def canonicalChartPointIdeal25 {k : Type*} [CommRing k] {i : Fin 4}
    (p : CanonicalChartPoint25 k i) : Ideal (CanonicalChartRing25 k i) :=
  RingHom.ker (canonicalChartEvaluation25 p).toRingHom

/-- A rational point has coefficient field as its affine residue quotient. -/
noncomputable def canonicalChartPointResidueEquiv25 {k : Type*} [CommRing k] {i : Fin 4}
    (p : CanonicalChartPoint25 k i) :
    (CanonicalChartRing25 k i ⧸ canonicalChartPointIdeal25 p) ≃ₐ[k] k :=
  Ideal.quotientKerAlgEquivOfSurjective (fun a =>
    ⟨algebraMap k (CanonicalChartRing25 k i) a, (canonicalChartEvaluation25 p).commutes a⟩)

/-- The cusp [0:0:0:1] in the W-chart. -/
def canonicalCuspAChart25 (k : Type*) [CommRing k] : CanonicalChartPoint25 k 3 :=
  ⟨![0,0,0,1], by simp [canonicalQuadric], by simp [canonicalCubic], rfl⟩

/-- The cusp [0:-1:1:0] in the Z-chart. -/
def canonicalCuspBChart25 (k : Type*) [CommRing k] : CanonicalChartPoint25 k 2 :=
  ⟨![0,-1,1,0], by simp [canonicalQuadric], by simp [canonicalCubic], rfl⟩

/-- The cusp [1:1:0:1] in the W-chart. -/
def canonicalCuspCChart25 (k : Type*) [CommRing k] : CanonicalChartPoint25 k 3 :=
  ⟨![1,1,0,1], by simp [canonicalQuadric], by simp [canonicalCubic], rfl⟩

/-- The cusp [0:0:1:0] in the Z-chart. -/
def canonicalCuspDChart25 (k : Type*) [CommRing k] : CanonicalChartPoint25 k 2 :=
  ⟨![0,0,1,0], by simp [canonicalQuadric], by simp [canonicalCubic], rfl⟩

/-- The cusp [1:0:0:0] in the X-chart. -/
def canonicalCuspEChart25 (k : Type*) [CommRing k] : CanonicalChartPoint25 k 0 :=
  ⟨![1,0,0,0], by simp [canonicalQuadric], by simp [canonicalCubic], rfl⟩

/-- Normalize a nonzero pivot of a homogeneous canonical point. -/
def canonicalChartPointOfHomogeneous25 {k : Type*} [Field k]
    (v : Fin 4 → k) (i : Fin 4) (hi : v i ≠ 0)
    (hq : canonicalQuadric (v 0) (v 1) (v 2) (v 3) = 0)
    (hc : canonicalCubic (v 0) (v 1) (v 2) (v 3) = 0) :
    CanonicalChartPoint25 k i where
  coordinates j := (v i)⁻¹ * v j
  quadric := by
    have h : canonicalQuadric ((v i)⁻¹*v 0) ((v i)⁻¹*v 1)
        ((v i)⁻¹*v 2) ((v i)⁻¹*v 3) = (v i)⁻¹^2 *
        canonicalQuadric (v 0) (v 1) (v 2) (v 3) := by
      unfold canonicalQuadric; ring
    rw [h, hq, mul_zero]
  cubic := by
    have h : canonicalCubic ((v i)⁻¹*v 0) ((v i)⁻¹*v 1)
        ((v i)⁻¹*v 2) ((v i)⁻¹*v 3) = (v i)⁻¹^3 *
        canonicalCubic (v 0) (v 1) (v 2) (v 3) := by
      unfold canonicalCubic; ring
    rw [h, hc, mul_zero]
  pivot := inv_mul_cancel₀ hi

/-- A two-column minor of the homogeneous Jacobian of Q,C. -/
def canonicalJacobianMinor25 (k : Type*) [CommRing k] (i j : Fin 4) :
    CanonicalChartPolynomial25 k :=
  let q : CanonicalChartPolynomial25 k := canonicalQuadric (X 0) (X 1) (X 2) (X 3)
  let c : CanonicalChartPolynomial25 k := canonicalCubic (X 0) (X 1) (X 2) (X 3)
  pderiv i q * pderiv j c - pderiv i c * pderiv j q

end N25


