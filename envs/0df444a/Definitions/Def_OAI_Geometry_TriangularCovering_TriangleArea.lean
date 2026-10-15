-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
-- name    : OAI_Geometry_TriangularCovering_TriangleArea
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:36:10.785517+00:00
-- url     : https://prove2.me/theorems/39caca2d-2d1b-4939-ac63-739534b96c60
-- title:
--   Triangles as convex hulls and the Gram-determinant formula for their area
-- statement:
--   This file introduces closed triangles in a real vector space and computes their two-dimensional measure, first in $\mathbb{R}^2$ and then in a plane inside a Euclidean space. For vectors $b,c$ of a real inner product space write
--   $$
--   G(b,c)=\langle b,b\rangle\langle c,c\rangle-\langle b,c\rangle^2
--   $$
--   for their Gram determinant.
--
--   1. **Triangles.** For points $a,b,c$ of a real vector space $E$, the triangle $\triangle(a,b,c)=\operatorname{conv}\{a,b,c\}$ is the closed convex hull of the three points (it may be degenerate). Included facts: a linear or affine map $L$ maps $\triangle(a,b,c)$ onto $\triangle(La,Lb,Lc)$; $\triangle(a,b,c)=a+\triangle(0,b-a,c-a)$; and $\triangle(0,b,c)$ is the image of the standard simplex under the linear map $(s_0,s_1)\mapsto s_0b+s_1c$.
--   2. **Standard simplex.** In $\mathbb{R}^2$, $\Delta_2=\{(s_0,s_1):\ s_0\ge0,\ s_1\ge0,\ s_0+s_1\le1\}$. It is convex, equals $\triangle((0,0),(1,0),(0,1))$, and has Lebesgue measure $\frac12$.
--   3. **Area of a planar triangle.** With the wedge product $b\wedge c=b_0c_1-b_1c_0$ on $\mathbb{R}^2$ (the determinant of $(s_0,s_1)\mapsto s_0b+s_1c$),
--   $$
--   \lambda^2\big(\triangle(a,b,c)\big)=\frac{|(b-a)\wedge(c-a)|}{2}.
--   $$
--   4. **Coordinates on a Euclidean plane.** For an orthonormal basis of a two-dimensional real inner product space $E$, the coordinate map $E\to\mathbb{R}^2$ is a measure-preserving linear isomorphism, and the squared wedge of the coordinates of $b,c$ equals $G(b,c)$. Consequently the volume of a triangle in $E$ is $\frac12\sqrt{G(b-a,c-a)}$.
--   5. **Triangles in a plane of a larger space.** Let $E$ be a finite-dimensional real inner product space and $\mathcal H^2$ its two-dimensional Hausdorff measure. If $a,b,c$ lie in a two-dimensional subspace, then
--   $$
--   \mathcal H^2\big(\triangle(a,b,c)\big)=\frac12\sqrt{G(b-a,c-a)} .
--   $$
--   In particular, if $\dim E=3$ and $a,b,c$ are all orthogonal to a fixed nonzero vector $u$, the same formula holds.
--
--   These formulas compute the base areas of triangular cylinders: the base of every cylinder in the covering of the tetrahedron is a triangle in a plane through the origin orthogonal to the cylinder axis, and item 5 turns its area into an explicit algebraic expression.
--
--   **Formalization Note** $\mathcal H^2$ is Mathlib's `Measure.euclideanHausdorffMeasure 2`, which agrees with Lebesgue measure on two-dimensional subspaces; measures take values in $[0,\infty]$ and the formulas are stated with `ENNReal.ofReal`. The main names are `triangle`, `twoSpan`, `Planar.standard`, `Planar.wedge`, `planeCoord`, `Planar.triangle_volume`, `volume_triangle_basis`, `subspace_triangle_measure` and `perpendicular_triangle_measure`. The lemmas `closed_region_volume` (closed and open regions between two graphs have the same area) and `measurePreserving_image` are measure-theoretic plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/TriangleArea.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/TriangleArea.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering.Planar

abbrev Coord := Fin 2 → ℝ

def standard : Set Coord := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

def vertices : Fin 3 → Coord := ![0, ![1, 0], ![0, 1] ]

lemma standard_convex : Convex ℝ standard := by
  intro x hx y hy a b ha hb hab
  simp only [standard, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), by
      nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
        mul_le_mul_of_nonneg_left hy.2.2 hb]⟩

lemma standard_eq_convexHull : standard = convexHull ℝ (range vertices) := by
  apply le_antisymm
  · intro x hx
    refine mem_convexHull_of_exists_fintype
      (![1 - x 0 - x 1, x 0, x 1] : Fin 3 → ℝ) vertices ?_ ?_ ?_ ?_
    · intro i; fin_cases i <;> dsimp <;>
        linarith [hx.1, hx.2.1, hx.2.2]
    · simp [Fin.sum_univ_succ]
    · exact fun i => mem_range_self i
    · ext i; fin_cases i <;> simp [vertices, Fin.sum_univ_succ]
  · refine convexHull_min ?_ standard_convex
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> norm_num [standard, vertices]

lemma closed_region_volume (f g : ℝ → ℝ) (s : Set ℝ)
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    (volume.prod volume) {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      (volume.prod volume) (regionBetween f g s) := by
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

lemma standard_volume : volume standard = ENNReal.ofReal (1 / 2 : ℝ) := by
  let s : Set (ℝ × ℝ) := {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}
  have heq : standard = (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) ⁻¹' s := by
    ext x
    simp only [standard, mem_ofPred_eq, mem_preimage, s, MeasurableEquiv.piFinTwo_apply,
      mem_Icc]
    constructor
    · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, by linarith⟩, h1, by linarith⟩
    · rintro ⟨⟨h0, _⟩, h1, h2⟩; exact ⟨h0, h1, by linarith⟩
  rw [heq, volume_pi,
    (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))).measure_preimage_equiv]
  change (volume.prod volume) s = _
  rw [closed_region_volume (fun _ => 0) (fun x => 1-x) (Icc 0 1)
    measurable_const (by fun_prop) measurableSet_Icc]
  have hf : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) :=
    continuous_const.integrableOn_Icc
  have hg : IntegrableOn (fun x : ℝ => 1 - x) (Icc 0 1) :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  rw [volume_regionBetween_eq_integral hf hg measurableSet_Icc
    (by intro x hx; linarith [hx.2])]
  congr 1
  simp only [Pi.sub_apply, sub_zero]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _), integral_id]
  norm_num

end TriangularCovering.Planar

namespace TriangularCovering

section Triangles
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def triangle (a b c : E) : Set E := convexHull ℝ (range (![a, b, c] : Fin 3 → E))

def twoSpan (b c : E) : Planar.Coord →ₗ[ℝ] E :=
  (LinearMap.proj 0).smulRight b + (LinearMap.proj 1).smulRight c

@[simp] lemma twoSpan_apply (b c : E) (x : Planar.Coord) :
    twoSpan b c x = x 0 • b + x 1 • c := rfl

lemma triangle_image_linear (L : E →ₗ[ℝ] F) (a b c : E) :
    L '' triangle a b c = triangle (L a) (L b) (L c) := by
  rw [triangle, L.image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> rfl

lemma triangle_image_affine (L : E →ᵃ[ℝ] F) (a b c : E) :
    L '' triangle a b c = triangle (L a) (L b) (L c) := by
  rw [triangle, L.image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> rfl

lemma triangle_zero_image (b c : E) : triangle 0 b c = twoSpan b c '' Planar.standard := by
  rw [Planar.standard_eq_convexHull, (twoSpan b c).image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> simp [Planar.vertices, twoSpan]

lemma triangle_translate (a b c : E) :
    triangle a b c = (fun x => a + x) '' triangle 0 (b-a) (c-a) := by
  have h := triangle_image_affine (AffineEquiv.constVAdd ℝ E a).toAffineMap 0 (b-a) (c-a)
  simpa using h.symm

end Triangles

namespace Planar

def wedge (b c : Coord) : ℝ := b 0 * c 1 - b 1 * c 0

lemma twoSpan_det (b c : Coord) : LinearMap.det (twoSpan b c) = wedge b c := by
  have h : twoSpan b c = Matrix.toLin' (!![b 0, c 0; b 1, c 1]) := by
    apply LinearMap.ext
    intro x
    funext i
    fin_cases i <;> simp [twoSpan_apply, Matrix.toLin'_apply, Matrix.vecHead, Matrix.vecTail, mul_comm]
    all_goals ring
  rw [h, LinearMap.det_toLin', Matrix.det_fin_two]
  simp [wedge, mul_comm]

lemma triangle_volume (a b c : Coord) :
    volume (triangle a b c) = ENNReal.ofReal (|wedge (b-a) (c-a)| / 2) := by
  rw [triangle_translate, image_add_left, measure_preimage_add,
    triangle_zero_image, volume.addHaar_image_linearMap, twoSpan_det, standard_volume,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

end Planar
end TriangularCovering

namespace TriangularCovering

lemma measurePreserving_image {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hm : MeasurePreserving f μ ν)
    (hf : MeasurableEmbedding f) (s : Set X) : ν (f '' s) = μ s := by
  rw [← hm.measure_preimage_emb hf, hf.injective.preimage_image]

section InnerPlane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def planeCoord (basis : OrthonormalBasis (Fin 2) ℝ E) : E ≃L[ℝ] Planar.Coord :=
  basis.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2) ℝ)

lemma planeCoord_measurePreserving (basis : OrthonormalBasis (Fin 2) ℝ E) :
    MeasurePreserving (planeCoord basis) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin 2)).comp basis.measurePreserving_repr

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma planeCoord_gram (basis : OrthonormalBasis (Fin 2) ℝ E) (b c : E) :
    (Planar.wedge (planeCoord basis b) (planeCoord basis c)) ^ 2 =
      inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2 := by
  rw [← basis.repr.inner_map_map b b, ← basis.repr.inner_map_map c c,
    ← basis.repr.inner_map_map b c]
  change (((basis.repr b).ofLp 0 * (basis.repr c).ofLp 1 -
    (basis.repr b).ofLp 1 * (basis.repr c).ofLp 0)^2) = _
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

lemma volume_triangle_basis (basis : OrthonormalBasis (Fin 2) ℝ E) (a b c : E) :
    volume (triangle a b c) = ENNReal.ofReal
      (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a))^2) / 2) := by
  rw [← measurePreserving_image (planeCoord_measurePreserving basis)
    (planeCoord basis).toHomeomorph.measurableEmbedding]
  change volume ((planeCoord basis).toLinearMap '' triangle a b c) = _
  rw [triangle_image_linear, Planar.triangle_volume]
  rw [← map_sub, ← map_sub, ← planeCoord_gram basis, Real.sqrt_sq_eq_abs]
  rfl

end InnerPlane
end TriangularCovering

namespace TriangularCovering

section SubspaceMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma subspace_triangle_measure (P : Submodule ℝ E) (hp : Module.finrank ℝ P = 2)
    (a b c : P) :
    Measure.euclideanHausdorffMeasure 2 (triangle (a : E) (b : E) (c : E)) =
      ENNReal.ofReal (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a)) ^ 2) / 2) := by
  change Measure.euclideanHausdorffMeasure 2
    (triangle (P.subtype a) (P.subtype b) (P.subtype c)) = _
  rw [← triangle_image_linear P.subtype a b c]
  change Measure.euclideanHausdorffMeasure 2 ((Subtype.val : P → E) '' triangle a b c) = _
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure P) = volume := by
    rw [← hp, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rw [hm]
  exact volume_triangle_basis ((stdOrthonormalBasis ℝ P).reindex (finCongr hp)) a b c

lemma perpendicular_triangle_measure (hrank : Module.finrank ℝ E = 3)
    (u a b c : E) (hu : u ≠ 0) (ha : inner ℝ u a = 0)
    (hb : inner ℝ u b = 0) (hc : inner ℝ u c = 0) :
    Measure.euclideanHausdorffMeasure 2 (triangle a b c) =
      ENNReal.ofReal (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a)) ^ 2) / 2) := by
  let P := (ℝ ∙ u)ᗮ
  have hp : Module.finrank ℝ P = 2 := by
    have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hu, hrank] at h
    change 1 + Module.finrank ℝ P = 3 at h
    omega
  have ha' : a ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ha
  have hb' : b ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hb
  have hc' : c ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hc
  exact subspace_triangle_measure P hp ⟨a,ha'⟩ ⟨b,hb'⟩ ⟨c,hc'⟩

end SubspaceMeasure
end TriangularCovering

end

end OAI


