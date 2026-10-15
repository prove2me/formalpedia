-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_Projection
-- name    : OAI_Geometry_RuledCovering_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:14:11.22992+00:00
-- url     : https://prove2.me/theorems/eca22c73-a718-4b05-bf05-f7c475a589ec
-- title:
--   Physical embedding of the plane, slanted unit axes and perpendicularly projected cylinders
-- statement:
--   Throughout, $\mathbb{R}^2$ and $\mathbb{R}^3$ carry their Euclidean inner products $\langle\cdot,\cdot\rangle$, and points are written $p=(p_1,p_2)$ and $z=(z_1,z_2,z_3)$. A *cylinder* in $\mathbb{R}^3$ consists of a unit axis $u$ and a base set $B$ contained in the plane $u^{\perp}$; its carrier is $\{b+tu:\ b\in B,\ t\in\mathbb{R}\}$ and its area is the two-dimensional Lebesgue measure of $B$ inside $u^{\perp}$. Fix a vertical scale $h\in\mathbb{R}$ and a slope vector $g=(g_1,g_2)\in\mathbb{R}^2$. The file defines the following objects.
--
--   1. **Physical embedding of the parameter plane.** The linear map $E_h:\mathbb{R}^2\to\mathbb{R}^3$,
--   $$E_h(p)=(0,\ p_1,\ h\,p_2).$$
--   2. **Physical direction.** The vector
--   $$d_{h,g}=(1,\ g_1,\ h\,g_2)\in\mathbb{R}^3 .$$
--   Its first coordinate is $1$, so $d_{h,g}\neq 0$ and $\|d_{h,g}\|>0$; both facts are recorded.
--   3. **Unit axis.** $u_{h,g}=d_{h,g}/\|d_{h,g}\|$, which has norm $1$.
--   4. **Perpendicular projection.** The linear map $\pi_{h,g}:\mathbb{R}^2\to u_{h,g}^{\perp}$,
--   $$\pi_{h,g}(p)=E_h(p)-\frac{\langle d_{h,g},E_h(p)\rangle}{\|d_{h,g}\|^{2}}\,d_{h,g},$$
--   that is, the orthogonal projection of the point $E_h(p)$ onto the plane through the origin perpendicular to $d_{h,g}$. It is first defined with values in $\mathbb{R}^3$, shown to take values orthogonal to $u_{h,g}$, and then regarded as a map into $u_{h,g}^{\perp}$.
--   5. **Projected cylinder.** For any set $P\subseteq\mathbb{R}^2$, $\mathcal{C}_{h,g}(P)$ is the cylinder with axis $u_{h,g}$ and base $\pi_{h,g}(P)\subseteq u_{h,g}^{\perp}$.
--
--   The file also records the coordinate formulas $\langle (a,b,c),(x,y,z)\rangle=ax+by+cz$ and $\|(a,b,c)\|^2=a^2+b^2+c^2$.
--
--   These objects turn planar tiles into genuine cylinders for the physically normalized ruled sets, whose points have the form $(s,\ p_1+s\,v_1(p),\ h(p_2+s\,v_2(p)))$ for a planar field $v$. Such a point equals $E_h(q)+s\,d_{h,g}$ with $q=p+s\,(v(p)-g)$, so the ruling segment through $p$ lies in $\mathcal{C}_{h,g}(P)$ as soon as $q\in P$ for all the times $s$ involved. Because the base is the true perpendicular cross-section and not the oblique copy $E_h(P)$, the area of $\mathcal{C}_{h,g}(P)$ is, for $h>0$, exactly $h\,|P|/\sqrt{1+g_1^2+h^2g_2^2}$, i.e. $h\,|P|$ times the physical weight of $g$ (this is shown in the same module); it is the source of the weighted integrals in the covering bounds.
--
--   **Formalization Note** `Plane` and `Space` are `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`, with coordinates indexed from $0$, so `p 0`, `p 1` are $p_1,p_2$ above. The definitions are `planeEmbedding`, `physicalDirection`, `physicalUnit`, `rawProjection` (valued in `Space`), `perpendicularProjection` (its corestriction to the orthogonal complement of the span of `physicalUnit h g`) and `projectedCylinder`. The `vec2_apply_*` and `vec3_apply_*` simp lemmas, `inner_vec3`, `norm_vec3_sq` and the non-vanishing lemmas are plumbing. No definition assumes $h\neq 0$; for $h=0$ the embedding $E_0$ is degenerate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

@[simp] lemma vec2_apply_zero (x y : ℝ) : vec2 x y 0 = x := rfl
@[simp] lemma vec2_apply_one (x y : ℝ) : vec2 x y 1 = y := rfl
@[simp] lemma vec3_apply_zero (x y z : ℝ) : vec3 x y z 0 = x := rfl
@[simp] lemma vec3_apply_one (x y z : ℝ) : vec3 x y z 1 = y := rfl
@[simp] lemma vec3_apply_two (x y z : ℝ) : vec3 x y z 2 = z := rfl

lemma inner_vec3 (a b c x y z : ℝ) :
    inner ℝ (vec3 a b c) (vec3 x y z) = a*x+b*y+c*z := by
  simp [vec3, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_succ]
  ring

lemma norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vec3]
  ring

/-- The transverse plane in the physical normalization. -/
def planeEmbedding (h : ℝ) : Plane →ₗ[ℝ] Space where
  toFun p := vec3 0 (p 0) (h * p 1)
  map_add' p q := by ext i; fin_cases i <;> simp [vec3, mul_add]
  map_smul' c p := by ext i; fin_cases i <;> simp [vec3, mul_left_comm]

@[simp] lemma planeEmbedding_apply (h : ℝ) (p : Plane) :
    planeEmbedding h p = vec3 0 (p 0) (h * p 1) := rfl

def physicalDirection (h : ℝ) (g : Plane) : Space := vec3 1 (g 0) (h * g 1)

lemma physicalDirection_ne_zero (h : ℝ) (g : Plane) : physicalDirection h g ≠ 0 := by
  intro hz
  have := congrArg (fun x : Space => x 0) hz
  simp [physicalDirection] at this

lemma physicalDirection_norm_pos (h : ℝ) (g : Plane) : 0 < ‖physicalDirection h g‖ :=
  norm_pos_iff.mpr (physicalDirection_ne_zero h g)

def physicalUnit (h : ℝ) (g : Plane) : Space :=
  ‖physicalDirection h g‖⁻¹ • physicalDirection h g

lemma physicalUnit_norm (h : ℝ) (g : Plane) : ‖physicalUnit h g‖ = 1 := by
  rw [physicalUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (physicalDirection_norm_pos h g).ne']

def rawProjection (h : ℝ) (g : Plane) : Plane →ₗ[ℝ] Space where
  toFun p := planeEmbedding h p -
    (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
      ‖physicalDirection h g‖ ^ 2) • physicalDirection h g
  map_add' p q := by simp only [map_add, inner_add_right, add_div, add_smul]; abel
  map_smul' c p := by
    simp only [map_smul, inner_smul_right, mul_div_assoc, mul_smul, smul_sub, RingHom.id_apply]

lemma rawProjection_mem (h : ℝ) (g p : Plane) :
    rawProjection h g p ∈ ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk, physicalUnit,
    inner_smul_left, RCLike.conj_to_real, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

def perpendicularProjection (h : ℝ) (g : Plane) :
    Plane →ₗ[ℝ] ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) :=
  (rawProjection h g).codRestrict _ (rawProjection_mem h g)

/-- A genuine cylinder in its perpendicular plane, not an oblique intercept patch. -/
def projectedCylinder (h : ℝ) (g : Plane) (P : Set Plane) : Cylinder where
  axis := physicalUnit h g
  unit_axis := physicalUnit_norm h g
  base := perpendicularProjection h g '' P

end RuledApproximation

end

end OAI


