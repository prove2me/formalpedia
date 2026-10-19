-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
-- name    : OAI_Geometry_Arnold_MidpointGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T09:01:08.734173+00:00
-- url     : https://prove2.me/theorems/14b20e52-14d4-48df-a78f-de5bd07b4566
-- title:
--   Implicit midpoint steps of a skew field preserve the unit quadric
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$, $B(z,w)=\sum_jz_jw_j$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$ is the projective quadric. A vector $v$ is skew at $z$ if $\operatorname{Re}B(\bar z,v)=0$ and $B(z,v)=0$.
--
--   1. **Expansions.** $|z+w|^2=|z|^2+2\operatorname{Re}B(\bar z,w)+|w|^2$, and real scalars act on $q$ and $|\cdot|^2$ quadratically. If $v$ is skew at $z$ and $s\in\mathbb{R}$, then
--   $$
--   |z+sv|^2=|z|^2+s^2|v|^2,\qquad q(z+sv)=q(z)+s^2q(v).
--   $$
--   2. **Norm comparison.** $|z|^2\le5\|z\|_\infty^2$, and $|z|^2\le1$ implies $\|z\|_\infty\le1$.
--   3. **Midpoint steps of the compact field.** Let $X$ be the compactly supported Hamiltonian field, which is skew at every point. Let $\tau$ satisfy $|\tau|\,\mathrm{Lip}(X)<1$, let $c$ be the midpoint centre and $\Phi$ the midpoint step. Then:
--      - $|z|^2=|c|^2+\tau^2|X(c)|^2$;
--      - $\Phi(t,\cdot)$ maps the unit quadric $S$ into itself;
--      - for $z\in S$, $|c(t,z)|^2\le1$, and if moreover $|\tau|\,\mathrm{Lip}(X)<\tfrac1{10}$ then $|c(t,z)|^2>\tfrac12$.
--
--   Because the field is skew, the centre is equidistant (in the quadratic sense) from the start and end points of a step. This forces the step to preserve both $|z|^2$ and $q$, so the discrete flow stays on the quadric, and its centre stays in the region where the field is the geometric one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/MidpointGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/MidpointGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology NNReal
open Set Filter

lemma normSquared_add (z w : CV) : normSquared (z+w) =
    normSquared z + 2 * (bilinear (star z) w).re + normSquared w := by
  simp only [normSquared, bilinear, Pi.add_apply, Pi.star_apply, Complex.normSq_add,
    Complex.re_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have h : ∑ i : Fin 5, 2 * (z i * (starRingEnd ℂ) (w i)).re =
      ∑ i : Fin 5, 2 * (star (z i) * w i).re := by
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.mul_re]
  rw [h]
  ring

lemma real_smul_complex (s : ℝ) (z : CV) : s • z = (s : ℂ) • z := by
  ext i; simp [Complex.real_smul]

lemma normSquared_real_smul (s : ℝ) (z : CV) : normSquared (s • z) = s^2 * normSquared z := by
  rw [real_smul_complex, normSquared_smul, Complex.normSq_ofReal]
  ring

lemma quadricPolynomial_real_smul (s : ℝ) (z : CV) :
    quadricPolynomial (s • z) = (s : ℂ)^2 * quadricPolynomial z := by
  rw [real_smul_complex, quadricPolynomial_smul]

lemma quadratic_skew (z v : CV) (hv : SkewAt z v) (s : ℝ) :
    normSquared (z+s•v) = normSquared z + s^2 * normSquared v ∧
    quadricPolynomial (z+s•v) = quadricPolynomial z + (s:ℂ)^2 * quadricPolynomial v := by
  constructor
  · rw [normSquared_add, normSquared_real_smul, real_smul_complex, bilinear_smul_right]
    simp [Complex.mul_re, hv.1]
  · rw [quadricPolynomial_add, quadricPolynomial_real_smul, real_smul_complex, bilinear_smul_right, hv.2]
    ring

lemma normSquared_le_maxNorm (z : CV) : normSquared z ≤ 5 * ‖z‖^2 := by
  calc
    normSquared z ≤ ∑ i : Fin 5, ‖z‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2
    _ = _ := by simp

lemma norm_le_one_of_normSquared {z : CV} (hz : normSquared z ≤ 1) : ‖z‖ ≤ 1 :=
  norm_bound_of_normSquared (by norm_num) (by simpa using hz)

variable {C : ℝ≥0} (hX : LipschitzWith C vectorField) (τ : ℝ → ℝ)
  (hτ : ∀ t, ‖τ t‖ * C < 1)

lemma center_quadratic (p : ℝ × CV) :
    normSquared p.2 = normSquared (Midpoint.resolvent vectorField hX τ hτ p) +
      (τ p.1)^2 * normSquared (vectorField (Midpoint.resolvent vectorField hX τ hτ p)) := by
  let u := Midpoint.resolvent vectorField hX τ hτ p
  have he : p.2 = u + (-τ p.1) • vectorField u := by
    have hh := Midpoint.resolvent_eq vectorField hX τ hτ p
    change u = p.2 + τ p.1 • vectorField u at hh
    rw [neg_smul]
    simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq.mpr hh.symm)
  rw [he, (quadratic_skew u _ (vectorField_skew u) _).1, neg_sq]

lemma midpoint_preserves (t : ℝ) (z : UnitQuadric) :
    IsUnitQuadric (Midpoint.step vectorField hX τ hτ (t,z)) := by
  let u := Midpoint.resolvent vectorField hX τ hτ (t,z)
  have he : (z : CV) = u + (-τ t) • vectorField u := by
    have hh := Midpoint.resolvent_eq vectorField hX τ hτ (t,z)
    change u = (z:CV) + τ t • vectorField u at hh
    rw [neg_smul]
    simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq.mpr hh.symm)
  have hp := (quadratic_skew u _ (vectorField_skew u) (-τ t)).2
  rw [← he, z.property.2, Complex.ofReal_neg, neg_sq] at hp
  rw [Midpoint.step_center]
  exact ⟨((quadratic_skew u _ (vectorField_skew u) (τ t)).1).trans
    ((center_quadratic hX τ hτ (t,z)).symm.trans z.property.1),
    ((quadratic_skew u _ (vectorField_skew u) (τ t)).2).trans hp.symm⟩

lemma center_norm_le_one (t : ℝ) (z : UnitQuadric) :
    normSquared (Midpoint.resolvent vectorField hX τ hτ (t,z)) ≤ 1 := by
  have he := center_quadratic hX τ hτ (t,z)
  rw [z.property.1] at he
  nlinarith [mul_nonneg (sq_nonneg (τ t)) (normSquared_nonneg
    (vectorField (Midpoint.resolvent vectorField hX τ hτ (t,z))))]

lemma center_norm_gt_half (hsmall : ∀ t, ‖τ t‖ * C < 1/10) (t : ℝ) (z : UnitQuadric) :
    1/2 < normSquared (Midpoint.resolvent vectorField hX τ hτ (t,z)) := by
  let u := Midpoint.resolvent vectorField hX τ hτ (t,z)
  have hu : ‖u‖ ≤ 1 := norm_le_one_of_normSquared (center_norm_le_one hX τ hτ t z)
  have hXb : ‖vectorField u‖ ≤ C := by
    have h := hX.dist_le_mul u 0
    rw [vectorField_zero, dist_zero_right, dist_zero_right] at h
    exact h.trans (by nlinarith [C.coe_nonneg])
  have hb : normSquared (vectorField u) ≤ 5 * (C:ℝ)^2 :=
    (normSquared_le_maxNorm _).trans (by nlinarith [norm_nonneg (vectorField u)])
  have he := center_quadratic hX τ hτ (t,z)
  change normSquared (z:CV) = normSquared u + (τ t)^2 * normSquared (vectorField u) at he
  rw [z.property.1] at he
  have hs := hsmall t
  have hn : 0 ≤ ‖τ t‖ * (C:ℝ) := mul_nonneg (norm_nonneg _) C.coe_nonneg
  have hsq : (τ t)^2 * (C:ℝ)^2 < 1/100 := by
    simp only [Real.norm_eq_abs] at hs hn
    nlinarith [sq_abs (τ t)]
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (τ t))
  nlinarith

end ArnoldCounterexample.Field

end

end OAI


