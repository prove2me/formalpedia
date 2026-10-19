-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Projective
-- name    : OAI_Geometry_Arnold_Projective
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:22:40.15698+00:00
-- url     : https://prove2.me/theorems/e6c8708e-bbb4-4f27-b693-33573f525b75
-- title:
--   Unit representatives, the bilinear pairing and a polynomial local section of the quadric cone
-- statement:
--   Write $q(z)=\sum_{j=0}^4z_j^2$ and $|z|^2=\sum_j|z_j|^2$ for $z\in\mathbb{C}^5$. The quadric is $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$. Its points are represented by unit isotropic vectors $z$, i.e. $|z|^2=1$ and $q(z)=0$, which form the unit quadric $S$, and $\pi:S\to Q_3$ is the projection $z\mapsto[z]$. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0$ and $\sum_jz_jv_j=0$. The form $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$ is the Fubini–Study form on horizontal vectors.
--
--   1. **Norm and scaling.** $|z|^2\ge0$, with equality only for $z=0$. Moreover $q(az)=a^2q(z)$ and $|az|^2=|a|^2|z|^2$ for $a\in\mathbb{C}$.
--   2. **Unit representatives.** Every point of $Q_3$ is $[z]$ for some unit isotropic $z$, i.e. $\pi$ is surjective. Horizontal vectors are closed under complex scaling.
--   3. **The bilinear pairing.** $B(z,w)=\sum_jz_jw_j$. It is symmetric and complex bilinear, with $B(z,z)=q(z)$, $B(\bar z,z)=|z|^2$, $q(\bar z)=\overline{q(z)}$ and $q(z+w)=q(z)+2B(z,w)+q(w)$.
--   4. **Local section.** For $z\in S$ and $v\in\mathbb{C}^5$,
--   $$
--   \sigma_z(v)=z+v-\frac{q(v)}{2}\,\bar z .
--   $$
--   For horizontal $v$, $\sigma_z(v)$ lies on the cone $q=0$, satisfies $B(\bar z,\sigma_z(v))=1$, and is nonzero.
--
--   The local section is an explicit polynomial chart of $Q_3$ around $[z]$, with derivative the identity on horizontal vectors. It identifies horizontal vectors with tangent vectors of $Q_3$ without appealing to any manifold structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Projective.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Projective.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

lemma normSquared_eq_zero_iff (z : CV) : normSquared z = 0 ↔ z = 0 := by
  rw [normSquared, Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ Complex.normSq_nonneg (z j))]
  simp only [Finset.mem_univ, forall_const, Complex.normSq_eq_zero]
  exact ⟨fun h ↦ funext h, fun h j ↦ congrFun h j⟩

lemma normSquared_nonneg (z : CV) : 0 ≤ normSquared z :=
  Finset.sum_nonneg (fun j _ ↦ Complex.normSq_nonneg (z j))

lemma normSquared_pos {z : CV} (hz : z ≠ 0) : 0 < normSquared z :=
  lt_of_le_of_ne (normSquared_nonneg z) (Ne.symm (mt (normSquared_eq_zero_iff z).mp hz))

lemma quadricPolynomial_smul (a : ℂ) (z : CV) :
    quadricPolynomial (a • z) = a ^ 2 * quadricPolynomial z := by
  simp only [quadricPolynomial, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma normSquared_smul (a : ℂ) (z : CV) :
    normSquared (a • z) = Complex.normSq a * normSquared z := by
  simp only [normSquared, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

/-- Every projective quadric point has a unit representative, proved without
assuming the standard quotient geometry. -/
theorem project_surjective : Function.Surjective project := by
  intro q
  obtain ⟨z, hz, hq, hp⟩ := q.property
  have hn : 0 < normSquared z := normSquared_pos hz
  have hs : 0 < Real.sqrt (normSquared z) := Real.sqrt_pos.mpr hn
  let a : ℂ := ((Real.sqrt (normSquared z))⁻¹ : ℝ)
  have ha : a ≠ 0 := by
    simp only [a, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact ne_of_gt hs
  have hnorm : normSquared (a • z) = 1 := by
    rw [normSquared_smul]
    simp only [a, Complex.normSq_ofReal]
    field_simp [ne_of_gt hs]
    nlinarith [Real.sq_sqrt hn.le]
  have hpoly : quadricPolynomial (a • z) = 0 := by
    rw [quadricPolynomial_smul, hp, mul_zero]
  refine ⟨⟨a • z, hnorm, hpoly⟩, ?_⟩
  apply Subtype.ext
  change Projectivization.mk ℂ (a • z) _ = q.val
  rw [← hq, Projectivization.mk_eq_mk_iff']
  exact ⟨a, rfl⟩

lemma horizontal_smul {z v : CV} (hv : Horizontal z v) (a : ℂ) :
    Horizontal z (a • v) := by
  constructor
  · calc
      (∑ j, star (z j) * (a • v) j) = a * ∑ j, star (z j) * v j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hv.1, mul_zero]
  · calc
      (∑ j, z j * (a • v) j) = a * ∑ j, z j * v j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hv.2, mul_zero]

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

/-- Complex-bilinear pairing defining the quadric. -/
def bilinear (z w : CV) : ℂ := ∑ j, z j * w j

lemma bilinear_comm (z w : CV) : bilinear z w = bilinear w z := by
  unfold bilinear
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma bilinear_add_left (z w v : CV) : bilinear (z + w) v = bilinear z v + bilinear w v := by
  simp [bilinear, add_mul, Finset.sum_add_distrib]

lemma bilinear_add_right (z w v : CV) : bilinear z (w + v) = bilinear z w + bilinear z v := by
  simp [bilinear, mul_add, Finset.sum_add_distrib]

lemma bilinear_smul_left (a : ℂ) (z w : CV) : bilinear (a • z) w = a * bilinear z w := by
  simp [bilinear, Finset.mul_sum, mul_assoc]

lemma bilinear_smul_right (a : ℂ) (z w : CV) : bilinear z (a • w) = a * bilinear z w := by
  rw [bilinear_comm, bilinear_smul_left, bilinear_comm w z]

@[simp] lemma bilinear_self (z : CV) : bilinear z z = quadricPolynomial z := by
  simp [bilinear, quadricPolynomial, pow_two]

@[simp] lemma bilinear_star_self (z : CV) : bilinear (star z) z = (normSquared z : ℂ) := by
  simp only [bilinear, Pi.star_apply, normSquared]
  rw [show ((∑ j, Complex.normSq (z j) : ℝ) : ℂ) =
      ∑ j, (Complex.normSq (z j) : ℂ) from map_sum Complex.ofRealHom _ _]
  apply Finset.sum_congr rfl
  intro j _
  exact (Complex.normSq_eq_conj_mul_self).symm

lemma quadricPolynomial_star (z : CV) : quadricPolynomial (star z) = star (quadricPolynomial z) := by
  simp [quadricPolynomial, star_sum, star_pow]

lemma quadricPolynomial_add (z w : CV) :
    quadricPolynomial (z + w) = quadricPolynomial z + 2 * bilinear z w + quadricPolynomial w := by
  simp only [quadricPolynomial, bilinear, Pi.add_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A concrete polynomial parametrization transverse to the complex scaling.
For horizontal v it stays on the quadric and its first derivative at zero is v.
This makes the horizontal tangent identification independent of any assumed atlas. -/
def localSection (z v : CV) : CV := z + v + (-(quadricPolynomial v / 2)) • star z

lemma localSection_on_quadric (z : UnitQuadric) {v : CV} (hv : Horizontal z v) :
    quadricPolynomial (localSection z v) = 0 := by
  have hzv : bilinear (z : CV) v = 0 := hv.2
  have hsv : bilinear (star (z : CV)) v = 0 := hv.1
  have hnorm : bilinear (z : CV) (star (z : CV)) = 1 := by
    rw [bilinear_comm, bilinear_star_self, z.property.1, Complex.ofReal_one]
  have hvstar : bilinear v (star (z : CV)) = 0 := (bilinear_comm _ _).trans hsv
  simp only [localSection, quadricPolynomial_add, quadricPolynomial_smul,
    bilinear_add_left, bilinear_smul_right, quadricPolynomial_star, z.property.2,
    star_zero, hnorm, hvstar, hzv]
  ring

lemma localSection_gauge (z : UnitQuadric) {v : CV} (hv : Horizontal z v) :
    bilinear (star (z : CV)) (localSection z v) = 1 := by
  have hnorm : bilinear (star (z : CV)) z = 1 := by
    rw [bilinear_star_self, z.property.1, Complex.ofReal_one]
  have hsv : bilinear (star (z : CV)) v = 0 := hv.1
  simp only [localSection, bilinear_add_right, bilinear_smul_right, hnorm, hsv,
    bilinear_self, quadricPolynomial_star, z.property.2, star_zero, mul_zero, add_zero]

lemma localSection_ne_zero (z : UnitQuadric) {v : CV} (hv : Horizontal z v) :
    localSection z v ≠ 0 := by
  intro h
  have hg := localSection_gauge z hv
  simp [h, bilinear] at hg

end ArnoldCounterexample.Quadric

end

end OAI


