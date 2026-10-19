-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Tangent
-- name    : OAI_Geometry_Arnold_Tangent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:24:47.919896+00:00
-- url     : https://prove2.me/theorems/cbe52d77-352b-4ca8-8f4e-1fe7d63c77ca
-- title:
--   Normalization, tangent curves and compactness of the unit isotropic quadric
-- statement:
--   Write $q(z)=\sum_{j=0}^4z_j^2$ and $|z|^2=\sum_j|z_j|^2$ for $z\in\mathbb{C}^5$. The quadric is $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$. Its points are represented by unit isotropic vectors $z$, i.e. $|z|^2=1$ and $q(z)=0$, which form the unit quadric $S$, and $\pi:S\to Q_3$ is the projection $z\mapsto[z]$. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0$ and $\sum_jz_jv_j=0$. The form $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$ is the Fubini–Study form on horizontal vectors.
--
--   1. **Smoothness.** $|z|^2$ and $q$ are smooth on $\mathbb{C}^5$, viewed as $\mathbb{R}^{10}$. The derivative of $|z|^2$ is $v\mapsto\sum_j2(\operatorname{Re}z_j\operatorname{Re}v_j+\operatorname{Im}z_j\operatorname{Im}v_j)$.
--   2. **Normalization.** $N(w)=|w|^{-1}w$ sends every nonzero isotropic vector to the unit quadric and fixes points of the unit quadric.
--   3. **Tangent curves.** For $z\in S$ and horizontal $v$, the polynomial curve
--   $$
--   \gamma(t)=z+t\,v-\frac{t^2}{2}\,q(v)\,\bar z\qquad(t\in\mathbb{R})
--   $$
--   is nonzero and isotropic, with $\gamma(0)=z$. Its normalization $N(\gamma(t))$ is a curve in $S$ starting at $z$.
--   4. **Compactness.** The unit quadric is closed, contained in the unit ball for the max norm, and compact.
--   5. **A base point.** $(1,i,0,0,0)$ is a nonzero isotropic vector. Its normalization is a point of $S$, so $S$ is nonempty.
--
--   Tangent curves realize every horizontal vector as a velocity on the quadric, and compactness of $S$ is used for extremal and averaging arguments on $Q_3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Tangent.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Tangent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

def normSquaredDiff (z : CV) : CV →L[ℝ] ℝ :=
  ∑ j, ((2 * (z j).re) • realCoord j + (2 * (z j).im) • imagCoord j)

lemma normSquared_smooth : ContDiff ℝ ∞ normSquared := by
  unfold normSquared
  simp only [Complex.normSq_apply]
  fun_prop

lemma quadricPolynomial_smooth : ContDiff ℝ ∞ quadricPolynomial := by
  unfold quadricPolynomial
  fun_prop

/-- Normalizing a nonzero isotropic vector gives a legitimate unit representative. -/
def normalize (w : CV) : CV := (Real.sqrt (normSquared w))⁻¹ • w

lemma normalize_unit {w : CV} (hw : w ≠ 0) (hp : quadricPolynomial w = 0) :
    IsUnitQuadric (normalize w) := by
  have hn : 0 < normSquared w := normSquared_pos hw
  have hs : Real.sqrt (normSquared w) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have heq : normalize w = (((Real.sqrt (normSquared w))⁻¹ : ℝ) : ℂ) • w := rfl
  rw [heq]
  constructor
  · rw [normSquared_smul, Complex.normSq_ofReal]
    field_simp [hs]
    nlinarith only [Real.sq_sqrt hn.le]
  · rw [quadricPolynomial_smul, hp, mul_zero]

lemma normalize_unit_self (z : UnitQuadric) : normalize (z : CV) = z := by
  simp [normalize, z.property.1]

/-- A polynomial curve on the nonzero isotropic cone realizing a horizontal vector. -/
def rawTangentCurve (z v : CV) (t : ℝ) : CV :=
  z + t • v - (t ^ 2 / 2) • (quadricPolynomial v • star z)

lemma rawTangentCurve_eq (z v : CV) (t : ℝ) :
    rawTangentCurve z v t = localSection z ((t : ℂ) • v) := by
  rw [localSection, quadricPolynomial_smul]
  funext j
  simp only [rawTangentCurve, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

@[simp] lemma rawTangentCurve_zero (z v : CV) : rawTangentCurve z v 0 = z := by
  simp [rawTangentCurve]

lemma rawTangentCurve_ne_zero (z : UnitQuadric) {v : CV} (hv : Horizontal z v) (t : ℝ) :
    rawTangentCurve z v t ≠ 0 := by
  rw [rawTangentCurve_eq]
  exact localSection_ne_zero z (horizontal_smul hv (t : ℂ))

lemma rawTangentCurve_polynomial (z : UnitQuadric) {v : CV} (hv : Horizontal z v) (t : ℝ) :
    quadricPolynomial (rawTangentCurve z v t) = 0 := by
  rw [rawTangentCurve_eq]
  exact localSection_on_quadric z (horizontal_smul hv (t : ℂ))

/-- A genuine curve in the unit cone, not an assumed tangent parametrization. -/
def tangentCurve (z : UnitQuadric) (v : CV) (hv : Horizontal z v) (t : ℝ) : UnitQuadric :=
  ⟨normalize (rawTangentCurve z v t), normalize_unit (rawTangentCurve_ne_zero z hv t)
    (rawTangentCurve_polynomial z hv t)⟩

@[simp] lemma tangentCurve_zero (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    tangentCurve z v hv 0 = z := by
  apply Subtype.ext
  exact (congrArg normalize (rawTangentCurve_zero z v)).trans (normalize_unit_self z)

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

theorem isClosed_unitQuadric : IsClosed {z : CV | IsUnitQuadric z} :=
  (isClosed_eq normSquared_smooth.continuous continuous_const).inter
    (isClosed_eq quadricPolynomial_smooth.continuous continuous_const)

lemma unitQuadric_norm_le (z : UnitQuadric) : ‖(z : CV)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  have hj : Complex.normSq ((z : CV) j) ≤ normSquared z :=
    Finset.single_le_sum (fun i _ ↦ Complex.normSq_nonneg ((z : CV) i)) (Finset.mem_univ j)
  rw [z.property.1, Complex.normSq_eq_norm_sq] at hj
  nlinarith [norm_nonneg ((z : CV) j)]

/-- Compactness of the literal unit cone, obtained from finite-dimensional
Heine--Borel and the exact polynomial constraints. -/
theorem isCompact_unitQuadric : IsCompact {z : CV | IsUnitQuadric z} := by
  apply (isCompact_closedBall (0 : CV) 1).of_isClosed_subset isClosed_unitQuadric
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using unitQuadric_norm_le ⟨z, hz⟩

instance unitQuadric_compactSpace : CompactSpace UnitQuadric :=
  isCompact_iff_compactSpace.mp isCompact_unitQuadric

def baseVector : CV := ![1, Complex.I, 0, 0, 0]

lemma baseVector_ne_zero : baseVector ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [baseVector] at hh

lemma baseVector_polynomial : quadricPolynomial baseVector = 0 := by
  norm_num [quadricPolynomial, baseVector, Fin.sum_univ_five, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Complex.I_sq]

def basePoint : UnitQuadric := ⟨normalize baseVector,
  normalize_unit baseVector_ne_zero baseVector_polynomial⟩

instance unitQuadric_nonempty : Nonempty UnitQuadric := ⟨basePoint⟩

end ArnoldCounterexample.Quadric

end

end OAI


