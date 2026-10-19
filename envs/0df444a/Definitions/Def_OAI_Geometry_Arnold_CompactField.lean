-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_CompactField
-- name    : OAI_Geometry_Arnold_CompactField
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:55:22.329246+00:00
-- url     : https://prove2.me/theorems/c1ee4144-6fd3-4952-9b53-7e384126f9d9
-- title:
--   A compactly supported, phase-equivariant Hamiltonian vector field agreeing with the core field near the unit quadric
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$, $B(z,w)=\sum_jz_jw_j$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$ is the projective quadric. Let $K$ be the potential and $Y$ its Hamiltonian field, so that $\omega(Y,\cdot)=dK$, and let $L,R$ be the sphere factors.
--
--   1. **Cut-off field.** Let $\chi$ be a smooth bump on $\mathbb{R}$ equal to $1$ on $[-4,4]$ and vanishing outside $(-8,8)$. Define
--   $$
--   X(z)=\chi\bigl(|z|^2\bigr)\,Y(z).
--   $$
--   2. **Properties of $X$.**
--      - $X$ is smooth, compactly supported and globally Lipschitz.
--      - $X=Y$ near every $z$ with $|z|^2<4$, so $\omega(X(w),\cdot)=dK(w)$ for $w$ near such $z$.
--      - $X(z)$ is skew at $z$ (tangent to spheres and to the quadric cone).
--      - $X(z)=0$ whenever $z_1=\dots=z_4=0$; in particular $X(0)=0$.
--   3. **Phase behaviour.** For $c\in\mathbb{C}$, the plane coordinates and the sphere factors scale by $|c|^2$. For $|c|=1$, the quantities $|L|^2$, $\langle L,R\rangle$ and $K$ are invariant, and
--   $$
--   Y(cz)=c\,Y(z),\qquad X(cz)=c\,X(z).
--   $$
--
--   $X$ is a globally Lipschitz Hamiltonian field on $\mathbb{C}^5$ that agrees with the geometric field near the unit quadric. This makes fixed-point iterations and implicit integration schemes for it well defined, and phase equivariance lets everything descend to $Q_3$.
--
--   **Formalization Note** The bump is `ContDiffBump (0 : ℝ)` with radii $4$ and $8$, and the Lipschitz constant comes from `ContDiff.lipschitzWith_of_hasCompactSupport`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/CompactField.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/CompactField.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology NNReal
open Set Filter

def cutoff : ContDiffBump (0 : ℝ) := ⟨4, 8, by norm_num, by norm_num⟩

def vectorField (z : CV) : CV := cutoff (normSquared z) • core z

lemma cutoff_eq_one {z : CV} (hz : normSquared z ≤ 4) : cutoff (normSquared z) = 1 := by
  apply cutoff.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (normSquared_nonneg z), cutoff] using hz

lemma vectorField_smooth : ContDiff ℝ ∞ vectorField :=
  (cutoff.contDiff.comp normSquared_smooth).smul core_smooth

lemma norm_bound_of_normSquared {z : CV} {R : ℝ} (hR : 0 ≤ R) (hz : normSquared z ≤ R^2) : ‖z‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  have hi : Complex.normSq (z i) ≤ normSquared z :=
    Finset.single_le_sum (fun j _ ↦ Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at hi
  nlinarith [norm_nonneg (z i)]

lemma vectorField_compact : HasCompactSupport vectorField := by
  apply (isCompact_closedBall (0 : CV) 4).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hn : normSquared z < 8 := by
    by_contra hh
    have hc : cutoff (normSquared z) = 0 := by
      apply cutoff.zero_of_le_dist
      simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (normSquared_nonneg z), cutoff] using le_of_not_gt hh
    exact hz (by simp [vectorField, hc])
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_bound_of_normSquared (by norm_num : (0 : ℝ) ≤ 4) (by nlinarith)

lemma vectorField_lipschitz : ∃ C : ℝ≥0, LipschitzWith C vectorField :=
  ContDiff.lipschitzWith_of_hasCompactSupport vectorField_compact vectorField_smooth (by simp)

lemma vectorField_local_core {z : CV} (hz : normSquared z < 4) :
    vectorField =ᶠ[𝓝 z] core := by
  filter_upwards [normSquared_smooth.continuous.continuousAt.eventually (Iio_mem_nhds hz)] with w hw
  simp only [vectorField, cutoff_eq_one hw.le, one_smul]

lemma vectorField_hamiltonian {z : CV} (hz : normSquared z < 4) :
    ∀ᶠ w in 𝓝 z, symplectic (vectorField w) = fderiv ℝ potential w := by
  filter_upwards [vectorField_local_core hz] with w hw
  rw [hw, core_hamiltonian]

lemma vectorField_skew (z : CV) : SkewAt z (vectorField z) := skewAt_smul (core_skew z) _

lemma vectorField_zero_rest (z : CV) (hz : ∀ i, i ≠ 0 → z i = 0) : vectorField z = 0 := by
  have hL (i : Fin 3) : leftOperator i z = 0 := by
    fin_cases i <;> simp [leftOperator, rotor_apply, hz, Pi.single_zero]
  have hR (i : Fin 3) : rightOperator i z = 0 := by
    fin_cases i <;> simp [rightOperator, rotor_apply, hz, Pi.single_zero]
  simp [vectorField, core, mixedField, selfField, hL, hR]

lemma vectorField_zero : vectorField 0 = 0 :=
  vectorField_zero_rest 0 (by simp)

lemma moment_scale (a b : Fin 5) (c : ℂ) (z : CV) : moment a b (c • z) = Complex.normSq c * moment a b z := by
  simp only [moment, Pi.smul_apply, smul_eq_mul, star_mul]
  rw [show star (z a) * star c * (c * z b) = (star c * c) * (star (z a) * z b) by ring,
    show star c * c = (Complex.normSq c : ℂ) from Complex.normSq_eq_conj_mul_self.symm]
  simp [Complex.mul_im]
  ring

lemma left_scale (c : ℂ) (z : CV) : leftSphere (c • z) = Complex.normSq c • leftSphere z := by
  ext i
  fin_cases i <;> simp [leftSphere, moment_scale, mul_add, mul_sub]

lemma right_scale (c : ℂ) (z : CV) : rightSphere (c • z) = Complex.normSq c • rightSphere z := by
  ext i
  fin_cases i <;> simp [rightSphere, moment_scale, mul_add, mul_sub]

lemma casimir_phase (c : ℂ) (hc : Complex.normSq c = 1) (z : CV) : casimir (c • z) = casimir z := by
  simp only [casimir, left_scale, hc, one_smul]

lemma pairing_phase (c : ℂ) (hc : Complex.normSq c = 1) (z : CV) : pairing (c • z) = pairing z := by
  simp only [pairing, left_scale, right_scale, hc, one_smul]

lemma core_phase (c : ℂ) (hc : Complex.normSq c = 1) (z : CV) : core (c • z) = c • core z := by
  have hm : mixedField (c • z) = c • mixedField z := by
    simp only [mixedField, left_scale, right_scale, hc, one_smul, left_phase, right_phase,
      Finset.smul_sum, smul_add, smul_comm c]
  have hs : selfField (c • z) = c • selfField z := by
    simp only [selfField, left_scale, hc, one_smul, left_phase, Finset.smul_sum, smul_comm c]
  simp only [core, left_phase, right_phase, casimir_phase c hc, pairing_phase c hc,
    hm, hs, smul_add, smul_sub, smul_comm c]

lemma vectorField_phase (c : ℂ) (hc : Complex.normSq c = 1) (z : CV) :
    vectorField (c • z) = c • vectorField z := by
  simp only [vectorField, normSquared_smul, hc, one_mul, core_phase c hc, smul_comm c]

lemma potential_phase (c : ℂ) (hc : Complex.normSq c = 1) (z : CV) : potential (c • z) = potential z := by
  simp only [potential, left_scale, right_scale, hc, one_smul, casimir_phase c hc, pairing_phase c hc]

end ArnoldCounterexample.Field

end

end OAI


