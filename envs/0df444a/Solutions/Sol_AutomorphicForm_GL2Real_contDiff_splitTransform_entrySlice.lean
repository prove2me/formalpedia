-- Prove2me | solution 1 for AutomorphicForm.GL2Real.contDiff_splitTransform_entrySlice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/99973166-e58f-5551-9a12-6de0d2f708c5

import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice

set_option autoImplicit false

open MeasureTheory Set Function
open scoped Convolution

noncomputable section

namespace AutomorphicForm
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular splitTransform entrySlice"
namespace SplitRegularity
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real"

def ent (a₁ a₂ θ u : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![Real.cos θ ^ 2 * a₁ + Real.sin θ ^ 2 * a₂ + Real.cos θ * Real.sin θ * u,
      Real.cos θ * Real.sin θ * (a₂ - a₁) + Real.cos θ ^ 2 * u],
    ![Real.cos θ * Real.sin θ * (a₂ - a₁) - Real.sin θ ^ 2 * u,
      Real.sin θ ^ 2 * a₁ + Real.cos θ ^ 2 * a₂ - Real.cos θ * Real.sin θ * u]]

@[scoped simp] lemma ent_00 (a₁ a₂ θ u : ℝ) : ent a₁ a₂ θ u 0 0 =
    Real.cos θ ^ 2 * a₁ + Real.sin θ ^ 2 * a₂ + Real.cos θ * Real.sin θ * u := rfl
@[scoped simp] lemma ent_01 (a₁ a₂ θ u : ℝ) : ent a₁ a₂ θ u 0 1 =
    Real.cos θ * Real.sin θ * (a₂ - a₁) + Real.cos θ ^ 2 * u := rfl
@[scoped simp] lemma ent_10 (a₁ a₂ θ u : ℝ) : ent a₁ a₂ θ u 1 0 =
    Real.cos θ * Real.sin θ * (a₂ - a₁) - Real.sin θ ^ 2 * u := rfl
@[scoped simp] lemma ent_11 (a₁ a₂ θ u : ℝ) : ent a₁ a₂ θ u 1 1 =
    Real.sin θ ^ 2 * a₁ + Real.cos θ ^ 2 * a₂ - Real.cos θ * Real.sin θ * u := rfl

lemma coe_rotation (θ : ℝ) :
    ((rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  simp [rotation]

lemma coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] := by
  simp [upperTriangular]

lemma rotation_mul_rotation (θ φ : ℝ) : rotation θ * rotation φ = rotation (θ + φ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_rotation, Real.cos_add, Real.sin_add]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma rotation_zero : rotation 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [coe_rotation, Real.cos_zero, Real.sin_zero, neg_zero,
    Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

lemma rotation_inv (θ : ℝ) : (rotation θ)⁻¹ = rotation (-θ) := by
  rw [inv_eq_iff_mul_eq_one, rotation_mul_rotation, add_neg_cancel, rotation_zero]

lemma rotation_add_two_pi (θ : ℝ) : rotation (θ + 2 * Real.pi) = rotation θ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [coe_rotation, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma coe_conj (a₁ a₂ u θ : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of (ent a₁ a₂ θ u) := by
  rw [rotation_inv]
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_rotation, coe_upperTriangular, Real.cos_neg,
    Real.sin_neg, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ent] <;> ring

lemma entrySlice_conj {P : Type*} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P)
    (a₁ a₂ u θ : ℝ) (h : a₁ * a₂ ≠ 0) :
    entrySlice Φ p (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) =
      Φ (ent a₁ a₂ θ u, p) := by
  simp only [entrySlice, coe_conj]
  rfl

lemma ent_det (a₁ a₂ θ u : ℝ) : Matrix.det (Matrix.of (ent a₁ a₂ θ u)) = a₁ * a₂ := by
  rw [Matrix.det_fin_two, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply]
  have h := Real.cos_sq_add_sin_sq θ
  simp only [ent_00, ent_01, ent_10, ent_11]
  linear_combination (a₁ * a₂ * (Real.cos θ ^ 2 + Real.sin θ ^ 2 + 1)) * h

lemma ent_trace (a₁ a₂ θ u : ℝ) : ent a₁ a₂ θ u 0 0 + ent a₁ a₂ θ u 1 1 = a₁ + a₂ := by
  have h := Real.cos_sq_add_sin_sq θ
  simp only [ent_00, ent_11]
  linear_combination (a₁ + a₂) * h

lemma ent_sub (a₁ a₂ θ u : ℝ) : ent a₁ a₂ θ u 0 1 - ent a₁ a₂ θ u 1 0 = u := by
  have h := Real.cos_sq_add_sin_sq θ
  simp only [ent_01, ent_10]
  linear_combination u * h

lemma ent_add_two_pi (a₁ a₂ θ u : ℝ) : ent a₁ a₂ (θ + 2 * Real.pi) u = ent a₁ a₂ θ u := by
  simp only [ent, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma contDiff_ent {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {a b θ u : X → ℝ} (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) (hθ : ContDiff ℝ n θ)
    (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => ent (a x) (b x) (θ x) (u x)) := by
  have hc : ContDiff ℝ n (fun x => Real.cos (θ x)) := Real.contDiff_cos.comp hθ
  have hs : ContDiff ℝ n (fun x => Real.sin (θ x)) := Real.contDiff_sin.comp hθ
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · exact ((hc.pow 2).mul ha).add ((hs.pow 2).mul hb) |>.add ((hc.mul hs).mul hu)
  · exact ((hc.mul hs).mul (hb.sub ha)).add ((hc.pow 2).mul hu)
  · exact ((hc.mul hs).mul (hb.sub ha)).sub ((hs.pow 2).mul hu)
  · exact (((hs.pow 2).mul ha).add ((hc.pow 2).mul hb)).sub ((hc.mul hs).mul hu)

lemma continuous_ent {X : Type*} [TopologicalSpace X]
    {a b θ u : X → ℝ} (ha : Continuous a) (hb : Continuous b) (hθ : Continuous θ)
    (hu : Continuous u) :
    Continuous (fun x => ent (a x) (b x) (θ x) (u x)) := by
  have hc : Continuous (fun x => Real.cos (θ x)) := Real.continuous_cos.comp hθ
  have hs : Continuous (fun x => Real.sin (θ x)) := Real.continuous_sin.comp hθ
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  · exact ((hc.pow 2).mul ha).add ((hs.pow 2).mul hb) |>.add ((hc.mul hs).mul hu)
  · exact ((hc.mul hs).mul (hb.sub ha)).add ((hc.pow 2).mul hu)
  · exact ((hc.mul hs).mul (hb.sub ha)).sub ((hs.pow 2).mul hu)
  · exact (((hs.pow 2).mul ha).add ((hc.pow 2).mul hb)).sub ((hc.mul hs).mul hu)

section Support

variable {P : Type*} [TopologicalSpace P]

lemma apply_eq_zero_of_notMem_tsupport {X : Type*} [TopologicalSpace X] (Φ : X → ℂ) {x : X}
    (hx : x ∉ tsupport Φ) : Φ x = 0 := by
  by_contra h
  exact hx (subset_tsupport _ h)

lemma exists_bounds (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ ∀ m p, Φ (m, p) ≠ 0 →
      (∀ i j, |m i j| ≤ B) ∧ δ ≤ |Matrix.det (Matrix.of m)| ∧ p ∈ Prod.snd '' tsupport Φ := by
  set K := tsupport Φ with hK
  have hKc : IsCompact K := hΦc.isCompact
  set K₁ : Set (Fin 2 → Fin 2 → ℝ) := Prod.fst '' K with hK₁
  have hK₁c : IsCompact K₁ := hKc.image continuous_fst
  obtain ⟨B₀, hB₀⟩ := hK₁c.isBounded.exists_norm_le

  have hent : ∀ m ∈ K₁, ∀ i j, |m i j| ≤ max B₀ 1 := by
    intro m hm i j
    have h1 : ‖m i j‖ ≤ ‖m i‖ := norm_le_pi_norm (m i) j
    have h2 : ‖m i‖ ≤ ‖m‖ := norm_le_pi_norm m i
    have h3 := hB₀ m hm
    rw [Real.norm_eq_abs] at h1
    exact le_trans (h1.trans (h2.trans h3)) (le_max_left _ _)

  have hmem : ∀ m p, Φ (m, p) ≠ 0 → (m, p) ∈ K := fun m p h => subset_tsupport _ h

  set d : (Fin 2 → Fin 2 → ℝ) → ℝ := fun m => |m 0 0 * m 1 1 - m 0 1 * m 1 0| with hd
  have hd_eq : ∀ m : Fin 2 → Fin 2 → ℝ, |Matrix.det (Matrix.of m)| = d m := by
    intro m
    simp only [hd, Matrix.det_fin_two, Matrix.of_apply]
  have hd_cont : Continuous d := by
    simp only [hd]
    fun_prop
  have hd_pos : ∀ m ∈ K₁, 0 < d m := by
    rintro m ⟨q, hq, rfl⟩
    have hu := hΦU hq
    simp only [mem_setOf_eq] at hu
    rw [← hd_eq]
    exact abs_pos.2 hu.ne_zero
  by_cases hne : K₁.Nonempty
  · obtain ⟨m₀, hm₀, hmin⟩ := hK₁c.exists_isMinOn hne hd_cont.continuousOn
    refine ⟨max B₀ 1, d m₀, lt_of_lt_of_le one_pos (le_max_right _ _), hd_pos m₀ hm₀, ?_⟩
    intro m p h
    have hmK : m ∈ K₁ := ⟨(m, p), hmem m p h, rfl⟩
    refine ⟨hent m hmK, ?_, ⟨(m, p), hmem m p h, rfl⟩⟩
    rw [hd_eq]
    exact hmin hmK
  · refine ⟨max B₀ 1, 1, lt_of_lt_of_le one_pos (le_max_right _ _), one_pos, ?_⟩
    intro m p h
    exact absurd ⟨m, (m, p), hmem m p h, rfl⟩ hne

lemma conseq {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {B δ : ℝ} (hB : 0 < B)
    (hBδ : ∀ m p, Φ (m, p) ≠ 0 →
      (∀ i j, |m i j| ≤ B) ∧ δ ≤ |Matrix.det (Matrix.of m)| ∧ p ∈ Prod.snd '' tsupport Φ)
    {a₁ a₂ θ u : ℝ} {p : P} (h : Φ (ent a₁ a₂ θ u, p) ≠ 0) :
    |u| ≤ 2 * B ∧ |a₁| ≤ 3 * B ∧ |a₂| ≤ 3 * B ∧ δ ≤ |a₁ * a₂| ∧ p ∈ Prod.snd '' tsupport Φ := by
  obtain ⟨hentry, hdet, hp⟩ := hBδ _ _ h
  rw [ent_det] at hdet
  have h00 := hentry 0 0
  have h01 := hentry 0 1
  have h10 := hentry 1 0
  have h11 := hentry 1 1
  have hu : |u| ≤ 2 * B := by
    rw [← ent_sub a₁ a₂ θ u]
    calc |ent a₁ a₂ θ u 0 1 - ent a₁ a₂ θ u 1 0|
        ≤ |ent a₁ a₂ θ u 0 1| + |ent a₁ a₂ θ u 1 0| := abs_sub _ _
      _ ≤ B + B := add_le_add h01 h10
      _ = 2 * B := by ring
  have htr : |a₁ + a₂| ≤ 2 * B := by
    rw [← ent_trace a₁ a₂ θ u]
    calc |ent a₁ a₂ θ u 0 0 + ent a₁ a₂ θ u 1 1|
        ≤ |ent a₁ a₂ θ u 0 0| + |ent a₁ a₂ θ u 1 1| := abs_add_le _ _
      _ ≤ B + B := add_le_add h00 h11
      _ = 2 * B := by ring
  have hdet' : |a₁ * a₂| ≤ 2 * B ^ 2 := by
    rw [← ent_det a₁ a₂ θ u, Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    calc |ent a₁ a₂ θ u 0 0 * ent a₁ a₂ θ u 1 1 - ent a₁ a₂ θ u 0 1 * ent a₁ a₂ θ u 1 0|
        ≤ |ent a₁ a₂ θ u 0 0 * ent a₁ a₂ θ u 1 1| + |ent a₁ a₂ θ u 0 1 * ent a₁ a₂ θ u 1 0| :=
          abs_sub _ _
      _ = |ent a₁ a₂ θ u 0 0| * |ent a₁ a₂ θ u 1 1| + |ent a₁ a₂ θ u 0 1| * |ent a₁ a₂ θ u 1 0| := by
          rw [abs_mul, abs_mul]
      _ ≤ B * B + B * B := by
          gcongr
      _ = 2 * B ^ 2 := by ring
  have hsq : a₁ ^ 2 + a₂ ^ 2 ≤ 8 * B ^ 2 := by
    have e : a₁ ^ 2 + a₂ ^ 2 = (a₁ + a₂) ^ 2 - 2 * (a₁ * a₂) := by ring
    have h1 : (a₁ + a₂) ^ 2 ≤ (2 * B) ^ 2 := by
      rw [← sq_abs (a₁ + a₂)]
      exact pow_le_pow_left₀ (abs_nonneg _) htr 2
    have h2 : -(2 * (a₁ * a₂)) ≤ 2 * (2 * B ^ 2) := by
      have := neg_abs_le (a₁ * a₂)
      linarith
    rw [e]
    linarith
  have ha₁ : |a₁| ≤ 3 * B := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (a₁ ^ 2) ≤ Real.sqrt ((3 * B) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg a₂]
      _ = 3 * B := Real.sqrt_sq (by linarith)
  have ha₂ : |a₂| ≤ 3 * B := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (a₂ ^ 2) ≤ Real.sqrt ((3 * B) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg a₁]
      _ = 3 * B := Real.sqrt_sq (by linarith)
  exact ⟨hu, ha₁, ha₂, hdet, hp⟩

lemma integrable_restrict_prod {F : ℝ × ℝ → ℂ} (hF : Continuous F) {B lo hi : ℝ}
    (hFB : ∀ t : ℝ × ℝ, B < |t.2| → F t = 0) {s : Set ℝ}
    (hsub : s ⊆ Icc lo hi) :
    Integrable F ((volume.restrict s).prod volume) := by
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
  change IntegrableOn F (s ×ˢ univ) volume
  have hbig : IntegrableOn F (Icc lo hi ×ˢ univ) volume := by
    rw [← integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)]
    have heq : indicator (Icc lo hi ×ˢ (univ : Set ℝ)) F =
        indicator (Icc lo hi ×ˢ Icc (-B) B) F := by
      funext t
      by_cases h1 : t.1 ∈ Icc lo hi
      · by_cases h2 : t.2 ∈ Icc (-B) B
        · rw [indicator_of_mem (mem_prod.2 ⟨h1, mem_univ _⟩),
            indicator_of_mem (mem_prod.2 ⟨h1, h2⟩)]
        · have : B < |t.2| := by
            simp only [mem_Icc, not_and_or, not_le] at h2
            rcases h2 with h2 | h2
            · exact lt_of_lt_of_le (by linarith) (neg_le_abs t.2)
            · exact lt_of_lt_of_le h2 (le_abs_self _)
          rw [indicator_of_mem (mem_prod.2 ⟨h1, mem_univ _⟩),
            indicator_of_notMem (fun h => h2 (mem_prod.1 h).2), hFB t this]
      · rw [indicator_of_notMem (fun h => h1 (mem_prod.1 h).1),
          indicator_of_notMem (fun h => h1 (mem_prod.1 h).1)]
    rw [heq, integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)]
    exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hbig.mono_set (prod_mono hsub subset_rfl)

end Support

section Conv

variable {P : Type*}

noncomputable def bump : ContDiffBump (Real.pi : ℝ) := ⟨Real.pi, Real.pi + 1, Real.pi_pos, by linarith⟩

lemma bump_eq_one {θ : ℝ} (h : θ ∈ Icc 0 (2 * Real.pi)) : (bump : ℝ → ℝ) θ = 1 := by
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  show |θ - Real.pi| ≤ Real.pi
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma bump_eq_zero {θ : ℝ} (h : Real.pi + 1 ≤ |θ - Real.pi|) : (bump : ℝ → ℝ) θ = 0 := by
  apply bump.zero_of_le_dist
  rw [Real.dist_eq]
  exact h

noncomputable def kern (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (q : ℝ × ℝ × P) (t : ℝ × ℝ) : ℂ :=
  (((bump : ℝ → ℝ) (-t.1) : ℝ) : ℂ) * Φ (ent q.1 q.2.1 (-t.1) (-t.2), q.2.2)

noncomputable def rough : ℝ × ℝ → ℝ := indicator (Icc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set ℝ)) (fun _ => 1)

noncomputable def conv (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (q : ℝ × ℝ × P) : ℂ :=
  (rough ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure (ℝ × ℝ))] kern Φ q) 0

lemma rough_smul_kern (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (q : ℝ × ℝ × P) (t : ℝ × ℝ) :
    rough t • kern Φ q (0 - t) =
      indicator (Icc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set ℝ))
        (fun t : ℝ × ℝ => Φ (ent q.1 q.2.1 t.1 t.2, q.2.2)) t := by
  by_cases ht : t ∈ Icc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set ℝ)
  · rw [indicator_of_mem ht, rough, indicator_of_mem ht]
    simp only [kern, zero_sub, Prod.fst_neg, Prod.snd_neg, neg_neg, one_smul]
    rw [bump_eq_one (mem_prod.1 ht).1]
    simp
  · rw [indicator_of_notMem ht, rough, indicator_of_notMem ht, zero_smul]

lemma conv_eq (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (q : ℝ × ℝ × P) :
    conv Φ q = ∫ t : ℝ × ℝ, indicator (Icc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set ℝ))
        (fun t : ℝ × ℝ => Φ (ent q.1 q.2.1 t.1 t.2, q.2.2)) t := by
  rw [conv, convolution_lsmul]
  simp_rw [rough_smul_kern]

lemma measurableSet_strip : MeasurableSet (Icc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set ℝ)) :=
  measurableSet_Icc.prod MeasurableSet.univ

lemma conv_eq_iterated (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (q : ℝ × ℝ × P)
    (hint : Integrable (fun t : ℝ × ℝ => Φ (ent q.1 q.2.1 t.1 t.2, q.2.2))
      ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))).prod volume)) :
    conv Φ q = ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, Φ (ent q.1 q.2.1 θ u, q.2.2) := by
  rw [conv_eq, integral_indicator measurableSet_strip, Measure.volume_eq_prod,
    ← Measure.restrict_prod_eq_prod_univ, integral_prod _ hint,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  exact integral_Icc_eq_integral_Ioc

lemma exists_ne_zero_of_conv_ne_zero (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) {q : ℝ × ℝ × P}
    (h : conv Φ q ≠ 0) : ∃ θ u : ℝ, Φ (ent q.1 q.2.1 θ u, q.2.2) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [conv_eq]
  have : (fun t : ℝ × ℝ => Φ (ent q.1 q.2.1 t.1 t.2, q.2.2)) = 0 := by
    funext t
    exact hcon t.1 t.2
  rw [this]
  simp

lemma contDiff_kern [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (↿(kern Φ) : (ℝ × ℝ × P) × (ℝ × ℝ) → ℂ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : (ℝ × ℝ × P) × (ℝ × ℝ) => (((bump : ℝ → ℝ) (-x.2.1) : ℝ) : ℂ)) := by
    refine (Complex.ofRealCLM.contDiff.of_le le_top).comp ?_
    exact bump.contDiff.comp (contDiff_neg.comp (contDiff_fst.comp contDiff_snd))
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : (ℝ × ℝ × P) × (ℝ × ℝ) => Φ (ent x.1.1 x.1.2.1 (-x.2.1) (-x.2.2), x.1.2.2)) := by
    refine hΦ.comp ?_
    refine ContDiff.prodMk ?_ (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))
    exact contDiff_ent (contDiff_fst.comp contDiff_fst)
      (contDiff_fst.comp (contDiff_snd.comp contDiff_fst))
      (contDiff_neg.comp (contDiff_fst.comp contDiff_snd))
      (contDiff_neg.comp (contDiff_snd.comp contDiff_snd))
  exact h1.mul h2

lemma continuous_kern [TopologicalSpace P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ) :
    Continuous (↿(kern Φ) : (ℝ × ℝ × P) × (ℝ × ℝ) → ℂ) := by
  have h1 : Continuous
      (fun x : (ℝ × ℝ × P) × (ℝ × ℝ) => (((bump : ℝ → ℝ) (-x.2.1) : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact bump.continuous.comp (continuous_neg.comp (continuous_fst.comp continuous_snd))
  have h2 : Continuous
      (fun x : (ℝ × ℝ × P) × (ℝ × ℝ) => Φ (ent x.1.1 x.1.2.1 (-x.2.1) (-x.2.2), x.1.2.2)) := by
    refine hΦ.comp ?_
    refine Continuous.prodMk ?_ (continuous_snd.comp (continuous_snd.comp continuous_fst))
    exact continuous_ent (continuous_fst.comp continuous_fst)
      (continuous_fst.comp (continuous_snd.comp continuous_fst))
      (continuous_neg.comp (continuous_fst.comp continuous_snd))
      (continuous_neg.comp (continuous_snd.comp continuous_snd))
  exact h1.mul h2

lemma contDiff_conv [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {B δ : ℝ} (hB : 0 < B)
    (hBδ : ∀ m p, Φ (m, p) ≠ 0 →
      (∀ i j, |m i j| ≤ B) ∧ δ ≤ |Matrix.det (Matrix.of m)| ∧ p ∈ Prod.snd '' tsupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (conv Φ) := by
  set k : Set (ℝ × ℝ) :=
    Metric.closedBall (-Real.pi) (Real.pi + 1) ×ˢ Metric.closedBall (0 : ℝ) (2 * B) with hk_def
  have hk : IsCompact k := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hgs : ∀ q : ℝ × ℝ × P, ∀ t : ℝ × ℝ, q ∈ (univ : Set (ℝ × ℝ × P)) → t ∉ k →
      kern Φ q t = 0 := by
    intro q t _ ht
    simp only [hk_def, mem_prod, Metric.mem_closedBall, not_and_or, not_le] at ht
    rcases ht with ht | ht
    ·
      have : Real.pi + 1 ≤ |(-t.1) - Real.pi| := by
        rw [Real.dist_eq] at ht
        have e : (-t.1) - Real.pi = -(t.1 - -Real.pi) := by ring
        rw [e, abs_neg]
        exact ht.le
      simp [kern, bump_eq_zero this]
    ·
      have hzero : Φ (ent q.1 q.2.1 (-t.1) (-t.2), q.2.2) = 0 := by
        by_contra hne
        have := (conseq hB hBδ hne).1
        rw [abs_neg] at this
        rw [Real.dist_eq, sub_zero] at ht
        linarith
      simp [kern, hzero]
  have hf : LocallyIntegrable rough (volume : Measure (ℝ × ℝ)) :=
    (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_strip
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿(kern Φ)) ((univ : Set (ℝ × ℝ × P)) ×ˢ univ) :=
    (contDiff_kern Φ hΦ).contDiffOn
  have hmain := contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ) (n := (⊤ : ℕ∞)) (μ := (volume : Measure (ℝ × ℝ)))
    (v := fun _ : ℝ × ℝ × P => (0 : ℝ × ℝ)) contDiffOn_const isOpen_univ hk hgs hf hg
  rw [contDiffOn_univ] at hmain
  exact hmain

lemma splitTransform_eq_conv [TopologicalSpace P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    {B δ : ℝ} (hB : 0 < B)
    (hBδ : ∀ m p, Φ (m, p) ≠ 0 →
      (∀ i j, |m i j| ≤ B) ∧ δ ≤ |Matrix.det (Matrix.of m)| ∧ p ∈ Prod.snd '' tsupport Φ)
    (q : ℝ × ℝ × P) :
    splitTransform (entrySlice Φ q.2.2) q.1 q.2.1 = (1 / (2 * Real.pi) : ℂ) * conv Φ q := by
  rw [splitTransform]
  split_ifs with h
  · congr 1
    simp_rw [entrySlice_conj]
    symm
    apply conv_eq_iterated
    refine integrable_restrict_prod (B := 2 * B) (lo := 0) (hi := 2 * Real.pi) ?_ ?_ subset_rfl
    · exact hΦ.comp ((continuous_ent continuous_const continuous_const continuous_fst
        continuous_snd).prodMk continuous_const)
    · intro t ht
      by_contra hne
      have := (conseq hB hBδ hne).1
      linarith
  ·
    push Not at h
    have hzero : ∀ θ u : ℝ, Φ (ent q.1 q.2.1 θ u, q.2.2) = 0 := by
      intro θ u
      apply apply_eq_zero_of_notMem_tsupport
      intro hmem
      have hu := hΦU hmem
      simp only [mem_setOf_eq, ent_det, h] at hu
      exact not_isUnit_zero hu
    have : conv Φ q = 0 := by
      by_contra hne
      obtain ⟨θ, u, hθu⟩ := exists_ne_zero_of_conv_ne_zero Φ hne
      exact hθu (hzero θ u)
    rw [this, mul_zero]

end Conv

section Symmetry

variable {P : Type*} [TopologicalSpace P]

lemma upperTriangular_swap {a₁ a₂ : ℝ} (hne : a₁ ≠ a₂) (u : ℝ) (h : a₁ * a₂ ≠ 0)
    (h' : a₂ * a₁ ≠ 0) :
    upperTriangular a₂ a₁ u h' =
      rotation (Complex.arg ⟨u, a₂ - a₁⟩) * upperTriangular a₁ a₂ u h *
        (rotation (Complex.arg ⟨u, a₂ - a₁⟩))⁻¹ := by
  set z : ℂ := ⟨u, a₂ - a₁⟩ with hz_def
  have hz : z ≠ 0 := by
    intro h0
    apply hne
    have := congrArg Complex.im h0
    simp [hz_def] at this
    linarith
  set N : ℝ := ‖z‖ with hN
  have hN0 : N ≠ 0 := norm_ne_zero_iff.2 hz
  have hc : Real.cos (Complex.arg z) = u / N := by rw [Complex.cos_arg hz]
  have hs : Real.sin (Complex.arg z) = (a₂ - a₁) / N := by rw [Complex.sin_arg]
  have hNsq : N ^ 2 = u ^ 2 + (a₂ - a₁) ^ 2 := by
    rw [hN, Complex.sq_norm, Complex.normSq_apply]
    simp [hz_def]
    ring
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_conj, coe_upperTriangular, Matrix.of_apply]
  fin_cases i <;> fin_cases j
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Fin.zero_eta, ent_00, hc, hs]
    field_simp
    linear_combination a₂ * hNsq
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Fin.zero_eta, Fin.mk_one, ent_01, hc, hs]
    field_simp
    linear_combination u * hNsq
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.mk_one, Fin.zero_eta, ent_10, hc, hs]
    field_simp
    ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.mk_one, ent_11, hc, hs]
    field_simp
    linear_combination a₁ * hNsq

lemma splitTransform_symm (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ)
    {B δ : ℝ} (hB : 0 < B)
    (hBδ : ∀ m p, Φ (m, p) ≠ 0 →
      (∀ i j, |m i j| ≤ B) ∧ δ ≤ |Matrix.det (Matrix.of m)| ∧ p ∈ Prod.snd '' tsupport Φ)
    (a₁ a₂ : ℝ) (p : P) :
    splitTransform (entrySlice Φ p) a₂ a₁ = splitTransform (entrySlice Φ p) a₁ a₂ := by
  by_cases h : a₁ * a₂ ≠ 0
  swap
  · have h' : ¬ (a₂ * a₁ ≠ 0) := by rwa [mul_comm]
    rw [splitTransform, splitTransform, dif_neg h, dif_neg h']
  have h' : a₂ * a₁ ≠ 0 := by rwa [mul_comm]
  rw [splitTransform, splitTransform, dif_pos h', dif_pos h]
  congr 1
  by_cases hne : a₁ = a₂
  · subst hne
    rfl
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity

  set φ : ℝ → ℝ := fun u => Complex.arg ⟨u, a₂ - a₁⟩ with hφ_def
  have hφc : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro u
    have hmk : Continuous fun v : ℝ => (⟨v, a₂ - a₁⟩ : ℂ) := by
      have : (fun v : ℝ => (⟨v, a₂ - a₁⟩ : ℂ)) =
          fun v : ℝ => ((v : ℝ) : ℂ) + ((a₂ - a₁ : ℝ) : ℂ) * Complex.I := by
        funext v
        apply Complex.ext <;> simp
      rw [this]
      fun_prop
    refine (Complex.continuousAt_arg ?_).comp hmk.continuousAt
    rw [Complex.mem_slitPlane_iff]
    right
    show a₂ - a₁ ≠ 0
    exact sub_ne_zero.2 (Ne.symm hne)

  have hkey : ∀ θ u : ℝ,
      entrySlice Φ p (rotation θ * upperTriangular a₂ a₁ u h' * (rotation θ)⁻¹) =
        Φ (ent a₁ a₂ (θ + φ u) u, p) := by
    intro θ u
    rw [upperTriangular_swap hne u h h', ← entrySlice_conj Φ p a₁ a₂ u (θ + φ u) h,
      ← rotation_mul_rotation, mul_inv_rev]
    simp only [hφ_def, mul_assoc]
  simp_rw [hkey, entrySlice_conj]

  set F : ℝ → ℝ → ℂ := fun θ u => Φ (ent a₁ a₂ θ u, p) with hF
  have hper : ∀ u, Function.Periodic (fun θ => F θ u) (2 * Real.pi) := by
    intro u θ
    simp only [hF, ent_add_two_pi]

  have hvan : ∀ θ u : ℝ, 2 * B < |u| → F θ u = 0 := by
    intro θ u hu
    by_contra hne'
    have := (conseq hB hBδ hne').1
    linarith
  have hI1 : Integrable (uncurry fun θ u => F (θ + φ u) u)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
    refine integrable_restrict_prod (B := 2 * B) (lo := 0) (hi := 2 * Real.pi) ?_ ?_
      Ioc_subset_Icc_self
    · show Continuous fun t : ℝ × ℝ => Φ (ent a₁ a₂ (t.1 + φ t.2) t.2, p)
      exact hΦ.comp ((continuous_ent continuous_const continuous_const
        (continuous_fst.add (hφc.comp continuous_snd)) continuous_snd).prodMk continuous_const)
    · intro t ht
      exact hvan _ _ ht
  have hI2 : Integrable (uncurry F) ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
    refine integrable_restrict_prod (B := 2 * B) (lo := 0) (hi := 2 * Real.pi) ?_ ?_
      Ioc_subset_Icc_self
    · show Continuous fun t : ℝ × ℝ => Φ (ent a₁ a₂ t.1 t.2, p)
      exact hΦ.comp ((continuous_ent continuous_const continuous_const
        continuous_fst continuous_snd).prodMk continuous_const)
    · intro t ht
      exact hvan _ _ ht
  show ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, F (θ + φ u) u =
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ, F θ u
  rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π,
    integral_integral_swap hI1, integral_integral_swap hI2]
  congr 1
  funext u
  rw [← intervalIntegral.integral_of_le h2π, ← intervalIntegral.integral_of_le h2π,
    intervalIntegral.integral_comp_add_right (fun θ => F θ u) (φ u), zero_add,
    show 2 * Real.pi + φ u = φ u + 2 * Real.pi by ring,
    (hper u).intervalIntegral_add_eq (φ u) 0, zero_add]

end Symmetry

end AutomorphicForm.GL2Real.SplitRegularity
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real.SplitRegularity"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm _root_.AutomorphicForm.GL2Real _root_.P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real AutomorphicForm.GL2Real.SplitRegularity in
theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ∧
      HasCompactSupport (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ∧
      tsupport (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ⊆
        {q | q.1 * q.2.1 ≠ 0} ∧
      ∀ (a₁ a₂ : ℝ) (p : P),
        splitTransform (entrySlice Φ p) a₂ a₁ = splitTransform (entrySlice Φ p) a₁ a₂ := by
  obtain ⟨B, δ, hB, hδ, hBδ⟩ := exists_bounds Φ hΦc hΦU
  have hcont : Continuous Φ := hΦ.continuous
  have hrep : (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) =
      fun q => (1 / (2 * Real.pi) : ℂ) * conv Φ q :=
    funext (splitTransform_eq_conv Φ hcont hΦU hB hBδ)

  have hnz : ∀ q : ℝ × ℝ × P, splitTransform (entrySlice Φ q.2.2) q.1 q.2.1 ≠ 0 →
      |q.1| ≤ 3 * B ∧ |q.2.1| ≤ 3 * B ∧ δ ≤ |q.1 * q.2.1| ∧ q.2.2 ∈ Prod.snd '' tsupport Φ := by
    intro q hq
    rw [splitTransform_eq_conv Φ hcont hΦU hB hBδ] at hq
    obtain ⟨θ, u, hθu⟩ := exists_ne_zero_of_conv_ne_zero Φ (mul_ne_zero_iff.1 hq).2
    obtain ⟨-, h1, h2, h3, h4⟩ := conseq hB hBδ hθu
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrep]
    exact contDiff_const.mul (contDiff_conv Φ hΦ hB hBδ)
  · apply HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) (3 * B)).prod
      ((isCompact_closedBall (0 : ℝ) (3 * B)).prod (hΦc.isCompact.image continuous_snd)))
    intro q hq
    by_contra hne
    apply hq
    obtain ⟨h1, h2, -, h4⟩ := hnz q hne
    refine mem_prod.2 ⟨?_, mem_prod.2 ⟨?_, h4⟩⟩
    · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact h1
    · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact h2
  · have hS : IsClosed {q : ℝ × ℝ × P | δ ≤ |q.1 * q.2.1|} :=
      isClosed_le continuous_const (by fun_prop)
    have hsub : Function.support
        (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ⊆
        {q : ℝ × ℝ × P | δ ≤ |q.1 * q.2.1|} := fun q hq => (hnz q hq).2.2.1
    refine (closure_minimal hsub hS).trans ?_
    intro q hq
    have hq' : δ ≤ |q.1 * q.2.1| := hq
    simp only [mem_setOf_eq]
    intro h0
    rw [h0, abs_zero] at hq'
    linarith
  · intro a₁ a₂ p
    exact splitTransform_symm Φ hcont hB hBδ a₁ a₂ p

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.AutomorphicForm.GL2Real.SplitRegularity"

end S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice (solution)
