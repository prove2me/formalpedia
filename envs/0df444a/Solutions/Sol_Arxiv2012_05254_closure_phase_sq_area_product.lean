-- Prove2me | solution 1 for Arxiv2012_05254.closure_phase_sq_area_product
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T06:03:02.275422+00:00
-- url     : https://prove2.me/submissions/ad032da5-2143-43cc-bbd7-0225493b76e8

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace S80TA
open Arxiv2012_05254

def T : Set Plane := {s | 0 ≤ s 0 ∧ 0 ≤ s 1 ∧ s 0 + s 1 ≤ 1}
def T2 : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

lemma T2_meas : MeasurableSet T2 := by
  unfold T2
  refine (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))

lemma vol_T2 : volume T2 = ENNReal.ofReal (1/2) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply T2_meas]
  have h : ∀ a : ℝ, volume (Prod.mk a ⁻¹' T2) =
      (Set.Icc (0:ℝ) 1).indicator (fun a => ENNReal.ofReal (1 - a)) a := by
    intro a
    by_cases ha : a ∈ Set.Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem ha]
      have : Prod.mk a ⁻¹' T2 = Set.Icc 0 (1 - a) := by
        ext b; simp only [T2, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨ha.1, h1, by linarith⟩
      rw [this, Real.volume_Icc]; congr 1; ring
    · rw [Set.indicator_of_notMem ha]
      have : Prod.mk a ⁻¹' T2 = ∅ := by
        ext b; simp only [T2, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨h0, h1, h2⟩; exact ha ⟨h0, by linarith⟩
      rw [this, measure_empty]
  simp_rw [h]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp; norm_num
  · exact (continuous_const.sub continuous_id).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    simp only [Pi.zero_apply]; linarith [ha.2]

lemma vol_T : volume T = ENNReal.ofReal (1/2) := by
  have hp := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))
  have : T = (⇑(MeasurableEquiv.finTwoArrow) ∘ (@WithLp.ofLp 2 (Fin 2 → ℝ))) ⁻¹' T2 := by
    ext s; simp [T, T2, MeasurableEquiv.finTwoArrow]
  rw [this, hp.measure_preimage T2_meas.nullMeasurableSet, vol_T2]


lemma T_convex : Convex ℝ T := by
  intro s hs t ht a b ha hb hab
  simp only [T, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hs ht ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

noncomputable def Lm (p q r : Plane) : Plane →ₗ[ℝ] Plane :=
  (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).toLinearMap.smulRight (q - p) +
  (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).toLinearMap.smulRight (r - p)

lemma Lm_apply (p q r s : Plane) : Lm p q r s = s 0 • (q - p) + s 1 • (r - p) := by
  simp [Lm]

lemma hull_eq (p q r : Plane) :
    convexHull ℝ ({p, q, r} : Set Plane) = (fun s => p + s) '' (Lm p q r '' T) := by
  apply subset_antisymm
  · apply convexHull_min
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h <;> rw [h]
      · exact ⟨0, ⟨0, by simp [T], by simp⟩, by simp⟩
      · exact ⟨q - p, ⟨EuclideanSpace.single 0 1, by simp [T], by simp [Lm_apply]⟩, by abel⟩
      · exact ⟨r - p, ⟨EuclideanSpace.single 1 1, by simp [T], by simp [Lm_apply]⟩, by abel⟩
    · exact (T_convex.linear_image (Lm p q r)).translate p
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have e : p + Lm p q r s = ∑ i : Fin 3, (![1 - s 0 - s 1, s 0, s 1] : Fin 3 → ℝ) i •
        (![p, q, r] : Fin 3 → Plane) i := by
      simp only [Lm_apply, Fin.sum_univ_three]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      module
    show p + Lm p q r s ∈ _
    rw [e]
    obtain ⟨h0, h1, h2⟩ := hs
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
    · fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_three]; ring
    · apply subset_convexHull
      fin_cases i <;> simp

lemma tri_area (p q r : Plane) :
    (volume (convexHull ℝ ({p, q, r} : Set Plane))).toReal = |cross (q - p) (r - p)| / 2 := by
  rw [hull_eq, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, vol_T]
  have hd : LinearMap.det (Lm p q r) = cross (q - p) (r - p) := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, Lm_apply, cross]
    ring
  rw [hd, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma exists_t (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) (ζ : Fin 3 → ℝ) :
    ∃ t : Plane, ∀ a b, ⟪x b - x a, t⟫ = ζ b - ζ a := by
  classical
  have hspan : affineSpan ℝ (Set.range x) = ⊤ := by
    rw [hx.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  let bs : AffineBasis (Fin 3) ℝ Plane := ⟨x, hx, hspan⟩
  have hb : ∀ a, bs a = x a := fun a => rfl
  let φ : Plane →ᵃ[ℝ] ℝ := ζ 0 • bs.coord 0 + ζ 1 • bs.coord 1 + ζ 2 • bs.coord 2
  have hφ : ∀ c, φ (x c) = ζ c := by
    intro c
    simp only [φ, AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ← hb, AffineBasis.coord_apply]
    fin_cases c <;> simp
  refine ⟨(InnerProductSpace.toDual ℝ Plane).symm (LinearMap.toContinuousLinearMap φ.linear),
    fun a b => ?_⟩
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.coe_toContinuousLinearMap']
  rw [show x b - x a = x b -ᵥ x a from rfl, AffineMap.linearMap_vsub, hφ, hφ, vsub_eq_sub]


lemma inner2 (u s : Plane) : ⟪u, s⟫ = u 0 * s 0 + u 1 * s 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma C_ne (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) :
    cross (x 1 - x 0) (x 2 - x 0) ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_t x hx ![0, 1, 0]
  obtain ⟨t', ht'⟩ := exists_t x hx ![0, 0, 1]
  have h1 := ht 0 1
  have h2 := ht 0 2
  have h3 := ht' 0 1
  have h4 := ht' 0 2
  simp only [inner2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, sub_zero, Fin.isValue] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  intro hc
  unfold cross at hc
  simp only [PiLp.sub_apply] at hc
  have : (1:ℝ) = 0 := by
    linear_combination (-((x 2 0 - x 0 0) * t' 0 + (x 2 1 - x 0 1) * t' 1)) * h1 - h4 +
      ((x 2 0 - x 0 0) * t 0 + (x 2 1 - x 0 1) * t 1) * h3 + (t 0 * t' 1 - t 1 * t' 0) * hc
  norm_num at this

noncomputable def vert (u v : Plane) (α β : ℝ) : Plane :=
  !₂[((-α / (2 * Real.pi)) * v 1 - (-β / (2 * Real.pi)) * u 1) / cross u v,
     (-(-α / (2 * Real.pi)) * v 0 + (-β / (2 * Real.pi)) * u 0) / cross u v]

lemma vert0 (u v : Plane) (α β : ℝ) : (vert u v α β) 0 =
    ((-α / (2 * Real.pi)) * v 1 - (-β / (2 * Real.pi)) * u 1) / cross u v := rfl
lemma vert1 (u v : Plane) (α β : ℝ) : (vert u v α β) 1 =
    (-(-α / (2 * Real.pi)) * v 0 + (-β / (2 * Real.pi)) * u 0) / cross u v := rfl

lemma mem2 (u v : Plane) (α β : ℝ) (h : cross u v ≠ 0) (s : Plane) :
    (s ∈ npc u α ∧ s ∈ npc v β) ↔ s = vert u v α β := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [npc, Set.mem_setOf_eq, inner2]
  constructor
  · rintro ⟨h1, h2⟩
    ext i; fin_cases i
    · show s 0 = vert u v α β 0
      rw [vert0, eq_div_iff h]; unfold cross; field_simp
      linear_combination v 1 * h1 - u 1 * h2
    · show s 1 = vert u v α β 1
      rw [vert1, eq_div_iff h]; unfold cross; field_simp
      linear_combination -(v 0 * h1) + u 0 * h2
  · rintro rfl
    rw [vert0, vert1]
    constructor
    · field_simp; unfold cross; ring
    · field_simp; unfold cross; ring

lemma e0 : (0 : Fin 3) + 1 = 1 := rfl
lemma e1 : (1 : Fin 3) + 1 = 2 := rfl
lemma e2 : (2 : Fin 3) + 1 = 0 := rfl

lemma crs (x : Fin 3 → Plane) :
    cross (spacing x 0) (spacing x 1) = cross (x 1 - x 0) (x 2 - x 0) ∧
    cross (spacing x 1) (spacing x 2) = cross (x 1 - x 0) (x 2 - x 0) ∧
    cross (spacing x 2) (spacing x 0) = cross (x 1 - x 0) (x 2 - x 0) := by
  simp only [cross, spacing, PiLp.sub_apply, e0, e1, e2]
  refine ⟨by ring, by ring, by ring⟩

lemma npcV (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x) (ψ : Fin 3 → ℝ) :
    npcVertices x ψ = {vert (spacing x 0) (spacing x 1) (ψ 0) (ψ 1),
      vert (spacing x 1) (spacing x 2) (ψ 1) (ψ 2), vert (spacing x 2) (spacing x 0) (ψ 2) (ψ 0)} := by
  have hC := C_ne x hx
  obtain ⟨c0, c1, c2⟩ := crs x
  have h0 : cross (spacing x 0) (spacing x 1) ≠ 0 := c0 ▸ hC
  have h1 : cross (spacing x 1) (spacing x 2) ≠ 0 := c1 ▸ hC
  have h2 : cross (spacing x 2) (spacing x 0) ≠ 0 := c2 ▸ hC
  ext s
  simp only [npcVertices, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha1, ha2⟩
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
    · rw [e0] at ha2; exact Or.inl ((mem2 _ _ _ _ h0 s).1 ⟨ha1, ha2⟩)
    · rw [e1] at ha2; exact Or.inr (Or.inl ((mem2 _ _ _ _ h1 s).1 ⟨ha1, ha2⟩))
    · rw [e2] at ha2; exact Or.inr (Or.inr ((mem2 _ _ _ _ h2 s).1 ⟨ha1, ha2⟩))
  · rintro (h | h | h)
    · exact ⟨0, by rw [e0]; exact (mem2 _ _ _ _ h0 s).2 h⟩
    · exact ⟨1, by rw [e1]; exact (mem2 _ _ _ _ h1 s).2 h⟩
    · exact ⟨2, by rw [e2]; exact (mem2 _ _ _ _ h2 s).2 h⟩

lemma range3 (x : Fin 3 → Plane) : Set.range x = {x 0, x 1, x 2} := by
  ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (h | h | h) <;> exact ⟨_, h.symm⟩

lemma keyK (u v : Plane) (a b c : ℝ) (h : cross u v ≠ 0) :
    cross u v * cross (vert v (-(u + v)) b c - vert u v a b) (vert (-(u + v)) u c a - vert u v a b) =
      (a + b + c) ^ 2 / (4 * Real.pi ^ 2) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : cross v (-(u + v)) = cross u v := by
    unfold cross; simp only [PiLp.neg_apply, PiLp.add_apply]; ring
  have h2 : cross (-(u + v)) u = cross u v := by
    unfold cross; simp only [PiLp.neg_apply, PiLp.add_apply]; ring
  rw [show ∀ p q : Plane, cross (p - q) = cross (p - q) from fun _ _ => rfl]
  have hc : ∀ p q : Plane, cross p q = p 0 * q 1 - p 1 * q 0 := fun _ _ => rfl
  rw [hc (vert v (-(u + v)) b c - vert u v a b)]
  simp only [PiLp.sub_apply, vert0, vert1, h1, h2]
  simp only [PiLp.neg_apply, PiLp.add_apply]
  field_simp
  rw [hc u v]
  ring

end S80TA

open Arxiv2012_05254 S80TA in
open scoped RealInnerProductSpace in
theorem solution (x : Fin 3 → Plane) (hx : AffineIndependent ℝ x)
    (ψ : Fin 3 → ℝ) :
    closurePhase ψ ^ 2 = 16 * Real.pi ^ 2 * apertureArea x * imageArea x ψ := by
  have hC := C_ne x hx
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold apertureArea imageArea
  rw [range3, tri_area, npcV x hx, tri_area]
  set K := cross (vert (spacing x 1) (spacing x 2) (ψ 1) (ψ 2) - vert (spacing x 0) (spacing x 1) (ψ 0) (ψ 1))
    (vert (spacing x 2) (spacing x 0) (ψ 2) (ψ 0) - vert (spacing x 0) (spacing x 1) (ψ 0) (ψ 1)) with hKdef
  have hK : cross (x 1 - x 0) (x 2 - x 0) * K = (ψ 0 + ψ 1 + ψ 2) ^ 2 / (4 * Real.pi ^ 2) := by
    obtain ⟨c0, -, -⟩ := crs x
    have hs2 : spacing x 2 = -(spacing x 0 + spacing x 1) := by
      simp only [spacing, e0, e1, e2]; abel
    rw [hKdef, hs2, ← c0]
    rw [← c0] at hC
    exact keyK _ _ _ _ _ hC
  have hab : |cross (x 1 - x 0) (x 2 - x 0)| * |K| = (ψ 0 + ψ 1 + ψ 2) ^ 2 / (4 * Real.pi ^ 2) := by
    rw [← abs_mul, hK, abs_of_nonneg (by positivity)]
  rw [closurePhase, Fin.sum_univ_three]
  have : 16 * Real.pi ^ 2 * (|cross (x 1 - x 0) (x 2 - x 0)| / 2) * (|K| / 2) =
      4 * Real.pi ^ 2 * (|cross (x 1 - x 0) (x 2 - x 0)| * |K|) := by ring
  rw [this, hab]; field_simp

