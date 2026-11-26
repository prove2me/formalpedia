-- Prove2me | solution 1 for Arxiv1606_07694.taylor_coefficient_recursions
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:07:39.562329+00:00
-- url     : https://prove2.me/submissions/235e6096-f444-4123-860b-13c5fc75c326

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

set_option autoImplicit false

open MeasureTheory Complex Filter Topology Asymptotics

namespace S76TR
open Arxiv1606_07694

lemma app0 {n m : ℕ} (κ : Fin n → Vec2) (i : Fin (n + m)) :
    Fin.append κ (0 : Fin m → Vec2) i = if h : (i : ℕ) < n then κ ⟨i, h⟩ else 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

lemma app00 {n m : ℕ} : Fin.append (0 : Fin n → Vec2) (0 : Fin m → Vec2) = 0 := by
  funext i; rw [app0]; split_ifs <;> rfl

lemma coef_eq {n : ℕ} (g : (Fin n → Vec2) → ℂ) (a : ℂ) (Dm : Matrix (Fin 2) (Fin 2) ℂ)
    (h : HasReducedExpansion g a Dm) : g 0 = a := by
  have := (h.isBigO.eq_zero_imp).self_of_nhds (by simp)
  unfold truncPoly crossSum at this
  simp at this
  linear_combination this

lemma hval_l (E : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : Fin 2) (t : ℝ) :
    (∑ μ', ∑ ν', E μ' ν' *
      (((t • (![EuclideanSpace.single μ 1, EuclideanSpace.single ν 1] : Fin 2 → Vec2)) 0 μ' : ℝ) : ℂ) *
      (((t • (![EuclideanSpace.single μ 1, EuclideanSpace.single ν 1] : Fin 2 → Vec2)) 1 ν' : ℝ) : ℂ))
      = (t : ℂ) ^ 2 * E μ ν := by
  fin_cases μ <;> fin_cases ν <;> simp [Fin.sum_univ_two, EuclideanSpace.single_apply] <;> ring

lemma bilin_zero (E : Matrix (Fin 2) (Fin 2) ℂ)
    (h : (fun κ : Fin 2 → Vec2 => ∑ μ, ∑ ν, E μ ν * (κ 0 μ : ℂ) * (κ 1 ν : ℂ)) =o[𝓝 0]
      (fun κ : Fin 2 → Vec2 => ‖κ‖ ^ 2)) : E = 0 := by
  ext μ ν
  set v : Fin 2 → Vec2 := ![EuclideanSpace.single μ 1, EuclideanSpace.single ν 1] with hv
  have hvt : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have h2 := h.comp_tendsto hvt
  have hval : ∀ t : ℝ, (∑ μ', ∑ ν', E μ' ν' * ((t • v) 0 μ' : ℂ) * ((t • v) 1 ν' : ℂ)) =
      (t : ℂ) ^ 2 * E μ ν := fun t => by rw [hv]; exact hval_l E μ ν t
  have hvpos : 0 < ‖v‖ := by
    apply norm_pos_iff.2
    intro h0
    have := congrArg (fun w : Fin 2 → Vec2 => w 0 μ) h0
    simp [hv] at this
  rw [isLittleO_iff] at h2
  by_contra hE
  have hEp : 0 < ‖E μ ν‖ := norm_pos_iff.2 hE
  have hc : 0 < ‖E μ ν‖ / (2 * ‖v‖ ^ 2) := by positivity
  have ev := h2 hc
  have ev2 := (ev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := {(0:ℝ)}ᶜ) (a := 0))
  obtain ⟨t, ht, ht0⟩ := ev2.exists
  simp only [Function.comp, hval, Set.mem_compl_iff, Set.mem_singleton_iff] at ht ht0
  rw [norm_mul, norm_pow, Complex.norm_real, norm_pow, norm_norm, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at ht
  have htp : 0 < t ^ 2 := by positivity
  have : ‖E μ ν‖ / (2 * ‖v‖ ^ 2) * (t ^ 2 * ‖v‖ ^ 2) = t ^ 2 * (‖E μ ν‖ / 2) := by
    field_simp
  rw [this] at ht
  nlinarith

lemma cross_app {m : ℕ} (Dm : Matrix (Fin 2) (Fin 2) ℂ) (κ : Fin 2 → Vec2) :
    crossSum Dm (Fin.append κ (0 : Fin m → Vec2)) =
      ∑ μ, ∑ ν, Dm μ ν * (κ 0 μ : ℂ) * (κ 1 ν : ℂ) := by
  unfold crossSum
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 + m))]
  · rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (2 + m))]
    · rw [app0, app0]; simp
    · intro j hj hj1
      have hj' : (j : ℕ) ≠ 1 := fun h => hj1 (Fin.ext h)
      have hj0 : 0 < (j : ℕ) := Fin.lt_iff_val_lt_val.1 (Finset.mem_Ioi.1 hj)
      rw [app0 (i := j), dif_neg (by omega)]; simp
    · intro h; exact absurd (Finset.mem_Ioi.2 (Fin.lt_iff_val_lt_val.2 (by norm_num))) h
  · intro i _ hi0
    have hi' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : (i : ℕ) < (j : ℕ) := Fin.lt_iff_val_lt_val.1 (Finset.mem_Ioi.1 hj)
    rw [app0 (i := j), dif_neg (by omega)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

lemma norm_app {m : ℕ} (κ : Fin 2 → Vec2) : ‖Fin.append κ (0 : Fin m → Vec2)‖ ≤ ‖κ‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg κ)).2
  intro i
  rw [app0]
  split_ifs
  · exact norm_le_pi_norm κ _
  · simp

end S76TR

open Arxiv1606_07694 S76TR in
theorem solution (G : KernelFamily) (A : ℕ → Vec2 → Vec2 → ℂ)
    (D : ℕ → Vec2 → Vec2 → Matrix (Fin 2) (Fin 2) ℂ) (R qv : Vec2 → ℂ)
    (hG : IsSymmetricKernel G)
    (h19 : ∀ (n : ℕ) (k k0 : Vec2), HasReducedExpansion (G n k k0) (A n k k0) (D n k k0))
    (h15 : ∀ (n m : ℕ) (k k0 : Vec2) (κ : Fin n → Vec2), 1 ≤ n → n ≤ 2 →
      G (n + m) k k0 (Fin.append κ (0 : Fin m → Vec2)) = shiftFactor qv k k0 ^ m * G n k k0 κ)
    (h15zero : ∀ (m : ℕ) (k0 : Vec2), G m k0 k0 0 = shiftFactor qv k0 k0 ^ m * G 0 k0 k0 0)
    (h7 : ∀ k0 : Vec2, G 0 k0 k0 0 = R k0) :
    (∀ (m : ℕ) (k0 : Vec2), A m k0 k0 = (2 * I * qv k0) ^ m * R k0) ∧
    (∀ (m : ℕ) (k k0 : Vec2), A (m + 1) k k0 = shiftFactor qv k k0 ^ m * A 1 k k0) ∧
    (∀ (m : ℕ) (k k0 : Vec2), A (m + 2) k k0 = shiftFactor qv k k0 ^ m * A 2 k k0) ∧
    (∀ (m : ℕ) (k k0 : Vec2), D (m + 2) k k0 = shiftFactor qv k k0 ^ m • D 2 k k0) := by
  have hA : ∀ n k k0, A n k k0 = G n k k0 0 := fun n k k0 => (coef_eq _ _ _ (h19 n k k0)).symm
  have hA3 : ∀ (m : ℕ) (k k0 : Vec2), A (m + 2) k k0 = shiftFactor qv k k0 ^ m * A 2 k k0 := by
    intro m k k0
    rw [Nat.add_comm m 2, hA, hA, ← h15 2 m k k0 0 (by norm_num) le_rfl, app00]
  refine ⟨?_, ?_, hA3, ?_⟩
  · intro m k0
    rw [hA, h15zero, h7]
    unfold shiftFactor; ring
  · intro m k k0
    rw [Nat.add_comm m 1, hA, hA, ← h15 1 m k k0 0 le_rfl (by norm_num), app00]
  · intro m k k0
    set s := shiftFactor qv k k0
    rw [← sub_eq_zero]
    apply bilin_zero
    -- expansion of G (2+m) along the embedding
    have hι : Tendsto (fun κ : Fin 2 → Vec2 => Fin.append κ (0 : Fin m → Vec2)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun κ : Fin 2 → Vec2 => Fin.append κ (0 : Fin m → Vec2)) := by
        apply continuous_pi; intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.append_left]; exact continuous_apply j
        · simp only [Fin.append_right]; exact continuous_const
      simpa [app00] using hc.tendsto 0
    have hb : (fun κ : Fin 2 → Vec2 => ‖Fin.append κ (0 : Fin m → Vec2)‖ ^ 2) =O[𝓝 0]
        (fun κ : Fin 2 → Vec2 => ‖κ‖ ^ 2) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun κ => by
        simp only [norm_pow, norm_norm, one_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_app κ) 2)
    have e1 := ((h19 (2 + m) k k0).comp_tendsto hι).trans_isBigO hb
    have e2 := (h19 2 k k0).const_mul_left (s ^ m)
    have e3 := e1.sub e2
    refine e3.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with κ
    simp only [Function.comp, Pi.sub_apply]
    rw [h15 2 m k k0 κ (by norm_num) le_rfl]
    unfold truncPoly
    rw [cross_app, Nat.add_comm 2 m, hA3 m k k0]
    unfold crossSum
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Fin.sum_univ_two, Finset.sum_sub_distrib, Finset.mul_sum, sub_mul]
    have : (Finset.Ioi (0 : Fin 2)) = {1} := by decide
    have h1 : (Finset.Ioi (1 : Fin 2)) = ∅ := by decide
    simp only [this, h1, Finset.sum_singleton, Finset.sum_empty, add_zero]
    ring
