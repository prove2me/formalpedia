-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLatticeLineExists
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLatticeLineExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:51.683497+00:00
-- url     : https://prove2.me/theorems/24c78d39-2ec5-4065-90ff-2eb9bdb3b2c4
-- title:
--   PLattice Line Exists
-- statement:
--   Definitions and structural lemmas for PLattice Line Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLatticeLineExists.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField Matrix
open scoped ComplexOrder ContDiff
noncomputable section
namespace LatticeLine
variable {K : Type} [Field K] [NumberField K] {r N : ℕ}
def recover (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ) (σ : K →+* ℂ) (z : Fin (N + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  fun j ↦ ∑ b, R σ j b * z b
def remainder (φ : Fin (N + 1) → Fin (r + 1) → K) (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ)
    (z : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun b ↦ z b - ∑ σ : K →+* ℂ, ∑ j, σ (φ b j) * recover R σ z j
def quad (F : HermLattice K (r + 1)) (φ : Fin (N + 1) → Fin (r + 1) → K)
    (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ) (z : Fin (N + 1) → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (recover R σ z) ⬝ᵥ (F.metric σ *ᵥ recover R σ z)).re +
    ∑ b, ‖remainder φ R z b‖ ^ 2
variable (F : HermLattice K (r + 1)) (φ : Fin (N + 1) → Fin (r + 1) → K)
  (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ)
theorem herm_re_pos (σ : K →+* ℂ) {v : Fin (r + 1) → ℂ} (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (F.metric σ *ᵥ v)).re :=
  (Complex.pos_iff.mp ((F.posDef σ).dotProduct_mulVec_pos hv)).1
theorem herm_re_nonneg (σ : K →+* ℂ) (v : Fin (r + 1) → ℂ) :
    0 ≤ (star v ⬝ᵥ (F.metric σ *ᵥ v)).re := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (herm_re_pos F σ hv).le
theorem quad_nonneg (z : Fin (N + 1) → ℂ) : 0 ≤ quad F φ R z :=
  add_nonneg (Finset.sum_nonneg fun σ _ ↦ herm_re_nonneg F σ _)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
theorem quad_pos {z : Fin (N + 1) → ℂ} (hz : z ≠ 0) : 0 < quad F φ R z := by
  by_cases h : ∀ σ, recover R σ z = 0
  · have hrem : remainder φ R z = z := by
      funext b
      simp [remainder, h]
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hz
    refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun σ _ ↦ herm_re_nonneg F σ _) ?_
    rw [hrem]
    exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨b, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hb) 2⟩
  · obtain ⟨σ, hσ⟩ := not_forall.mp h
    exact add_pos_of_pos_of_nonneg
      (Finset.sum_pos' (fun τ _ ↦ herm_re_nonneg F τ _) ⟨σ, Finset.mem_univ _, herm_re_pos F σ hσ⟩)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
omit [NumberField K] in
theorem recover_smul (σ : K →+* ℂ) (c : ℂ) (z : Fin (N + 1) → ℂ) :
    recover R σ (fun b ↦ c * z b) = c • recover R σ z := by
  funext j
  simp only [recover, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring
theorem remainder_smul (c : ℂ) (z : Fin (N + 1) → ℂ) :
    remainder φ R (fun b ↦ c * z b) = c • remainder φ R z := by
  funext b
  simp only [remainder, recover_smul, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
theorem herm_smul (σ : K →+* ℂ) (c : ℂ) (v : Fin (r + 1) → ℂ) :
    (star (c • v) ⬝ᵥ (F.metric σ *ᵥ (c • v))).re = ‖c‖ ^ 2 * (star v ⬝ᵥ (F.metric σ *ᵥ v)).re := by
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
theorem quad_smul (c : ℂ) (z : Fin (N + 1) → ℂ) :
    quad F φ R (fun b ↦ c * z b) = ‖c‖ ^ 2 * quad F φ R z := by
  simp only [quad, recover_smul, remainder_smul, herm_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    mul_add, Finset.mul_sum]
theorem contDiff_quad : ContDiff ℝ ∞ (quad F φ R) := by
  have hrec : ∀ σ j, ContDiff ℝ ∞ (fun z : Fin (N + 1) → ℂ ↦ recover R σ z j) := fun σ j ↦
    ContDiff.sum fun b _ ↦ contDiff_const.mul (contDiff_apply ℝ ℂ b)
  have hconj : ContDiff ℝ ∞ (fun x : ℂ ↦ star x) := Complex.conjCLE.contDiff
  refine ContDiff.add (ContDiff.sum fun σ _ ↦ Complex.reCLM.contDiff.comp ?_)
    (ContDiff.sum fun b _ ↦ (contDiff_norm_sq ℝ).comp ?_)
  · simp only [dotProduct, mulVec, Pi.star_apply]
    exact ContDiff.sum fun i _ ↦ (hconj.comp (hrec σ i)).mul
      (ContDiff.sum fun j _ ↦ contDiff_const.mul (hrec σ j))
  · exact (contDiff_apply ℝ ℂ b).sub
      (ContDiff.sum fun σ _ ↦ ContDiff.sum fun j _ ↦ contDiff_const.mul (hrec σ j))
def line : HermLine (fun _ : Unit ↦ N) where
  deg _ := 1
  metric z := Real.sqrt ((quad F φ R (z ()) + quad F φ R (fun b ↦ starRingEnd ℂ (z () b))) / 2)
  metric_pos z hz := by
    have h1 := quad_pos F φ R (hz ())
    have h2 := quad_nonneg F φ R (fun b ↦ starRingEnd ℂ (z () b))
    exact Real.sqrt_pos.mpr (by linarith)
  metric_smul c z _ _ := by
    have h2 : quad F φ R (fun b ↦ starRingEnd ℂ (c () * z () b)) =
        ‖c ()‖ ^ 2 * quad F φ R (fun b ↦ starRingEnd ℂ (z () b)) := by
      simp only [map_mul]
      rw [quad_smul, Complex.norm_conj]
    show Real.sqrt ((quad F φ R (fun b ↦ c () * z () b) +
      quad F φ R (fun b ↦ starRingEnd ℂ (c () * z () b))) / 2) = _
    rw [quad_smul, h2, ← mul_add, mul_div_assoc, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    simp
  metric_smooth := by
    have h0 : ContDiff ℝ ∞ (fun z : Cone (fun _ : Unit ↦ N) ℂ ↦ z ()) := contDiff_apply ℝ _ ()
    have h1 : ContDiff ℝ ∞ (fun z : Cone (fun _ : Unit ↦ N) ℂ ↦ fun b ↦ starRingEnd ℂ (z () b)) :=
      contDiff_pi.2 fun b ↦ Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ b).comp h0)
    have hq := (((contDiff_quad F φ R).comp h0).add ((contDiff_quad F φ R).comp h1)).div_const 2
    refine hq.contDiffOn.sqrt fun z hz ↦ ne_of_gt ?_
    have h3 := quad_pos F φ R (hz ())
    have h4 := quad_nonneg F φ R (fun b ↦ starRingEnd ℂ (z () b))
    simp only [Function.comp_apply]
    linarith
end LatticeLine
end
end GroundTheory.Heights₂.Heights


