-- Prove2me | solution 1 for Arxiv1310_4241.pec_debye_sources_decouple
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:21:38.904259+00:00
-- url     : https://prove2.me/submissions/fbd10e57-cda2-43c7-8e1a-d87004daddc3

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic
import Theorems.Thm_Arxiv1310_4241_pec_debye_boundary_operators

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma sommerfeldRoot_sq (k : ℂ) (ξ η : ℝ) :
    sommerfeldRoot k ξ η ^ 2 = (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2 := by
  unfold sommerfeldRoot
  set z : ℂ := (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2
  split_ifs with h
  · have hz : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [h.1]
    have hneg : 0 ≤ -z.re := by linarith [h.2]
    calc (-Complex.I * (Real.sqrt (-z.re) : ℂ)) ^ 2
        = (Complex.I ^ 2) * ((Real.sqrt (-z.re) : ℝ) : ℂ) ^ 2 := by ring
      _ = -1 * ((-z.re : ℝ) : ℂ) := by
          rw [Complex.I_sq]
          norm_cast
          rw [Real.sq_sqrt hneg]
      _ = (z.re : ℂ) := by push_cast; ring
      _ = z := hz.symm
  · by_cases hz0 : z = 0
    · simp [hz0]
    · rw [sq, ← Complex.cpow_add _ _ hz0]; norm_num

private lemma sommerfeldRoot_zero (ξ η : ℝ) :
    sommerfeldRoot 0 ξ η = (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) := by
  unfold sommerfeldRoot
  have hnn : 0 ≤ ξ ^ 2 + η ^ 2 := by positivity
  have hz : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (0 : ℂ) ^ 2 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hz]
  have hnot : ¬((((ξ ^ 2 + η ^ 2 : ℝ) : ℂ)).im = 0 ∧ (((ξ ^ 2 + η ^ 2 : ℝ) : ℂ)).re < 0) := by
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_lt]
    exact hnn
  rw [if_neg hnot, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hnn]
  norm_cast
  rw [Real.sqrt_eq_rpow]

theorem solution (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (hβ : sommerfeldRoot k ξ η ≠ 0) (a b r q : ℂ) :
    (∀ x y : ℝ,
      laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE ω ε μ ξ η r q)) (pt x y 0) +
          a * planeWave ξ η x y = 0 ∧
        pecH ω ε μ ξ η r q (pt x y 0) 2 + b * planeWave ξ η x y = 0) ↔
    (r = -(64 * Real.pi ^ 4 / csqrt μ) * a * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) /
        (sommerfeldRoot k ξ η - Complex.I * k) ∧
      q = -(8 * Real.pi ^ 2 / csqrt ε) * b * sommerfeldRoot k ξ η /
        (sommerfeldRoot k ξ η - Complex.I * k)) := by
  have hk0 : k ≠ 0 := by
    intro h
    have := hk.1
    rw [h] at this
    simp at this
  have hμ : μ ≠ 0 := by
    intro h
    apply hk0
    rw [hkdef, wavenumber, h, mul_zero, Complex.zero_cpow (by norm_num), mul_zero]
  have hε : ε ≠ 0 := by
    intro h
    apply hk0
    rw [hkdef, wavenumber, h, zero_mul, Complex.zero_cpow (by norm_num), mul_zero]
  have hcμ : csqrt μ ≠ 0 := by
    rw [csqrt]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hμ)
  have hcε : csqrt ε ≠ 0 := by
    rw [csqrt]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hε)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push_neg at h
    exact hξη (Prod.ext (by nlinarith [sq_nonneg ξ, sq_nonneg η]) (by nlinarith [sq_nonneg ξ, sq_nonneg η]))
  have hρ_pos : 0 < Real.sqrt (ξ ^ 2 + η ^ 2) := Real.sqrt_pos.mpr hρ2_real
  have hρ : (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  set β := sommerfeldRoot k ξ η
  have hβ_sq : β ^ 2 = (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - k ^ 2 := sommerfeldRoot_sq k ξ η
  have hβik : β - Complex.I * k ≠ 0 := by
    intro h
    have h1 : β = Complex.I * k := sub_eq_zero.mp h
    have h2 : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 = 0 := by
      have := hβ_sq
      rw [h1] at this
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination -this + k ^ 2 * hI
    have h3 : ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) = 0 := by simpa using h2
    exact hρ2_real.ne' (Complex.ofReal_eq_zero.mp h3)
  have hghat0 : ghat 0 ξ η 0 = 1 / (8 * (Real.pi : ℂ) ^ 2 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) := by
    simp [ghat, sommerfeldRoot_zero]
  have hghatk : ghat k ξ η 0 = 1 / (8 * (Real.pi : ℂ) ^ 2 * β) := by
    simp [ghat, β]
  have hop : ∀ x y : ℝ,
      laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE ω ε μ ξ η r q)) (pt x y 0) =
        csqrt μ * (β * (β - Complex.I * k)) * ghat 0 ξ η 0 * ghat k ξ η 0 * r * planeWave ξ η x y ∧
      pecH ω ε μ ξ η r q (pt x y 0) 2 =
        csqrt ε * (β - Complex.I * k) * ghat k ξ η 0 * q * planeWave ξ η x y := by
    intro x y
    have hM7 := pec_debye_boundary_operators ω ε μ k hkdef hk ξ η hξη hβ r q x y
    refine ⟨?_, hM7.2⟩
    rw [hM7.1, ← hβ_sq]
    ring
  have hcoeff1 :
      csqrt μ * (β * (β - Complex.I * k)) * ghat 0 ξ η 0 * ghat k ξ η 0 =
        csqrt μ * (β - Complex.I * k) / (64 * (Real.pi : ℂ) ^ 4 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) := by
    rw [hghat0, hghatk]
    field_simp [hπ, hβ, hρ]
    ring
  have hcoeff2 :
      csqrt ε * (β - Complex.I * k) * ghat k ξ η 0 =
        csqrt ε * (β - Complex.I * k) / (8 * (Real.pi : ℂ) ^ 2 * β) := by
    rw [hghatk]
    field_simp [hπ, hβ]
  constructor
  · intro hall
    have h00 := hall 0 0
    have hpw : planeWave ξ η 0 0 = 1 := by simp [planeWave]
    rw [(hop 0 0).1, (hop 0 0).2, hpw, hcoeff1, hcoeff2] at h00
    simp only [mul_one] at h00
    rcases h00 with ⟨hr, hq⟩
    constructor
    · field_simp [hcμ, hβik, hπ, hρ] at hr ⊢
      linear_combination hr
    · field_simp [hcε, hβik, hπ, hβ] at hq ⊢
      linear_combination hq
  · rintro ⟨rfl, rfl⟩ x y
    rw [(hop x y).1, (hop x y).2, hcoeff1, hcoeff2]
    constructor
    · field_simp [hcμ, hβik, hπ, hρ]
      ring
    · field_simp [hcε, hβik, hπ, hβ]
      ring
