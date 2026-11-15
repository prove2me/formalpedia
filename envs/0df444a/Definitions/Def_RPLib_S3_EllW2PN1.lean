-- Prove2me | Definitions.Def_RPLib_S3_EllW2PN1
-- name    : RPLib_S3_EllW2PN1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:27:09.516792+00:00
-- url     : https://prove2.me/theorems/46181521-8af1-4349-9f8c-aaa673b0bc0e
-- title:
--   The Eichler-Selberg trace formula in weight two: `∫_ℝ ((t - α)² (t - β)²)⁻¹ dt = 0`
-- statement:
--   `∫_ℝ ((t - α)² (t - β)²)⁻¹ dt = 0`.
--
--   For `α ≠ β` with the same nonzero imaginary part both poles lie on one side of `ℝ`, so the
--   integral vanishes. Proof by the explicit antiderivative
--   `F t = A (-(t-α)⁻¹ - (t-β)⁻¹) + C (log (t-α) - log (t-β))`, `A = δ⁻²`, `C = -2 δ⁻³`, `δ = α - β`,
--   which tends to `0` along `cocompact ℝ` (mean value bound for `log` on the segment `[t-α, t-β]`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib

/-!
# S3-ES-Wt2 (O6, file PN1): `∫_ℝ ((t - α)² (t - β)²)⁻¹ dt = 0`

For `α ≠ β` with the same nonzero imaginary part both poles lie on one side of `ℝ`, so the
integral vanishes. Proof by the explicit antiderivative
`F t = A (-(t-α)⁻¹ - (t-β)⁻¹) + C (log (t-α) - log (t-β))`, `A = δ⁻²`, `C = -2 δ⁻³`, `δ = α - β`,
which tends to `0` along `cocompact ℝ` (mean value bound for `log` on the segment `[t-α, t-β]`).
-/

open MeasureTheory Set Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- Mean value bound for the principal `log` along a segment inside the slit plane. -/
lemma norm_log_sub_le {z w : ℂ} {R : ℝ} (hR : 0 < R)
    (hslit : ∀ p ∈ segment ℝ z w, p ∈ Complex.slitPlane)
    (hnorm : ∀ p ∈ segment ℝ z w, R ≤ ‖p‖) :
    ‖Complex.log z - Complex.log w‖ ≤ R⁻¹ * ‖z - w‖ :=
  (convex_segment z w).norm_image_sub_le_of_norm_hasDerivWithin_le (f := Complex.log)
    (f' := fun p => p⁻¹) (fun p hp => (Complex.hasDerivAt_log (hslit p hp)).hasDerivWithinAt)
    (fun p hp => by rw [norm_inv]; exact inv_anti₀ hR (hnorm p hp))
    (right_mem_segment ℝ z w) (left_mem_segment ℝ z w)

lemma segment_sub_facts {α β : ℂ} (him : α.im = β.im) (t : ℝ) {p : ℂ}
    (hp : p ∈ segment ℝ ((t : ℂ) - α) ((t : ℂ) - β)) :
    p.im = -α.im ∧ |t| - (‖α‖ + ‖β‖) ≤ ‖p‖ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  have e : a • ((t : ℂ) - α) + b • ((t : ℂ) - β) = (t : ℂ) - (a • α + b • β) := by
    simp only [Complex.real_smul]
    linear_combination (t : ℂ) * hab'
  rw [e]
  constructor
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.smul_im, smul_eq_mul]
    rw [← him]
    linear_combination (-α.im) * hab
  · have h1 : ‖a • α + b • β‖ ≤ ‖α‖ + ‖β‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      have ha1 : a ≤ 1 := by linarith
      have hb1 : b ≤ 1 := by linarith
      nlinarith [norm_nonneg α, norm_nonneg β]
    have h2 := norm_sub_norm_le (t : ℂ) (a • α + b • β)
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    linarith

lemma sub_ne_zero_of_im {γ : ℂ} (h : γ.im ≠ 0) (t : ℝ) : (t : ℂ) - γ ≠ 0 := fun h' => by
  have := congrArg Complex.im h'
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
  exact h (by linarith)

lemma sub_mem_slitPlane {γ : ℂ} (h : γ.im ≠ 0) (t : ℝ) : (t : ℂ) - γ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
  exact neg_ne_zero.2 h

/-- **Both poles on one side**: `∫_ℝ ((t - α)² (t - β)²)⁻¹ dt = 0`. -/
theorem integral_inv_sq_mul_sq {α β : ℂ} (hab : α ≠ β) (him : α.im = β.im) (h0 : α.im ≠ 0)
    (hint : Integrable fun t : ℝ => (((t : ℂ) - α) ^ 2 * ((t : ℂ) - β) ^ 2)⁻¹) :
    ∫ t : ℝ, (((t : ℂ) - α) ^ 2 * ((t : ℂ) - β) ^ 2)⁻¹ = 0 := by
  have hδ : α - β ≠ 0 := sub_ne_zero.2 hab
  have h0' : β.im ≠ 0 := him ▸ h0
  set A : ℂ := ((α - β) ^ 2)⁻¹ with hA
  set C : ℂ := -2 * ((α - β) ^ 3)⁻¹ with hC
  set F : ℝ → ℂ := fun t => A * (-((t : ℂ) - α)⁻¹ - ((t : ℂ) - β)⁻¹) +
      C * (Complex.log ((t : ℂ) - α) - Complex.log ((t : ℂ) - β)) with hF
  have hl : ∀ (γ : ℂ) (t : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) - γ) 1 t := fun γ t => by
    have := ((hasDerivAt_id t).ofReal_comp).sub_const γ
    simpa using this
  have hderiv : ∀ t : ℝ, HasDerivAt F ((((t : ℂ) - α) ^ 2 * ((t : ℂ) - β) ^ 2)⁻¹) t := by
    intro t
    have hX := sub_ne_zero_of_im h0 t
    have hY := sub_ne_zero_of_im h0' t
    have h1 := (hl α t).inv hX
    have h2 := (hl β t).inv hY
    have h3 := (hl α t).clog_real (sub_mem_slitPlane h0 t)
    have h4 := (hl β t).clog_real (sub_mem_slitPlane h0' t)
    have hF' := ((h1.neg.sub h2).const_mul A).add ((h3.sub h4).const_mul C)
    refine hF'.congr_deriv ?_
    rw [hA, hC]
    field_simp
    ring
  set K : ℝ := ‖α‖ + ‖β‖ with hK
  have hbound : ∀ t : ℝ, K + 1 ≤ |t| →
      ‖F t‖ ≤ (2 * ‖A‖ + ‖C‖ * ‖α - β‖) / (|t| - K) := by
    intro t ht
    have hR : 0 < |t| - K := by linarith
    have hR0 : |t| - K ≠ 0 := hR.ne'
    have hinv : ∀ γ : ℂ, ‖γ‖ ≤ K → ‖((t : ℂ) - γ)⁻¹‖ ≤ (|t| - K)⁻¹ := fun γ hγ => by
      rw [norm_inv]
      refine inv_anti₀ hR ?_
      have := norm_sub_norm_le (t : ℂ) γ
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hX := hinv α (by rw [hK]; linarith [norm_nonneg β])
    have hY := hinv β (by rw [hK]; linarith [norm_nonneg α])
    have hlog : ‖Complex.log ((t : ℂ) - α) - Complex.log ((t : ℂ) - β)‖ ≤
        (|t| - K)⁻¹ * ‖α - β‖ := by
      have e : ((t : ℂ) - α) - ((t : ℂ) - β) = -(α - β) := by ring
      have := norm_log_sub_le hR (fun p hp => ?_) (fun p hp => (segment_sub_facts him t hp).2)
      · rwa [e, norm_neg] at this
      · rw [Complex.mem_slitPlane_iff]
        right
        rw [(segment_sub_facts him t hp).1]
        exact neg_ne_zero.2 h0
    calc ‖F t‖ ≤ ‖A‖ * (‖((t : ℂ) - α)⁻¹‖ + ‖((t : ℂ) - β)⁻¹‖) +
          ‖C‖ * ‖Complex.log ((t : ℂ) - α) - Complex.log ((t : ℂ) - β)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          gcongr
          exact (norm_sub_le _ _).trans_eq (by rw [norm_neg])
      _ ≤ ‖A‖ * ((|t| - K)⁻¹ + (|t| - K)⁻¹) + ‖C‖ * ((|t| - K)⁻¹ * ‖α - β‖) := by
          gcongr
      _ = (2 * ‖A‖ + ‖C‖ * ‖α - β‖) / (|t| - K) := by
          field_simp
          ring
  have hnorm : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop :=
    (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun t => Real.norm_eq_abs t
  have hev : ∀ᶠ t : ℝ in cocompact ℝ, K + 1 ≤ |t| := hnorm.eventually_ge_atTop (K + 1)
  have hlim : Tendsto F (cocompact ℝ) (𝓝 0) := by
    have hg : Tendsto (fun t : ℝ => (2 * ‖A‖ + ‖C‖ * ‖α - β‖) / (|t| - K)) (cocompact ℝ) (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds
        ((tendsto_atTop_add_const_right _ (-K) hnorm).congr fun t => (sub_eq_add_neg _ _).symm)
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hev] with t ht using hbound t ht
  have hbot : atBot ≤ cocompact ℝ := by
    first
    | exact atBot_le_cocompact
    | (rw [Real.cocompact_eq]; exact le_sup_left)
  have htop : atTop ≤ cocompact ℝ := by
    first
    | exact atTop_le_cocompact
    | (rw [Real.cocompact_eq]; exact le_sup_right)
  have := integral_of_hasDerivAt_of_tendsto
    (f' := fun t : ℝ => (((t : ℂ) - α) ^ 2 * ((t : ℂ) - β) ^ 2)⁻¹) hderiv hint
    (hlim.mono_left hbot) (hlim.mono_left htop)
  rw [this, sub_self]

end RamanujanPetersson.EllW2


