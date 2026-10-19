-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_exists_thetaSum_rowElt_eq_tsum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T04:52:15.216118+00:00
-- url     : https://prove2.me/submissions/3d9a07af-8762-4945-9213-d56a186684bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_exists_mellin_thetaAverage_eq_tsum
import Mathlib


section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L3T: the candidate cut `L3T_Cut63V` — Lemma 6.3 *before* the exact radial smoothing.

It is Prop 5.1 + Cor 5.2 + Lemmas 5.3, 5.4 (sheet profiles), 6.1 (first formula, (6.?)
`eq:reflection-unreflected`), 6.2 and the unfolding in the proof of Lemma 6.3, for the quotient
average `T_m(l)` of (6.?) `eq:reflection-theta-average`:
* the forward side is `T_m(l) = ∑ γ₂(𝔠) q_𝔠^{-1/2} q_𝔫^{-1} ϑ(𝔄) χ_𝔄(m) V(q_𝔄 l)`, with the
  radial profile `V` of (5.20), whose Mellin transform is (5.21);
* the reflected side is (6.22)'s expansion with the unsmoothed sheet profiles
  `H(x/l)` (`H_{υ,κ}` of (6.?) `eq:reflection-profiles`, summed over `ℓ`) in place of
  `Φ(Z x)`; `H` obeys (5.17).
Cut63 follows from it by Lemma 5.5 (proved in `L3T_Gamma`/`L3T_Kernel`/`L3T_Smooth`) and the
`T`-average `B_m(Z) = ∫ K(T) T_m(T/Z) dT/T` (`L3T_Main`). -/

open Classical in
/-- The candidate cut: Lemma 6.3 before the exact radial smoothing (see the module doc). -/
def L3T_Cut63V (n : ℕ) (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : Prop :=
  let βp : ℝ → ℕ → ℝ := fun q e =>
    if e = 0 then 1
    else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
    else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
    else 0
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
    ∃ (V : ℝ → ℝ) (rr : ℕ) (C₀ A₀ : ℝ), Measurable V ∧ 0 < C₀ ∧ 0 < A₀ ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (V t : ℂ)) s ∧
        mellin (fun t => (V t : ℂ)) s =
          (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) ∧
    ∃ (T : Type) (_ : Fintype T)
      (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
      (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
        Ideal (𝓞 F) → ℂ)
      (H : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
      (α : ℝ), 0 < α ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
        ∏ P ∈ (normalizedFactors 𝔣).toFinset,
          βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
      (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
        ‖iteratedDeriv j (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
          C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
      (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
        ∀ l : ℝ, 0 < l →
        ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
            {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
          gaussPhase g 2 p.1.1 /
              ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
            χ.thetaChar g (p.1.1 * p.2.1 ^ 3) *
            residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) (rowElt g r) *
            ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ) =
          ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
              {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
            ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
              ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
              ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                  residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                  ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                  H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                    (l⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                      ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                        (Ideal.absNorm k.1.1 : ℝ) ^ 2)))

end ArtinPrimitiveRoots

end
end

section
section
/-! L3T, Lemma 5.5 part 1: bounds for `1/Γ` on vertical strips and the entire function
`R_V(s) = e^{s²} / V̂(s)` of the proof of Lemma 5.5, for `V̂(s) = C₀ A₀^s (Γ(s+5/6) Γ(s+7/6))^r`. -/

open Complex Real Set Filter Topology MeasureTheory

namespace ArtinPrimitiveRoots.L3T

lemma norm_Gamma_le {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [mem_Ioi] at hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖cexp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖cexp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have ha : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have hb : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  calc ‖(cexp (-z * I) - cexp (z * I)) * I / 2‖
      = ‖cexp (-z * I) - cexp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; norm_num
    _ ≤ (‖cexp (-z * I)‖ + ‖cexp (z * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by rw [h1, h2]; gcongr
    _ = Real.exp |z.im| := by ring

lemma norm_inv_Gamma_le_of_re_lt_one {z : ℂ} (hz : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (1 - z.re) * Real.exp (π * |z.im|) / π := by
  have hG1 : 0 < Real.Gamma (1 - z.re) := Real.Gamma_pos_of_pos (by linarith)
  by_cases h0 : Complex.Gamma z = 0
  · rw [h0, inv_zero, norm_zero]; positivity
  have hre : 0 < (1 - z).re := by simp; linarith
  have hG' : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hr := Complex.Gamma_mul_Gamma_one_sub z
  have hs : Complex.sin (π * z) ≠ 0 := by
    intro hs; rw [hs, div_zero] at hr; exact mul_ne_zero h0 hG' hr
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
    field_simp
    rw [hr]; field_simp
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hg := norm_Gamma_le hre
  have hsn := norm_sin_le (π * z)
  have him : (↑π * z).im = π * z.im := by simp
  rw [him, abs_mul, abs_of_pos Real.pi_pos] at hsn
  have : (1 - z).re = 1 - z.re := by simp
  rw [this] at hg
  gcongr

/-- `1/Γ` grows at most like `e^{π|Im z|}` on the part `|Im z| ≥ 1` of any left half-strip. -/
lemma norm_inv_Gamma_le_aux (L : ℝ) (hL : 1 / 2 ≤ L) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ z : ℂ,
    -L ≤ z.re → z.re ≤ 1 / 2 + n → 1 ≤ |z.im| → ‖(Complex.Gamma z)⁻¹‖ ≤ B * Real.exp (π * |z.im|) := by
  have hcpt : IsCompact (Icc (1 / 2 : ℝ) (1 + L)) := isCompact_Icc
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) (1 + L)) := by
    intro x hx
    refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt.continuousWithinAt
    have : (0 : ℝ) < x := by linarith [hx.1]
    intro h; rw [h] at this; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  obtain ⟨G, hG⟩ := hcpt.exists_bound_of_continuousOn hcont
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG (1 / 2) ⟨le_rfl, by linarith⟩)
  refine ⟨G / π, div_nonneg hG0 Real.pi_pos.le, fun n => ?_⟩
  induction n with
  | zero =>
    intro z hz1 hz2 _
    simp at hz2
    refine (norm_inv_Gamma_le_of_re_lt_one (by linarith)).trans ?_
    have hx : 1 - z.re ∈ Icc (1 / 2 : ℝ) (1 + L) := ⟨by linarith, by linarith⟩
    have := hG _ hx
    rw [Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by linarith [hx.1])).le] at this
    rw [div_mul_eq_mul_div]
    gcongr
  | succ n ih =>
    intro z hz1 hz2 hz3
    by_cases hle : z.re ≤ 1 / 2 + n
    · exact ih z hz1 hle hz3
    push Not at hle
    set w := z - 1 with hw
    have hwne : w ≠ 0 := by
      intro h; have : w.im = 0 := by rw [h]; simp
      simp [hw] at this; rw [this] at hz3; simp at hz3; linarith
    have hzw : z = w + 1 := by rw [hw]; ring
    have hwre : w.re = z.re - 1 := by simp [hw]
    have hwim : w.im = z.im := by simp [hw]
    have hnorm : 1 ≤ ‖w‖ := by
      calc (1 : ℝ) ≤ |w.im| := by rw [hwim]; exact hz3
        _ ≤ ‖w‖ := Complex.abs_im_le_norm w
    rw [show Complex.Gamma z = w * Complex.Gamma w by rw [hzw, Complex.Gamma_add_one w hwne],
      mul_inv, norm_mul, norm_inv]
    have hih := ih w (by rw [hwre]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (by rw [hwre]; push_cast at hz2; linarith) (by rw [hwim]; exact hz3)
    rw [hwim] at hih
    calc ‖w‖⁻¹ * ‖(Complex.Gamma w)⁻¹‖ ≤ 1 * ‖(Complex.Gamma w)⁻¹‖ := by
          gcongr; exact inv_le_one_of_one_le₀ hnorm
      _ ≤ _ := by rw [one_mul]; exact hih

/-- `‖1/Γ(z)‖ ≤ B e^{π |Im z|}` on every vertical strip. -/
lemma norm_inv_Gamma_le_strip (a b : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
    ‖(Complex.Gamma z)⁻¹‖ ≤ B * Real.exp (π * |z.im|) := by
  obtain ⟨B₂, hB₂0, hB₂⟩ := norm_inv_Gamma_le_aux (max (1 / 2) (-a)) (le_max_left _ _)
  have hK : IsCompact (Icc a b ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn
    (Complex.differentiable_one_div_Gamma.continuous.continuousOn (s := _))
  refine ⟨max B₁ 0 + B₂, by positivity, fun z hz1 hz2 => ?_⟩
  have he : 1 ≤ Real.exp (π * |z.im|) := Real.one_le_exp (by positivity)
  by_cases him : |z.im| ≤ 1
  · have hmem : z ∈ Icc a b ×ℂ Icc (-1 : ℝ) 1 :=
      ⟨⟨hz1, hz2⟩, ⟨(abs_le.1 him).1, (abs_le.1 him).2⟩⟩
    calc ‖(Complex.Gamma z)⁻¹‖ ≤ B₁ := hB₁ z hmem
      _ ≤ max B₁ 0 + B₂ := by linarith [le_max_left B₁ 0]
      _ ≤ (max B₁ 0 + B₂) * Real.exp (π * |z.im|) := by
          have : 0 ≤ max B₁ 0 + B₂ := by positivity
          nlinarith
  · push Not at him
    have hb : z.re ≤ 1 / 2 + (⌈b⌉₊ : ℝ) := by
      have := Nat.le_ceil b; linarith
    have h1 : -max (1 / 2) (-a) ≤ z.re := by
      have := le_max_right (1 / 2 : ℝ) (-a); linarith
    calc ‖(Complex.Gamma z)⁻¹‖ ≤ B₂ * Real.exp (π * |z.im|) := hB₂ ⌈b⌉₊ z h1 hb him.le
      _ ≤ (max B₁ 0 + B₂) * Real.exp (π * |z.im|) := by
          gcongr; linarith [le_max_right B₁ 0]

/-- `R_V(s) = e^{s²} / (C₀ A₀^s (Γ(s+5/6) Γ(s+7/6))^r)`, written with `1/Γ` (entire). -/
noncomputable def Rk (C₀ A₀ : ℝ) (rr : ℕ) (s : ℂ) : ℂ :=
  cexp (s ^ 2) * (C₀ : ℂ)⁻¹ * (A₀ : ℂ) ^ (-s) *
    ((Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹) ^ rr

lemma Rk_differentiable (C₀ A₀ : ℝ) (hA : 0 < A₀) (rr : ℕ) :
    Differentiable ℂ (Rk C₀ A₀ rr) := by
  have hg := Complex.differentiable_one_div_Gamma
  have hA' : (A₀ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  unfold Rk
  refine Differentiable.mul (Differentiable.mul (Differentiable.mul ?_ ?_) ?_) ?_
  · exact (differentiable_id.pow 2).cexp
  · exact differentiable_const _
  · exact fun s => (differentiableAt_id.neg).const_cpow (Or.inl hA')
  · exact ((hg.comp (differentiable_id.add_const _)).mul
      (hg.comp (differentiable_id.add_const _))).pow rr

lemma Rk_mul_mellin (C₀ A₀ : ℝ) (hC : 0 < C₀) (hA : 0 < A₀) (rr : ℕ) {s : ℂ}
    (hs : -(5 / 6 : ℝ) < s.re) :
    Rk C₀ A₀ rr s * ((C₀ : ℂ) * (A₀ : ℂ) ^ s *
      (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr) = cexp (s ^ 2) := by
  have hA' : (A₀ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hC' : (C₀ : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have h1 : Complex.Gamma (s + 5 / 6) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp; norm_num at hs ⊢; linarith)
  have h2 : Complex.Gamma (s + 7 / 6) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp; norm_num at hs ⊢; linarith)
  have hp : (A₀ : ℂ) ^ (-s) * (A₀ : ℂ) ^ s = 1 := by
    have : (A₀ : ℂ) ^ s ≠ 0 := by rw [Complex.cpow_def_of_ne_zero hA']; exact Complex.exp_ne_zero _
    rw [Complex.cpow_neg, inv_mul_cancel₀ this]
  unfold Rk
  calc cexp (s ^ 2) * (C₀ : ℂ)⁻¹ * (A₀ : ℂ) ^ (-s) *
        ((Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹) ^ rr *
        ((C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr)
      = cexp (s ^ 2) * ((C₀ : ℂ)⁻¹ * C₀) * ((A₀ : ℂ) ^ (-s) * (A₀ : ℂ) ^ s) *
        (((Complex.Gamma (s + 5 / 6))⁻¹ * Complex.Gamma (s + 5 / 6)) *
          ((Complex.Gamma (s + 7 / 6))⁻¹ * Complex.Gamma (s + 7 / 6))) ^ rr := by ring
    _ = cexp (s ^ 2) := by
      rw [inv_mul_cancel₀ hC', hp, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]; simp

lemma Rk_bound (C₀ A₀ : ℝ) (hC : 0 < C₀) (hA : 0 < A₀) (rr : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖Rk C₀ A₀ rr s‖ ≤ C * Real.exp (-(1 / 2) * s.im ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := norm_inv_Gamma_le_strip (a + 5 / 6) (b + 7 / 6)
  refine ⟨Real.exp (a ^ 2 + b ^ 2) * C₀⁻¹ * (A₀ ^ (-a) + A₀ ^ (-b)) * (B ^ 2) ^ rr *
    Real.exp (2 * π ^ 2 * rr ^ 2), by positivity, fun s h1 h2 => ?_⟩
  set σ := s.re
  set t := s.im
  have hn1 : ‖(Complex.Gamma (s + 5 / 6))⁻¹‖ ≤ B * Real.exp (π * |t|) := by
    have := hB (s + 5 / 6) (by simp; norm_num; linarith) (by simp; norm_num; linarith)
    simpa using this
  have hn2 : ‖(Complex.Gamma (s + 7 / 6))⁻¹‖ ≤ B * Real.exp (π * |t|) := by
    have := hB (s + 7 / 6) (by simp; norm_num; linarith) (by simp; norm_num; linarith)
    simpa using this
  have he : ‖cexp (s ^ 2)‖ = Real.exp (σ ^ 2 - t ^ 2) := by
    rw [Complex.norm_exp]; congr 1; simp [sq, σ, t]
  have hσ : σ ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total 0 σ with h | h
    · have := pow_le_pow_left₀ h h2 2; nlinarith [sq_nonneg a]
    · have := pow_le_pow_left₀ (neg_nonneg.2 h) (neg_le_neg h1) 2
      rw [neg_sq, neg_sq] at this; nlinarith [sq_nonneg b]
  have hAσ : A₀ ^ (-σ) ≤ A₀ ^ (-a) + A₀ ^ (-b) := by
    rcases le_or_gt 1 A₀ with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show -σ ≤ -a by linarith)
      linarith [Real.rpow_nonneg hA.le (-b)]
    · have := Real.rpow_le_rpow_of_exponent_ge hA h.le (show -b ≤ -σ by linarith)
      linarith [Real.rpow_nonneg hA.le (-a)]
  have hexp : Real.exp (-t ^ 2) * (Real.exp (π * |t|) * Real.exp (π * |t|)) ^ rr ≤
      Real.exp (2 * π ^ 2 * rr ^ 2) * Real.exp (-(1 / 2) * t ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith [sq_nonneg (|t| - 2 * π * rr)]
  have hnorm : ‖Rk C₀ A₀ rr s‖ = Real.exp (σ ^ 2 - t ^ 2) * C₀⁻¹ * A₀ ^ (-σ) *
      (‖(Complex.Gamma (s + 5 / 6))⁻¹‖ * ‖(Complex.Gamma (s + 7 / 6))⁻¹‖) ^ rr := by
    unfold Rk
    rw [norm_mul, norm_mul, norm_mul, he, norm_pow, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hC.le, Complex.norm_cpow_eq_rpow_re_of_pos hA]
    simp [σ]
  rw [hnorm]
  calc Real.exp (σ ^ 2 - t ^ 2) * C₀⁻¹ * A₀ ^ (-σ) *
        (‖(Complex.Gamma (s + 5 / 6))⁻¹‖ * ‖(Complex.Gamma (s + 7 / 6))⁻¹‖) ^ rr
      ≤ Real.exp (a ^ 2 + b ^ 2) * Real.exp (-t ^ 2) * C₀⁻¹ * (A₀ ^ (-a) + A₀ ^ (-b)) *
        (B * Real.exp (π * |t|) * (B * Real.exp (π * |t|))) ^ rr := by
        rw [sub_eq_add_neg, Real.exp_add]
        gcongr
    _ = Real.exp (a ^ 2 + b ^ 2) * C₀⁻¹ * (A₀ ^ (-a) + A₀ ^ (-b)) * (B ^ 2) ^ rr *
        (Real.exp (-t ^ 2) * (Real.exp (π * |t|) * Real.exp (π * |t|)) ^ rr) := by ring
    _ ≤ Real.exp (a ^ 2 + b ^ 2) * C₀⁻¹ * (A₀ ^ (-a) + A₀ ^ (-b)) * (B ^ 2) ^ rr *
        (Real.exp (2 * π ^ 2 * rr ^ 2) * Real.exp (-(1 / 2) * t ^ 2)) := by gcongr
    _ = _ := by ring

end ArtinPrimitiveRoots.L3T

end
end

section
section
/-! # C3P_Shift: one-variable contour shifts of vertical line integrals

* `C3P_shift`: no pole, with a decaying integrable majorant `g (Im s)` on the strip;
* `C3P_shift_pole`: one simple pole `p` inside the strip, `f = A / (s - p)`; the majorant is only
  required on the two lines and for `|Im s| ≥ 1`.

The pole computation follows `OAI.SevenEighths.PrincipalMellinResidues.verticalIntegral_simple_pole`
(copied and adapted). -/

set_option maxHeartbeats 1000000

open Complex MeasureTheory Filter Topology Set

namespace ArtinPrimitiveRoots

namespace C3P

lemma integrable_line_of_le {f : ℂ → ℂ} {g : ℝ → ℝ} {c : ℝ}
    (hc : ContinuousOn f {s | s.re = c}) (hg : Integrable g)
    (hb : ∀ t : ℝ, ‖f (c + t * I)‖ ≤ g t) :
    Integrable fun t : ℝ => f (c + t * I) := by
  refine hg.mono' ?_ (Eventually.of_forall hb)
  refine (hc.comp_continuous (by fun_prop) fun t => ?_).aestronglyMeasurable
  simp

lemma horizontal_tendsto {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atTop (𝓝 0)) (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → 1 ≤ T → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + T * I)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun T : ℝ => g T * |b - a|) atTop (𝓝 0) := by
    simpa using hg.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  exact hb x T hx.1.le hx.2 hT

lemma horizontal_tendsto_neg {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : Tendsto g atBot (𝓝 0))
    (hb : ∀ x T : ℝ, a ≤ x → x ≤ b → T ≤ -1 → ‖f (x + T * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, f (x + (-T) * I)) atTop (𝓝 0) := by
  have hg' : Tendsto (fun T : ℝ => g (-T)) atTop (𝓝 0) := hg.comp tendsto_neg_atTop_atBot
  have hexp : Tendsto (fun T : ℝ => g (-T) * |b - a|) atTop (𝓝 0) := by
    simpa using hg'.mul_const |b - a|
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 1] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  have := hb x (-T) hx.1.le hx.2 (by linarith)
  simpa using this

/-- Shifting a vertical line integral across a strip on which `f` is holomorphic, given an
integrable majorant `g (Im s)` tending to `0` at `±∞`. -/
theorem C3P_shift {f : ℂ → ℂ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {s | a ≤ s.re ∧ s.re ≤ b})
    (hg : Integrable g) (hgt : Tendsto g atTop (𝓝 0)) (hgb : Tendsto g atBot (𝓝 0))
    (hb : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g s.im) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  have hc : ∀ c, a ≤ c → c ≤ b → ContinuousOn f {s | s.re = c} := fun c h1 h2 =>
    hf.continuousOn.mono fun s hs => by simp only [Set.mem_ofPred_eq] at hs ⊢; constructor <;> linarith
  have hia := integrable_line_of_le (hc a le_rfl hab) hg fun t => by
    simpa using hb (a + t * I) (by simp) (by simp [hab])
  have hib := integrable_line_of_le (hc b hab le_rfl) hg fun t => by
    simpa using hb (b + t * I) (by simp [hab]) (by simp)
  have hrect : ∀ T : ℝ, (∫ x : ℝ in a..b, f (x + (-T) * I)) - (∫ x : ℝ in a..b, f (x + T * I)) +
      I • (∫ y : ℝ in -T..T, f (b + y * I)) - I • (∫ y : ℝ in -T..T, f (a + y * I)) = 0 := by
    intro T
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
      (hf.mono fun z hz => by
        rw [mem_reProdIm, Set.uIcc_of_le hab] at hz
        exact ⟨hz.1.1, hz.1.2⟩)
    simpa using this
  have hup := horizontal_tendsto (f := f) hab hgt fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hlow := horizontal_tendsto_neg (f := f) hab hgb fun x T h1 h2 _ => by
    simpa using hb (x + T * I) (by simpa using h1) (by simpa using h2)
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (a + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (a + τ * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, f (b + y * I)) atTop
      (𝓝 (∫ τ : ℝ, f (b + τ * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h1 := ((hlow.sub hup).add ((hvb.const_smul I).sub (hva.const_smul I)))
  have h2 : Tendsto (fun T : ℝ => (0 : ℂ)) atTop
      (𝓝 ((0 - 0) + ((I • ∫ τ : ℝ, f (b + τ * I)) - I • ∫ τ : ℝ, f (a + τ * I)))) := by
    refine h1.congr fun T => ?_
    rw [← hrect T]
    ring
  have h3 := tendsto_nhds_unique tendsto_const_nhds h2
  simp only [sub_self, zero_add, smul_eq_mul] at h3
  rw [← mul_sub, eq_comm, mul_eq_zero, sub_eq_zero] at h3
  exact (h3.resolve_left I_ne_zero).symm

/-! ### A simple pole -/

end C3P

end ArtinPrimitiveRoots

end
end

section
section
/-! L3T, Lemma 5.5 part 2: the kernel `K(e^τ) = (2π)^{-1} ∫ R_V(c+it) e^{(c+it)τ} dt` of (5.26),
independent of `c`, with the two-sided decay (5.22) in the log variable. -/

open Complex Real Set Filter Topology MeasureTheory

namespace ArtinPrimitiveRoots.L3T

variable (C₀ A₀ : ℝ) (rr : ℕ)

/-- The line integral `∫ R_V(c+it) e^{(c+it)τ} dt`. -/
noncomputable def lineK (c τ : ℝ) : ℂ :=
  ∫ t : ℝ, Rk C₀ A₀ rr (c + t * I) * cexp ((c + t * I) * τ)

/-- The kernel of Lemma 5.5 in the log variable: `kk τ = K(e^τ)`. -/
noncomputable def kk (τ : ℝ) : ℂ := (2 * π : ℂ)⁻¹ * lineK C₀ A₀ rr 0 τ

lemma tendsto_gauss_atTop : Tendsto (fun t : ℝ => Real.exp (-(1 / 2) * t ^ 2)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have := (tendsto_pow_atTop (α := ℝ) two_ne_zero).const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := tendsto_neg_atTop_atBot.comp this
  refine h2.congr fun t => ?_
  simp

lemma tendsto_gauss_atBot : Tendsto (fun t : ℝ => Real.exp (-(1 / 2) * t ^ 2)) atBot (𝓝 0) := by
  have := tendsto_gauss_atTop.comp tendsto_neg_atBot_atTop
  refine this.congr fun t => ?_
  simp

lemma norm_cexp_line (c t τ : ℝ) : ‖cexp ((c + t * I) * τ)‖ = Real.exp (c * τ) := by
  rw [Complex.norm_exp]; congr 1; simp

variable {C₀ A₀}

lemma lineK_eq (hC : 0 < C₀) (hA : 0 < A₀) {a b : ℝ} (hab : a ≤ b) (τ : ℝ) :
    lineK C₀ A₀ rr a τ = lineK C₀ A₀ rr b τ := by
  obtain ⟨C, hC0, hR⟩ := Rk_bound C₀ A₀ hC hA rr a b
  unfold lineK
  refine C3P.C3P_shift (f := fun s => Rk C₀ A₀ rr s * cexp (s * τ))
    (g := fun t => C * Real.exp ((|a| + |b|) * |τ|) * Real.exp (-(1 / 2) * t ^ 2)) hab ?_ ?_ ?_ ?_ ?_
  · exact ((Rk_differentiable C₀ A₀ hA rr).mul
      (differentiable_id.mul_const _).cexp).differentiableOn
  · exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  · simpa using tendsto_gauss_atTop.const_mul (C * Real.exp ((|a| + |b|) * |τ|))
  · simpa using tendsto_gauss_atBot.const_mul (C * Real.exp ((|a| + |b|) * |τ|))
  · intro s h1 h2
    rw [norm_mul]
    have he : ‖cexp (s * τ)‖ ≤ Real.exp ((|a| + |b|) * |τ|) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.2
      have : (s * τ).re = s.re * τ := by simp
      rw [this]
      have hs : |s.re| ≤ |a| + |b| := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le a, abs_nonneg b]
        · linarith [le_abs_self b, abs_nonneg a]
      calc s.re * τ ≤ |s.re * τ| := le_abs_self _
        _ = |s.re| * |τ| := abs_mul _ _
        _ ≤ (|a| + |b|) * |τ| := by gcongr
    calc ‖Rk C₀ A₀ rr s‖ * ‖cexp (s * τ)‖
        ≤ (C * Real.exp (-(1 / 2) * s.im ^ 2)) * Real.exp ((|a| + |b|) * |τ|) :=
          mul_le_mul (hR s h1 h2) he (norm_nonneg _) (by positivity)
      _ = _ := by ring

lemma kk_eq_lineK (hC : 0 < C₀) (hA : 0 < A₀) (c τ : ℝ) :
    kk C₀ A₀ rr τ = (2 * π : ℂ)⁻¹ * lineK C₀ A₀ rr c τ := by
  unfold kk
  rcases le_total 0 c with h | h
  · rw [lineK_eq rr hC hA h]
  · rw [lineK_eq rr hC hA h]

/-- (5.22) for `j = 0`, one-sided: `|K(e^τ)| ≪_c e^{cτ}` for every real `c`. -/
lemma kk_bound (hC : 0 < C₀) (hA : 0 < A₀) (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, ‖kk C₀ A₀ rr τ‖ ≤ K * Real.exp (c * τ) := by
  obtain ⟨C, hC0, hR⟩ := Rk_bound C₀ A₀ hC hA rr c c
  set G := ∫ t : ℝ, Real.exp (-(1 / 2) * t ^ 2)
  have hG : 0 ≤ G := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨(2 * π)⁻¹ * (C * G), by positivity, fun τ => ?_⟩
  rw [kk_eq_lineK rr hC hA c τ, norm_mul]
  have hpi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv]; congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hpi, mul_assoc]
  gcongr
  unfold lineK
  have hint : Integrable fun t : ℝ => C * Real.exp (-(1 / 2) * t ^ 2) * Real.exp (c * τ) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C).mul_const _
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_mul, norm_cexp_line]
    gcongr
    simpa using hR (c + t * I) (by simp) (by simp)
  · rw [integral_mul_const, integral_const_mul]

lemma kk_continuous (hC : 0 < C₀) (hA : 0 < A₀) : Continuous (kk C₀ A₀ rr) := by
  obtain ⟨C, hC0, hR⟩ := Rk_bound C₀ A₀ hC hA rr 0 0
  unfold kk lineK
  refine continuous_const.mul (continuous_of_dominated (bound := fun t =>
    C * Real.exp (-(1 / 2) * t ^ 2)) (fun τ => ?_) (fun τ => Eventually.of_forall fun t => ?_)
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C)
    (Eventually.of_forall fun t => ?_))
  · refine Continuous.aestronglyMeasurable ?_
    exact ((Rk_differentiable C₀ A₀ hA rr).continuous.comp (by fun_prop)).mul (by fun_prop)
  · rw [norm_mul, norm_cexp_line]
    simpa using hR ((0 : ℝ) + t * I) (by simp) (by simp)
  · exact continuous_const.mul (by fun_prop)

/-- From two-sided exponential bounds: `τ ↦ ‖f τ‖ e^{cτ}` is integrable for every `c`. -/
lemma integrable_mul_exp_of_bounds {f : ℝ → ℂ} (hf : Continuous f)
    (hb : ∀ c : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, ‖f τ‖ ≤ K * Real.exp (c * τ)) (c : ℝ) :
    Integrable fun τ : ℝ => ‖f τ‖ * Real.exp (c * τ) := by
  obtain ⟨K₁, hK₁, h₁⟩ := hb (-c - 1)
  obtain ⟨K₂, hK₂, h₂⟩ := hb (-c + 1)
  refine (integrable_inv_one_add_sq.const_mul (2 * (K₁ + K₂))).mono'
    ((hf.norm.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hq := Real.quadratic_le_exp_of_nonneg (abs_nonneg τ)
  have hsq : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  have key : ‖f τ‖ * Real.exp (c * τ) ≤ (K₁ + K₂) * Real.exp (-|τ|) := by
    rcases le_total 0 τ with h | h
    · have := h₁ τ
      calc ‖f τ‖ * Real.exp (c * τ) ≤ K₁ * Real.exp ((-c - 1) * τ) * Real.exp (c * τ) := by
            gcongr
        _ = K₁ * Real.exp (-|τ|) := by
            rw [mul_assoc, ← Real.exp_add, abs_of_nonneg h]; ring_nf
        _ ≤ (K₁ + K₂) * Real.exp (-|τ|) := by gcongr; linarith
    · have := h₂ τ
      calc ‖f τ‖ * Real.exp (c * τ) ≤ K₂ * Real.exp ((-c + 1) * τ) * Real.exp (c * τ) := by
            gcongr
        _ = K₂ * Real.exp (-|τ|) := by
            rw [mul_assoc, ← Real.exp_add, abs_of_nonpos h]; ring_nf
        _ ≤ (K₁ + K₂) * Real.exp (-|τ|) := by gcongr; linarith
  refine key.trans ?_
  rw [Real.exp_neg, mul_assoc]
  have he : 0 < Real.exp |τ| := Real.exp_pos _
  have : (Real.exp |τ|)⁻¹ ≤ 2 * (1 + τ ^ 2)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ he]
    rw [show 2 * (1 + τ ^ 2)⁻¹ * Real.exp |τ| = 2 * Real.exp |τ| / (1 + τ ^ 2) by ring,
      le_div_iff₀ hpos]
    nlinarith [abs_nonneg τ]
  calc (K₁ + K₂) * (Real.exp |τ|)⁻¹ ≤ (K₁ + K₂) * (2 * (1 + τ ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

end ArtinPrimitiveRoots.L3T

end
end

section
section
/-! L3T, Lemma 5.4's convolution part (5.17), in the log variable: if `k` decays faster than
every exponential at both ends and `h` is `C²` with `|h^{(j)}(x)| ≤ C min(e^{αx}, e^{-Nx})`,
then `k ⋆ h` is `C²` with the same kind of bound. -/

open Complex Real Set Filter Topology MeasureTheory

set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots.L3T

/-- `(k ⋆ h^{(j)})(t) = ∫ k(τ) h^{(j)}(t - τ) dτ`. -/
noncomputable def convJ (k h : ℝ → ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  ∫ τ : ℝ, k τ * iteratedDeriv j h (t - τ)

variable {k h : ℝ → ℂ} {α C : ℝ}

section
variable (hk : Continuous k)
  (hkb : ∀ c : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, ‖k τ‖ ≤ K * Real.exp (c * τ))
  (hα : 0 < α) (hh : ContDiff ℝ 2 h)
  (hb : ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ, ‖iteratedDeriv j h x‖ ≤ C * Real.exp (α * x))
include hk hkb hα hh hb

lemma conv_bound_int (t₀ : ℝ) :
    Integrable fun τ : ℝ => C * Real.exp (α * (t₀ + 1)) * (‖k τ‖ * Real.exp (-α * τ)) :=
  (integrable_mul_exp_of_bounds hk hkb (-α)).const_mul _

lemma conv_dom {j : ℕ} (hj : j ≤ 2) {t₀ t : ℝ} (ht : t ∈ Metric.ball t₀ 1) (τ : ℝ) :
    ‖k τ * iteratedDeriv j h (t - τ)‖ ≤
      C * Real.exp (α * (t₀ + 1)) * (‖k τ‖ * Real.exp (-α * τ)) := by
  rw [norm_mul]
  have h1 := hb j hj (t - τ)
  have ht' : t ≤ t₀ + 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht; linarith [le_abs_self (t - t₀)]
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  calc ‖k τ‖ * ‖iteratedDeriv j h (t - τ)‖ ≤ ‖k τ‖ * (C * Real.exp (α * (t - τ))) := by gcongr
    _ ≤ ‖k τ‖ * (C * Real.exp (α * (t₀ + 1) + -α * τ)) := by
        gcongr; nlinarith
    _ = _ := by rw [Real.exp_add]; ring

lemma conv_meas (j : ℕ) (hj : j ≤ 2) (t : ℝ) :
    AEStronglyMeasurable (fun τ : ℝ => k τ * iteratedDeriv j h (t - τ)) volume :=
  (hk.mul ((hh.continuous_iteratedDeriv j (by exact_mod_cast hj)).comp
    (continuous_const.sub continuous_id))).aestronglyMeasurable

lemma conv_integrable (j : ℕ) (hj : j ≤ 2) (t : ℝ) :
    Integrable fun τ : ℝ => k τ * iteratedDeriv j h (t - τ) :=
  (conv_bound_int hk hkb hα hh hb t).mono' (conv_meas hk hkb hα hh hb j hj t)
    (Eventually.of_forall fun τ => conv_dom hk hkb hα hh hb hj (Metric.mem_ball_self one_pos) τ)

lemma conv_hasDerivAt (j : ℕ) (hj : j < 2) (t₀ : ℝ) :
    HasDerivAt (convJ k h j) (convJ k h (j + 1) t₀) t₀ := by
  have hdiff : Differentiable ℝ (iteratedDeriv j h) :=
    hh.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t τ => k τ * iteratedDeriv j h (t - τ))
    (F' := fun t τ => k τ * iteratedDeriv (j + 1) h (t - τ)) (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => conv_meas hk hkb hα hh hb j hj.le t)
    (conv_integrable hk hkb hα hh hb j hj.le t₀)
    (conv_meas hk hkb hα hh hb (j + 1) hj t₀)
    (Eventually.of_forall fun τ t ht => conv_dom hk hkb hα hh hb hj ht τ)
    (conv_bound_int hk hkb hα hh hb t₀)
    (Eventually.of_forall fun τ t _ => by
      have hg : HasDerivAt (iteratedDeriv j h) (iteratedDeriv (j + 1) h (t - τ)) (t - τ) := by
        rw [iteratedDeriv_succ]; exact (hdiff (t - τ)).hasDerivAt
      have := hg.scomp t ((hasDerivAt_id t).sub_const τ)
      simpa using this.const_mul (k τ))
  exact this.2

lemma conv_continuous_two : Continuous (convJ k h 2) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  exact continuousAt_of_dominated (Eventually.of_forall fun t => conv_meas hk hkb hα hh hb 2 le_rfl t)
    (eventually_of_mem (Metric.ball_mem_nhds t₀ one_pos) fun t ht =>
      Eventually.of_forall fun τ => conv_dom hk hkb hα hh hb le_rfl ht τ)
    (conv_bound_int hk hkb hα hh hb t₀)
    (Eventually.of_forall fun τ => (continuous_const.mul
      ((hh.continuous_iteratedDeriv 2 le_rfl).comp (continuous_id.sub continuous_const))).continuousAt)

lemma conv_deriv (j : ℕ) (hj : j < 2) : deriv (convJ k h j) = convJ k h (j + 1) :=
  funext fun t => (conv_hasDerivAt hk hkb hα hh hb j hj t).deriv

lemma conv_iteratedDeriv (j : ℕ) (hj : j ≤ 2) : iteratedDeriv j (convJ k h 0) = convJ k h j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih (by omega), conv_deriv hk hkb hα hh hb j (by omega)]

lemma conv_contDiff : ContDiff ℝ 2 (convJ k h 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (conv_hasDerivAt hk hkb hα hh hb 0 (by norm_num) t).differentiableAt,
    by simp, ?_⟩
  rw [conv_deriv hk hkb hα hh hb 0 (by norm_num), contDiff_one_iff_deriv]
  refine ⟨fun t => (conv_hasDerivAt hk hkb hα hh hb 1 (by norm_num) t).differentiableAt, ?_⟩
  rw [conv_deriv hk hkb hα hh hb 1 (by norm_num)]
  exact conv_continuous_two hk hkb hα hh hb

end

/-- The two-ended bound for `k ⋆ h^{(j)}`, with a constant `C · Kc` where `Kc` depends only on
`k, α, N`. -/
lemma conv_norm_le (hk : Continuous k)
    (hkb : ∀ c : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, ‖k τ‖ ≤ K * Real.exp (c * τ))
    {N : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hgb : ∀ x : ℝ, ‖g x‖ ≤ C * min (Real.exp (α * x)) (Real.exp (-(N * x)))) (t : ℝ) :
    ‖∫ τ : ℝ, k τ * g (t - τ)‖ ≤
      C * max (∫ τ : ℝ, ‖k τ‖ * Real.exp (-α * τ)) (∫ τ : ℝ, ‖k τ‖ * Real.exp (N * τ)) *
        min (Real.exp (α * t)) (Real.exp (-(N * t))) := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hgb 0)
    exact nonneg_of_mul_nonneg_left this (lt_min (Real.exp_pos _) (Real.exp_pos _))
  have hi1 := integrable_mul_exp_of_bounds hk hkb (-α)
  have hi2 := integrable_mul_exp_of_bounds hk hkb N
  set I₁ := ∫ τ : ℝ, ‖k τ‖ * Real.exp (-α * τ)
  set I₂ := ∫ τ : ℝ, ‖k τ‖ * Real.exp (N * τ)
  have hmeas : AEStronglyMeasurable (fun τ : ℝ => k τ * g (t - τ)) volume :=
    (hk.mul (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have b1 : ‖∫ τ : ℝ, k τ * g (t - τ)‖ ≤ C * Real.exp (α * t) * I₁ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi1.const_mul _) (Eventually.of_forall fun τ => ?_)
    rw [norm_mul]
    calc ‖k τ‖ * ‖g (t - τ)‖ ≤ ‖k τ‖ * (C * Real.exp (α * (t - τ))) := by
          gcongr; exact (hgb _).trans (by gcongr; exact min_le_left _ _)
      _ = C * Real.exp (α * t) * (‖k τ‖ * Real.exp (-α * τ)) := by
          rw [show α * (t - τ) = α * t + -α * τ by ring, Real.exp_add]; ring
  have b2 : ‖∫ τ : ℝ, k τ * g (t - τ)‖ ≤ C * Real.exp (-(N * t)) * I₂ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi2.const_mul _) (Eventually.of_forall fun τ => ?_)
    rw [norm_mul]
    calc ‖k τ‖ * ‖g (t - τ)‖ ≤ ‖k τ‖ * (C * Real.exp (-(N * (t - τ)))) := by
          gcongr; exact (hgb _).trans (by gcongr; exact min_le_right _ _)
      _ = C * Real.exp (-(N * t)) * (‖k τ‖ * Real.exp (N * τ)) := by
          rw [show -(N * (t - τ)) = -(N * t) + N * τ by ring, Real.exp_add]; ring
  have hI₁ : I₁ ≤ max I₁ I₂ := le_max_left _ _
  have hI₂ : I₂ ≤ max I₁ I₂ := le_max_right _ _
  rcases le_total (Real.exp (α * t)) (Real.exp (-(N * t))) with h | h
  · rw [min_eq_left h]
    calc _ ≤ C * Real.exp (α * t) * I₁ := b1
      _ ≤ C * Real.exp (α * t) * max I₁ I₂ := by gcongr
      _ = _ := by ring
  · rw [min_eq_right h]
    calc _ ≤ C * Real.exp (-(N * t)) * I₂ := b2
      _ ≤ C * Real.exp (-(N * t)) * max I₁ I₂ := by gcongr
      _ = _ := by ring

end ArtinPrimitiveRoots.L3T

end
end

section
section
/-! L3T, Lemma 5.5 part 3: the exact Gaussian smoothing (5.23),
`∫ K(T) V(uT) dT/T = P_G(u)`, in the log variable `T = e^τ`. -/

open Complex Real Set Filter Topology MeasureTheory

namespace ArtinPrimitiveRoots.L3T

lemma rexp_image_univ : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]

lemma ofReal_exp_cpow (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ w = cexp (x * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

lemma exp_smul_cpow (x : ℝ) (s : ℂ) :
    (|Real.exp x| : ℝ) • (((Real.exp x : ℝ) : ℂ) ^ (s - 1)) = cexp (s * x) := by
  rw [abs_of_pos (Real.exp_pos x), ofReal_exp_cpow, Complex.real_smul, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1; ring

/-- The Mellin transform as an integral over the log variable. -/
lemma mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ σ : ℝ, cexp (s * σ) * f (Real.exp σ) := by
  unfold mellin
  rw [← rexp_image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    Measure.restrict_univ]
  congr 1; funext σ
  rw [← smul_assoc, exp_smul_cpow, smul_eq_mul]

lemma integrable_exp_of_mellinConvergent {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    Integrable fun σ : ℝ => cexp (s * σ) * f (Real.exp σ) := by
  unfold MellinConvergent at hf
  rw [← rexp_image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integrableOn_univ] at hf
  refine hf.congr (Eventually.of_forall fun σ => ?_)
  simp only
  rw [← smul_assoc, exp_smul_cpow, smul_eq_mul]

/-- Real moments: `σ ↦ e^{bσ} |V(e^σ)|` is integrable for `b > -5/6`. -/
lemma integrable_moment {V : ℝ → ℝ} {b : ℝ}
    (hV : MellinConvergent (fun t => (V t : ℂ)) (b : ℂ)) :
    Integrable fun σ : ℝ => Real.exp (b * σ) * |V (Real.exp σ)| := by
  refine (integrable_exp_of_mellinConvergent hV).norm.congr (Eventually.of_forall fun σ => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, show (b : ℂ) * σ = ((b * σ : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_ofReal]

variable {C₀ A₀ : ℝ} {rr : ℕ}

/-- **Lemma 5.5, (5.23)**: `∫ K(e^τ) V(u e^τ) dτ = P_G(u) = (2√π)^{-1} e^{-(log u)²/4}`. -/
theorem smooth_eq (hC : 0 < C₀) (hA : 0 < A₀) {V : ℝ → ℝ} (hVm : Measurable V)
    (hV : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
      MellinConvergent (fun t => (V t : ℂ)) s ∧
      mellin (fun t => (V t : ℂ)) s =
        (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr)
    {u : ℝ} (hu : 0 < u) :
    ∫ τ : ℝ, kk C₀ A₀ rr τ * (V (u * Real.exp τ) : ℂ) =
      (((2 * Real.sqrt π)⁻¹ * Real.exp (-(Real.log u) ^ 2 / 4) : ℝ) : ℂ) := by
  set L := Real.log u with hL
  have huL : u = Real.exp L := (Real.exp_log hu).symm
  -- the two integrable factors
  obtain ⟨C, hC0, hR⟩ := Rk_bound C₀ A₀ hC hA rr 0 0
  have hRi : Integrable fun t : ℝ => ‖Rk C₀ A₀ rr (t * I)‖ := by
    refine ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C).mono'
      ((Rk_differentiable C₀ A₀ hA rr).continuous.comp (by fun_prop)).norm.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_norm]; simpa using hR (t * I) (by simp) (by simp)
  have hV0 := (hV 0 (by simp)).1
  have hmom := integrable_moment (b := 0) (by simpa using hV0)
  simp only [zero_mul, Real.exp_zero, one_mul] at hmom
  have hVu : Integrable fun τ : ℝ => |V (u * Real.exp τ)| := by
    have := hmom.comp_add_right L
    refine this.congr (Eventually.of_forall fun τ => ?_)
    simp only; rw [huL, ← Real.exp_add, add_comm]
  have hVmeas : Measurable fun τ : ℝ => V (u * Real.exp τ) :=
    hVm.comp (measurable_const.mul Real.measurable_exp)
  -- the swap
  set f : ℝ → ℝ → ℂ := fun τ t =>
    Rk C₀ A₀ rr (t * I) * cexp ((t * I) * τ) * (V (u * Real.exp τ) : ℂ) with hf
  have hfi : Integrable (Function.uncurry f) (volume.prod volume) := by
    refine (hVu.mul_prod hRi).mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · exact ((Rk_differentiable C₀ A₀ hA rr).continuous.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) * I)).measurable
      · exact (by fun_prop : Continuous fun p : ℝ × ℝ => cexp ((p.2 : ℂ) * I * p.1)).measurable
      · exact Complex.measurable_ofReal.comp (hVmeas.comp measurable_fst)
    · simp only [Function.uncurry, hf]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : ‖cexp ((p.2 : ℂ) * I * p.1)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one, mul_comm]
  have hkk : ∀ τ, kk C₀ A₀ rr τ = (2 * π : ℂ)⁻¹ * ∫ t : ℝ, Rk C₀ A₀ rr (t * I) * cexp ((t * I) * τ) := by
    intro τ; unfold kk lineK; simp
  calc ∫ τ : ℝ, kk C₀ A₀ rr τ * (V (u * Real.exp τ) : ℂ)
      = (2 * π : ℂ)⁻¹ * ∫ τ : ℝ, ∫ t : ℝ, f τ t := by
        rw [← integral_const_mul]; congr 1; funext τ
        rw [hkk, mul_assoc, ← integral_mul_const]
    _ = (2 * π : ℂ)⁻¹ * ∫ t : ℝ, ∫ τ : ℝ, f τ t := by rw [integral_integral_swap hfi]
    _ = (2 * π : ℂ)⁻¹ * ∫ t : ℝ, cexp ((-1) * (t : ℂ) ^ 2 + (-(I * L)) * t + 0) := by
        congr 1; congr 1; funext t
        have hinner : ∫ τ : ℝ, f τ t = Rk C₀ A₀ rr (t * I) *
            (cexp (-(t * I * L)) * mellin (fun x => (V x : ℂ)) (t * I)) := by
          simp only [hf]
          rw [mellin_eq_integral_exp, ← integral_const_mul, ← integral_const_mul,
            ← integral_sub_right_eq_self _ L]
          congr 1; funext σ
          rw [huL, ← Real.exp_add, show L + (σ - L) = σ by ring]
          have : cexp (↑t * I * ↑(σ - L)) = cexp (-(↑t * I * ↑L)) * cexp (↑t * I * ↑σ) := by
            rw [← Complex.exp_add]; congr 1; push_cast; ring
          rw [this]; ring
        rw [hinner, mul_left_comm, (hV (t * I) (by simp)).2,
          Rk_mul_mellin C₀ A₀ hC hA rr (by simp), ← Complex.exp_add]
        congr 1; ring_nf; rw [Complex.I_sq]; ring
    _ = _ := by
        rw [integral_cexp_quadratic (by simp) (-(I * L)) 0]
        have hs : ((π : ℂ) / -(-1)) ^ (1 / 2 : ℂ) = ((Real.sqrt π : ℝ) : ℂ) := by
          rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
          push_cast; ring_nf
        have he : cexp (0 - (-(I * ↑L)) ^ 2 / (4 * -1)) = ((Real.exp (-L ^ 2 / 4) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
        have hsq : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
          rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
        have hs0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
        rw [hs, he]; push_cast
        rw [← hsq]; field_simp

end ArtinPrimitiveRoots.L3T

end
end

section
section
/-! L3T: generic exchange of a countable sum and an integral over `ℝ` under a product majorant,
and the translated moments of the profile `V`. -/

open Complex Real Set Filter Topology MeasureTheory

namespace ArtinPrimitiveRoots.L3T

lemma exch {ι : Type*} [Countable ι] {G : ι → ℝ → ℂ} {a : ℝ → ℝ} {b : ι → ℝ} {A : ℝ}
    (hG : ∀ i, Continuous (G i)) (ha : Integrable a) (ha0 : ∀ τ, 0 ≤ a τ) (haA : ∀ τ, a τ ≤ A)
    (hb : Summable b) (hb0 : ∀ i, 0 ≤ b i) (hab : ∀ i τ, ‖G i τ‖ ≤ a τ * b i) :
    Continuous (fun τ => ∑' i, G i τ) ∧ (∀ τ, ‖∑' i, G i τ‖ ≤ a τ * ∑' i, b i) ∧
      Integrable (fun τ => ∑' i, G i τ) ∧ ∫ τ, ∑' i, G i τ = ∑' i, ∫ τ, G i τ := by
  have hcont : Continuous (fun τ => ∑' i, G i τ) :=
    continuous_tsum hG (hb.mul_left A) fun i τ =>
      (hab i τ).trans (mul_le_mul_of_nonneg_right (haA τ) (hb0 i))
  have hnorm : ∀ τ, ‖∑' i, G i τ‖ ≤ a τ * ∑' i, b i := by
    intro τ
    have hs : Summable fun i => ‖G i τ‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hab i τ) (hb.mul_left (a τ))
    calc ‖∑' i, G i τ‖ ≤ ∑' i, ‖G i τ‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' i, a τ * b i := Summable.tsum_le_tsum (fun i => hab i τ) hs (hb.mul_left _)
      _ = a τ * ∑' i, b i := tsum_mul_left
  have hint : Integrable (fun τ => ∑' i, G i τ) :=
    (ha.mul_const _).mono' hcont.aestronglyMeasurable (Eventually.of_forall hnorm)
  have hGi : ∀ i, Integrable (G i) := fun i =>
    (ha.mul_const (b i)).mono' (hG i).aestronglyMeasurable (Eventually.of_forall (hab i))
  have hsum : Summable fun i => ∫ τ, ‖G i τ‖ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) (hb.mul_left (∫ τ, a τ))
    rw [← integral_mul_const]
    exact integral_mono (hGi i).norm (ha.mul_const _) (hab i)
  exact ⟨hcont, hnorm, hint, (integral_tsum_of_summable_integral_norm hGi hsum).symm⟩

/-- Translated moments: `∫ e^{bτ} |V(u e^τ)| dτ = u^{-b} ∫ e^{bσ} |V(e^σ)| dσ`. -/
lemma moment_translate {V : ℝ → ℝ} {b : ℝ}
    (hV : Integrable fun σ : ℝ => Real.exp (b * σ) * |V (Real.exp σ)|) {u : ℝ} (hu : 0 < u) :
    Integrable (fun τ : ℝ => Real.exp (b * τ) * |V (u * Real.exp τ)|) ∧
      ∫ τ : ℝ, Real.exp (b * τ) * |V (u * Real.exp τ)| =
        u ^ (-b) * ∫ σ : ℝ, Real.exp (b * σ) * |V (Real.exp σ)| := by
  set L := Real.log u
  have huL : u = Real.exp L := (Real.exp_log hu).symm
  have hpt : ∀ τ : ℝ, Real.exp (b * τ) * |V (u * Real.exp τ)| =
      u ^ (-b) * (Real.exp (b * (τ + L)) * |V (Real.exp (τ + L))|) := by
    intro τ
    rw [Real.rpow_def_of_pos hu, show (τ + L) = L + τ by ring, Real.exp_add L τ, ← huL]
    rw [show b * (L + τ) = b * L + b * τ by ring, Real.exp_add, show Real.log u = L from rfl]
    rw [show L * -b = -(b * L) by ring, Real.exp_neg]
    field_simp
  refine ⟨?_, ?_⟩
  · exact ((hV.comp_add_right L).const_mul (u ^ (-b))).congr
      (Eventually.of_forall fun τ => (hpt τ).symm)
  · simp_rw [hpt]
    rw [integral_const_mul, integral_add_right_eq_self
      (fun σ => Real.exp (b * σ) * |V (Real.exp σ)|) L]

end ArtinPrimitiveRoots.L3T

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField Filter Topology

/-! L2D: ideal counting in a number field. -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_finite_le (t : ℝ) : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ t}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le ⌊t⌋₊).subset fun I hI => Nat.le_floor hI

/-- The finite set of ideals of norm `≤ t` (including `⊥`). -/
noncomputable def L2D_le (F : Type*) [Field F] [NumberField F] (t : ℝ) : Finset (Ideal (𝓞 F)) :=
  (L2D_finite_le (F := F) t).toFinset

@[simp] lemma L2D_mem_le {t : ℝ} {I : Ideal (𝓞 F)} :
    I ∈ L2D_le F t ↔ (Ideal.absNorm I : ℝ) ≤ t := by
  simp [L2D_le]

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: candidate cuts beneath C1b (Proposition 4.1 (4.5)).

* `L2D_Cut64`: Lemma 6.4 (p. 38), the quadratic large sieve for `χ_𝔡(c)^3`
  (Goldmakher–Louvel, Thm 1.1).
* `L2D_Cut63`: Lemma 6.3 (p. 34) with (6.22) (p. 33), the reflected expansion of `B_m(Z)`, with
  the coefficients, row/column functions and profiles existentially quantified and only their
  stated bounds retained. -/

/-- `β_p(e)` of (6.20) (p. 33), at a prime of norm `q`. -/
noncomputable def L2D_betaP (q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1
  else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
  else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
  else 0

open Classical in
/-- `β_𝔣(𝔞')` of (6.20): the product of `β_p(v_p(𝔞'))` over the primes `p ∣ 𝔣`, and `0` when
`𝔞'` has a prime factor outside `𝔣` (so it vanishes off `A(𝔣)`). -/
noncomputable def L2D_beta {F : Type*} [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)) : ℝ :=
  if ∀ P ∈ normalizedFactors 𝔞, P ∣ 𝔣 then
    ∏ P ∈ (normalizedFactors 𝔣).toFinset,
      L2D_betaP (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)
  else 0

end ArtinPrimitiveRoots

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

theorem lseriesSummable_card {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) y := by
  have hlim : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue F)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (s := (y : ℂ)) (by simpa using hy)
  simpa using h

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- `∑_I N(I)^{-σ}` converges for `σ > 1`. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card (F := F) hσ).norm.congr fun n => ?_
  have hfib : ∀ y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      ((Ideal.absNorm (e ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
    simp [e, Equiv.sigmaFiberEquiv, y.2]
  simp only [Function.comp_apply, hfib, tsum_const, nsmul_eq_mul, LSeries.norm_term_eq,
    Complex.ofReal_re, Complex.norm_natCast]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_pow {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) (n : ℕ) :
    χ.toFun (I ^ n) = χ.toFun I ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, toFun_top]
  | succ n ih => rw [pow_succ, χ.map_mul', ih, pow_succ]

/-- **(a)** A Hecke character of nonzero modulus takes values of norm `≤ 1`. -/
theorem norm_le_one {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) (χ : HeckeChar F 𝔪) (I : Ideal (𝓞 F)) :
    ‖χ.toFun I‖ ≤ 1 := by
  by_cases h0 : χ.toFun I = 0
  · simp [h0]
  have hI : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
    have := (χ.eq_zero_iff' I).not.1 h0
    push Not at this
    exact this
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hI0 : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI.1
  have hIh0 : I ^ h ∈ (Ideal (𝓞 F))⁰ := pow_mem hI0 h
  have hprin : (I ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hIh0]
    have : (⟨I ^ h, hIh0⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI0⟩ ^ h := rfl
    rw [this, map_pow, hh, pow_card_eq_one]
  set β := Submodule.IsPrincipal.generator (I ^ h)
  have hβ : Ideal.span {β} = I ^ h := Ideal.span_singleton_generator (I ^ h)
  have hβ0 : β ≠ 0 := by
    intro hb
    rw [hb, Ideal.span_singleton_eq_bot.2 rfl] at hβ
    exact hI.1 (pow_eq_zero_iff hpos.ne' |>.1 hβ.symm)
  have hcop : Ideal.span {β} ⊔ 𝔪 = ⊤ := by
    rw [hβ, sup_comm]
    exact Ideal.sup_pow_eq_top' (by rw [sup_comm]; exact hI.2)
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪 β) := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {β} ⊔ 𝔪 := by rw [hcop]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔪 a) ?_
    rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.2 hyz.symm, map_sub, map_one,
      Ideal.Quotient.eq_zero_iff_mem.2 hz, sub_zero]
  have : Finite (𝓞 F ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  have : Finite (𝓞 F ⧸ 𝔪)ˣ := Finite.of_injective _ Units.val_injective
  set k := Nat.card (𝓞 F ⧸ 𝔪)ˣ
  have hk : 0 < k := Nat.card_pos
  have hβk : Ideal.Quotient.mk 𝔪 (β ^ k) = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_pow, map_one, ← hunit.unit_spec, ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one]
  have hval := χ.map_principal' (β ^ k) (pow_ne_zero _ hβ0) (Ideal.Quotient.eq.1 hβk)
  rw [← Ideal.span_singleton_pow, hβ, ← pow_mul, toFun_pow] at hval
  exact (Complex.norm_eq_one_of_pow_eq_one hval (Nat.mul_ne_zero hpos.ne' hk.ne')).le

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: factorization combinatorics for the proof of (4.5). -/

variable {F : Type*} [Field F] [NumberField F]

/-- The number of distinct prime factors. -/
noncomputable def L2D_omega (I : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).toFinset.card

lemma L2D_prime_of_mem {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P hP

lemma L2D_two_le_absNorm {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) :
    2 ≤ Ideal.absNorm P := by
  have hp := L2D_prime_of_mem hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    intro h; exact hp.not_isUnit (Ideal.isUnit_iff.2 h)
  omega

lemma L2D_eq_of_nf_eq {a b : Ideal (𝓞 F)} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (h : normalizedFactors a = normalizedFactors b) : a = b := by
  have h1 := prod_normalizedFactors ha
  have h2 := prod_normalizedFactors hb
  rw [associated_iff_eq] at h1 h2
  rw [← h1, ← h2, h]

lemma L2D_mem_nf_of_dvd {f Q : Ideal (𝓞 F)} (hf : f ≠ ⊥) (hQ : Prime Q) (hQf : Q ∣ f) :
    Q ∈ normalizedFactors f := by
  obtain ⟨Q', hQ', hassoc⟩ := exists_mem_normalizedFactors_of_dvd hf hQ.irreducible hQf
  rw [associated_iff_eq] at hassoc
  rwa [hassoc]

/-! ### `β_p` and the sum of `β_𝔣` -/

/-- The geometric constant bounding `∑_e β_p(e)`. -/
noncomputable def L2D_E0 : ℝ := 2 / (1 - (2 : ℝ) ^ (-(1 / 3 : ℝ)))

lemma L2D_r_lt_one : (2 : ℝ) ^ (-(1 / 3 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma L2D_r_pos : 0 < (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity

lemma L2D_E0_pos : 0 < L2D_E0 := by
  unfold L2D_E0
  have := L2D_r_lt_one
  apply div_pos (by norm_num); linarith

lemma L2D_betaP_nonneg (q : ℝ) (hq : 0 ≤ q) (e : ℕ) : 0 ≤ L2D_betaP q e := by
  unfold L2D_betaP
  split_ifs <;> first | exact Real.rpow_nonneg hq _ | norm_num

lemma L2D_betaP_le (q : ℝ) (hq : 2 ≤ q) (e : ℕ) :
    L2D_betaP q e ≤ 2 * ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ e := by
  have hr : ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ e = (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  rw [hr]
  -- write e = 3k + j
  set k := e / 3 with hk
  have he : (e : ℝ) = 3 * k + (e % 3 : ℕ) := by
    have := Nat.div_add_mod e 3
    exact_mod_cast this.symm
  have hmod : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  -- `q^x ≤ 2^x` for `x ≤ 0`
  have hq2 : ∀ x : ℝ, x ≤ 0 → q ^ x ≤ (2 : ℝ) ^ x := fun x hx =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq hx
  unfold L2D_betaP
  split_ifs with h0 h1 h2
  · subst h0; norm_num
  · -- e = 3k + 1
    have hk' : (e : ℝ) = 3 * k + 1 := by rw [he, h1]; push_cast; ring
    calc q ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-(k : ℝ)) := hq2 _ (by simp)
      _ ≤ 2 * (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
        rw [hk']
        have : (2 : ℝ) ^ (-(k : ℝ)) = 2 * (2 : ℝ) ^ (-(k : ℝ) - 1) := by
          rw [Real.rpow_sub (by norm_num), Real.rpow_one]; field_simp
        rw [this]
        gcongr
        · norm_num
        · linarith
  · -- e = 3k, k ≥ 1
    have hk' : (e : ℝ) = 3 * k := by rw [he, h2]; push_cast; ring
    have hk1 : (1 : ℝ) ≤ k := by
      have : 1 ≤ k := by omega
      exact_mod_cast this
    calc q ^ ((1 : ℝ) / 2 - k) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2 - k) := hq2 _ (by linarith)
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) - k) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * (2 : ℝ) ^ (-((e : ℝ) / 3)) := by
        rw [hk', Real.rpow_sub (by norm_num), Real.rpow_one]
        rw [show -(3 * (k : ℝ) / 3) = -(k : ℝ) by ring, Real.rpow_neg (by norm_num)]
        ring
  · positivity

lemma L2D_sum_betaP_le (q : ℝ) (hq : 2 ≤ q) (M : ℕ) :
    ∑ e ∈ Finset.range M, L2D_betaP q e ≤ L2D_E0 := by
  set r := (2 : ℝ) ^ (-(1 / 3 : ℝ))
  have hr0 : 0 ≤ r := L2D_r_pos.le
  have hr1 : r < 1 := L2D_r_lt_one
  calc ∑ e ∈ Finset.range M, L2D_betaP q e ≤ ∑ e ∈ Finset.range M, 2 * r ^ e :=
        Finset.sum_le_sum fun e _ => L2D_betaP_le q hq e
    _ = 2 * ∑ e ∈ Finset.range M, r ^ e := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑' e : ℕ, r ^ e := by
        gcongr
        exact Summable.sum_le_tsum _ (fun _ _ => by positivity)
          (summable_geometric_of_lt_one hr0 hr1)
    _ = L2D_E0 := by rw [tsum_geometric_of_lt_one hr0 hr1]; unfold L2D_E0; ring

open Classical in
lemma L2D_beta_nonneg (𝔣 𝔞 : Ideal (𝓞 F)) : 0 ≤ L2D_beta 𝔣 𝔞 := by
  unfold L2D_beta
  split_ifs
  · exact Finset.prod_nonneg fun P _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
  · exact le_rfl

open Classical in
/-- `∑_{𝔞 ∈ s} β_𝔣(𝔞) ≤ E₀^{ω(𝔣)}` for every finite set `s` of nonzero ideals. -/
lemma L2D_sum_beta_le (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (s : Finset (Ideal (𝓞 F)))
    (hs : ∀ a ∈ s, a ≠ ⊥) :
    ∑ a ∈ s, L2D_beta 𝔣 a ≤ L2D_E0 ^ L2D_omega 𝔣 := by
  let Pf := (normalizedFactors 𝔣).toFinset
  let ι := {P // P ∈ Pf}
  let φ : Ideal (𝓞 F) → ι → ℕ := fun a P => (normalizedFactors a).count P.1
  let supp : Ideal (𝓞 F) → Prop := fun a => ∀ P ∈ normalizedFactors a, P ∣ 𝔣
  let s' := s.filter supp
  let M := ∑ a ∈ s', Multiset.card (normalizedFactors a) + 1
  let g : (ι → ℕ) → ℝ := fun e => ∏ i : ι, L2D_betaP (Ideal.absNorm i.1) (e i)
  have hβ : ∀ a ∈ s', L2D_beta 𝔣 a = g (φ a) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    unfold L2D_beta
    rw [if_pos ha.2]
    exact (Finset.prod_coe_sort Pf (fun P => L2D_betaP (Ideal.absNorm P)
      ((normalizedFactors a).count P))).symm
  have hzero : ∑ a ∈ s, L2D_beta 𝔣 a = ∑ a ∈ s', L2D_beta 𝔣 a := by
    rw [Finset.sum_filter_of_ne]
    intro a _ hne
    by_contra hns
    apply hne
    unfold L2D_beta
    rw [if_neg hns]
  have hinj : Set.InjOn φ s' := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, s'] at ha hb
    apply L2D_eq_of_nf_eq (hs a ha.1) (hs b hb.1)
    ext Q
    by_cases hQ : Q ∈ Pf
    · exact congr_fun hab ⟨Q, hQ⟩
    · have hQa : Q ∉ normalizedFactors a := by
        intro hm
        exact hQ (Multiset.mem_toFinset.2
          (L2D_mem_nf_of_dvd h𝔣 (L2D_prime_of_mem hm) (ha.2 Q hm)))
      have hQb : Q ∉ normalizedFactors b := by
        intro hm
        exact hQ (Multiset.mem_toFinset.2
          (L2D_mem_nf_of_dvd h𝔣 (L2D_prime_of_mem hm) (hb.2 Q hm)))
      rw [Multiset.count_eq_zero_of_notMem hQa, Multiset.count_eq_zero_of_notMem hQb]
  have hsub : s'.image φ ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have h1 : (normalizedFactors a).count i.1 ≤ Multiset.card (normalizedFactors a) :=
      Multiset.count_le_card _ _
    have h2 : Multiset.card (normalizedFactors a) ≤
        ∑ a ∈ s', Multiset.card (normalizedFactors a) :=
      Finset.single_le_sum (f := fun a => Multiset.card (normalizedFactors a))
        (fun _ _ => Nat.zero_le _) ha
    change (normalizedFactors a).count i.1 < M
    omega
  have hg0 : ∀ e, 0 ≤ g e := fun e =>
    Finset.prod_nonneg fun i _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
  calc ∑ a ∈ s, L2D_beta 𝔣 a = ∑ a ∈ s', L2D_beta 𝔣 a := hzero
    _ = ∑ a ∈ s', g (φ a) := Finset.sum_congr rfl hβ
    _ = ∑ e ∈ s'.image φ, g e := (Finset.sum_image hinj).symm
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range M), g e :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => hg0 e
    _ = ∏ i : ι, ∑ n ∈ Finset.range M, L2D_betaP (Ideal.absNorm i.1) n :=
        by rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, L2D_E0 := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun n _ => L2D_betaP_nonneg _ (Nat.cast_nonneg _) _
        · intro i _
          apply L2D_sum_betaP_le
          have := L2D_two_le_absNorm (Multiset.mem_toFinset.1 i.2)
          exact_mod_cast this
    _ = L2D_E0 ^ L2D_omega 𝔣 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]; rfl
open Classical in
lemma L2D_simplePart_dvd (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ∣ 𝔟 := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  have hle : ((normalizedFactors 𝔟).toFinset.filter
      fun P => (normalizedFactors 𝔟).count P = 1).val ≤ normalizedFactors 𝔟 := by
    rw [Finset.filter_val, Multiset.toFinset_val]
    exact (Multiset.filter_le _ _).trans (Multiset.dedup_le _)
  have h1 := Multiset.prod_dvd_prod_of_le hle
  have h2 := prod_normalizedFactors h𝔟
  rw [associated_iff_eq] at h2
  rw [h2] at h1
  exact h1


lemma L2D_simplePart_ne_bot (𝔟 : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) : simplePart 𝔟 ≠ ⊥ := by
  intro h
  have hd := L2D_simplePart_dvd 𝔟 h𝔟
  rw [h] at hd
  exact h𝔟 (by simpa using zero_dvd_iff.1 (show (0 : Ideal (𝓞 F)) ∣ 𝔟 from hd))

open Classical in
lemma L2D_simplePart_nf (𝔟 : Ideal (𝓞 F)) :
    normalizedFactors (simplePart 𝔟) =
      ((normalizedFactors 𝔟).toFinset.filter fun P => (normalizedFactors 𝔟).count P = 1).val := by
  unfold simplePart
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id]
  apply normalizedFactors_prod_of_prime
  intro P hP
  rw [Finset.mem_val, Finset.mem_filter, Multiset.mem_toFinset] at hP
  exact L2D_prime_of_mem hP.1

/-- Powerful ideals: nonzero, every prime exponent `≥ 2`. -/
def L2D_Powerful (h : Ideal (𝓞 F)) : Prop :=
  h ≠ ⊥ ∧ ∀ P ∈ normalizedFactors h, 2 ≤ (normalizedFactors h).count P

lemma L2D_powerful_of_mul (𝔟 h : Ideal (𝓞 F)) (h𝔟 : 𝔟 ≠ ⊥) (hh : h * simplePart 𝔟 = 𝔟) :
    L2D_Powerful h := by
  classical
  have hh0 : h ≠ ⊥ := by
    rintro rfl; apply h𝔟; rw [← hh]; simp
  refine ⟨hh0, fun P hP => ?_⟩
  have hnf := normalizedFactors_mul hh0 (L2D_simplePart_ne_bot 𝔟 h𝔟)
  rw [hh, L2D_simplePart_nf] at hnf
  have hc := congr_arg (Multiset.count P) hnf
  rw [Multiset.count_add] at hc
  have hpos : 1 ≤ (normalizedFactors h).count P := Multiset.one_le_count_iff_mem.2 hP
  by_cases h1 : (normalizedFactors 𝔟).count P = 1
  · have hmem : P ∈ ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1) := by
      rw [Finset.mem_filter, Multiset.mem_toFinset]
      exact ⟨Multiset.one_le_count_iff_mem.1 (by omega), h1⟩
    have : Multiset.count P ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1).val = 1 :=
      Multiset.count_eq_one_of_mem (Finset.nodup _) hmem
    omega
  · have hnm : P ∉ ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1) := by
      rw [Finset.mem_filter]; tauto
    have : Multiset.count P ((normalizedFactors 𝔟).toFinset.filter
        fun P => (normalizedFactors 𝔟).count P = 1).val = 0 :=
      Multiset.count_eq_zero_of_notMem hnm
    omega

lemma L2D_nf_subset_of_dvd {f h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (hfh : f ∣ h) :
    (normalizedFactors f).toFinset ⊆ (normalizedFactors h).toFinset := by
  classical
  intro P hP
  rw [Multiset.mem_toFinset] at *
  have hf : f ≠ ⊥ := by rintro rfl; exact hh (zero_dvd_iff.1 hfh)
  exact (dvd_iff_normalizedFactors_le_normalizedFactors hf hh).1 hfh |> Multiset.subset_of_le
    |> fun h => h hP

lemma L2D_omega_mono {f h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (hfh : f ∣ h) :
    L2D_omega f ≤ L2D_omega h :=
  Finset.card_le_card (L2D_nf_subset_of_dvd hh hfh)

/-- The admissible active products: squarefree `𝔣` with `𝔣² ∣ 𝔥`. -/
noncomputable def L2D_Fset (h : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (L2D_le F (Ideal.absNorm h)).filter fun f => Squarefree f ∧ f * f ∣ h

lemma L2D_mem_Fset {h f : Ideal (𝓞 F)} (hh : h ≠ ⊥) :
    f ∈ L2D_Fset h ↔ Squarefree f ∧ f * f ∣ h := by
  classical
  unfold L2D_Fset
  rw [Finset.mem_filter, L2D_mem_le]
  constructor
  · exact fun h => h.2
  · intro hf
    refine ⟨?_, hf⟩
    have hd : f ∣ h := (dvd_mul_right f f).trans hf.2
    have hN0 : Ideal.absNorm h ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (map_dvd Ideal.absNorm hd)


end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

/-! L2D: Fourier separation of a profile in the log variable ((5.19), (6.43), simplified). -/

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D core, part 1: the data of Cut63 for fixed `𝔪, χ, g`, and the elementary bounds. -/

variable {F : Type*} [Field F] [NumberField F]

/-- The frozen keys `(𝔣, 𝔞', 𝔫', s)` of Lemma 6.3 for the powerful part `𝔥`. -/
abbrev L2D_Key (𝔪 : Ideal (𝓞 F)) (T : Type) (𝔥 : Ideal (𝓞 F)) : Type _ :=
  {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
    {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T

/-- The columns: squarefree exterior ideals. -/
abbrev L2D_Col (𝔪 : Ideal (𝓞 F)) : Type _ := {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠}

/-! ### Elementary bounds -/

lemma L2D_norm_sext_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow, ← map_pow]
      have := h2.choose_spec.1
      rw [this]
      simp
    rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
  · simp

lemma L2D_norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_one₀ (L2D_norm_sext_le ι 𝔪 P x) (norm_nonneg _) ih

lemma L2D_one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/-- A finite partial sum over keys is bounded by a product of the factor bounds. -/
lemma L2D_key_sum_le {A B C' D : Type*} [Fintype D] (g : A × (B × (C' × D)) → ℝ)
    (u : A → B → ℝ) (v : C' → ℝ) (hu : ∀ a b, 0 ≤ u a b) (hv : ∀ c, 0 ≤ v c)
    (hgle : ∀ k, g k ≤ u k.1 k.2.1 * v k.2.2.1) (Ub V : ℝ)
    (hU : ∀ (sa : Finset A) (sb : Finset B), ∑ a ∈ sa, ∑ b ∈ sb, u a b ≤ Ub)
    (hV : ∀ sc : Finset C', ∑ c ∈ sc, v c ≤ V) (s : Finset (A × (B × (C' × D)))) :
    ∑ k ∈ s, g k ≤ Ub * V * Fintype.card D := by
  classical
  set sa := s.image Prod.fst
  set sb := s.image fun k => k.2.1
  set sc := s.image fun k => k.2.2.1
  have hsub : s ⊆ sa ×ˢ (sb ×ˢ (sc ×ˢ Finset.univ)) := by
    intro k hk
    simp only [Finset.mem_product, Finset.mem_univ, and_true, sa, sb, sc, Finset.mem_image]
    exact ⟨⟨k, hk, rfl⟩, ⟨k, hk, rfl⟩, ⟨k, hk, rfl⟩⟩
  have hV0 : 0 ≤ V := by simpa using hV ∅
  have hg' : ∀ k : A × (B × (C' × D)), 0 ≤ u k.1 k.2.1 * v k.2.2.1 :=
    fun k => mul_nonneg (hu _ _) (hv _)
  calc ∑ k ∈ s, g k ≤ ∑ k ∈ s, u k.1 k.2.1 * v k.2.2.1 := Finset.sum_le_sum fun k _ => hgle k
    _ ≤ ∑ k ∈ sa ×ˢ (sb ×ˢ (sc ×ˢ Finset.univ)), u k.1 k.2.1 * v k.2.2.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hg' k
    _ = (∑ a ∈ sa, ∑ b ∈ sb, u a b) * ((∑ c ∈ sc, v c) * Fintype.card D) := by
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_product, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_product]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro c _
        ring
    _ ≤ Ub * (V * Fintype.card D) := by
        have h1 : 0 ≤ ∑ a ∈ sa, ∑ b ∈ sb, u a b :=
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hu a b
        have h2 : 0 ≤ ∑ c ∈ sc, v c := Finset.sum_nonneg fun c _ => hv c
        apply mul_le_mul (hU sa sb) _ (by positivity) ((h1.trans (hU sa sb)))
        gcongr
        exact hV sc
    _ = Ub * V * Fintype.card D := by ring

end ArtinPrimitiveRoots

end
end

section
section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid
open scoped FourierTransform

/-! L2D core, part 2: the split of the reflected expansion into retained and tail parts. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

section defs
variable (υ : SClass 𝔪) (h d : Ideal (𝓞 F)) (Z R0 : ℝ)

end defs

/-! ### Basic positivity -/

lemma L2D_absNorm_pos {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (0 : ℝ) < Ideal.absNorm I :=
  lt_of_lt_of_le one_pos (L2D_one_le_absNorm hI)

lemma L2D_col_ne_bot (c : L2D_Col 𝔪) : c.1 ≠ ⊥ := c.2.1.1

lemma L2D_key_f_ne_bot {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) : k.1.1 ≠ ⊥ :=
  k.1.2.1.ne_zero

lemma L2D_key_n_ne_bot {T : Type} {h : Ideal (𝓞 F)} (k : L2D_Key 𝔪 T h) : k.2.2.1.1 ≠ ⊥ :=
  k.2.2.1.2.1

/-! ### The profile constants -/

/-! ### Term bounds -/

lemma L2D_sqrt_inv_mul_inv (y : ℝ) (hy : 0 < y) :
    (Real.sqrt y)⁻¹ * y⁻¹ = y ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_neg_one, ← Real.rpow_add hy]
  norm_num

/-- The Dedekind-type sum `∑ N(I)^{-σ}` over all ideals. -/
noncomputable def L2D_zeta (F : Type*) [Field F] [NumberField F] (σ : ℝ) : ℝ :=
  ∑' I : Ideal (𝓞 F), ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ)

lemma L2D_col_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable fun c : L2D_Col 𝔪 => ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-σ) :=
  (T12B.summable_absNorm_rpow (F := F) hσ).comp_injective Subtype.val_injective

lemma L2D_col_tsum_le (σ : ℝ) (hσ : 1 < σ) :
    ∑' c : L2D_Col 𝔪, ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-σ) ≤ L2D_zeta F σ :=
  Summable.tsum_subtype_le (f := fun I : Ideal (𝓞 F) => ((Ideal.absNorm I : ℕ) : ℝ) ^ (-σ))
    _ (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (T12B.summable_absNorm_rpow hσ)

/-! ### Coefficient bounds -/

lemma L2D_E0_ge_one : 1 ≤ L2D_E0 := by
  unfold L2D_E0
  have h1 := L2D_r_pos
  have h2 := L2D_r_lt_one
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `∑_{𝔣 ∈ sa} ∑_{𝔞' ∈ sb} β_𝔣(𝔞') ≤ #F(𝔥) E₀^{ω(𝔥)}`. -/
lemma L2D_key_beta_le (h : Ideal (𝓞 F)) (hh : h ≠ ⊥)
    (sa : Finset {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ h})
    (sb : Finset {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥}) :
    ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 ≤ (L2D_Fset h).card * L2D_E0 ^ L2D_omega h := by
  classical
  have hinner : ∀ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 ≤ L2D_E0 ^ L2D_omega h := by
    intro f _
    have hf0 : f.1 ≠ ⊥ := f.2.1.ne_zero
    have h1 : ∑ a ∈ sb, L2D_beta f.1 a.1 = ∑ a ∈ sb.map (Function.Embedding.subtype _),
        L2D_beta f.1 a := by rw [Finset.sum_map]; rfl
    rw [h1]
    calc ∑ a ∈ sb.map (Function.Embedding.subtype _), L2D_beta f.1 a
        ≤ L2D_E0 ^ L2D_omega f.1 := by
          apply L2D_sum_beta_le f.1 hf0
          intro a ha
          rw [Finset.mem_map] at ha
          obtain ⟨a', _, rfl⟩ := ha
          exact a'.2
      _ ≤ L2D_E0 ^ L2D_omega h := pow_le_pow_right₀ L2D_E0_ge_one
          (L2D_omega_mono hh ((dvd_mul_right f.1 f.1).trans f.2.2))
  have hcard : sa.card ≤ (L2D_Fset h).card := by
    calc sa.card = (sa.map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (L2D_Fset h).card := by
          apply Finset.card_le_card
          intro f hf
          rw [Finset.mem_map] at hf
          obtain ⟨f', _, rfl⟩ := hf
          exact (L2D_mem_Fset hh).2 f'.2
  calc ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 ≤ ∑ _f ∈ sa, L2D_E0 ^ L2D_omega h :=
        Finset.sum_le_sum hinner
    _ = sa.card * L2D_E0 ^ L2D_omega h := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L2D_Fset h).card * L2D_E0 ^ L2D_omega h := by
        gcongr
        · have := L2D_E0_pos; positivity

end ArtinPrimitiveRoots

end
end

section
section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D core, part 3: the tail estimate and the decomposition `B = Ret + Tail`. -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

lemma L2D_absNorm_f_sq_le {T : Type} {h : Ideal (𝓞 F)} (hh : h ≠ ⊥) (k : L2D_Key 𝔪 T h) :
    (Ideal.absNorm k.1.1 : ℝ) ^ 2 ≤ Ideal.absNorm h := by
  have hd : Ideal.absNorm (k.1.1 * k.1.1) ∣ Ideal.absNorm h := map_dvd Ideal.absNorm k.1.2.2
  have hN0 : Ideal.absNorm h ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd
  rw [map_mul] at this
  rw [sq]; exact_mod_cast this

lemma L2D_ext_sum_le_zeta (σ : ℝ) (hσ : 1 < σ) (sc : Finset {n : Ideal (𝓞 F) // IsExterior 𝔪 n}) :
    ∑ n ∈ sc, ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-σ) ≤ L2D_zeta F σ := by
  have h1 : ∑ n ∈ sc, ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-σ) =
      ∑ x ∈ sc.map (Function.Embedding.subtype _), ((Ideal.absNorm x : ℕ) : ℝ) ^ (-σ) := by
    rw [Finset.sum_map]; rfl
  rw [h1]
  exact (T12B.summable_absNorm_rpow hσ).sum_le_tsum _
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma L2D_rpow_four (n : ℝ) (hn : 0 < n) : n⁻¹ * (n ^ 3)⁻¹ = n ^ (-(4 : ℝ)) := by
  rw [Real.rpow_neg hn.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← mul_inv]
  ring

end ArtinPrimitiveRoots

end
end

section
section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid Real MeasureTheory Filter

/-! L3T: the data of `L3T_Cut63V` for fixed `𝔪, χ, g`; the smoothed profiles
`Φ(x) = ∫ K(e^τ) H(x e^{-τ}) dτ` and their (6.22) bounds. -/

variable {F : Type*} [Field F] [NumberField F]

/-- The forward theta average `T_m(l)` of Lemma 6.1, for the profile `V`. -/
noncomputable def L3T_TV {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (V : ℝ → ℝ) (m : SInt 𝔪) (l : ℝ) : ℂ :=
  ∑' p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
      {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫},
    gaussPhase g 2 p.1.1 /
        ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
      χ.thetaChar g (p.1.1 * p.2.1 ^ 3) * residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) m *
      ((V (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) * l) : ℝ) : ℂ)

/-- The reflected side of `L3T_Cut63V` for a general profile family `P` and length `l`. -/
noncomputable def L3T_RH {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (T : Type)
    (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
    (ρ lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
      Ideal (𝓞 F) → ℂ)
    (P : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
    (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)) (l : ℝ) : ℂ :=
  ∑' k : L2D_Key 𝔪 T 𝔥,
    ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
      ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
      ∑' 𝔠 : L2D_Col 𝔪,
        lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
          residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
          ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
          P r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
            (l * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
              ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                (Ideal.absNorm k.1.1 : ℝ) ^ 2))

structure L3T_Data {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪) where
  V : ℝ → ℝ
  rr : ℕ
  C₀ : ℝ
  A₀ : ℝ
  hVm : Measurable V
  hC₀ : 0 < C₀
  hA₀ : 0 < A₀
  hV : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
      MellinConvergent (fun t => (V t : ℂ)) s ∧
      mellin (fun t => (V t : ℂ)) s =
        (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ rr
  T : Type
  fT : Fintype T
  ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ
  ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → Ideal (𝓞 F) → ℂ
  lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → Ideal (𝓞 F) → ℂ
  H : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ
  α : ℝ
  hα : 0 < α
  hω : ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤ L2D_beta 𝔣 𝔞
  hρ : ∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1
  hlam : ∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1
  hH : ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))
  hHb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
    ‖iteratedDeriv j (fun t => H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
      C * min (Real.exp (α * t)) (Real.exp (-(N * t)))
  hid : ∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
    ∀ l : ℝ, 0 < l → L3T_TV g χ V (rowElt g r) l = L3T_RH g T ω ρ lam H r 𝔥 l⁻¹

attribute [instance] L3T_Data.fT

open Classical in
lemma L3T_data_of_cut (n : ℕ) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (h : L3T_Cut63V n F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪), ∃ Dd : L3T_Data χ g,
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → Dd.ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖Dd.ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
          ∏ P ∈ (normalizedFactors 𝔣).toFinset,
            L2D_betaP (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) := by
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨V, rr, C₀, A₀, hVm, hC₀, hA₀, hV, T, fT, ω, ρ, lam, H, α, hα, hω, hω0, hρ, hlam, hH,
    hHb, hid⟩ := hN₀ 𝔪 h𝔪 hs χ g
  have hω' : ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤ L2D_beta 𝔣 𝔞 := by
    intro υ 𝔥 𝔣 𝔞 𝔫 s
    unfold L2D_beta
    split_ifs with hsupp
    · exact hω υ 𝔥 𝔣 𝔞 𝔫 s
    · push Not at hsupp
      rw [hω0 υ 𝔥 𝔣 𝔞 𝔫 s hsupp, norm_zero]
  refine ⟨⟨V, rr, C₀, A₀, hVm, hC₀, hA₀, hV, T, fT, ω, ρ, lam, H, α, hα, hω', hρ, hlam, hH, hHb,
    fun r 𝔥 hh l hl => ?_⟩, hω0, hω⟩
  rw [L3T_TV, hid r 𝔥 hh l hl, L3T_RH]

namespace L3T_Data

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

/-- The kernel of Lemma 5.5 for the data. -/
noncomputable def kk (Dd : L3T_Data χ g) : ℝ → ℂ := L3T.kk Dd.C₀ Dd.A₀ Dd.rr

/-- The smoothed profiles `Φ(x) = ∫ K(e^τ) H(x e^{-τ}) dτ` (`Φ_{υ,κ}` of (6.21)). -/
noncomputable def Phi (Dd : L3T_Data χ g) (υ : SClass 𝔪) (𝔥 𝔣 𝔞 𝔫 : Ideal (𝓞 F)) (s : Dd.T)
    (x : ℝ) : ℂ :=
  ∫ τ : ℝ, Dd.kk τ * Dd.H υ 𝔥 𝔣 𝔞 𝔫 s (x * Real.exp (-τ))

lemma kk_cont (Dd : L3T_Data χ g) : Continuous Dd.kk := L3T.kk_continuous Dd.rr Dd.hC₀ Dd.hA₀

lemma kk_bd (Dd : L3T_Data χ g) :
    ∀ c : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, ‖Dd.kk τ‖ ≤ K * Real.exp (c * τ) :=
  fun c => L3T.kk_bound Dd.rr Dd.hC₀ Dd.hA₀ c

lemma Phi_exp (Dd : L3T_Data χ g) (υ 𝔥 𝔣 𝔞 𝔫 s) :
    (fun t => Dd.Phi υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) =
      L3T.convJ Dd.kk (fun t => Dd.H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) 0 := by
  funext t
  unfold Phi L3T.convJ
  congr 1; funext τ
  rw [iteratedDeriv_zero, ← Real.exp_add, sub_eq_add_neg]

lemma H_le_exp (Dd : L3T_Data χ g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 →
    ∀ t : ℝ, ‖iteratedDeriv j (fun t => Dd.H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
      C * Real.exp (Dd.α * t) ∧
    ‖iteratedDeriv j (fun t => Dd.H υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤ C * Real.exp (-t) := by
  obtain ⟨C, hC⟩ := Dd.hHb 1 one_pos
  refine ⟨max C 0, le_max_right _ _, fun υ 𝔥 𝔣 𝔞 𝔫 s j hj t => ⟨?_, ?_⟩⟩
  · refine (hC υ 𝔥 𝔣 𝔞 𝔫 s j hj t).trans ?_
    calc C * min (Real.exp (Dd.α * t)) (Real.exp (-(1 * t)))
        ≤ max C 0 * min (Real.exp (Dd.α * t)) (Real.exp (-(1 * t))) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * Real.exp (Dd.α * t) := by
          gcongr; exact min_le_left _ _
  · refine (hC υ 𝔥 𝔣 𝔞 𝔫 s j hj t).trans ?_
    calc C * min (Real.exp (Dd.α * t)) (Real.exp (-(1 * t)))
        ≤ max C 0 * min (Real.exp (Dd.α * t)) (Real.exp (-(1 * t))) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * Real.exp (-t) := by
          gcongr; exact (min_le_right _ _).trans (by simp)

lemma Phi_contDiff (Dd : L3T_Data χ g) (υ 𝔥 𝔣 𝔞 𝔫 s) :
    ContDiff ℝ 2 (fun t => Dd.Phi υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) := by
  obtain ⟨C, _, hC⟩ := Dd.H_le_exp
  rw [Phi_exp]
  exact L3T.conv_contDiff Dd.kk_cont Dd.kk_bd Dd.hα (Dd.hH υ 𝔥 𝔣 𝔞 𝔫 s)
    (fun j hj x => (hC υ 𝔥 𝔣 𝔞 𝔫 s j hj x).1)

lemma Phi_bound (Dd : L3T_Data χ g) : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ,
    j ≤ 2 → ∀ t : ℝ,
    ‖iteratedDeriv j (fun t => Dd.Phi υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
      C * min (Real.exp (Dd.α * t)) (Real.exp (-(N * t))) := by
  intro N hN
  obtain ⟨C, hC⟩ := Dd.hHb N hN
  obtain ⟨C1, _, hC1⟩ := Dd.H_le_exp
  refine ⟨C * max (∫ τ : ℝ, ‖Dd.kk τ‖ * Real.exp (-Dd.α * τ))
    (∫ τ : ℝ, ‖Dd.kk τ‖ * Real.exp (N * τ)), fun υ 𝔥 𝔣 𝔞 𝔫 s j hj t => ?_⟩
  rw [Phi_exp, L3T.conv_iteratedDeriv Dd.kk_cont Dd.kk_bd Dd.hα (Dd.hH υ 𝔥 𝔣 𝔞 𝔫 s)
    (fun j hj x => (hC1 υ 𝔥 𝔣 𝔞 𝔫 s j hj x).1) j hj]
  exact L3T.conv_norm_le Dd.kk_cont Dd.kk_bd
    ((Dd.hH υ 𝔥 𝔣 𝔞 𝔫 s).continuous_iteratedDeriv j (by exact_mod_cast hj))
    (hC υ 𝔥 𝔣 𝔞 𝔫 s j hj) t

end L3T_Data

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

/-- `𝓞 → R/𝔞R` is onto for exterior `𝔞`. -/
lemma exists_sub_mem_map {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  let O' : Submodule (𝓞 F) (SInt 𝔪) := LinearMap.range (Algebra.linearMap (𝓞 F) (SInt 𝔪))
  let J : Ideal (𝓞 F) := O'.colon {r}
  have hJ : J ⊔ 𝔞 = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hne
    have h𝔞M : 𝔞 ≤ M := le_trans le_sup_right hJM
    have hM0 : M ≠ ⊥ := fun h => h𝔞.1 (eq_bot_iff.mpr (h ▸ h𝔞M))
    let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hM0⟩
    have hvS : v ∉ placesOf 𝔪 := by
      intro hv
      have : (⊤ : Ideal (𝓞 F)) ≤ M := h𝔞.2 ▸ sup_le h𝔞M hv
      exact hM.ne_top (eq_top_iff.mpr this)
    obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hvS)
    have hdJ : d ∈ J := by
      rw [Submodule.mem_colon_singleton]
      refine ⟨n, ?_⟩
      apply Subtype.ext
      show ((algebraMap (𝓞 F) (SInt 𝔪) n : SInt 𝔪) : F) = ((d • r : SInt 𝔪) : F)
      rw [C3B.coe_algebraMap_SInt, Algebra.smul_def, Subalgebra.coe_mul, C3B.coe_algebraMap_SInt]
      have h2 : ((n : 𝓞 F) : F) = (d : F) * (r : F) := by rw [mul_comm]; exact hnd.symm
      exact h2
    exact hd (le_trans le_sup_left hJM hdJ)
  obtain ⟨j, hj, a, ha, hja⟩ := Submodule.mem_sup.mp (hJ ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ J ⊔ 𝔞)
  rw [Submodule.mem_colon_singleton] at hj
  obtain ⟨b, hb⟩ := hj
  refine ⟨b, ?_⟩
  have hb' : algebraMap (𝓞 F) (SInt 𝔪) b = algebraMap (𝓞 F) (SInt 𝔪) j * r := by
    rw [← Algebra.smul_def]; exact hb
  have : r - algebraMap (𝓞 F) (SInt 𝔪) b = algebraMap (𝓞 F) (SInt 𝔪) a * r := by
    rw [hb']
    have h1 : (1 : SInt 𝔪) = algebraMap (𝓞 F) (SInt 𝔪) j + algebraMap (𝓞 F) (SInt 𝔪) a := by
      rw [← map_add, hja, map_one]
    linear_combination r * h1
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

lemma finite_quot {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Finite (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ 𝔞) := Ring.HasFiniteQuotients.finiteQuotient h𝔞.1
  let f := Ideal.quotientMap (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪))
    Ideal.le_comap_map
  refine Finite.of_surjective f ?_
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_sub_mem_map h𝔞 r
  refine ⟨Ideal.Quotient.mk 𝔞 a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  rw [← neg_mem_iff, neg_sub]; exact ha

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-!
# L2B_Bound: crude norm bounds for the arithmetic factors

`|e| ≤ 1`, `|χ_𝔞| ≤ 1`, `|g_𝔞(k)| ≤ q_𝔞`, `|γ_j(𝔠)| ≤ q_𝔠^{1/2}`, `|F(𝔰,𝔄,h)| ≤ q_𝔰 q_𝔄`,
`|Λ(𝔞)|, |G(𝔞)| ≤ q_𝔞^{1/2}`, `|ϑ(𝔞)| ≤ q_𝔞`.
-/

namespace ArtinPrimitiveRoots.L2B

open NumberField IsDedekindDomain UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F]

/-! ### Generic lemmas -/

theorem norm_prod_map_le {α : Type*} (s : Multiset α) (f : α → ℂ) (b : α → ℝ)
    (hb : ∀ a ∈ s, 0 ≤ b a) (h : ∀ a ∈ s, ‖f a‖ ≤ b a) :
    ‖(s.map f).prod‖ ≤ (s.map b).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have hs : ∀ a ∈ s, 0 ≤ b a := fun x hx => hb x (Multiset.mem_cons_of_mem hx)
    exact mul_le_mul (h a (Multiset.mem_cons_self _ _))
      (ih hs fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      (hb a (Multiset.mem_cons_self _ _))

theorem norm_finsum_le {α : Type*} [Finite α] (f : α → ℂ) (B : ℝ) (h : ∀ a, ‖f a‖ ≤ B) :
    ‖∑ᶠ a, f a‖ ≤ Nat.card α * B := by
  have := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a, ‖f a‖ ≤ ∑ _a : α, B := Finset.sum_le_sum fun a _ => h a
    _ = Fintype.card α * B := by simp

theorem norm_prod_factors_le_sqrt (s : Multiset (Ideal (𝓞 F))) (f : Ideal (𝓞 F) → ℂ)
    (h : ∀ P ∈ s, ‖f P‖ ≤ Real.sqrt (Ideal.absNorm P)) :
    ‖(s.map f).prod‖ ≤ Real.sqrt (Ideal.absNorm s.prod) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, map_mul, Nat.cast_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    exact mul_le_mul (h a (Multiset.mem_cons_self _ _))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _) (Real.sqrt_nonneg _)

/-! ### Characters -/

theorem norm_sAddChar_le (𝔪 : Ideal (𝓞 F)) (x : F) : ‖sAddChar 𝔪 x‖ ≤ 1 := by
  unfold sAddChar
  split_ifs
  · rw [Complex.norm_exp]
    simp
  · simp

theorem norm_sexticResidueSymbol_le (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h0 h
  · simp
  · have h6 : (ι ((h.choose : 𝓞 F) : F)) ^ 6 = 1 := by
      have h' : ((h.choose : 𝓞 F) : F) ^ 6 = 1 := by
        have := congrArg (algebraMap (𝓞 F) F) h.choose_spec.1
        simpa using this
      rw [← map_pow, h', map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)).le
  · simp

theorem norm_residueSymbol_le (ι : F →+* ℂ) (𝔪 𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  refine (norm_prod_map_le _ _ (fun _ => 1) (fun _ _ => zero_le_one)
    fun P _ => norm_sexticResidueSymbol_le ι 𝔪 P x).trans ?_
  simp

theorem norm_cubicResidueChar_le (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (x : 𝓞 F ⧸ P) :
    ‖cubicResidueChar ι P x‖ ≤ 1 := by
  unfold cubicResidueChar
  split_ifs with h0 h
  · simp
  · have h3 : (ι ((h.choose : 𝓞 F) : F)) ^ 3 = 1 := by
      have h' : ((h.choose : 𝓞 F) : F) ^ 3 = 1 := by
        have := congrArg (algebraMap (𝓞 F) F) h.choose_spec.1
        simpa using this
      rw [← map_pow, h', map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num)).le
  · simp

/-! ### Quotients -/

variable {𝔪 : Ideal (𝓞 F)}

theorem card_quot_le {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    Nat.card (SInt 𝔪 ⧸ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) ≤ Ideal.absNorm 𝔞 := by
  have : Finite (𝓞 F ⧸ 𝔞) := Ring.HasFiniteQuotients.finiteQuotient h𝔞.1
  let f := Ideal.quotientMap (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪))
    Ideal.le_comap_map
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := C3M.exists_sub_mem_map h𝔞 r
    refine ⟨Ideal.Quotient.mk 𝔞 a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]; exact ha
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_surjective f hf

variable {ι : F →+* ℂ}

theorem norm_gaussPhase_le (g : AllowedGen ι 𝔪) (j : ℕ) {𝔠 : Ideal (𝓞 F)}
    (h𝔠 : IsExterior 𝔪 𝔠) : ‖gaussPhase g j 𝔠‖ ≤ Real.sqrt (Ideal.absNorm 𝔠) := by
  have := C3M.finite_quot h𝔠
  unfold gaussPhase
  have hN : (0 : ℝ) < Ideal.absNorm 𝔠 := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => h𝔠.1 (Ideal.absNorm_eq_zero_iff.1 h))
  have hs : 0 < Real.sqrt (Ideal.absNorm 𝔠) := Real.sqrt_pos.2 hN
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  have hsum : ‖∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)),
      residueSymbol ι 𝔪 𝔠 (quotLift x) ^ j * sAddChar 𝔪 ((quotLift x : F) / (g.gen 𝔠 : F))‖ ≤
      Ideal.absNorm 𝔠 := by
    refine (norm_finsum_le _ 1 fun v => ?_).trans ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_residueSymbol_le ι 𝔪 𝔠 _))
        (norm_nonneg _) (norm_sAddChar_le _ _)
    · rw [mul_one]; exact_mod_cast card_quot_le h𝔠
  rw [inv_mul_le_iff₀ hs]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) := hsum
    _ = Real.sqrt (Ideal.absNorm 𝔠) * Real.sqrt (Ideal.absNorm 𝔠) :=
      (Real.mul_self_sqrt hN.le).symm

theorem norm_cubicJacobiSum_le (ι : F →+* ℂ) {P : Ideal (𝓞 F)} (hP : P ≠ ⊥) :
    ‖cubicJacobiSum ι P‖ ≤ Ideal.absNorm P := by
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  unfold cubicJacobiSum
  refine (norm_finsum_le _ 1 fun x => ?_).trans ?_
  · rw [norm_mul]
    exact mul_le_one₀ (norm_cubicResidueChar_le ι P _) (norm_nonneg _)
      (norm_cubicResidueChar_le ι P _)
  · rw [mul_one, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem norm_gaussLambda_le (ι : F →+* ℂ) {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) :
    ‖gaussLambda ι 𝔞‖ ≤ Real.sqrt (Ideal.absNorm 𝔞) := by
  unfold gaussLambda
  conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self h𝔞]
  refine norm_prod_factors_le_sqrt _ _ fun P hP => ?_
  have hP0 : P ≠ ⊥ := (prime_of_normalized_factor P hP).ne_zero
  have hN : (0 : ℝ) < Ideal.absNorm P := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hs : 0 < Real.sqrt (Ideal.absNorm P) := Real.sqrt_pos.2 hN
  rw [norm_neg, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le,
    inv_mul_le_iff₀ hs, Real.mul_self_sqrt hN.le]
  exact norm_cubicJacobiSum_le ι hP0

theorem norm_gaussG_le (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    ‖gaussG g 𝔞‖ ≤ Real.sqrt (Ideal.absNorm 𝔞) := by
  unfold gaussG
  conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self h𝔞.1]
  refine norm_prod_factors_le_sqrt _ _ fun P hP => ?_
  have hPe := (C3M.exterior_of_mem_factors h𝔞 hP).2
  rw [norm_mul, Complex.norm_conj]
  calc _ ≤ 1 * Real.sqrt (Ideal.absNorm P) :=
        mul_le_mul (norm_sexticResidueSymbol_le ι 𝔪 P _) (norm_gaussPhase_le g 3 hPe)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_thetaChar_le (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    ‖χ.thetaChar g 𝔞‖ ≤ Ideal.absNorm 𝔞 := by
  unfold HeckeChar.thetaChar
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have h1 := norm_gaussLambda_le ι h𝔞.1
  have h2 := norm_gaussG_le g h𝔞
  have h3 := T12B.norm_le_one h𝔪 χ 𝔞
  calc _ ≤ Real.sqrt (Ideal.absNorm 𝔞) * Real.sqrt (Ideal.absNorm 𝔞) * 1 := by
        gcongr
    _ = _ := by rw [mul_one, Real.mul_self_sqrt (Nat.cast_nonneg _)]

end ArtinPrimitiveRoots.L2B

end
end

section
section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid Real MeasureTheory Filter

/-! L3T: the forward side. `B_m(Z) = ∫ K(e^τ) T_m(e^τ/Z) dτ` (Lemma 6.1, second formula), from
Lemma 5.5 term by term and an absolute exchange (crude bounds suffice: `K` decays fast). -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

instance L3T_countable_ideal : Countable (Ideal (𝓞 F)) := by
  have : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
    ext I; simp
  have hc : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [this]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
  exact Set.countable_univ_iff.1 hc

lemma L3T_ext_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.2 hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.2 hJ.2
  exact Ideal.isCoprime_iff_sup_eq.1 (h1.mul_left h2)

lemma L3T_ext_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) : IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, top_sup_eq]
  | succ n ih => rw [pow_succ]; exact L3T_ext_mul ih hI

/-- The coefficient of `B_m`. -/
noncomputable def L3T_cp (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) (m : SInt 𝔪)
    (p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} × {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫}) :
    ℂ :=
  gaussPhase g 2 p.1.1 / ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ) *
    χ.thetaChar g (p.1.1 * p.2.1 ^ 3) * residueSymbol ι 𝔪 (p.1.1 * p.2.1 ^ 3) m

lemma L3T_cp_le (h𝔪 : 𝔪 ≠ ⊥) (m : SInt 𝔪) (p) :
    ‖L3T_cp g χ m p‖ ≤ Ideal.absNorm (p.1.1 * p.2.1 ^ 3) := by
  unfold L3T_cp
  have hc := p.1.2.1
  have hn := p.2.2
  have hA := L3T_ext_mul hc (L3T_ext_pow hn 3)
  have h1 := L2B.norm_gaussPhase_le g 2 hc
  have h2 := L2B.norm_thetaChar_le h𝔪 g χ hA
  have h3 := L2B.norm_residueSymbol_le ι 𝔪 (p.1.1 * p.2.1 ^ 3) m
  have hs : 0 < Real.sqrt (Ideal.absNorm p.1.1) := Real.sqrt_pos.2 (L2D_absNorm_pos hc.1)
  have hN : (1 : ℝ) ≤ Ideal.absNorm p.2.1 := L2D_one_le_absNorm hn.1
  have hq : ‖gaussPhase g 2 p.1.1 / ((Real.sqrt (Ideal.absNorm p.1.1) * Ideal.absNorm p.2.1 : ℝ) : ℂ)‖
      ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    nlinarith
  rw [norm_mul, norm_mul]
  calc _ ≤ 1 * (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) * 1 := by gcongr
    _ = _ := by ring

lemma L3T_absNorm_A (p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
    {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫}) :
    (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) =
      (Ideal.absNorm p.1.1 : ℝ) * (Ideal.absNorm p.2.1 : ℝ) ^ 3 := by
  rw [map_mul, map_pow]; push_cast; ring

lemma L3T_summable_pairs :
    Summable fun p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
        {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} =>
      ((Ideal.absNorm p.1.1 : ℝ) ^ 2)⁻¹ * ((Ideal.absNorm p.2.1 : ℝ) ^ 6)⁻¹ := by
  have h1 : Summable fun c : L2D_Col 𝔪 => ((Ideal.absNorm c.1 : ℝ) ^ 2)⁻¹ := by
    refine (L2D_col_summable (𝔪 := 𝔪) 2 (by norm_num)).congr fun c => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]
  have h2 : Summable fun n : {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} =>
      ((Ideal.absNorm n.1 : ℝ) ^ 6)⁻¹ := by
    refine ((T12B.summable_absNorm_rpow (F := F) (σ := 6) (by norm_num)).comp_injective
      Subtype.val_injective).congr fun n => ?_
    simp only [Function.comp]
    rw [Real.rpow_neg (Nat.cast_nonneg _), show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  exact h1.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => by positivity)

/-- **Lemma 6.1, (6.?) second formula**: `B_m(Z) = ∫ K(e^τ) T_m(e^τ/Z) dτ`. -/
theorem L3T_fwd (h𝔪 : 𝔪 ≠ ⊥) (Dd : L3T_Data χ g) (m : SInt 𝔪) {Z : ℝ} (hZ : 0 < Z) :
    χ.thetaSum g m Z = ∫ τ : ℝ, Dd.kk τ * L3T_TV g χ Dd.V m (Real.exp τ / Z) := by
  set N : _ → ℝ := fun p : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠} ×
    {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} => (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) with hNdef
  have hNpos : ∀ p, 0 < N p := fun p =>
    L2D_absNorm_pos (mul_ne_zero p.1.2.1.1 (pow_ne_zero 3 p.2.2.1))
  set G : _ → ℝ → ℂ := fun p τ => L3T_cp g χ m p * (Dd.kk τ * (Dd.V (N p / Z * Real.exp τ) : ℂ))
    with hG
  -- Step A: Lemma 5.5 term by term
  have hA : χ.thetaSum g m Z = ∑' p, ∫ τ : ℝ, G p τ := by
    unfold HeckeChar.thetaSum
    congr 1; funext p
    simp only [hG]
    rw [integral_const_mul]
    have := L3T.smooth_eq Dd.hC₀ Dd.hA₀ Dd.hVm Dd.hV (div_pos (hNpos p) hZ)
    unfold L3T_Data.kk
    rw [this]
    unfold gaussianPG L3T_cp
    rfl
  -- Step B: exchange
  obtain ⟨K3, hK30, hK3⟩ := Dd.kk_bd 3
  have hmom := L3T.integrable_moment (V := Dd.V) (b := 3) (by
    simpa using (Dd.hV 3 (by norm_num)).1)
  set M3 := ∫ σ : ℝ, Real.exp (3 * σ) * |Dd.V (Real.exp σ)|
  have hM30 : 0 ≤ M3 := integral_nonneg fun _ => by positivity
  have hdom : ∀ p τ, ‖G p τ‖ ≤ ‖L3T_cp g χ m p‖ * K3 *
      (Real.exp (3 * τ) * |Dd.V (N p / Z * Real.exp τ)|) := by
    intro p τ
    simp only [hG]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := hK3 τ
    calc _ ≤ ‖L3T_cp g χ m p‖ * (K3 * Real.exp (3 * τ) * |Dd.V (N p / Z * Real.exp τ)|) := by
          gcongr
      _ = _ := by ring
  have hGi : ∀ p, Integrable (G p) := by
    intro p
    refine (((L3T.moment_translate hmom (div_pos (hNpos p) hZ)).1).const_mul
      (‖L3T_cp g χ m p‖ * K3)).mono' ?_ (Eventually.of_forall (hdom p))
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_const.mul (Dd.kk_cont.measurable.mul (Complex.measurable_ofReal.comp
      (Dd.hVm.comp (measurable_const.mul Real.measurable_exp))))
  have hsum : Summable fun p => ∫ τ : ℝ, ‖G p τ‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _)
      (fun p => ?_) ((L3T_summable_pairs (𝔪 := 𝔪)).mul_left (K3 * M3 * Z ^ 3))
    have hmt := L3T.moment_translate hmom (div_pos (hNpos p) hZ)
    calc ∫ τ : ℝ, ‖G p τ‖ ≤ ∫ τ : ℝ, ‖L3T_cp g χ m p‖ * K3 *
          (Real.exp (3 * τ) * |Dd.V (N p / Z * Real.exp τ)|) :=
          integral_mono (hGi p).norm (hmt.1.const_mul _) (hdom p)
      _ = ‖L3T_cp g χ m p‖ * K3 * ((N p / Z) ^ (-(3 : ℝ)) * M3) := by
          rw [integral_const_mul, hmt.2]
      _ ≤ N p * K3 * ((N p / Z) ^ (-(3 : ℝ)) * M3) := by
          gcongr; exact L3T_cp_le h𝔪 m p
      _ = K3 * M3 * Z ^ 3 * (((Ideal.absNorm p.1.1 : ℝ) ^ 2)⁻¹ *
            ((Ideal.absNorm p.2.1 : ℝ) ^ 6)⁻¹) := by
          rw [Real.rpow_neg (div_pos (hNpos p) hZ).le,
            show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have hc := L2D_absNorm_pos p.1.2.1.1
          have hn := L2D_absNorm_pos p.2.2.1
          simp only [hNdef]
          rw [L3T_absNorm_A]
          field_simp
  rw [hA, integral_tsum_of_summable_integral_norm hGi hsum]
  congr 1; funext τ
  simp only [hG]
  unfold L3T_TV
  rw [← tsum_mul_left]
  congr 1; funext p
  unfold L3T_cp
  rw [show N p / Z * Real.exp τ = (Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) * (Real.exp τ / Z) by
    simp only [hNdef]; ring]
  ring

end ArtinPrimitiveRoots

end
end

section
section
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid Real MeasureTheory Filter

/-! L3T: the reflected side. `∫ K(e^τ) · [expansion with H at length e^τ/Z] dτ` is the
expansion with `Φ = K ⋆ H` at `Z` (the `T`-average in the proof of Lemma 6.3), by two absolute
exchanges (the bound `|H(y)| ≤ C/y` suffices). -/

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
  {χ : HeckeChar F 𝔪} {g : AllowedGen ι 𝔪}

namespace L3T_Data

lemma H_le_inv (Dd : L3T_Data χ g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ y : ℝ, 0 < y →
    ‖Dd.H υ 𝔥 𝔣 𝔞 𝔫 s y‖ ≤ C * y⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := Dd.H_le_exp
  refine ⟨C, hC0, fun υ 𝔥 𝔣 𝔞 𝔫 s y hy => ?_⟩
  have := (hC υ 𝔥 𝔣 𝔞 𝔫 s 0 (by norm_num) (Real.log y)).2
  rwa [iteratedDeriv_zero, Real.exp_log hy, Real.exp_neg, Real.exp_log hy] at this

end L3T_Data

/-- The profile argument at length `Z`. -/
noncomputable def L3T_x {T : Type} {𝔥 : Ideal (𝓞 F)} (Z : ℝ) (d : Ideal (𝓞 F))
    (k : L2D_Key 𝔪 T 𝔥) (c : L2D_Col 𝔪) : ℝ :=
  Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm c.1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
    ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2)

lemma L3T_x_pos {T : Type} {𝔥 : Ideal (𝓞 F)} {Z : ℝ} (hZ : 0 < Z) {d : Ideal (𝓞 F)} (hd : d ≠ ⊥)
    (k : L2D_Key 𝔪 T 𝔥) (c : L2D_Col 𝔪) : 0 < L3T_x Z d k c := by
  unfold L3T_x
  have := L2D_absNorm_pos k.2.1.2
  have := L2D_absNorm_pos (L2D_col_ne_bot c)
  have := L2D_absNorm_pos (L2D_key_n_ne_bot k)
  have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
  have := L2D_absNorm_pos hd
  positivity

lemma L3T_harg {T : Type} {𝔥 : Ideal (𝓞 F)} {Z : ℝ} (hZ : 0 < Z) {d : Ideal (𝓞 F)} (hd : d ≠ ⊥)
    (k : L2D_Key 𝔪 T 𝔥) (c : L2D_Col 𝔪) (τ : ℝ) :
    (Real.exp τ / Z)⁻¹ * Ideal.absNorm k.2.1.1 * Ideal.absNorm c.1 *
        (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
      ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2) =
      L3T_x Z d k c * Real.exp (-τ) := by
  unfold L3T_x
  have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
  have := L2D_absNorm_pos hd
  rw [Real.exp_neg]
  field_simp

theorem L3T_rev (Dd : L3T_Data χ g) (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F))
    (hh : 𝔥 * simplePart r.1.1 = r.1.1) {Z : ℝ} (hZ : 0 < Z) :
    ∫ τ : ℝ, Dd.kk τ * L3T_RH g Dd.T Dd.ω Dd.ρ Dd.lam Dd.H r 𝔥 (Real.exp τ / Z)⁻¹ =
      L3T_RH g Dd.T Dd.ω Dd.ρ Dd.lam Dd.Phi r 𝔥 Z := by
  classical
  have hb0 : r.1.1 ≠ ⊥ := r.1.2.1
  set d := simplePart r.1.1 with hddef
  have hd : d ≠ ⊥ := L2D_simplePart_ne_bot _ hb0
  have hh0 : 𝔥 ≠ ⊥ := (L2D_powerful_of_mul _ 𝔥 hb0 hh).1
  obtain ⟨C1, hC10, hC1⟩ := Dd.H_le_inv
  obtain ⟨K1, hK10, hK1⟩ := Dd.kk_bd (-1)
  set a : ℝ → ℝ := fun τ => ‖Dd.kk τ‖ * Real.exp (1 * τ) with ha
  have hai : Integrable a := L3T.integrable_mul_exp_of_bounds Dd.kk_cont Dd.kk_bd 1
  have ha0 : ∀ τ, 0 ≤ a τ := fun τ => by positivity
  have haK : ∀ τ, a τ ≤ K1 := fun τ => by
    simp only [ha]
    calc ‖Dd.kk τ‖ * Real.exp (1 * τ) ≤ K1 * Real.exp (-1 * τ) * Real.exp (1 * τ) := by
          gcongr; exact hK1 τ
      _ = K1 := by rw [mul_assoc, ← Real.exp_add]; simp
  -- the column terms
  set cf : L2D_Key 𝔪 Dd.T 𝔥 → L2D_Col 𝔪 → ℂ := fun k c =>
    Dd.lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c.1 *
      residueSymbol ι 𝔪 d (g.gen c.1) ^ 3 / ((Real.sqrt (Ideal.absNorm c.1) : ℝ) : ℂ) with hcf
  set G : L2D_Key 𝔪 Dd.T 𝔥 → L2D_Col 𝔪 → ℝ → ℂ := fun k c τ =>
    cf k c * (Dd.kk τ * Dd.H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (L3T_x Z d k c * Real.exp (-τ)))
    with hG
  set ck : L2D_Key 𝔪 Dd.T 𝔥 → ℝ := fun k =>
    C1 * ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2) /
      (Z * Ideal.absNorm k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3) with hck
  have hck0 : ∀ k, 0 ≤ ck k := fun k => by
    have := L2D_absNorm_pos k.2.1.2
    have := L2D_absNorm_pos (L2D_key_n_ne_bot k)
    simp only [hck]; positivity
  set b : L2D_Key 𝔪 Dd.T 𝔥 → L2D_Col 𝔪 → ℝ := fun k c =>
    ck k * ((Ideal.absNorm c.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) with hb
  have hb0 : ∀ k c, 0 ≤ b k c := fun k c => mul_nonneg (hck0 k) (Real.rpow_nonneg (by positivity) _)
  have hbs : ∀ k, Summable (b k) := fun k => (L2D_col_summable (𝔪 := 𝔪) (3 / 2) (by norm_num)).mul_left _
  have hcf_le : ∀ k c, ‖cf k c‖ ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ := by
    intro k c
    simp only [hcf]
    have hs : 0 < Real.sqrt (Ideal.absNorm c.1) := Real.sqrt_pos.2 (L2D_absNorm_pos (L2D_col_ne_bot c))
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have h1 := Dd.hlam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 c.1
    have h2 := L2D_norm_residueSymbol_le ι 𝔪 d (g.gen c.1)
    calc _ ≤ 1 * 1 ^ 3 / Real.sqrt (Ideal.absNorm c.1) := by gcongr
      _ = _ := by simp
  have hGb : ∀ k c τ, ‖G k c τ‖ ≤ a τ * b k c := by
    intro k c τ
    have hx := L3T_x_pos hZ hd k c
    have hc := L2D_absNorm_pos (L2D_col_ne_bot c)
    have hs : 0 < Real.sqrt (Ideal.absNorm c.1) := Real.sqrt_pos.2 hc
    have hH := hC1 r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 _ (mul_pos hx (Real.exp_pos (-τ)))
    simp only [hG, ha, hb]
    rw [norm_mul, norm_mul]
    calc ‖cf k c‖ * (‖Dd.kk τ‖ * ‖Dd.H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
          (L3T_x Z d k c * Real.exp (-τ))‖)
        ≤ (Real.sqrt (Ideal.absNorm c.1))⁻¹ *
          (‖Dd.kk τ‖ * (C1 * (L3T_x Z d k c * Real.exp (-τ))⁻¹)) := by
          gcongr; exact hcf_le k c
      _ = ‖Dd.kk τ‖ * Real.exp (1 * τ) * (ck k * ((Real.sqrt (Ideal.absNorm c.1))⁻¹ *
            (Ideal.absNorm c.1 : ℝ)⁻¹)) := by
          simp only [hck, L3T_x]
          have := L2D_absNorm_pos k.2.1.2
          have := L2D_absNorm_pos (L2D_key_n_ne_bot k)
          have := L2D_absNorm_pos (L2D_key_f_ne_bot k)
          have := L2D_absNorm_pos hd
          rw [mul_inv, Real.exp_neg, inv_inv, one_mul]
          field_simp
      _ = _ := by rw [L2D_sqrt_inv_mul_inv _ hc]
  have hGc : ∀ k c, Continuous (G k c) := by
    intro k c
    have hx := L3T_x_pos hZ hd k c
    have hfun : (fun τ => Dd.H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (L3T_x Z d k c * Real.exp (-τ)))
        = fun τ => (fun t => Dd.H r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (Real.exp t))
          (Real.log (L3T_x Z d k c) - τ) := by
      funext τ; simp only; rw [Real.exp_sub, Real.exp_log hx, div_eq_mul_inv, Real.exp_neg]
    have hcH := (Dd.hH r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2).continuous
    simp only [hG]
    refine continuous_const.mul (Dd.kk_cont.mul ?_)
    rw [hfun]; exact hcH.comp (continuous_const.sub continuous_id)
  have hin := fun k => L3T.exch (hGc k) hai ha0 haK (hbs k) (hb0 k) (hGb k)
  -- the outer terms
  set A : L2D_Key 𝔪 Dd.T 𝔥 → ℂ := fun k =>
    Dd.ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
      Dd.ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 d with hA
  have hAle : ∀ k, ‖A k‖ ≤ L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ := by
    intro k
    simp only [hA]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    have h1 := Dd.hω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
    have h2 := Dd.hρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 d
    have hn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
    calc _ ≤ L2D_beta k.1.1 k.2.1.1 / (Ideal.absNorm k.2.2.1.1 : ℝ) * 1 := by
          gcongr; exact div_nonneg (L2D_beta_nonneg _ _) hn.le
      _ = _ := by ring
  set G' : L2D_Key 𝔪 Dd.T 𝔥 → ℝ → ℂ := fun k τ => A k * ∑' c, G k c τ with hG'
  set b' : L2D_Key 𝔪 Dd.T 𝔥 → ℝ := fun k => ‖A k‖ * ∑' c, b k c with hb'
  have hb'0 : ∀ k, 0 ≤ b' k := fun k => mul_nonneg (norm_nonneg _) (tsum_nonneg (hb0 k))
  have hG'b : ∀ k τ, ‖G' k τ‖ ≤ a τ * b' k := by
    intro k τ
    simp only [hG', hb']
    rw [norm_mul]
    calc ‖A k‖ * ‖∑' c, G k c τ‖ ≤ ‖A k‖ * (a τ * ∑' c, b k c) := by
          gcongr; exact (hin k).2.1 τ
      _ = _ := by ring
  have hG'c : ∀ k, Continuous (G' k) := fun k => continuous_const.mul (hin k).1
  set Mk := C1 * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥) / Z * L2D_zeta F (3 / 2)
  have hM0 : 0 ≤ Mk := by
    have : 0 ≤ L2D_zeta F (3 / 2) := tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hb'le : ∀ k, b' k ≤ (Mk * L2D_beta k.1.1 k.2.1.1) *
      ((Ideal.absNorm k.2.2.1.1 : ℕ) : ℝ) ^ (-(4 : ℝ)) := by
    intro k
    have hn := L2D_absNorm_pos (L2D_key_n_ne_bot k)
    have ha1 := L2D_one_le_absNorm k.2.1.2
    have hf2 := L2D_absNorm_f_sq_le hh0 k
    have hbeta := L2D_beta_nonneg k.1.1 k.2.1.1
    have hz : ∑' c, b k c ≤ ck k * L2D_zeta F (3 / 2) := by
      simp only [hb]; rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (L2D_col_tsum_le (3 / 2) (by norm_num)) (hck0 k)
    have hck : ck k ≤ C1 * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥) / Z *
        ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ := by
      simp only [hck]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ C1 * (Ideal.absNorm d : ℝ) ^ 2 := by positivity
      calc C1 * ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2) * Z
          ≤ C1 * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥) * Z * Ideal.absNorm k.2.1.1 := by
            have e1 : (Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2 ≤
                (Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥 :=
              mul_le_mul_of_nonneg_left hf2 (by positivity)
            have e2 : C1 * ((Ideal.absNorm d : ℝ) ^ 2 * (Ideal.absNorm k.1.1 : ℝ) ^ 2) ≤
                C1 * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥) * Ideal.absNorm k.2.1.1 :=
              (mul_le_mul_of_nonneg_left e1 hC10).trans (le_mul_of_one_le_right (by positivity) ha1)
            calc _ ≤ C1 * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥) * Ideal.absNorm k.2.1.1 * Z :=
                  mul_le_mul_of_nonneg_right e2 hZ.le
              _ = _ := by ring
        _ = _ := by field_simp
    simp only [hb']
    calc ‖A k‖ * ∑' c, b k c ≤ (L2D_beta k.1.1 k.2.1.1 * (Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹) *
          (C1 * ((Ideal.absNorm d : ℝ) ^ 2 * Ideal.absNorm 𝔥) / Z *
            ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹ * L2D_zeta F (3 / 2)) := by
          refine mul_le_mul (hAle k) (hz.trans ?_) (tsum_nonneg (hb0 k)) (by positivity)
          have : 0 ≤ L2D_zeta F (3 / 2) :=
            tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
          gcongr
      _ = (Mk * L2D_beta k.1.1 k.2.1.1) * ((Ideal.absNorm k.2.2.1.1 : ℝ)⁻¹ *
            ((Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3)⁻¹) := by ring
      _ = _ := by rw [L2D_rpow_four _ hn]
  have hb's : Summable b' := by
    have hpart : ∀ s : Finset (L2D_Key 𝔪 Dd.T 𝔥), ∑ k ∈ s, b' k ≤
        (Mk * ((L2D_Fset 𝔥).card * L2D_E0 ^ L2D_omega 𝔥)) * L2D_zeta F 4 *
          Fintype.card Dd.T := by
      intro s
      apply L2D_key_sum_le _ (fun f a => Mk * L2D_beta f.1 a.1)
        (fun n => ((Ideal.absNorm n.1 : ℕ) : ℝ) ^ (-(4 : ℝ)))
        (fun f a => mul_nonneg hM0 (L2D_beta_nonneg _ _))
        (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hb'le
      · intro sa sb
        calc ∑ f ∈ sa, ∑ a ∈ sb, Mk * L2D_beta f.1 a.1 =
              Mk * ∑ f ∈ sa, ∑ a ∈ sb, L2D_beta f.1 a.1 := by
              rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
          _ ≤ Mk * ((L2D_Fset 𝔥).card * L2D_E0 ^ L2D_omega 𝔥) := by
              gcongr; exact L2D_key_beta_le 𝔥 hh0 sa sb
      · intro sc; exact L2D_ext_sum_le_zeta 4 (by norm_num) sc
    exact summable_of_sum_le hb'0 hpart
  have hout := L3T.exch hG'c hai ha0 haK hb's hb'0 hG'b
  -- assemble
  have hpt : ∀ τ, Dd.kk τ * L3T_RH g Dd.T Dd.ω Dd.ρ Dd.lam Dd.H r 𝔥 (Real.exp τ / Z)⁻¹ =
      ∑' k, G' k τ := by
    intro τ
    unfold L3T_RH
    rw [← tsum_mul_left]
    congr 1; funext k
    simp only [hG', hA, hG]
    rw [mul_left_comm, ← tsum_mul_left]
    congr 2; funext c
    rw [L3T_harg hZ hd k c τ]
    simp only [hcf]; ring
  simp_rw [hpt]
  rw [hout.2.2.2]
  unfold L3T_RH
  congr 1; funext k
  simp only [hG']
  rw [integral_const_mul, (hin k).2.2.2]
  congr 1; congr 1; funext c
  simp only [hG]
  rw [integral_const_mul]
  simp only [hcf]
  unfold L3T_Data.Phi L3T_x
  rfl

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L3T: Cut63 (`exists_cutoff_exists_thetaSum_rowElt_eq_tsum`, Lemma 6.3 + (6.22)) from the
candidate cut `L3T_Cut63V` (Lemma 6.3 before the radial smoothing), via Lemma 5.5 (proved),
the forward `T`-average (`L3T_fwd`) and the reflected `T`-average (`L3T_rev`). -/

open Classical in
theorem L3T_chk_of_cut (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) (hcut : L3T_Cut63V n F ι) :
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
      ∃ (T : Type) (_ : Fintype T)
        (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
        (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (Φ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
        (α : ℝ), 0 < α ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
          ∏ P ∈ (normalizedFactors 𝔣).toFinset,
            βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
        (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
          ‖iteratedDeriv j (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
            C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
        (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
          ∀ Z : ℝ, 0 < Z →
          χ.thetaSum g (rowElt g r) Z =
            ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
                {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
              ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
                ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
                ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                  lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                    residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                    ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                    Φ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                      (Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                          (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                        ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                          (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  intro βp
  obtain ⟨N₀, hN₀⟩ := L3T_data_of_cut n F ι hcut
  refine ⟨N₀, fun 𝔪 h𝔪 hs χ g => ?_⟩
  obtain ⟨Dd, hω0, hω⟩ := hN₀ 𝔪 h𝔪 hs χ g
  refine ⟨Dd.T, Dd.fT, Dd.ω, Dd.ρ, Dd.lam, Dd.Phi, Dd.α, Dd.hα,
    fun υ 𝔥 𝔣 𝔞 𝔫 s => hω υ 𝔥 𝔣 𝔞 𝔫 s, hω0, Dd.hρ, Dd.hlam, Dd.Phi_contDiff, Dd.Phi_bound, ?_⟩
  intro r 𝔥 hh Z hZ
  rw [L3T_fwd h𝔪 Dd (rowElt g r) hZ]
  have hpt : ∀ τ : ℝ, L3T_TV g χ Dd.V (rowElt g r) (Real.exp τ / Z) =
      L3T_RH g Dd.T Dd.ω Dd.ρ Dd.lam Dd.H r 𝔥 (Real.exp τ / Z)⁻¹ :=
    fun τ => Dd.hid r 𝔥 hh _ (div_pos (Real.exp_pos τ) hZ)
  simp_rw [hpt]
  rw [L3T_rev Dd r 𝔥 hh hZ]
  rfl

end ArtinPrimitiveRoots

end
end

section
section
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L3T: Cut63 (Lemma 6.3 + (6.22)) from the published cut
`exists_cutoff_exists_mellin_thetaAverage_eq_tsum` (Lemma 6.3 before the radial smoothing), whose
statement is `L3T_Cut63V` with the house argument order. -/

/-- The published cut's statement is `L3T_Cut63V`. -/
theorem L3T_cut63V_of_stub (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    L3T_Cut63V n F ι :=
  exists_cutoff_exists_mellin_thetaAverage_eq_tsum n hn0 hn F ι

open Classical in
theorem exists_cutoff_exists_thetaSum_rowElt_eq_tsum (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
      ∃ (T : Type) (_ : Fintype T)
        (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
        (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (Φ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
        (α : ℝ), 0 < α ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
          ∏ P ∈ (normalizedFactors 𝔣).toFinset,
            βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
        (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
          ‖iteratedDeriv j (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
            C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
        (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
          ∀ Z : ℝ, 0 < Z →
          χ.thetaSum g (rowElt g r) Z =
            ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
                {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
              ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
                ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
                ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                  lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                    residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                    ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                    Φ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                      (Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                          (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                        ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                          (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  exact L3T_chk_of_cut n hn0 hn F ι (L3T_cut63V_of_stub n hn0 hn F ι)

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

open Classical in
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    let βp : ℝ → ℕ → ℝ := fun q e =>
      if e = 0 then 1
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 0 then q ^ ((1 : ℝ) / 2 - ((e / 3 : ℕ) : ℝ))
      else 0
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
      ∃ (T : Type) (_ : Fintype T)
        (ω : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℂ)
        (ρ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (lam : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T →
          Ideal (𝓞 F) → ℂ)
        (Φ : SClass 𝔪 → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → T → ℝ → ℂ)
        (α : ℝ), 0 < α ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ‖ω υ 𝔥 𝔣 𝔞 𝔫 s‖ ≤
          ∏ P ∈ (normalizedFactors 𝔣).toFinset,
            βp (Ideal.absNorm P) ((normalizedFactors 𝔞).count P)) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, (∃ P ∈ normalizedFactors 𝔞, ¬ P ∣ 𝔣) → ω υ 𝔥 𝔣 𝔞 𝔫 s = 0) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡, ‖ρ υ 𝔥 𝔣 𝔞 𝔫 s 𝔡‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s 𝔠, ‖lam υ 𝔥 𝔣 𝔞 𝔫 s 𝔠‖ ≤ 1) ∧
        (∀ υ 𝔥 𝔣 𝔞 𝔫 s, ContDiff ℝ 2 (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t))) ∧
        (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ υ 𝔥 𝔣 𝔞 𝔫 s, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
          ‖iteratedDeriv j (fun t => Φ υ 𝔥 𝔣 𝔞 𝔫 s (Real.exp t)) t‖ ≤
            C * min (Real.exp (α * t)) (Real.exp (-(N * t)))) ∧
        (∀ (r : RowClass 𝔪) (𝔥 : Ideal (𝓞 F)), 𝔥 * simplePart r.1.1 = r.1.1 →
          ∀ Z : ℝ, 0 < Z →
          χ.thetaSum g (rowElt g r) Z =
            ∑' k : {𝔣 : Ideal (𝓞 F) // Squarefree 𝔣 ∧ 𝔣 * 𝔣 ∣ 𝔥} × {𝔞 : Ideal (𝓞 F) // 𝔞 ≠ ⊥} ×
                {𝔫 : Ideal (𝓞 F) // IsExterior 𝔪 𝔫} × T,
              ω r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 / (Ideal.absNorm k.2.2.1.1 : ℂ) *
                ρ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 (simplePart r.1.1) *
                ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠},
                  lam r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2 𝔠.1 *
                    residueSymbol ι 𝔪 (simplePart r.1.1) (g.gen 𝔠.1) ^ 3 /
                    ((Real.sqrt (Ideal.absNorm 𝔠.1) : ℝ) : ℂ) *
                    Φ r.2 𝔥 k.1.1 k.2.1.1 k.2.2.1.1 k.2.2.2
                      (Z * Ideal.absNorm k.2.1.1 * Ideal.absNorm 𝔠.1 *
                          (Ideal.absNorm k.2.2.1.1 : ℝ) ^ 3 /
                        ((Ideal.absNorm (simplePart r.1.1) : ℝ) ^ 2 *
                          (Ideal.absNorm k.1.1 : ℝ) ^ 2))) := by
  exact ArtinPrimitiveRoots.exists_cutoff_exists_thetaSum_rowElt_eq_tsum n hn0 hn F ι

end
