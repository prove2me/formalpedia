-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0366_parallel1
-- name    : PNT_ZeroFree_433_0366_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:15:29.628481+00:00
-- url     : https://prove2.me/theorems/4a4369ef-b3fe-47f4-81b1-e3fd25585067
-- title:
--   Zero-free region foundations: Hecke.DetectorProfiles, Hecke.DetectorProfilesBounds, Hecke.DetectorProfilesUniform, Hecke.DetectorFourier, Hecke.DetectorFourierSeparation [0366_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorProfiles
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesBounds
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesUniform
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorFourier
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorProfiles.lean#L9-L73
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesBounds.lean#L9-L87
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesUniform.lean#L9-L79
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorFourier.lean#L11-L87
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorFourierSeparation.lean#L10-L74

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0012
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorProfiles.lean#L9-L73
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesBounds.lean#L9-L87
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorProfilesUniform.lean#L9-L79
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorFourier.lean#L11-L87
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorFourierSeparation.lean#L10-L74
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfiles
section
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def expNeg (x : ℝ) : ℂ := Complex.exp (-(x : ℂ))

lemma expNeg_smooth : ContDiff ℝ ∞ expNeg := by
  exact Complex.ofRealCLM.contDiff.neg.cexp

lemma expNeg_hasDerivAt (x : ℝ) : HasDerivAt expNeg (-expNeg x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).neg).cexp
  convert! h using 1; simp [expNeg]

lemma iteratedDeriv_expNeg (n : ℕ) :
    iteratedDeriv n expNeg = fun x => (-1 : ℂ)^n*expNeg x := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (expNeg_hasDerivAt x).deriv, pow_succ]
    ring

lemma expNeg_derivative_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n expNeg x‖ = Real.exp (-x) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expNeg]
  simp [expNeg, norm_pow, Complex.norm_exp]

lemma expNeg_derivative_decay (n i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1+x)^n*‖iteratedFDeriv ℝ i expNeg x‖ ≤ (n.factorial : ℝ)*Real.exp 1 := by
  rw [expNeg_derivative_norm]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1+x) (by linarith : 0 ≤ 1+x) n)
  calc
    _ ≤ (Real.exp (1+x)*(n.factorial : ℝ))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, show (1+x)+(-x) = 1 by ring]
      ring

def productProfile (Ω V T : ℝ → ℂ) (A B C s : ℝ) : ℂ :=
  Ω s*(1-V (A*s))*expNeg (B*s)*T (C*s)

def inverseProfile (W V : ℝ → ℂ) (R x : ℝ) : ℂ := W x*V (R*x)

def logSourceFun (Ω V T : ℝ → ℂ) (A B C y : ℝ) : ℂ :=
  Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y)

lemma logSource_smooth (Ω V T : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (A B C : ℝ) :
    ContDiff ℝ ∞ (logSourceFun Ω V T A B C) := by
  unfold logSourceFun
  have hE := expNeg_smooth
  fun_prop

lemma logSource_compact (Ω V T : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (A B C : ℝ) :
    HasCompactSupport (logSourceFun Ω V T A B C) :=
  ((hΩ.mul_right).mul_right).mul_right

def logSource (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C : ℝ) : SchwartzMap ℝ ℂ :=
  (logSource_compact Ω V T hΩc A B C).toSchwartzMap (logSource_smooth Ω V T hΩ hV hT A B C)

@[simp] lemma logSource_apply (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C y : ℝ) :
    logSource Ω V T hΩc hΩ hV hT A B C y =
      Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y) := rfl

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesBounds
section
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := FourierBridge.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (FourierBridge.schwartzDerivativeDecayConstant F K K)
    (FourierBridge.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using FourierBridge.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by first | simp | exact_mod_cast le_top))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by first | simp | exact_mod_cast le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesUniform
section
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_window_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  have each (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖iteratedFDeriv ℝ i Ω y‖ ≤ C := by
    have hb : BddAbove (Set.range (fun y => ‖iteratedFDeriv ℝ i Ω y‖)) :=
      (hΩ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
        ((hΩc.iteratedFDeriv i).comp_left norm_zero)
    obtain ⟨C, hC⟩ := hb
    exact ⟨max C 0, le_max_right _ _, fun y =>
      (hC (Set.mem_range_self y)).trans (le_max_left _ _)⟩
  choose C hC0 hC using each
  let CΩ : ℝ := ∑ i ∈ Finset.range (K + 1), C i
  have hCΩ : 0 ≤ CΩ := Finset.sum_nonneg (fun i _ => hC0 i)
  have hbΩ : ∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i Ω y‖ ≤ CΩ := by
    intro i hi y
    exact (hC i y).trans (Finset.single_le_sum (fun j _ => hC0 j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  obtain ⟨CV,hCV,hbV⟩ := scaled_schwartz_derivatives V L hL K
  obtain ⟨CT,hCT,hbT⟩ := scaled_schwartz_derivatives T L hL K
  obtain ⟨CE,hCE,hbE⟩ := scaled_expNeg_derivatives L hL K
  let P := (2 : ℝ)^K
  refine ⟨P*(P*(P*CΩ*(1+CV))*CE)*CT,by dsimp [P]; positivity,?_⟩
  intro A B D hA hB hD j hj y hy
  let v : ℝ → ℂ := fun z => V (A*Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B*Real.exp z)
  let t : ℝ → ℂ := fun z => T (D*Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1-v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) : ‖iteratedFDeriv ℝ i (fun z => 1-v z) y‖ ≤ 1+CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y hy)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)) y‖ ≤ P*CΩ*(1+CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1+CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)*e z) y‖ ≤ P*(P*CΩ*(1+CV))*CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [P]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y hy)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [P]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y hy)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)
        ≤ L^k*C := by
  obtain ⟨C,hC,hb⟩ := logSource_window_derivatives Ω V T hΩc hΩ L hL K
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k*‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L^k*C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
    (hb A B D hA hB hD j hj y hy) (norm_nonneg _) (pow_nonneg hL k)

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorFourier
section
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeDetectorProfiles
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(FourierBridge.coefficientMomentBound 0 C'+
    FourierBridge.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 C' hC')
      (FourierBridge.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := FourierBridge.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hiN := AnalyticBridge.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem uniform_fourier_tail (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C/R^N := by
  obtain ⟨C,hC,hb⟩ := uniform_fourier_moment Ω V T hΩc hΩ L hL hwindow (J+N)
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD R hR
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa [mul_comm] using (schwartz_weighted_tail
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J N R hR).trans
    (hb A B D hA hB hD)

theorem logSource_product_inversion (Ω V T : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B D x y : ℝ) :
    logSourceFun Ω V T A B D (x+y) =
      ∫ t : ℝ, FourierBridge.logPhase t x * FourierBridge.logPhase t y *
        (𝓕 (logSource Ω V T hΩc hΩ hV hT A B D)) t := by
  have hh := FourierBridge.schwartz_log_inversion
    (logSource Ω V T hΩc hΩ hV hT A B D) (x+y)
  change logSourceFun Ω V T A B D (x+y) = _ at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← FourierBridge.logPhase_add]
  congr 1
  simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
  congr 2
  ring_nf

end
end SevenEighths.HeckeDetectorFourier

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation
section
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*FourierBridge.logPhase t (x i)

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (FourierBridge.logPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*FourierBridge.logPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, FourierBridge.logPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
  rw [FourierBridge.schwartz_log_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Complex.exp (↑(2*Real.pi*inner ℝ t (x+y))*Complex.I) =
      FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
    rw [← FourierBridge.logPhase_add]
    simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
    congr 2
    ring_nf
  rw [hp]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end SevenEighths.HeckeDetectorFourier

end OAI

end


