-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeLFunctionLeZetaThreeHalvesPow
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeLFunctionLeZetaThreeHalvesPow
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:42.521004+00:00
-- url     : https://prove2.me/theorems/3dbf1a0e-61bd-447f-906a-b66bd3cd37b6
-- title:
--   Norm Hecke LFunction Le Zeta Three Halves Pow
-- statement:
--   Definitions and structural lemmas for Norm Hecke LFunction Le Zeta Three Halves Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormHeckeLFunctionLeZetaThreeHalvesPow.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_finPart_unifAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
noncomputable section
namespace GlobalTheory.HeckeLBound
variable {E : Type} [Field E] [NumberField E]
def ratPrime (v : HeightOneSpectrum (𝓞 E)) : ℕ := Ideal.absNorm (v.asIdeal.under ℤ)
theorem ratPrime_prime (v : HeightOneSpectrum (𝓞 E)) : (ratPrime v).Prime := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact Nat.absNorm_under_prime v.asIdeal
theorem absNorm_eq_ratPrime_pow (v : HeightOneSpectrum (𝓞 E)) : ∃ f : ℕ, Ideal.absNorm v.asIdeal = ratPrime v ^ f :=
  have : v.asIdeal.LiesOver (Ideal.span {((ratPrime v : ℕ) : ℤ)}) := Int.liesOver_span_absNorm v.asIdeal
  ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal (ratPrime_prime v)⟩
theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 E)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega
theorem ratPrime_le_absNorm (v : HeightOneSpectrum (𝓞 E)) : ratPrime v ≤ Ideal.absNorm v.asIdeal := by
  obtain ⟨f, hf⟩ := absNorm_eq_ratPrime_pow v
  have h2 := two_le_absNorm v
  have hp := ratPrime_prime v
  rw [hf] at h2 ⊢
  have hf0 : f ≠ 0 := by rintro rfl; simp at h2
  calc ratPrime v = ratPrime v ^ 1 := (pow_one _).symm
    _ ≤ ratPrime v ^ f := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.2 hf0)
theorem mem_primesOverFinset_ratPrime (v : HeightOneSpectrum (𝓞 E)) :
    v.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((ratPrime v : ℕ) : ℤ)}) (𝓞 E) := by
  have hp := ratPrime_prime v
  have : (Ideal.span {((ratPrime v : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hp.ne_zero])]
  exact ⟨v.isPrime, Int.liesOver_span_absNorm v.asIdeal⟩
theorem card_filter_ratPrime_le (u : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) (hp : p.Prime) :
    (u.filter fun x => ratPrime x = p).card ≤ Module.finrank ℚ E := by
  classical
  have : (Ideal.span {(p:ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  refine le_trans ?_ (Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E (p := Ideal.span {(p:ℤ)}) (by simp [hp.ne_zero]))
  refine Finset.card_le_card_of_injOn (fun x => x.asIdeal) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter] at hx
    have := mem_primesOverFinset_ratPrime x
    rw [hx.2] at this
    exact this
  · intro x _ y _ hxy
    exact HeightOneSpectrum.ext hxy
def fac (x : ℝ) : ℝ := (1 - x ^ (-(3 / 2 : ℝ)))⁻¹
theorem one_sub_rpow_neg_three_halves_mem_Ioc {x : ℝ} (hx : 2 ≤ x) : 0 < 1 - x ^ (-(3 / 2 : ℝ)) ∧ 1 - x ^ (-(3 / 2 : ℝ)) ≤ 1 := by
  have h1 : x ^ (-(3 / 2 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have h2 : 0 < x ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  constructor <;> linarith
theorem one_le_fac {x : ℝ} (hx : 2 ≤ x) : 1 ≤ fac x := by
  obtain ⟨h1, h2⟩ := one_sub_rpow_neg_three_halves_mem_Ioc hx
  exact one_le_inv₀ h1 |>.2 h2
theorem fac_anti {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : fac y ≤ fac x := by
  obtain ⟨h1, _⟩ := one_sub_rpow_neg_three_halves_mem_Ioc hx
  unfold fac
  apply inv_anti₀ h1
  have : y ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by norm_num)
  linarith
end GlobalTheory.HeckeLBound
noncomputable section
namespace GlobalTheory.HeckeLBound
variable {E : Type} [Field E] [NumberField E]
open Filter Topology
theorem norm_val_eq_one {χ : HChar E} (hU : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  rw [← finPart_unifAt]
  exact hU _
theorem norm_eulerFactor_le {χ : HChar E} (hU : IsUnitary χ) {s : ℂ} (hs : 3 / 2 ≤ s.re) (v : HeightOneSpectrum (𝓞 E)) :
    ‖eulerFactor χ s v‖ ≤ fac (Ideal.absNorm v.asIdeal : ℝ) := by
  have hN : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  obtain ⟨h1, h2⟩ := one_sub_rpow_neg_three_halves_mem_Ioc hN
  unfold eulerFactor
  split_ifs with h
  · have hpos : 0 < Ideal.absNorm v.asIdeal := by have := two_le_absNorm v; omega
    have hc : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hpos]; simp
    have hle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hlow : 1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        ‖1 - ((χ.val v : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (((χ.val v : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
      rw [norm_mul, norm_val_eq_one hU, hc, norm_one] at this
      linarith
    rw [norm_inv]
    exact inv_anti₀ h1 hlow
  · rw [norm_one]; exact one_le_fac hN
theorem prod_fac_le_zeta (T : Finset Nat.Primes) : ∏ p ∈ T, fac ((p : ℕ) : ℝ) ≤ ‖riemannZeta (3 / 2)‖ := by
  have h := riemannZeta_eulerProduct_hasProd (s := 3 / 2) (by norm_num)
  have hf : (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(3 / 2 : ℂ)))⁻¹) = fun p : Nat.Primes => ((fac ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
    funext p
    unfold fac
    rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  rw [hf] at h
  have h' : Tendsto (fun T : Finset Nat.Primes => ∏ p ∈ T, fac ((p : ℕ) : ℝ)) atTop (𝓝 ‖riemannZeta (3 / 2)‖) := by
    have := (continuous_norm.tendsto _).comp h
    refine this.congr fun T => ?_
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_prod, Complex.norm_of_nonneg]
    exact Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le))
  refine ge_of_tendsto h' ?_
  filter_upwards [Filter.eventually_ge_atTop T] with T' hT
  rw [← Finset.prod_sdiff hT]
  have h1 : 1 ≤ ∏ p ∈ T' \ T, fac ((p : ℕ) : ℝ) :=
    by simpa using Finset.prod_le_prod (s := T' \ T) (f := fun _ => (1:ℝ)) (fun _ _ => zero_le_one) (fun p _ => one_le_fac (by exact_mod_cast p.2.two_le))
  have h0 : 0 ≤ ∏ p ∈ T, fac ((p : ℕ) : ℝ) :=
    Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le))
  nlinarith
end GlobalTheory.HeckeLBound
noncomputable section
namespace GlobalTheory.HeckeLBound
variable {E : Type} [Field E] [NumberField E]
open Filter Topology
theorem prod_fac_absNorm_le (F : Finset (HeightOneSpectrum (𝓞 E))) :
    ∏ v ∈ F, fac (Ideal.absNorm v.asIdeal : ℝ) ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  classical
  let g : HeightOneSpectrum (𝓞 E) → Nat.Primes := fun v => ⟨ratPrime v, ratPrime_prime v⟩
  have hg2 : ∀ v, (2 : ℝ) ≤ ((g v : ℕ) : ℝ) := fun v => by exact_mod_cast (ratPrime_prime v).two_le
  have step1 : ∏ v ∈ F, fac (Ideal.absNorm v.asIdeal : ℝ) ≤ ∏ v ∈ F, fac ((g v : ℕ) : ℝ) :=
    Finset.prod_le_prod (fun v _ => le_trans zero_le_one (one_le_fac (le_trans (hg2 v) (by exact_mod_cast ratPrime_le_absNorm v))))
      (fun v _ => fac_anti (hg2 v) (by exact_mod_cast ratPrime_le_absNorm v))
  rw [Finset.prod_comp (fun p : Nat.Primes => fac ((p : ℕ) : ℝ)) g] at step1
  refine le_trans step1 (le_trans (Finset.prod_le_prod (g := fun p : Nat.Primes => fac ((p : ℕ) : ℝ) ^ Module.finrank ℚ E) (fun p _ => ?_) (fun p _ => ?_)) ?_)
  · exact pow_nonneg (le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le))) _
  · refine pow_le_pow_right₀ (one_le_fac (by exact_mod_cast p.2.two_le)) ?_
    have : (F.filter fun v => g v = p) = F.filter fun v => ratPrime v = (p : ℕ) := by
      apply Finset.filter_congr
      intro v _
      exact Subtype.ext_iff
    rw [this]
    exact card_filter_ratPrime_le F p p.2
  · rw [Finset.prod_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun p _ => le_trans zero_le_one (one_le_fac (by exact_mod_cast p.2.two_le)))
      (prod_fac_le_zeta _) _
theorem norm_heckeL_le (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ) :
    IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  intro hU hL hS
  have h := hL.2 S (by linarith)
  have h' := (continuous_norm.tendsto _).comp h
  refine le_of_tendsto' h' fun F => ?_
  simp only [Function.comp_apply]
  refine le_trans (Finset.norm_prod_le _ _) (le_trans ?_ (prod_fac_absNorm_le F))
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v _ => norm_eulerFactor_le hU hS v)
end GlobalTheory.HeckeLBound
example : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ), IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E :=
  GlobalTheory.HeckeLBound.norm_heckeL_le


