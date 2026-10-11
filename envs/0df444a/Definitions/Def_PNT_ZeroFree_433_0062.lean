-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0062
-- name    : PNT_ZeroFree_433_0062
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:18:47.55449+00:00
-- url     : https://prove2.me/theorems/5b0ef47e-b577-4280-910d-feea3cbda83b
-- title:
--   Zero-free region foundations: GaussSum.ReflectionBrackets [0062]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ReflectionBrackets.lean#L79-L638

import Definitions.Def_PNT_ZeroFree_433_0061

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ReflectionBrackets.lean#L79-L638
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar

section
variable {F : Type*} [Field F] [Fintype F]

theorem bracket_eq_zero_iff (χ : MulChar F ℂ) (j : ℕ) (hj4 : j ≠ 4) (x : F) :
    bracket χ j x = 0 ↔ x = 0 := by
  have hr : (rootCard F : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos))
  by_cases hj0 : j = 0
  · simp only [bracket, if_neg hj4, if_pos hj0, mul_eq_zero, hr, false_or,
      MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not]
  · simp only [bracket, if_neg hj4, if_neg hj0, MulChar.apply_eq_zero_iff,
      isUnit_iff_ne_zero, not_not]

theorem norm_bracket_nonexceptional_le_one (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) : ‖bracket χ j x‖ ≤ 1 := by
  rw [norm_bracket_nonexceptional χ j hj4 hj0]
  split_ifs <;> norm_num

theorem norm_bracket_zero_le (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ ≤ (rootCard F)⁻¹ := by
  rw [norm_bracket_zero]
  split_ifs <;> simp only [mul_zero, mul_one, le_refl]
  exact inv_nonneg.mpr rootCard_pos.le

open ActualEisensteinCubic
noncomputable local instance quotientFieldBounds (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeBounds (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_A5_norm_cases (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      if j = 4 then
        (if x = 0 then ((Fintype.card (O ⧸ P) : ℝ) - 1) / rootCard (O ⧸ P)
         else (rootCard (O ⧸ P))⁻¹)
      else if j = 0 then (rootCard (O ⧸ P))⁻¹ * (if x = 0 then 0 else 1)
      else if x = 0 then 0 else 1 := by
  rw [canonical_A5_norm_eq_bracket P hgood hchar ψ hψ j hj6 σ ε x]
  by_cases hj4 : j = 4
  · subst j
    simp only [↓reduceIte]
    by_cases hx : x = 0
    · subst x
      simp only [↓reduceIte]
      exact norm_bracket_four_zero _
    · rw [if_neg hx]
      exact norm_bracket_four_nonzero _ x hx
  · rw [if_neg hj4]
    by_cases hj0 : j = 0
    · subst j
      simp only [↓reduceIte]
      exact norm_bracket_zero _ x
    · rw [if_neg hj0]
      exact norm_bracket_nonexceptional _ j hj4 hj0 x

theorem actual_trace_A5_normalized (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ Ideal.span {p})ˣ) (x : O ⧸ Ideal.span {p}) :
    let χ := canonicalSextic (Ideal.span {p}) hgood
    let ψ := ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    activeRow χ ψ j σ ε x = ((χ⁻¹) ^ 2) σ * phase χ ψ j ε * bracket χ j x := by
  exact canonical_A5_normalized (Ideal.span {p}) hgood hchar _
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp) j hj6 σ ε x

theorem actual_bracket_four_divisibility_split (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (n b : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) 4 (Ideal.Quotient.mk (Ideal.span {p}) (n * b ^ 3)) =
      -(rootCard (O ⧸ Ideal.span {p}) : ℂ)⁻¹ +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if p ∣ n then 1 else 0) +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if ¬p ∣ n ∧ p ∣ b then 1 else 0) := by
  simpa only [Ideal.mem_span_singleton] using canonical_bracket_four_cube_split (Ideal.span {p}) hgood n b

theorem actual_bracket_zero_iff (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (j : ℕ) (hj4 : j ≠ 4) (n : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) j (Ideal.Quotient.mk (Ideal.span {p}) n) = 0 ↔ p ∣ n := by
  rw [bracket_eq_zero_iff _ j hj4, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem rootCard_span (p : O) [(Ideal.span {p}).IsMaximal] :
    rootCard (O ⧸ Ideal.span {p}) = ‖ConcreteTraceCRT.eisEmbedding p‖ := by
  rw [rootCard, ← Nat.card_eq_fintype_card]
  change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

end

variable {F : Type*} [Field F] [Fintype F]

def zeroFourierCoefficient (χ : MulChar F ℂ) (j : ℕ) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ t : F, (χ ^ j) t

theorem zeroFourierCoefficient_zero (χ : MulChar F ℂ) :
    zeroFourierCoefficient χ 0 = 1 - (Fintype.card F : ℂ)⁻¹ := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  rw [zeroFourierCoefficient, pow_zero, MulChar.sum_one_eq_card_units, Fintype.card_units,
    Nat.cast_sub hq, Nat.cast_one]
  field_simp

theorem zeroFourierCoefficient_nontrivial (χ : MulChar F ℂ) (j : ℕ) (hj : χ ^ j ≠ 1) :
    zeroFourierCoefficient χ j = 0 := by
  rw [zeroFourierCoefficient, MulChar.sum_eq_zero_of_ne_one hj, mul_zero]

theorem zeroFourierCoefficient_zero_norm_le_one (χ : MulChar F ℂ) :
    ‖zeroFourierCoefficient χ 0‖ ≤ 1 := by
  rw [zeroFourierCoefficient_zero]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hqpos : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le zero_lt_one hq
  have hinv : (Fintype.card F : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hqpos).mpr
    exact hq
  have hnonneg : 0 ≤ 1 - (Fintype.card F : ℝ)⁻¹ := sub_nonneg.mpr hinv
  have heq : (1 : ℂ) - (Fintype.card F : ℂ)⁻¹ = ((1 - (Fintype.card F : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  exact sub_le_self _ (inv_nonneg.mpr hqpos.le)

open ActualEisensteinCubic
noncomputable local instance quotientFieldInactive (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeInactive (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_zeroFourierCoefficient (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) (j : ℕ) (hj6 : j < 6) :
    zeroFourierCoefficient (canonicalSextic P hgood) j =
      if j = 0 then 1 - (Fintype.card (O ⧸ P) : ℂ)⁻¹ else 0 := by
  by_cases hj : j = 0
  · subst j
    simpa using zeroFourierCoefficient_zero (canonicalSextic P hgood)
  · rw [if_neg hj]
    exact zeroFourierCoefficient_nontrivial _ j (canonicalSextic_pow_ne_one P hgood hchar hj hj6)

theorem finite_active_scalar_norm_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ ε : ∀ i, (O ⧸ P i)ˣ) :
    ‖∏ i, (((canonicalSextic (P i) (hgood i))⁻¹) ^ 2) (σ i) *
      phase (canonicalSextic (P i) (hgood i)) (ψ i) (j i) (ε i)‖ = 1 := by
  rw [norm_prod]
  have hlocal (i : ι) :
      ‖(((canonicalSextic (P i) (hgood i))⁻¹) ^ 2) (σ i) *
        phase (canonicalSextic (P i) (hgood i)) (ψ i) (j i) (ε i)‖ = 1 := by
    rw [norm_mul, FiniteRayExpansion.norm_char_unit,
      canonical_phase_norm (P i) (hgood i) (hchar i) (ψ i) (hψ i) (j i) (hj6 i) (ε i), one_mul]
  simp only [hlocal, Finset.prod_const_one]

end LocalReflectionBrackets

namespace EisensteinSchwartzPoisson
open MeasureTheory MeasureTheory.Measure Set Real
open scoped SchwartzMap FourierTransform

theorem complex_radial_norm_sq_integral (F : ℝ → ℂ) :
    (∫ z : ℂ, F (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by
  have hsub : (∫ r : ℝ in Ioi 0, (2 * r) • F (r ^ 2)) = ∫ t : ℝ in Ioi 0, F t := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
      using (integral_comp_rpow_Ioi_of_pos (g := F) (by norm_num : (0 : ℝ) < 2))
  have hsub' : (2 : ℂ) * (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) =
      ∫ t : ℝ in Ioi 0, F t := by
    simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_assoc, integral_const_mul] using hsub
  calc
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * F (p.1 ^ 2) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp only [Complex.norm_polarCoord_symm, sq_abs, Complex.real_smul]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) *
        ∫ _θ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp only [mul_one]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) * (2 * Real.pi : ℂ) := by
      congr 1
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter, volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]),
        sub_neg_eq_add, Complex.real_smul, mul_one]
      push_cast
      ring
    _ = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by rw [← hsub']; ring

theorem paperRadialFourier_zero_eq_halfline (F : ℝ → ℂ) :
    paperRadialFourier F 0 = (2 * Real.pi / Real.sqrt 3 : ℂ) *
      ∫ t : ℝ in Ioi 0, F t := by
  have he : paperE 0 = 1 := by simp [paperE_eq_exp]
  simp only [paperRadialFourier, paperFourier, Real.sqrt_zero, Complex.ofReal_zero,
    mul_zero, neg_zero, he, one_mul]
  rw [complex_radial_norm_sq_integral]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem quadratic_principal_zero_modes_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (fun t : ℝ => paperRadialFourier W (t ^ 2)) 0 =
      paperRadialFourier (fun t : ℝ => W (t ^ 2)) 0 := by
  rw [paperRadialFourier_zero_eq_halfline, paperRadialFourier_zero_eq_halfline,
    paperRadialFourier_halfline_integral]

def quadraticSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  horizontalSlice (radialTest W) 0

@[simp] theorem quadraticSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSquareProfile W x = W (x ^ 2) := by
  simp [quadraticSquareProfile, horizontalSlice_apply, complexPoint_eq,
    radialTest_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def quadraticTransformedSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))
      (horizontalSlice (𝓕 (radialTest W)) 0)

@[simp] theorem quadraticTransformedSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticTransformedSquareProfile W x = paperRadialFourier W (x ^ 2) := by
  simp only [quadraticTransformedSquareProfile, _root_.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, horizontalSlice_apply]
  rw [paperRadialFourier_square]
  simp only [complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero,
    SchwartzMap.fourier_coe, mul_comm x (2 / Real.sqrt 3)]
  rfl

theorem quadraticSquareProfile_principal_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (quadraticTransformedSquareProfile W) 0 =
      paperRadialFourier (quadraticSquareProfile W) 0 := by
  have h1 : (quadraticTransformedSquareProfile W : ℝ → ℂ) =
      fun x => paperRadialFourier W (x ^ 2) := by funext x; exact quadraticTransformedSquareProfile_apply W x
  have h2 : (quadraticSquareProfile W : ℝ → ℂ) = fun x => W (x ^ 2) := by
    funext x; exact quadraticSquareProfile_apply W x
  rw [h1, h2, quadratic_principal_zero_modes_equal]

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

theorem masked_principal_radial_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * ∑ E ∈ S.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
        ∑' h : O, paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
  let Q : Empty → Ideal O := Empty.elim
  let : ∀ i, (Q i).IsMaximal := fun i => nomatch i
  have hcop : Pairwise (Function.onFun IsCoprime Q) := by intro i; cases i
  have hg : ∀ i, lambda ∉ Q i := fun i => nomatch i
  have hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2 := fun i => nomatch i
  have hj0 : ∀ i : Empty, (1 : ℕ) ≠ 0 := fun i => nomatch i
  have hj6 : ∀ i : Empty, (1 : ℕ) < 6 := fun i => nomatch i
  have hp := canonical_masked_radial_poisson_collected P hinj S Q hcop hg hc
    (fun _ => 1) hj0 hj6 V M hM
  simpa only [finiteSexticRow_of_isEmpty, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    star_one, one_mul, one_pow, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast] using hp

def maskedPrincipalRemainder {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (V : ℝ → ℂ) (M : ℝ) : ℂ :=
  (M : ℂ) * ∑ E ∈ S.powerset,
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier V
      (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))

theorem masked_principal_radial_poisson_zero_split {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * paperRadialFourier V 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) +
        maskedPrincipalRemainder P S V M := by
  have hp (E : Finset ι) : 0 < (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hs (E : Finset ι) :
      (∑' h : O, paperRadialFourier V
        (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))) =
      paperRadialFourier V 0 +
        ∑' h : O, if h = 0 then 0 else paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
    have hsum := (paperRadialFourier_lattice_summable_norm V
      (M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) (div_pos hM (hp E))).of_norm
    have heq (h : O) : M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) * ‖eisEmbedding h‖ ^ 2 =
        M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by ring
    simp_rw [heq] at hsum
    simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      using hsum.tsum_eq_add_tsum_ite 0
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  rw [masked_principal_radial_poisson P hinj S V M hM]
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  rw [primeSubset_moebius_norm_sum P hprime hinj S]
  unfold maskedPrincipalRemainder
  ring

theorem quadratic_square_poisson_main_cancel {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z *
      paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) =
      maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M -
      maskedPrincipalRemainder P S (quadraticSquareProfile W) M := by
  have h1 := masked_principal_radial_poisson_zero_split P hinj S
    (quadraticTransformedSquareProfile W) M hM
  have h2 := masked_principal_radial_poisson_zero_split P hinj S (quadraticSquareProfile W) M hM
  simp only [quadraticTransformedSquareProfile_apply] at h1
  simp only [quadraticSquareProfile_apply] at h2
  rw [h1, h2, quadraticSquareProfile_principal_equal]
  ring

end ActualEisensteinCubic

open scoped BigOperators Classical
namespace PrimaryIdealUnitReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

abbrev GoodIdeal := {I : Ideal O // primaryGenerator I ≠ 0}
abbrev GoodElement := {z : O // primaryGenerator (Ideal.span {z}) ≠ 0}

theorem finite_units : Finite Oˣ := by
  let f : Oˣ → {z : O // z ∈ rowNormDisk 1} := fun u => ⟨u.val, by
    rw [mem_rowNormDisk]
    rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
    norm_num⟩
  exact Finite.of_injective f (fun u v h => Units.ext (congrArg Subtype.val h))

theorem span_unit_primary (u : Oˣ) (I : GoodIdeal) :
    Ideal.span {(u : O) * primaryGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact (primaryGenerator_spec I.val I.property).1

def unitIdealToElement (p : Oˣ × GoodIdeal) : GoodElement :=
  ⟨p.1.val * primaryGenerator p.2.val, by rw [span_unit_primary]; exact p.2.property⟩

theorem unitIdealToElement_injective : Function.Injective unitIdealToElement := by
  intro p q hpq
  have he : p.1.val * primaryGenerator p.2.val = q.1.val * primaryGenerator q.2.val :=
    congrArg Subtype.val hpq
  have hI : p.2 = q.2 := by
    apply Subtype.ext
    simpa only [span_unit_primary] using congrArg (fun z : O => Ideal.span {z}) he
  have hu : p.1 = q.1 := by
    apply Units.ext
    rw [hI] at he
    exact mul_right_cancel₀ q.2.property he
  exact Prod.ext hu hI

theorem unitIdealToElement_surjective : Function.Surjective unitIdealToElement := by
  intro z
  let I : GoodIdeal := ⟨Ideal.span {z.val}, z.property⟩
  have ha : Associated (primaryGenerator I.val) z.val :=
    Ideal.span_singleton_eq_span_singleton.mp (primaryGenerator_spec I.val I.property).1
  obtain ⟨u, hu⟩ := ha
  refine ⟨(u, I), Subtype.ext ?_⟩
  change u.val * primaryGenerator I.val = z.val
  simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × GoodIdeal ≃ GoodElement :=
  Equiv.ofBijective unitIdealToElement ⟨unitIdealToElement_injective, unitIdealToElement_surjective⟩

theorem tsum_good_elements_product (f : O → ℂ) :
    (∑' z : GoodElement, f z.val) =
      ∑' p : Oˣ × GoodIdeal, f (p.1.val * primaryGenerator p.2.val) := by
  exact (unitIdealEquiv.tsum_eq (fun z : GoodElement => f z.val)).symm

theorem tsum_good_elements_unit_invariant (f : O → ℂ)
    (hf : Summable (fun z : GoodElement => f z.val))
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : GoodElement, f z.val) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have hp : Summable (fun p : Oˣ × GoodIdeal => f (p.1.val * primaryGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr hf
  rw [tsum_good_elements_product, hp.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

theorem lambda_prime_actual : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K).zeta_sub_one_prime'

theorem primaryGenerator_ne_zero_of_good_factors (I : Ideal O) (hI : I ≠ 0)
    (hg : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, lambda ∉ P) :
    primaryGenerator I ≠ 0 := by
  rw [primaryGenerator, if_neg hI]
  apply Multiset.prod_ne_zero
  intro hz
  obtain ⟨P, hP, hzero⟩ := Multiset.mem_map.mp hz
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  exact primaryPrime_ne_zero P (hg P hP) hzero

theorem primaryGenerator_span_ne_zero_iff (z : O) :
    primaryGenerator (Ideal.span {z}) ≠ 0 ↔ ¬ lambda ∣ z := by
  constructor
  · intro hg hdiv
    have hs := primaryGenerator_spec (Ideal.span {z}) hg
    have hzgen : z ∣ primaryGenerator (Ideal.span {z}) := by
      apply Ideal.mem_span_singleton.mp
      exact hs.1.le (Ideal.subset_span (by simp))
    have hgen := hdiv.trans hzgen
    have hminus : lambda ∣ primaryGenerator (Ideal.span {z}) - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hs.2
    have hone : lambda ∣ (1 : O) := by
      convert! dvd_sub hgen hminus using 1 ; ring
    exact lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  · intro hdiv
    have hz : z ≠ 0 := by intro h; subst z; exact hdiv (dvd_zero _)
    have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
    apply primaryGenerator_ne_zero_of_good_factors _ hI
    intro P hP hlam
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzin : z ∈ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
      (Ideal.subset_span (by simp))
    have hcop : IsCoprime lambda z := lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hdiv
    obtain ⟨a, b, hab⟩ := hcop
    have hone : (1 : O) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left a hlam) (P.mul_mem_left b hzin)
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).mpr hone)

theorem tsum_ramified_mask (f : O → ℂ) :
    (∑' z : O, if lambda ∣ z then 0 else f z) = ∑' z : GoodElement, f z.val := by
  calc
    _ = ∑' z : O, ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O).indicator f z := by
      apply tsum_congr
      intro z
      simp only [Set.indicator, Set.mem_ofPred_eq, primaryGenerator_span_ne_zero_iff]
      split_ifs <;> rfl
    _ = _ := (tsum_subtype ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O) f).symm

theorem tsum_ramified_mask_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : O, if lambda ∣ z then 0 else f z) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  rw [tsum_ramified_mask]
  exact tsum_good_elements_unit_invariant f (hf.subtype _) hu

end PrimaryIdealUnitReindex

open scoped BigOperators Classical
namespace QuadraticUnitInvariance
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay

theorem principalNormalizedGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) :
    principalNormalizedGauss P hcop hg (fun _ => 3) c hc hc0 = quadraticGammaO c hc0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let e := (Ideal.quotEquivOfEq hc).trans (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (P i) (hg i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ P i) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hchar

theorem principalNormalizedGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) :
    principalNormalizedGauss P hcop hg (fun _ => 3) c hc hc0 = quadraticRayValue (residue c) := by
  rw [principalNormalizedGauss_three_eq_quadraticGamma P hcop hg hchar c hc hc0,
    quadraticGammaO_eq_rayValue]

theorem quadratic_unit_phase
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val *
      quadraticRayValue (residue (∏ i, p i)) =
        quadraticRayValue (residue (u.val * ∏ i, p i)) := by
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hn : Ideal.span {∏ i, p i} = ∏ i, Ideal.span {p i} := span_finset_prod _ _
  have hc : Ideal.span {u.val * ∏ i, p i} = ∏ i, Ideal.span {p i} := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hn]
  have h := principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hg (fun _ => 3)
    (u.val * ∏ i, p i) (∏ i, p i) hc hn (mul_ne_zero u.ne_zero hn0) hn0 u rfl
  rw [principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar,
    principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar] at h
  exact h.symm

theorem finiteSexticRow_three_star
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (z : O) :
    star (finiteSexticRow P hg (fun _ => 3) z) = finiteSexticRow P hg (fun _ => 3) z := by
  simp only [finiteSexticRow, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [canonicalSextic_pow_three_quadratic]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, star_intCast]

theorem quadratic_unit_value_eq_of_same_ray
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val =
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val := by
  have hne : quadraticRayValue (residue (∏ i, p i)) ≠ 0 := by
    rw [← canonicalProductGauss_three_eq_rayValue p hp hcop hg hchar]
    exact norm_ne_zero_iff.mp (by rw [norm_canonicalProductGauss p hp hcop hg hchar
      (fun _ => 3) (fun _ => by decide) (fun _ => by decide)]; norm_num)
  apply mul_right_cancel₀ hne
  rw [quadratic_unit_phase p hp hcop hg hchar, hray,
    quadratic_unit_phase q hq hcopq hgq hcharq, residue_mul, residue_mul, hray]

theorem quadratic_pair_unit_invariant
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) (z : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * z) *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * z) =
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z := by
  have hu := quadratic_unit_value_eq_of_same_ray p hp hcop hg hchar q hq hcopq hgq hcharq hray u
  have hs := finiteSexticRow_unit_mul_star (fun i => Ideal.span {q i}) hgq (fun _ => 3) u
  rw [finiteSexticRow_three_star] at hs
  rw [finiteSexticRow_mul, finiteSexticRow_mul, hu]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) := by ring
    _ = _ := by rw [hs, one_mul]

end QuadraticUnitInvariance

end

end OAI

end


