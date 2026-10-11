-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T16:14:33.483831+00:00
-- url     : https://prove2.me/submissions/f5690ec0-922c-4b55-91e5-dbfbed4b089d

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_principalCoeff_prime_pow_mul_eq_mul
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_conj_gaussG_pow_six_eq_one

section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma sAddChar_congr {𝔪 : Ideal (𝓞 F)} (x x' : F)
    (H : ∀ y : F, (x - y ∈ (placesOf 𝔪).integer F) ↔ (x' - y ∈ (placesOf 𝔪).integer F)) :
    sAddChar 𝔪 x = sAddChar 𝔪 x' := by
  classical
  let G : (F → Prop) → ℂ := fun p => if h : ∃ y, p y then
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F h.choose : ℚ) : ℂ)) else 0
  have e1 : sAddChar 𝔪 x = G (fun y => x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  have e2 : sAddChar 𝔪 x' = G (fun y => x' - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  rw [e1, e2]
  congr 1
  funext y
  exact propext (and_congr_left' (H y))

/-- `e` is invariant under translation by `R`. -/
lemma sAddChar_add_mem {𝔪 : Ideal (𝓞 F)} (x r : F) (hr : r ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 (x + r) = sAddChar 𝔪 x := by
  have key : ∀ y : F, (x + r - y ∈ (placesOf 𝔪).integer F) ↔ (x - y ∈ (placesOf 𝔪).integer F) := by
    intro y
    constructor
    · intro h
      have := sub_mem h hr
      rwa [show x + r - y - r = x - y by ring] at this
    · intro h
      have := add_mem h hr
      rwa [show x - y + r = x + r - y by ring] at this
  exact sAddChar_congr _ _ key

/-- `e` is trivial on `R`. -/
lemma sAddChar_of_mem {𝔪 : Ideal (𝓞 F)} (x : F) (hx : x ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 x = 1 := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 :=
    ⟨0, by simpa using hx, fun v _ => by simp⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set y := hex.choose
  have hy : y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem hx h1
    rwa [sub_sub_cancel] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact h2 v hv
    · exact hy v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F y hall
  have htr : Algebra.trace ℚ F y = ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [← hz, Algebra.coe_trace_int]
  rw [htr]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [← this]
  congr 1
  push_cast
  ring

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma div_gen_top_mem {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) : x / (g.gen ⊤ : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨u, hu⟩ := isUnit_gen_top g
  have hinv : ((↑(u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((g.gen ⊤ : SInt 𝔪) : F)⁻¹ := by
    rw [← hu]
    have h1 : ((↑u : SInt 𝔪) : F) * ((↑(u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    exact (eq_inv_of_mul_eq_one_right h1)
  rw [div_eq_mul_inv, ← hinv]
  exact mul_mem hx (SetLike.coe_mem _)

lemma subsingleton_quot_top {𝔪 : Ideal (𝓞 F)} :
    Subsingleton (SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.map_top]
  infer_instance

lemma finsum_quot_top {𝔪 : Ideal (𝓞 F)}
    (f : SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) → ℂ) :
    ∑ᶠ x, f x = f 0 := by
  have := subsingleton_quot_top (𝔪 := 𝔪)
  exact finsum_eq_single f 0 (fun x hx => absurd (Subsingleton.elim x 0) hx)

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, normalizedFactors_top]

lemma gaussPhase_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (j : ℕ) :
    gaussPhase g j ⊤ = 1 := by
  rw [gaussPhase, finsum_quot_top, residueSymbol_top, one_pow, one_mul,
    sAddChar_of_mem _ (div_gen_top_mem g _ (SetLike.coe_mem _))]
  simp [Ideal.absNorm_top]

lemma thetaChar_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) : χ.thetaChar g ⊤ = 1 := by
  have h1 : χ.toFun ⊤ = 1 := by
    have := χ.map_principal' 1 one_ne_zero (by simp)
    rwa [Ideal.span_singleton_one] at this
  simp [HeckeChar.thetaChar, gaussLambda, gaussG, normalizedFactors_top, h1]

lemma gaussSumAt_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (k : F)
    (hk : k ∈ (placesOf 𝔪).integer F) : gaussSumAt g ⊤ k = 1 := by
  rw [gaussSumAt, finsum_quot_top, residueSymbol_top, one_mul,
    sAddChar_of_mem _ (div_gen_top_mem g _ (mul_mem hk (SetLike.coe_mem _)))]

lemma poissonFactor_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (h : SInt 𝔪) :
    poissonFactor g ⊤ ⊤ h = 1 := by
  rw [poissonFactor, finsum_quot_top, if_pos (by rw [Ideal.map_top]; exact Submodule.mem_top),
    residueSymbol_top, one_mul,
    gaussSumAt_top g _ (div_gen_top_mem g _ (SetLike.coe_mem _))]

/-- **(i)** `a(1,1,1,1) = 1`, for every `h` in place of `u`. -/
theorem coeff_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (h : SInt 𝔪) :
    gaussPhase g 2 ⊤ * χ.thetaChar g (⊤ * ⊤ ^ 3) * poissonFactor g ⊤ (⊤ * ⊤ ^ 3) h = 1 := by
  rw [← Ideal.one_eq_top, one_pow, one_mul, Ideal.one_eq_top, gaussPhase_top, thetaChar_top, poissonFactor_top]
  ring

end C3B

end ArtinPrimitiveRoots
end

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

/-- The primes at which the sextic symbol behaves: exterior primes with `6 ∣ N P − 1`. -/
def GoodP (𝔪 P : Ideal (𝓞 F)) : Prop :=
  P.IsPrime ∧ P ≠ ⊥ ∧ ¬ 𝔪 ≤ P ∧ 6 ∣ Ideal.absNorm P - 1

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma exists_sub_mem_map (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (h𝔪 : ¬ 𝔪 ≤ P)
    (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hP0⟩
  have hvS : v ∉ placesOf 𝔪 := h𝔪
  have hv : v.valuation F (r : F) ≤ 1 := r.2 v hvS
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) hv
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have hd' : Ideal.Quotient.mk P d ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hd
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P d)⁻¹
  refine ⟨c * n, ?_⟩
  have h1 : 1 - c * d ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hc, inv_mul_cancel₀ hd',
      sub_self]
  have h2 : r - algebraMap (𝓞 F) (SInt 𝔪) (c * n) =
      r * algebraMap (𝓞 F) (SInt 𝔪) (1 - c * d) := by
    apply Subtype.ext
    have hnd' := hnd
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_algebraMap_SInt]
    push_cast at hnd' ⊢
    linear_combination ((c : 𝓞 F) : F) * hnd'
  rw [h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ h1)

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

/-- Fermat in `R/PR`. -/
lemma pow_absNorm_eq (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (h𝔪 : ¬ 𝔪 ≤ P)
    (y : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : y ^ Ideal.absNorm P = y := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_sub_mem_map P hP hP0 h𝔪 r
  have hra : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) r =
      Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) a) := Ideal.Quotient.eq.mpr ha
  rw [hra, ← map_pow, Ideal.Quotient.eq, ← map_pow, ← map_sub]
  apply Ideal.mem_map_of_mem
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq, map_pow, ← card_quot P hP0]
  exact FiniteField.pow_card _

lemma unit_pow_sub_one (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (h𝔪 : ¬ 𝔪 ≤ P)
    (μ : (SInt 𝔪)ˣ) :
    Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (μ : SInt 𝔪) ^
      (Ideal.absNorm P - 1) = 1 := by
  set z := Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (μ : SInt 𝔪)
  have hu : IsUnit z := μ.isUnit.map _
  have hN : 1 ≤ Ideal.absNorm P := by
    rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hP0
  have h := pow_absNorm_eq P hP hP0 h𝔪 z
  rw [← Nat.sub_add_cancel hN, pow_succ] at h
  exact (hu.mul_eq_right).mp h

lemma sexticResidueSymbol_eq_of_mk_eq (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x =
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :
    sexticResidueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P y := by
  unfold sexticResidueSymbol
  rw [h]

lemma sexticResidueSymbol_unit_pow_six (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (hP : GoodP 𝔪 P)
    (μ : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 P ((μ : SInt 𝔪) ^ 6 * x) = sexticResidueSymbol ι 𝔪 P x := by
  classical
  obtain ⟨hPp, hP0, h𝔪, h6⟩ := hP
  set mk := Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪)))
  let Φ : (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) →
      (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ := fun z w =>
    if z = 0 then 0 else
      if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ mk (algebraMap (𝓞 F) (SInt 𝔪) ζ) = w
      then ι (h.choose : F) else 0
  have e : ∀ t, sexticResidueSymbol ι 𝔪 P t = Φ (mk t) (mk t ^ ((Ideal.absNorm P - 1) / 6)) :=
    fun t => rfl
  rw [e, e]
  have hu : IsUnit (mk (μ : SInt 𝔪)) := μ.isUnit.map _
  have h1 : mk ((μ : SInt 𝔪) ^ 6 * x) = mk (μ : SInt 𝔪) ^ 6 * mk x := by
    rw [map_mul, map_pow]
  have h2 : mk ((μ : SInt 𝔪) ^ 6 * x) ^ ((Ideal.absNorm P - 1) / 6) =
      mk x ^ ((Ideal.absNorm P - 1) / 6) := by
    rw [h1, mul_pow, ← pow_mul, Nat.mul_div_cancel' h6,
      unit_pow_sub_one P hPp hP0 h𝔪 μ, one_mul]
  have h3 : (mk ((μ : SInt 𝔪) ^ 6 * x) = 0) ↔ (mk x = 0) := by
    rw [h1]
    exact (hu.pow 6).mul_right_eq_zero
  simp only [Φ, h2, h3]

lemma residueSymbol_unit_pow_six (ι : F →+* ℂ) (𝔞 : Ideal (𝓞 F))
    (h𝔞 : ∀ P ∈ normalizedFactors 𝔞, GoodP 𝔪 P) (μ : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((μ : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  unfold residueSymbol
  congr 1
  exact Multiset.map_congr rfl fun P hP => sexticResidueSymbol_unit_pow_six ι P (h𝔞 P hP) μ x

lemma residueSymbol_congr (ι : F →+* ℂ) (𝔞 : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : x - y ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔞 x = residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  apply sexticResidueSymbol_eq_of_mk_eq
  rw [Ideal.Quotient.eq]
  exact Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)) h

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma gen_ne_zero (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    ((g.gen I : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have h0' : g.gen I = 0 := Subtype.ext h0
  have hs := g.span_gen I hI
  rw [h0', Ideal.span_singleton_eq_bot.mpr rfl] at hs
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI.1
  have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ ha
  rw [← hs, Ideal.mem_bot] at this
  apply ha0
  have := congrArg (fun z : SInt 𝔪 => (z : F)) this
  simp only [coe_algebraMap_SInt, ZeroMemClass.coe_zero] at this
  exact_mod_cast this

lemma mem_map_iff (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪) :
    x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ ∃ r : SInt 𝔪, x = g.gen I * r := by
  rw [← g.span_gen I hI, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← hr, mul_comm]⟩
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [hr, mul_comm]⟩

lemma div_gen_mem (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪)
    (hx : x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    (x : F) / (g.gen I : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨r, rfl⟩ := (mem_map_iff g I hI x).mp hx
  have h0 := gen_ne_zero g I hI
  rw [Subalgebra.coe_mul, mul_div_cancel_left₀ _ h0]
  exact r.2

lemma gaussSumAt_add_mem (g : AllowedGen ι 𝔪) (𝔄 : Ideal (𝓞 F)) (h𝔄 : IsExterior 𝔪 𝔄) (k : F)
    (a : SInt 𝔪) (ha : a ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    gaussSumAt g 𝔄 (k + a) = gaussSumAt g 𝔄 k := by
  unfold gaussSumAt
  refine finsum_congr fun v => ?_
  congr 1
  have hmem : (a : F) / (g.gen 𝔄 : F) * (quotLift v : F) ∈ (placesOf 𝔪).integer F :=
    mul_mem (div_gen_mem g 𝔄 h𝔄 a ha) (quotLift v).2
  rw [show (k + a) * (quotLift v : F) / (g.gen 𝔄 : F) =
      k * (quotLift v : F) / (g.gen 𝔄 : F) + (a : F) / (g.gen 𝔄 : F) * (quotLift v : F) by ring]
  exact sAddChar_add_mem _ _ hmem

lemma coe_unit_pow_mul_inv (μ : (SInt 𝔪)ˣ) :
    (((μ : SInt 𝔪) : F)) ^ 6 * (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) ^ 6 = 1 := by
  rw [← mul_pow]
  have : ((μ : SInt 𝔪) : F) * (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  rw [this, one_pow]

lemma gaussSumAt_unit_pow_six (g : AllowedGen ι 𝔪) (𝔄 : Ideal (𝓞 F)) (h𝔄 : IsExterior 𝔪 𝔄)
    (h𝔄g : ∀ P ∈ normalizedFactors 𝔄, GoodP 𝔪 P) (μ : (SInt 𝔪)ˣ) (k : F)
    (hk : k ∈ (placesOf 𝔪).integer F) :
    gaussSumAt g 𝔄 (((μ : SInt 𝔪) : F) ^ 6 * k) = gaussSumAt g 𝔄 k := by
  set I := 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪))
  set c : (SInt 𝔪 ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom (μ⁻¹ ^ 6)
  unfold gaussSumAt
  rw [← finsum_comp_equiv (Units.mulLeft c)]
  refine finsum_congr fun v => ?_
  simp only [Units.mulLeft_apply]
  set q := (quotLift v : SInt 𝔪)
  set q' := (quotLift ((c : SInt 𝔪 ⧸ I) * v) : SInt 𝔪)
  set ν : SInt 𝔪 := ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have hq' : q' - ν ^ 6 * q ∈ I := by
    rw [← Ideal.Quotient.eq]
    simp only [q', q, quotLift, Function.surjInv_eq Ideal.Quotient.mk_surjective, map_mul,
      map_pow, c, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, ν]
    rfl
  congr 1
  · rw [residueSymbol_congr ι 𝔄 q' (ν ^ 6 * q) hq']
    exact residueSymbol_unit_pow_six ι 𝔄 h𝔄g μ⁻¹ q
  · set δ := q' - ν ^ 6 * q
    have hq'eq : (q' : F) = (ν : F) ^ 6 * (q : F) + (δ : F) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow]; ring
    have hmem : ((μ : SInt 𝔪) : F) ^ 6 * k * ((δ : F) / (g.gen 𝔄 : F)) ∈
        (placesOf 𝔪).integer F :=
      mul_mem (mul_mem (pow_mem (μ : SInt 𝔪).2 6) hk) (div_gen_mem g 𝔄 h𝔄 δ hq')
    have hμν := coe_unit_pow_mul_inv μ
    rw [show ((μ : SInt 𝔪) : F) ^ 6 * k * (q' : F) / (g.gen 𝔄 : F) =
        k * (q : F) / (g.gen 𝔄 : F) + ((μ : SInt 𝔪) : F) ^ 6 * k * ((δ : F) / (g.gen 𝔄 : F)) by
      rw [hq'eq]
      have : ((μ : SInt 𝔪) : F) ^ 6 * (ν : F) ^ 6 = 1 := hμν
      linear_combination (k * (q : F) / (g.gen 𝔄 : F)) * this]
    exact sAddChar_add_mem _ _ hmem

/-- **(iv)** `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for an `S`-unit `μ`. -/
theorem poissonFactor_unit_pow_six (g : AllowedGen ι 𝔪) (𝔰 𝔄 : Ideal (𝓞 F))
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄)
    (h𝔰g : ∀ P ∈ normalizedFactors 𝔰, GoodP 𝔪 P) (h𝔄g : ∀ P ∈ normalizedFactors 𝔄, GoodP 𝔪 P)
    (μ : (SInt 𝔪)ˣ) (h : SInt 𝔪) :
    poissonFactor g 𝔰 𝔄 ((μ : SInt 𝔪) ^ 6 * h) = poissonFactor g 𝔰 𝔄 h := by
  classical
  set I := 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  set c : (SInt 𝔪 ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom (μ ^ 6)
  unfold poissonFactor
  rw [← finsum_comp_equiv (Units.mulLeft c)]
  refine finsum_congr fun d => ?_
  simp only [Units.mulLeft_apply]
  set q := (quotLift d : SInt 𝔪)
  set q' := (quotLift ((c : SInt 𝔪 ⧸ I) * d) : SInt 𝔪)
  set m : SInt 𝔪 := (μ : SInt 𝔪)
  set A := g.gen 𝔄
  have hq' : q' - m ^ 6 * q ∈ I := by
    rw [← Ideal.Quotient.eq]
    simp only [q', q, quotLift, Function.surjInv_eq Ideal.Quotient.mk_surjective, map_mul,
      map_pow, c, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, m]
    rfl
  set δ := q' - m ^ 6 * q
  have hm6 : IsUnit (m ^ 6) := (μ.isUnit).pow 6
  have hcond : (m ^ 6 * h - A * q' ∈ I) ↔ (h - A * q ∈ I) := by
    have e1 : m ^ 6 * h - A * q' = m ^ 6 * (h - A * q) - A * δ := by
      simp only [δ]; ring
    rw [e1]
    constructor
    · intro hh
      have := add_mem hh (Ideal.mul_mem_left I A hq')
      rw [sub_add_cancel] at this
      exact (Ideal.unit_mul_mem_iff_mem I hm6).mp this
    · intro hh
      exact sub_mem ((Ideal.unit_mul_mem_iff_mem I hm6).mpr hh) (Ideal.mul_mem_left I A hq')
  by_cases hc : h - A * q ∈ I
  · rw [if_pos (hcond.mpr hc), if_pos hc]
    congr 1
    · rw [residueSymbol_congr _ 𝔰 q' (m ^ 6 * q) hq']
      exact residueSymbol_unit_pow_six _ 𝔰 h𝔰g μ q
    · obtain ⟨ρ, hρ⟩ := (mem_map_iff g 𝔰 h𝔰 δ).mp hq'
      have hs0 := gen_ne_zero g 𝔰 h𝔰
      have hk : (((h - A * q : SInt 𝔪)) : F) / (g.gen 𝔰 : F) ∈ (placesOf 𝔪).integer F :=
        div_gen_mem g 𝔰 h𝔰 _ hc
      have hAρ : -(A * ρ) ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        apply neg_mem
        rw [mem_map_iff g 𝔄 h𝔄]
        exact ⟨ρ, rfl⟩
      have harg : (((m ^ 6 * h - A * q' : SInt 𝔪)) : F) / (g.gen 𝔰 : F) =
          (m : F) ^ 6 * ((((h - A * q : SInt 𝔪)) : F) / (g.gen 𝔰 : F)) +
            ((-(A * ρ) : SInt 𝔪) : F) := by
        have hδ : (q' : F) = (m : F) ^ 6 * (q : F) + (g.gen 𝔰 : F) * (ρ : F) := by
          have := congrArg (fun z : SInt 𝔪 => (z : F)) hρ
          simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow] at this
          linear_combination this
        simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow,
          NegMemClass.coe_neg]
        rw [hδ]
        field_simp
        ring
      rw [harg, gaussSumAt_add_mem g 𝔄 h𝔄 _ _ hAρ, gaussSumAt_unit_pow_six g 𝔄 h𝔄 h𝔄g μ _ hk]
  · rw [if_neg (fun hh => hc (hcond.mp hh)), if_neg hc]

end gen

/-- The principal frequency element is the sixth power of an `S`-unit. -/
theorem freqElt_principalFreq {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    ∃ μ : (SInt 𝔪)ˣ, freqElt g (principalFreq 𝔪) = (μ : SInt 𝔪) ^ 6 := by
  -- the representative of the trivial class is a sixth power
  set w := Function.surjInv (QuotientGroup.mk_surjective
    (s := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range)) (1 : SClass 𝔪)
  have hw : (w : SClass 𝔪) = 1 := Function.surjInv_eq _ _
  rw [QuotientGroup.eq_one_iff] at hw
  obtain ⟨ν, hν⟩ := hw
  -- the generator of the unit ideal is the inverse sixth power of an `S`-unit
  obtain ⟨ε, hε⟩ := g.gen_mul ⊤ ⊤ ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  have hG0 := gen_ne_zero g ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  have hG : (g.gen ⊤ : F) * ((ε : Fˣ) : F) ^ 6 = 1 := by
    have h2 : (g.gen ⊤ : F) * 1 = (g.gen ⊤ : F) * (((ε : Fˣ) : F) ^ 6 * (g.gen ⊤ : F)) := by
      rw [mul_one]; nth_rewrite 1 [hε]; ring
    have := mul_left_cancel₀ hG0 h2
    linear_combination -this
  set ν' := Set.unitEquivUnitsInteger (placesOf 𝔪) F ν
  set ε' := Set.unitEquivUnitsInteger (placesOf 𝔪) F ε
  refine ⟨ν' * ε'⁻¹, ?_⟩
  apply Subtype.ext
  have hrep : ((SClass.rep (1 : SClass 𝔪) : SInt 𝔪) : F) = ((ν : Fˣ) : F) ^ 6 := by
    change (((Set.unitEquivUnitsInteger (placesOf 𝔪) F w : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = _
    rw [← hν]
    simp [powMonoidHom_apply]
  have hε'inv : (((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) * ((ε : Fˣ) : F) = 1 := by
    have : (((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) * ((ε' : SInt 𝔪) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.inv_mul]; rfl
    simpa [ε'] using this
  have hfe : freqElt g (principalFreq 𝔪) = SClass.rep (1 : SClass 𝔪) * g.gen ⊤ := rfl
  rw [hfe, Subalgebra.coe_mul, hrep, Subalgebra.coe_pow, Units.val_mul, Subalgebra.coe_mul]
  have hν' : ((ν' : SInt 𝔪) : F) = ((ν : Fˣ) : F) := rfl
  rw [hν', mul_pow]
  congr 1
  have hG' : (g.gen ⊤ : F) = ((((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F)) ^ 6 := by
    have h3 : ((((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F)) ^ 6 * ((ε : Fˣ) : F) ^ 6 = 1 := by
      rw [← mul_pow, hε'inv, one_pow]
    have hε0 : ((ε : Fˣ) : F) ^ 6 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    exact mul_right_cancel₀ hε0 (hG.trans h3.symm)
  exact hG'

end C3B

end ArtinPrimitiveRoots
end

section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- A prime of norm divisible by the rational prime `p` has norm at most `p^[F:ℚ]`. -/
theorem absNorm_le_of_prime_dvd (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    [P.IsMaximal] (hpd : p ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ p ^ Module.finrank ℤ (𝓞 F) := by
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard := card_quot P hP0
  obtain ⟨f, hq, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at hpd
  have hpq : p = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
  have hp0 : ((p : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [hpq]; exact ringChar.Nat.cast_ringChar
  have hmem : (p : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  have hle : Ideal.span {(p : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (p : 𝓞 F) = algebraMap ℤ (𝓞 F) p by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd

/-- In `ℚ(μ_n)` with `6 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `6 ∣ N P − 1`. -/
theorem six_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 6 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 6 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h3le : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 6 := by
    have c2 : Q.Coprime 2 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (6 : ℕ) = 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right c2 c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ6.toInteger) 6 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ6.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- Every prime factor of an exterior ideal is good, once `N₀ ≥ 3^[F:ℚ]`. -/
theorem goodP_of_mem (n : ℕ) (hn0 : 0 < n) (hn : 6 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : 3 ^ Module.finrank ℤ (𝓞 F) ≤ N₀) {𝔪 : Ideal (𝓞 F)}
    (hsm : SmallPrimesDvd N₀ 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    ∀ P ∈ normalizedFactors 𝔞, GoodP 𝔪 P := by
  intro P hP
  have hPp : Prime P := prime_of_normalized_factor P hP
  have hPi : P.IsPrime := Ideal.isPrime_of_prime hPp
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  have hle : 𝔞 ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hPi.ne_top
    rw [eq_top_iff, ← h𝔞.2]
    exact sup_le hle h
  refine ⟨hPi, hP0, h𝔪, six_dvd_absNorm_sub_one n hn0 hn P hPi hP0 ?_⟩
  by_contra hcon
  exact h𝔪 (hsm P hPi hP0 (by omega))

end C3B

end ArtinPrimitiveRoots
end

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

/-- The coefficient at `u = 1`: `γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)`. -/
noncomputable def coeffOne {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) (𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F)) : ℂ :=
  gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
    poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (g.gen 𝔯 ^ 6)

/-- **Cut (ii)**: cross-prime multiplicativity of the coefficients at `u = 1`. -/
def CutMul (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
        ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
          IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
          coeffOne g χ (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
            coeffOne g χ (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * coeffOne g χ 𝔠 𝔫 𝔰 𝔯

/-- **Cut (iii)**: the local Poisson factor at a prime power. -/
def CutF (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
      poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (g.gen (P ^ m) ^ 6) =
        poissonLocal (Ideal.absNorm P) (gaussPhase g 1 P) e₀ l k m

/-- **Cut (v)**: Davenport–Hasse in the form `γ₁ γ₂ Λ̄ Ḡ = −1` at exterior primes. -/
def CutHD (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
      gaussPhase g 1 P * gaussPhase g 2 P * starRingEnd ℂ (gaussLambda ι P) *
        starRingEnd ℂ (gaussG g P) = -1

/-- **Cut (v′)**: `Ḡ(P)⁶ = 1` at exterior primes. -/
def CutG6 (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → starRingEnd ℂ (gaussG g P) ^ 6 = 1

/-! ### Elementary lemmas -/

lemma smallPrimesDvd_mono {N N' : ℕ} (h : N' ≤ N) {𝔪 : Ideal (𝓞 F)}
    (hs : SmallPrimesDvd N 𝔪) : SmallPrimesDvd N' 𝔪 :=
  fun P hP hP0 hle => hs P hP hP0 (hle.trans h)

lemma isExterior_top (𝔪 : Ideal (𝓞 F)) : IsExterior 𝔪 ⊤ := ⟨top_ne_bot, top_sup_eq _⟩

lemma isExterior_mul {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {𝔪 I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact isExterior_top 𝔪
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

lemma normalizedFactors_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    normalizedFactors (P ^ t) = Multiset.replicate t P := by
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [normalizedFactors_pow, normalizedFactors_irreducible hirr, normalize_eq,
    Multiset.nsmul_singleton]

lemma thetaChar_prime_pow {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (χ : HeckeChar F 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (t : ℕ) :
    χ.thetaChar g (P ^ t) = χ.thetaChar g P ^ t := by
  have hχ : χ.toFun (P ^ t) = χ.toFun P ^ t := by
    induction t with
    | zero =>
      rw [pow_zero, pow_zero, Ideal.one_eq_top]
      have := χ.map_principal' 1 one_ne_zero (by simp)
      rwa [Ideal.span_singleton_one] at this
    | succ k ih => rw [pow_succ, χ.map_mul', ih, pow_succ]
  have h1 := normalizedFactors_prime_pow hP hP0 t
  have h0 := normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h0
  simp only [HeckeChar.thetaChar, gaussLambda, gaussG, h1, h0, Multiset.map_replicate,
    Multiset.prod_replicate, Multiset.map_singleton, Multiset.prod_singleton, hχ, map_pow]
  ring

lemma gaussLambda_prime_pow_six {ι : F →+* ℂ} {P : Ideal (𝓞 F)} (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : gaussLambda ι P ^ 6 = jacobiPhaseSix ι P := by
  have h0 := normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h0
  simp only [gaussLambda, h0, Multiset.map_singleton, Multiset.prod_singleton, jacobiPhaseSix]
  have hs : ((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ) ^ 2 = (Ideal.absNorm P : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have : (-(((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ)⁻¹ * cubicJacobiSum ι P)) ^ 6 =
      ((((Real.sqrt (Ideal.absNorm P) : ℝ) : ℂ) ^ 2) ^ 3)⁻¹ * cubicJacobiSum ι P ^ 6 := by
    rw [neg_pow, mul_pow, inv_pow, ← pow_mul]; norm_num
  rw [this, hs]

/-- The table algebra: `γ₂^{e₀} ϑ^{e₀+3l} · poissonLocal = principalLocalCoeff`. -/
lemma principalLocalCoeff_eq (Q : ℕ) (η θ γ₁ γ₂ ϑ : ℂ) (hHD : γ₁ * γ₂ * ϑ = -η)
    (h6 : ϑ ^ 6 = θ) (e₀ l k m : ℕ) (he : e₀ ≤ 1) :
    γ₂ ^ e₀ * ϑ ^ (e₀ + 3 * l) * poissonLocal Q γ₁ e₀ l k m =
      principalLocalCoeff Q η θ e₀ l k m := by
  have hl : ∀ l, Even l → ϑ ^ (3 * l) = θ ^ (l / 2) := by
    intro l hl
    obtain ⟨d, rfl⟩ := hl
    rw [← h6, ← pow_mul, show d + d = 2 * d by ring,
      Nat.mul_div_cancel_left d (by norm_num : 0 < 2)]
    congr 1; ring
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · simp only [poissonLocal, principalLocalCoeff, if_true, pow_zero, one_mul, zero_add]
    by_cases hl0 : l = 0
    · subst hl0; simp
    · rw [if_neg hl0, if_neg hl0]
      by_cases hle : Even l
      · rw [if_pos hle, if_pos hle, hl l hle]
        split_ifs <;> ring
      · rw [if_neg hle, if_neg hle, mul_zero]
  · simp only [poissonLocal, principalLocalCoeff, one_ne_zero, if_false, true_and, pow_one]
    by_cases hle : Even l
    · rw [if_pos hle, if_pos hle, pow_add, pow_one, hl l hle]
      split_ifs
      · linear_combination ((θ ^ (l / 2)) * (Real.sqrt Q : ℂ) * (Q : ℂ) ^ (3 * l)) * hHD
      · linear_combination ((θ ^ (l / 2)) * (Real.sqrt Q : ℂ) * (Q : ℂ) ^ (3 * l) *
          ((Q : ℂ) - 1)) * hHD
      · ring
    · rw [if_neg hle, if_neg hle, mul_zero]

end C3B

end ArtinPrimitiveRoots
end

section
/-! # C3B_Final: the cut 8a9ce98d from `CutMul`, `CutF`, `CutHD`, `CutG6` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma gaussPhase_prime_pow {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (P : Ideal (𝓞 F)) {e₀ : ℕ} (he : e₀ ≤ 1) :
    gaussPhase g 2 (P ^ e₀) = gaussPhase g 2 P ^ e₀ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · rw [pow_zero, pow_zero, Ideal.one_eq_top, gaussPhase_top]
  · rw [pow_one, pow_one]

/-- The local value `b(P^{e₀}, P^l, P^k, P^m) = principalLocalCoeff …`, from `CutF`, `CutHD`,
`CutG6`. -/
lemma coeffOne_local {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪)
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (e₀ l k m : ℕ) (he : e₀ ≤ 1)
    (hF : poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (g.gen (P ^ m) ^ 6) =
      poissonLocal (Ideal.absNorm P) (gaussPhase g 1 P) e₀ l k m)
    (hHD : gaussPhase g 1 P * gaussPhase g 2 P * starRingEnd ℂ (gaussLambda ι P) *
        starRingEnd ℂ (gaussG g P) = -1)
    (hG6 : starRingEnd ℂ (gaussG g P) ^ 6 = 1) :
    coeffOne g χ (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) =
      principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
        (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m := by
  have hpow : P ^ e₀ * (P ^ l) ^ 3 = P ^ (e₀ + 3 * l) := by
    rw [← pow_mul, ← pow_add, mul_comm l 3]
  rw [coeffOne, hF, gaussPhase_prime_pow g P he, hpow, thetaChar_prime_pow g χ hP hP0]
  apply principalLocalCoeff_eq _ _ _ _ _ _ _ _ _ _ _ _ he
  · show gaussPhase g 1 P * gaussPhase g 2 P *
        (starRingEnd ℂ (gaussLambda ι P) * starRingEnd ℂ (gaussG g P) * χ.toFun P) = _
    linear_combination (χ.toFun P) * hHD
  · show (starRingEnd ℂ (gaussLambda ι P) * starRingEnd ℂ (gaussG g P) * χ.toFun P) ^ 6 = _
    rw [mul_pow, mul_pow, hG6, ← map_pow, gaussLambda_prime_pow_six hP hP0, mul_one]

end C3B

open C3B in
/-- The published cut 8a9ce98d (statement verbatim), from the four cuts of `C3B_Main`. -/
theorem chk_exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul_of_cuts (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hMul : CutMul F ι) (hFc : CutF F ι) (hHDc : CutHD F ι) (hG6c : CutG6 F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
        let a : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g (principalFreq 𝔪) * g.gen 𝔯 ^ 6)
        a ⊤ ⊤ ⊤ ⊤ = 1 ∧
        ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            a (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                  (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m * a 𝔠 𝔫 𝔰 𝔯 := by
  obtain ⟨N1, h1⟩ := hMul
  obtain ⟨N2, h2⟩ := hFc
  obtain ⟨N3, h3⟩ := hHDc
  obtain ⟨N4, h4⟩ := hG6c
  have hn6 : 6 ∣ n := dvd_trans (by norm_num) hn
  set d := 3 ^ Module.finrank ℤ (𝓞 F)
  refine ⟨max (max N1 N2) (max (max N3 N4) d), ?_⟩
  intro 𝔪 _ hsm χ g
  have s1 : SmallPrimesDvd N1 𝔪 := smallPrimesDvd_mono (by omega) hsm
  have s2 : SmallPrimesDvd N2 𝔪 := smallPrimesDvd_mono (by omega) hsm
  have s3 : SmallPrimesDvd N3 𝔪 := smallPrimesDvd_mono (by omega) hsm
  have s4 : SmallPrimesDvd N4 𝔪 := smallPrimesDvd_mono (by omega) hsm
  have hd : d ≤ max (max N1 N2) (max (max N3 N4) d) := by omega
  have h𝔪0 : 𝔪 ≠ ⊥ := by assumption
  obtain ⟨μ, hμ⟩ := freqElt_principalFreq g
  have key : ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → IsExterior 𝔪 𝔫 → IsExterior 𝔪 𝔰 →
      gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
        poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g (principalFreq 𝔪) * g.gen 𝔯 ^ 6) =
      coeffOne g χ 𝔠 𝔫 𝔰 𝔯 := by
    intro 𝔠 𝔫 𝔰 𝔯 hc hn' hs
    have hA := isExterior_mul hc (isExterior_pow hn' 3)
    rw [coeffOne, hμ, poissonFactor_unit_pow_six g 𝔰 (𝔠 * 𝔫 ^ 3) hs hA
      (goodP_of_mem n hn0 hn6 hd hsm hs) (goodP_of_mem n hn0 hn6 hd hsm hA) μ]
  intro a
  refine ⟨coeff_top g χ _, ?_⟩
  intro P hP hPe e₀ l k m he 𝔠 𝔫 𝔰 𝔯 hc hcs hn' hs hr hcP hnP hsP hrP
  have hPe' := fun j => isExterior_pow hPe j
  simp only [a]
  rw [key _ _ _ _ (isExterior_mul (hPe' e₀) hc) (isExterior_mul (hPe' l) hn')
      (isExterior_mul (hPe' k) hs),
    key _ _ _ _ hc hn' hs,
    h1 𝔪 h𝔪0 s1 χ g P hP hPe e₀ l k m he 𝔠 𝔫 𝔰 𝔯 hc hcs hn' hs hr hcP hnP hsP hrP,
    coeffOne_local g χ P hP hPe.1 e₀ l k m he (h2 𝔪 h𝔪0 s2 g P hP hPe e₀ l k m he)
      (h3 𝔪 h𝔪0 s3 g P hP hPe) (h4 𝔪 h𝔪0 s4 g P hP hPe)]

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
        let a : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (freqElt g (principalFreq 𝔪) * g.gen 𝔯 ^ 6)
        a ⊤ ⊤ ⊤ ⊤ = 1 ∧
        ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            a (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              principalLocalCoeff (Ideal.absNorm P) (χ.toFun P)
                  (starRingEnd ℂ (jacobiPhaseSix ι P) * χ.toFun P ^ 6) e₀ l k m * a 𝔠 𝔫 𝔰 𝔯 :=
  chk_exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul_of_cuts n hn0 hn F ι
    (exists_cutoff_principalCoeff_prime_pow_mul_eq_mul n hn0 hn F ι)
    (exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal n hn0 hn F ι)
    (exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
      n hn0 hn F ι)
    (exists_cutoff_conj_gaussG_pow_six_eq_one n hn0 hn F ι)
end
