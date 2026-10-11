-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T19:41:08.542652+00:00
-- url     : https://prove2.me/submissions/56c1533d-70c3-4bc5-bf31-830e46ba9aee

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckePoissonLocal

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

lemma gaussSumAt_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (k : F)
    (hk : k ∈ (placesOf 𝔪).integer F) : gaussSumAt g ⊤ k = 1 := by
  rw [gaussSumAt, finsum_quot_top, residueSymbol_top, one_mul,
    sAddChar_of_mem _ (div_gen_top_mem g _ (mul_mem hk (SetLike.coe_mem _)))]

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

end gen

end C3B

end ArtinPrimitiveRoots
end

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

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_le_one (hv : v ∉ placesOf 𝔪) (r : SInt 𝔪) : v.valuation F (r : F) ≤ 1 := r.2 v hv

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

/-- Elements of `v^j R` have valuation at most `exp(-j)`. -/
lemma val_le_of_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) {r : SInt 𝔪}
    (hr : r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (r : F) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.map] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_alg, val_alg]
    exact (v.intValuation_le_pow_iff_mem a j).2 ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * exp (-(j : ℤ)) :=
          mul_le_mul' (val_le_one hv a) hx
      _ = _ := one_mul _

/-- An element of `𝓞` not in `v` has an inverse modulo `v^j`. -/
lemma exists_mul_sub_one_mem (j : ℕ) {d : 𝓞 F} (hd : d ∉ v.asIdeal) :
    ∃ c : 𝓞 F, c * d - 1 ∈ v.asIdeal ^ j := by
  have h1 : IsCoprime v.asIdeal (Ideal.span {d}) := by
    obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hd
    exact Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * d, Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self d), by rw [add_comm]; exact hyi⟩
  obtain ⟨i, hi, x, hx, hix⟩ := (h1.pow_left (m := j)).exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨c, ?_⟩
  have : c * d - 1 = -i := by linear_combination hix
  rw [this]
  exact neg_mem hi

/-- Every `x ∈ F` with `v(x) ≤ 1` is congruent modulo `v^j` (in valuation) to an element of `𝓞`. -/
lemma exists_val_sub_le (j : ℕ) (x : F) (hx : v.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, v.valuation F (x - algebraMap (𝓞 F) F a) ≤ exp (-(j : ℤ)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) x hx
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  refine ⟨c * n, ?_⟩
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have heq : x - algebraMap (𝓞 F) F (c * n) =
      -(x * algebraMap (𝓞 F) F (c * d - 1)) := by
    have hnd' : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
    rw [map_mul, ← hnd', map_sub, map_mul, map_one]; ring
  rw [heq, Valuation.map_neg, map_mul, val_alg]
  calc v.valuation F x * v.intValuation (c * d - 1) ≤ 1 * exp (-(j : ℤ)) :=
        mul_le_mul' hx ((v.intValuation_le_pow_iff_mem _ j).2 hc)
    _ = _ := one_mul _

/-- Elements of `R` of valuation at most `exp(-j)` lie in `v^j R`. -/
lemma mem_of_val_le (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : v.valuation F (r : F) ≤ exp (-(j : ℤ))) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hv)
  have hnd' : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have hn : n ∈ v.asIdeal ^ j := by
    rw [← v.intValuation_le_pow_iff_mem, ← val_alg (v := v), ← hnd', map_mul, hvd, mul_one]
    exact h
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  have heq : r = algebraMap (𝓞 F) (SInt 𝔪) (c * n) -
      r * algebraMap (𝓞 F) (SInt 𝔪) (c * d - 1) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg, coe_alg, map_mul, map_sub, map_mul,
      map_one, ← hnd']
    ring
  rw [heq]
  exact sub_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hn))
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc))

lemma mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      v.valuation F (r : F) ≤ exp (-(j : ℤ)) :=
  ⟨val_le_of_mem hv j, mem_of_val_le hv j r⟩

lemma alg_mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      a ∈ v.asIdeal ^ j := by
  rw [mem_map_pow_iff hv, coe_alg, val_alg, v.intValuation_le_pow_iff_mem]

lemma exists_sub_mem_map_pow (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈
      (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j (r : F) (r.2 v hv)
  exact ⟨a, mem_of_val_le hv j _ (by rw [Subalgebra.coe_sub, coe_alg]; exact ha)⟩

/-- Discreteness: a valuation strictly above `exp(-(j+1))` is at least `exp(-j)`. -/
lemma exp_le_of_lt {γ : ℤᵐ⁰} {j : ℤ} (h : exp (j - 1) < γ) : exp j ≤ γ := by
  have hγ : γ ≠ 0 := ne_zero_of_lt h
  rw [← exp_log hγ] at h ⊢
  rw [exp_lt_exp] at h
  rw [exp_le_exp]
  omega

lemma exp_le_val_of_not_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : r ∉ (v.asIdeal ^ (j + 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    exp (-(j : ℤ)) ≤ v.valuation F (r : F) := by
  rw [mem_map_pow_iff hv, not_le] at h
  apply exp_le_of_lt
  convert h using 2
  push_cast; ring

lemma le_of_mul_le_mul_ne {a b c : ℤᵐ⁰} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  have := mul_le_mul_right h c⁻¹
  rwa [mul_comm c⁻¹, mul_comm c⁻¹, mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at this

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

/-- A uniformizer in `𝓞`. -/
lemma exists_uniformizer : ∃ p : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F p) = exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  exact ⟨p, by rw [val_alg, hp]⟩

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

lemma quotHom_bijective (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Function.Bijective (quotHom 𝔪 (v.asIdeal ^ j)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, alg_mem_map_pow_iff hv] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow hv j r
    exact ⟨Ideal.Quotient.mk _ a, by rw [quotHom_mk]; exact (Ideal.Quotient.eq.mpr ha).symm⟩

/-- `𝓞/v^j ≃+* R/v^j R`. -/
noncomputable def quotEquiv (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    𝓞 F ⧸ v.asIdeal ^ j ≃+* SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  RingEquiv.ofBijective _ (quotHom_bijective hv j)

lemma finite_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Finite (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ v.asIdeal ^ j) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ (quotEquiv hv j).toEquiv

lemma natCard_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Nat.card (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal ^ j := by
  rw [← Nat.card_congr (quotEquiv hv j).toEquiv, ← map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- `v R` is a maximal ideal of `R`. -/
lemma isMaximal_map (hv : v ∉ placesOf 𝔪) :
    (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := by
  have e := quotEquiv (𝔪 := 𝔪) hv 1
  rw [pow_one] at e
  apply Ideal.Quotient.maximal_of_isField
  have : (v.asIdeal).IsMaximal := v.isMaximal
  have hf : IsField (𝓞 F ⧸ v.asIdeal) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp this
  exact MulEquiv.isField hf e.symm.toMulEquiv

end quot

section fibre

/-- Summing a function of the class modulo `J` over `R/I` (`I ≤ J`), weighted. -/
lemma finsum_fibre_mul {I J : Ideal (SInt 𝔪)} (hIJ : I ≤ J) [Finite (SInt 𝔪 ⧸ I)]
    [Finite (SInt 𝔪 ⧸ J)] (f : SInt 𝔪 → ℂ) (hf : ∀ x y, x - y ∈ J → f x = f y) :
    (∑ᶠ x : SInt 𝔪 ⧸ I, f (quotLift x)) * (Nat.card (SInt 𝔪 ⧸ J) : ℂ) =
      (Nat.card (SInt 𝔪 ⧸ I) : ℂ) * ∑ᶠ y : SInt 𝔪 ⧸ J, f (quotLift y) := by
  classical
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ I)
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ J)
  set red := Ideal.Quotient.factor hIJ
  have hsurj : Function.Surjective red := Ideal.Quotient.factor_surjective hIJ
  have hg : ∀ x, f (quotLift x) = f (quotLift (red x)) := by
    intro x
    apply hf
    rw [← Ideal.Quotient.eq]
    have h1 : Ideal.Quotient.mk J (quotLift x) = red x := by
      conv_rhs => rw [← Function.surjInv_eq Ideal.Quotient.mk_surjective x]
      rfl
    rw [h1]
    exact (Function.surjInv_eq Ideal.Quotient.mk_surjective (red x)).symm
  set c := (Finset.univ.filter fun x : SInt 𝔪 ⧸ I => red x = 0).card
  have hc : ∀ y, (Finset.univ.filter fun x : SInt 𝔪 ⧸ I => red x = y).card = c := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range red.toAddMonoidHom (hsurj y) (hsurj 0)
  have hcard : Nat.card (SInt 𝔪 ⧸ I) = c * Nat.card (SInt 𝔪 ⧸ J) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := red) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2
        (Finset.mem_univ _))]
    simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [hg]
  rw [← Finset.sum_fiberwise Finset.univ red (fun x => f (quotLift (red x)))]
  have : ∀ y, ∑ x ∈ Finset.univ.filter (fun x : SInt 𝔪 ⧸ I => red x = y), f (quotLift (red x)) =
      (c : ℂ) * f (quotLift y) := by
    intro y
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
      hc, nsmul_eq_mul]
  simp_rw [this, ← Finset.mul_sum, hcard]
  push_cast
  ring

variable {v : HeightOneSpectrum (𝓞 F)}

/-- Summing a function of the class modulo `v^i R` over `R/v^j R`, `i ≤ j`. -/
lemma finsum_quot_fibre (hv : v ∉ placesOf 𝔪) {i j : ℕ} (hij : i ≤ j) (f : SInt 𝔪 → ℂ)
    (hf : ∀ x y, x - y ∈ (v.asIdeal ^ i).map (algebraMap (𝓞 F) (SInt 𝔪)) → f x = f y) :
    ∑ᶠ x : SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)), f (quotLift x) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (j - i) *
        ∑ᶠ y : SInt 𝔪 ⧸ (v.asIdeal ^ i).map (algebraMap (𝓞 F) (SInt 𝔪)), f (quotLift y) := by
  have := finite_quot (𝔪 := 𝔪) hv j
  have := finite_quot (𝔪 := 𝔪) hv i
  have h := finsum_fibre_mul (Ideal.map_mono (Ideal.pow_le_pow_right hij)) f hf
  rw [natCard_quot hv, natCard_quot hv] at h
  have hQ : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hQi : (Ideal.absNorm v.asIdeal : ℂ) ^ i ≠ 0 := pow_ne_zero _ hQ
  apply mul_right_cancel₀ hQi
  push_cast at h
  rw [h, ← Nat.sub_add_cancel hij, pow_add, Nat.add_sub_cancel]
  ring

end fibre

end C3I

end ArtinPrimitiveRoots
end

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

/-- `x` has a witness in the definition of `sAddChar`. -/
def HasWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧ ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1

/-- The value of `e` through any witness. -/
lemma sAddChar_eq_of_wit {x y : F} (h1 : x - y ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) :
    sAddChar 𝔪 x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F y : ℚ) : ℂ)) := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 := ⟨y, h1, h2⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  set y' := hex.choose
  have hd : y' - y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem h1 k1
    rwa [show x - y - (x - y') = y' - y by ring] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y' - y) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact (Valuation.map_sub _ _ _).trans (max_le (k2 v hv) (h2 v hv))
    · exact hd v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  have htr : Algebra.trace ℚ F y' = Algebra.trace ℚ F y + ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [Algebra.coe_trace_int, show ((z : 𝓞 F) : F) = algebraMap (𝓞 F) F z from rfl, hz, map_sub]
    ring
  rw [htr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℂ) =
      ((-(Algebra.trace ℤ (𝓞 F) z) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring, this,
    mul_one]

/-- `e` is additive on elements with witnesses. -/
lemma sAddChar_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') :
    sAddChar 𝔪 (x + x') = sAddChar 𝔪 x * sAddChar 𝔪 x' := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  have hs1 : x + x' - (y + y') ∈ (placesOf 𝔪).integer F := by
    rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1'
  have hs2 : ∀ v ∈ placesOf 𝔪, v.valuation F (y + y') ≤ 1 :=
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))
  rw [sAddChar_eq_of_wit hs1 hs2, sAddChar_eq_of_wit hy1 hy2, sAddChar_eq_of_wit hy1' hy2',
    ← Complex.exp_add, map_add]
  push_cast
  ring_nf

/-- A witness exists when `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
lemma hasWit_of_mul_mem (x : F) (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤)
    (hx : ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨i, hi, w, hw, hiw⟩ := hcop.exists
  refine ⟨x * algebraMap (𝓞 F) F w, ?_, fun v hv => ?_⟩
  · have hw' : algebraMap (𝓞 F) F w = 1 - algebraMap (𝓞 F) F i := by
      rw [← map_one (algebraMap (𝓞 F) F), ← hiw, map_add]; ring
    have : x - x * algebraMap (𝓞 F) F w = x * algebraMap (𝓞 F) F i := by
      rw [hw']; ring
    rw [this]; exact hx i hi
  · have hvm : 𝔪 ≤ v.asIdeal := hv
    -- `d ∉ v^N`
    have hdN : d ∉ v.asIdeal ^ N := by
      intro hmem
      have hle : Ideal.span {d} ≤ v.asIdeal ^ N := (Ideal.span_singleton_le_iff_mem _).2 hmem
      have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [map_pow] at hdvd
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
      have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
        have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
        have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
        omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
      have h3 : 2 ^ N ≤ Ideal.absNorm v.asIdeal ^ N := Nat.pow_le_pow_left h2 N
      have h4 : N < 2 ^ N := Nat.lt_two_pow_self
      omega
    have hvd : exp (-(N : ℤ)) < v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
    have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
      rw [val_alg, v.intValuation_le_pow_iff_mem]
      exact Ideal.pow_right_mono hvm N hw
    have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
    have hxd : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
      rw [← hbd, div_mul_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    have key : v.valuation F (x * algebraMap (𝓞 F) F w) * v.valuation F (algebraMap (𝓞 F) F d) ≤
        1 * v.valuation F (algebraMap (𝓞 F) F d) := by
      rw [← map_mul, show x * algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [← hxd]; ring, map_mul]
      calc v.valuation F (algebraMap (𝓞 F) F b) * v.valuation F (algebraMap (𝓞 F) F w)
          ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) :=
            mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
        _ = _ := rfl
    exact le_of_mul_le_mul_ne key hdpos

variable {ι : F →+* ℂ}

/-- `a / gen 𝔞` has a witness. -/
lemma hasWit_div_gen (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a : SInt 𝔪) : HasWit 𝔪 ((a : F) / (g.gen 𝔞 : F)) := by
  apply hasWit_of_mul_mem _ 𝔞 h𝔞.2
  intro i hi
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ hi
  have := C3B.div_gen_mem g 𝔞 h𝔞 _ hm
  rw [coe_alg] at this
  rw [show (a : F) / (g.gen 𝔞 : F) * algebraMap (𝓞 F) F i =
    (a : F) * (algebraMap (𝓞 F) F i / (g.gen 𝔞 : F)) by ring]
  exact mul_mem a.2 this

/-- `e(a/c + b/c) = e(a/c) e(b/c)` for `c` an allowed generator. -/
lemma sAddChar_div_gen_add (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a b : SInt 𝔪) :
    sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F) + (b : F) / (g.gen 𝔞 : F)) =
      sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F)) * sAddChar 𝔪 ((b : F) / (g.gen 𝔞 : F)) :=
  sAddChar_add (hasWit_div_gen g 𝔞 h𝔞 a) (hasWit_div_gen g 𝔞 h𝔞 b)

/-! ### The inverse different -/

/-- For `P ∤ 𝔇`, some `z ∈ P⁻¹` has non-integral trace. -/
lemma exists_trace_not_int (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ P) :
    ∃ z : F, (∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a) ∧
      ∀ n : ℤ, Algebra.trace ℚ F z ≠ n := by
  rw [differentialIdeal_le_iff (K := ℚ) (L := F) hP0, Submodule.map_le_iff_le_comap] at hD
  rw [SetLike.not_le_iff_exists] at hD
  obtain ⟨z, hz, hz'⟩ := hD
  have hP' : (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using hP0
  have hz2 : z ∈ ((P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹) := hz
  rw [FractionalIdeal.mem_inv_iff hP'] at hz2
  refine ⟨z, fun p hp => ?_, fun n hn => hz' ?_⟩
  · have := hz2 (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨a, ha.symm⟩
  · simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
    exact ⟨n, by rw [hn]; simp⟩

/-- For `P` exterior and `z ∈ P⁻¹` with non-integral trace, `e(z) ≠ 1`. -/
lemma sAddChar_ne_one_of_dual (P : Ideal (𝓞 F)) (hPS : P ⊔ 𝔪 = ⊤) (z : F)
    (hz : ∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    (htr : ∀ n : ℤ, Algebra.trace ℚ F z ≠ n) : sAddChar 𝔪 z ≠ 1 := by
  have hw : ∀ v ∈ placesOf 𝔪, v.valuation F z ≤ 1 := by
    intro v hv
    have hvm : 𝔪 ≤ v.asIdeal := hv
    have hPv : ¬ P ≤ v.asIdeal := by
      intro h
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hPS]
      exact sup_le h hvm
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp hPv
    obtain ⟨a, ha⟩ := hz p hp
    have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
    rw [← ha, map_mul, h1, mul_one] at this
    exact this
  rw [sAddChar_eq_of_wit (y := z) (by simp) hw]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply htr (-n)
  have h2 : ((Algebra.trace ℚ F z : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `z (v R) ⊆ R` for `z ∈ v⁻¹`. -/
lemma mul_mem_of_mem_map (z : F)
    (hz : ∀ p ∈ v.asIdeal, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    {y : SInt 𝔪} (hy : y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    z * (y : F) ∈ (placesOf 𝔪).integer F := by
  rw [Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hz p hp
    rw [coe_alg, ha]
    exact (algebraMap (𝓞 F) (SInt 𝔪) a).2
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_left_comm]
    exact mul_mem a.2 hx

/-- Primitivity of `x ↦ e(x / gen(P^j))` on `R / P^j R`: for `x ∉ P^j R` there is `r ∈ R` with
`e(x r / gen(P^j)) ≠ 1`, when `P ∤ 𝔇`. -/
lemma exists_sAddChar_ne_one (g : AllowedGen ι 𝔪) (hv : v ∉ placesOf 𝔪)
    (hPS : v.asIdeal ⊔ 𝔪 = ⊤) (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) {j : ℕ} (hj : 1 ≤ j)
    (x : SInt 𝔪) (hx : x ∉ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, sAddChar 𝔪 ((x : F) * (r : F) / (g.gen (v.asIdeal ^ j) : F)) ≠ 1 := by
  obtain ⟨z, hz, htr⟩ := exists_trace_not_int v.asIdeal v.ne_bot hD
  have hez := sAddChar_ne_one_of_dual v.asIdeal hPS z hz htr
  have hext : IsExterior 𝔪 (v.asIdeal ^ j) :=
    isExterior_pow ⟨v.ne_bot, hPS⟩ j
  set B := g.gen (v.asIdeal ^ j)
  have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ hext
  have hBmem : B ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen _ hext]; exact Ideal.mem_span_singleton_self _
  have hB1 : B ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have : (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.map_mono (by simpa using Ideal.pow_le_pow_right (I := v.asIdeal) hj)
    exact this hBmem
  -- `w = z B ∈ R`
  have hwR : z * (B : F) ∈ (placesOf 𝔪).integer F := mul_mem_of_mem_map z hz hB1
  set w : SInt 𝔪 := ⟨z * (B : F), hwR⟩
  -- valuations
  have hvz : v.valuation F z ≤ exp (1 : ℤ) := by
    obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : p ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    obtain ⟨a, ha⟩ := hz p hpm
    have h1 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h1
    rw [← ha, map_mul, hp] at h1
    have : v.valuation F z * exp (-1 : ℤ) * exp 1 ≤ 1 * exp 1 := mul_le_mul_left h1 _
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at this
  have hvB := val_le_of_mem hv j hBmem
  have hvw : v.valuation F (w : F) ≤ exp (1 - (j : ℤ)) := by
    change v.valuation F (z * (B : F)) ≤ _
    rw [map_mul, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, exp_add]
    exact mul_le_mul' hvz hvB
  have hvx : exp (1 - (j : ℤ)) ≤ v.valuation F (x : F) := by
    have := exp_le_val_of_not_mem hv (j - 1) x (by rwa [Nat.sub_add_cancel hj])
    convert this using 2
    push_cast [Nat.cast_sub hj]; ring
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact exp_ne_zero (le_antisymm hvx bot_le)
  have hvx0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hx0
  -- `f = w / x` is `v`-integral
  have hvf : v.valuation F ((w : F) / (x : F)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.2 hvx0)]
    exact hvw.trans hvx
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j _ hvf
  -- `w - x a ∈ P^j R`
  set δ : SInt 𝔪 := w - x * algebraMap (𝓞 F) (SInt 𝔪) a
  have hδ : δ ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    apply mem_of_val_le hv j
    have : (δ : F) = (x : F) * ((w : F) / (x : F) - algebraMap (𝓞 F) F a) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg]
      field_simp
    rw [this, map_mul]
    calc v.valuation F (x : F) * v.valuation F ((w : F) / (x : F) - algebraMap (𝓞 F) F a)
        ≤ 1 * exp (-(j : ℤ)) := mul_le_mul' (val_le_one hv x) ha
      _ = _ := one_mul _
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, fun h1 => hez ?_⟩
  have hzeq : z = (x : F) * ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) / (B : F) +
      (δ : F) / (B : F) := by
    simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul]
    change z = _ + (z * (B : F) - _) / (B : F)
    field_simp
    ring
  rw [hzeq, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g _ hext δ hδ), h1]

end prim

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The standing hypotheses at the prime `v`. -/
structure Good (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  cop : v.asIdeal ⊔ 𝔪 = ⊤
  twelve : 12 ∣ Ideal.absNorm v.asIdeal - 1
  diff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

variable {v : HeightOneSpectrum (𝓞 F)}

lemma Good.notS (h : Good 𝔪 v) : v ∉ placesOf 𝔪 := fun hv =>
  v.isPrime.ne_top (eq_top_iff.2 (h.cop ▸ sup_le le_rfl hv))

lemma Good.ext (h : Good 𝔪 v) : IsExterior 𝔪 v.asIdeal := ⟨v.ne_bot, h.cop⟩

lemma absNorm_ne_one (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

lemma Good.coprime_six (h : Good 𝔪 v) : (Ideal.absNorm v.asIdeal).Coprime 6 := by
  have h1 := absNorm_pos v
  obtain ⟨k, hk⟩ := h.twelve
  have : Ideal.absNorm v.asIdeal = 12 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (12 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

lemma isMaximal_v (h : Good 𝔪 v) : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal :=
  isMaximal_map h.notS

lemma finite_L (h : Good 𝔪 v) : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have := finite_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one] at this

lemma natCard_L (h : Good 𝔪 v) :
    Nat.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm v.asIdeal := by
  have := natCard_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one, pow_one] at this

lemma quotHom_bijective_one (h : v ∉ placesOf 𝔪) :
    Function.Bijective (quotHom 𝔪 v.asIdeal) := by
  have := quotHom_bijective (𝔪 := 𝔪) h 1
  rwa [pow_one] at this

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

/-- Choice-free value of a root of unity: if `f ζ = f ω ^ i` then `ι ζ = ι ω ^ i`. -/
lemma iota_eq_pow_of_map {K : Type*} [CommRing K] [IsDomain K] (f : 𝓞 F →+* K) {m : ℕ}
    (hm : 0 < m) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω m) (hωf : IsPrimitiveRoot (f ω) m)
    {ζ : 𝓞 F} (hζ : ζ ^ m = 1) {i : ℕ} (h : f ζ = f ω ^ i) : ι (ζ : F) = ι (ω : F) ^ i := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one hζ
  have hpow : ∀ (z : K) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have hpowC : ∀ (z : ℂ) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have h1 : f ω ^ j = f ω ^ (i % m) := by
    rw [← map_pow, h, hpow _ hωf.pow_eq_one]
  have hji : j = i % m := hωf.pow_inj hj (Nat.mod_lt _ hm) h1
  have hιω : ι (ω : F) ^ m = 1 := by
    rw [← map_pow, ← map_pow (algebraMap (𝓞 F) F), hω.pow_eq_one, map_one, map_one]
  rw [show ((ω ^ j : 𝓞 F) : F) = (ω : F) ^ j from map_pow (algebraMap (𝓞 F) F) ω j, map_pow, hji,
    ← hpowC _ hιω]

end roots

section chi

/-- The function underlying `sexticResidueSymbol` on `L = R / P R`. -/
noncomputable def sexFun (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ := by
  classical
  exact if y = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
    then ι (h.choose : F) else 0

lemma sexticResidueSymbol_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x =
      sexFun ι 𝔪 v (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) x) := by
  unfold sexticResidueSymbol sexFun
  congr 1

variable {ι : F →+* ℂ}

/-- The image of `ω` in `L`. -/
noncomputable abbrev omegaL (ω : 𝓞 F) : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) ω)

lemma omegaL_prim (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (omegaL (𝔪 := 𝔪) (v := v) ω) 6 := by
  have h1 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
    hω.idealQuotient_mk (absNorm_ne_one v) h.coprime_six
  have h2 := h1.map_of_injective (quotHom_bijective_one (𝔪 := 𝔪) h.notS).1
  exact h2

lemma pow_card_sub_one_L (h : Good 𝔪 v)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    y ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [← natCard_L h, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one y hy

lemma six_mul_e (h : Good 𝔪 v) :
    6 * ((Ideal.absNorm v.asIdeal - 1) / 6) = Ideal.absNorm v.asIdeal - 1 :=
  Nat.mul_div_cancel' ((Nat.dvd_trans (by norm_num) h.twelve))

/-- Every nonzero `y ∈ L` has `y^e` a power of `ω`. -/
lemma exists_pow_e (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ∃ i : ℕ, i < 6 ∧ y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h6 : (y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, six_mul_e h, pow_card_sub_one_L h hy]
  obtain ⟨i, hi, hi'⟩ := (omegaL_prim h hω).eq_pow_of_pow_eq_one h6
  exact ⟨i, hi, hi'.symm⟩

lemma sexFun_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    sexFun ι 𝔪 v y = ι (ω : F) ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) :=
    ⟨ω ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
      rw [map_pow, map_pow, hi]⟩
  classical
  unfold sexFun
  rw [if_neg hy, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set f : 𝓞 F →+* SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (SInt 𝔪))
  exact iota_eq_pow_of_map ι f (by norm_num) hω (omegaL_prim h hω) h1 (by
    change Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) hex.choose) = omegaL ω ^ i
    rw [h2, hi])

lemma sexFun_zero : sexFun ι 𝔪 v (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  classical
  unfold sexFun; rw [if_pos rfl]

lemma iota_omega_prim {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : IsPrimitiveRoot (ι (ω : F)) 6 :=
  (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective

/-- `χ_P` as a multiplicative character of `L`. -/
noncomputable def chi (ι : F →+* ℂ) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun := sexFun ι 𝔪 v
  map_one' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [sexFun_eq_pow h hω one_ne_zero (i := 0) (by rw [one_pow, pow_zero])]
    simp
  map_mul' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro x y
    by_cases hx : x = 0
    · simp [hx, sexFun_zero]
    by_cases hy : y = 0
    · simp [hy, sexFun_zero]
    obtain ⟨i, -, hi⟩ := exists_pow_e h hω hx
    obtain ⟨j, -, hj⟩ := exists_pow_e h hω hy
    rw [sexFun_eq_pow h hω hx hi, sexFun_eq_pow h hω hy hj,
      sexFun_eq_pow h hω (mul_ne_zero hx hy) (i := i + j) (by rw [mul_pow, hi, hj, pow_add]),
      pow_add]
  map_nonunit' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro a ha
    have : a = 0 := by
      by_contra h'
      exact ha (Ne.isUnit h')
    rw [this]; exact sexFun_zero

lemma chi_mk (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪) :
    chi ι h hω (Ideal.Quotient.mk _ x) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
  (sexticResidueSymbol_eq ι 𝔪 v x).symm

lemma chi_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    chi ι h hω y = ι (ω : F) ^ i :=
  sexFun_eq_pow h hω hy hi

lemma chi_neg_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω (-1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hne : (-1 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 0 :=
    neg_ne_zero.2 one_ne_zero
  have heven : Even ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    obtain ⟨k, hk⟩ := h.twelve
    rw [hk, show 12 * k = 6 * (2 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact even_two_mul k
  rw [chi_eq_pow h hω hne (i := 0) (by rw [heven.neg_one_pow, pow_zero]), pow_zero]

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

lemma chi_pow_six (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    chi ι h hω ^ 6 = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  ext u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply_coe]
  exact chi_pow_six_apply h hω u.ne_zero

/-- `χ` has exact order `6`: `χ^j ≠ 1` unless `6 ∣ j`. -/
lemma chi_pow_ne_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) {j : ℕ}
    (hj : ¬ 6 ∣ j) : chi ι h hω ^ j ≠ 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set Q := Ideal.absNorm v.asIdeal
  set e := (Q - 1) / 6
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (SInt 𝔪 ⧸ v.asIdeal.map
    (algebraMap (𝓞 F) (SInt 𝔪)))ˣ)
  have hog : orderOf γ = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, natCard_L h]
  obtain ⟨i, hi6, hi⟩ := exists_pow_e h hω
    (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))) γ.ne_zero
  -- `ω^i` is a primitive sixth root
  have hcop : Nat.Coprime i 6 := by
    have hord : orderOf ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) = 6 := by
      have hγ' : orderOf (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Q - 1 := by
        rw [orderOf_units, hog]
      rw [orderOf_pow' _ (by
        have := six_mul_e h; have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
        omega), hγ']
      have := six_mul_e h
      have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
      rw [show Q - 1 = 6 * e from (six_mul_e h).symm, Nat.gcd_mul_left_left]
      have he : 0 < e := by omega
      rw [Nat.mul_div_cancel _ he]
    have hprim : IsPrimitiveRoot ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) 6 := by
      rw [← hord]; exact IsPrimitiveRoot.orderOf _
    rw [hi] at hprim
    exact ((omegaL_prim h hω).pow_iff_coprime (by norm_num) i).1 hprim
  intro hone
  have h1 : chi ι h hω (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ j = 1 := by
    rw [← MulChar.pow_apply' _ (by rintro rfl; exact hj (dvd_zero 6)), hone,
      MulChar.one_apply_coe]
  rw [chi_eq_pow h hω (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
    γ.ne_zero hi, ← pow_mul, (iota_omega_prim hω).pow_eq_one_iff_dvd] at h1
  exact hj (hcop.symm.dvd_of_dvd_mul_left h1)

end chi

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3I_Gauss: the additive character, Gauss sums and Davenport–Hasse on `L = R / P R`

* `psi g h : AddChar L ℂ`, `psi_mk : psi (mk x) = e(x / gen P)`, `psi_isPrimitive`.
* `card_sqrt`: `#{u | u² = w} = 1 + χ³(w)`; `jacobi_dh`: `χ(4) J(χ, χ) = J(χ³, χ)`.
* Gauss sums `g_j = gaussSum (χ^j) ψ`: `gs_mul_gs_inv`, `gs_three_sq`, `star_gs`, `dh`:
  `χ(4) g₁ g₃ = g₂²`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma quotLift_mk_sub {I : Ideal (SInt 𝔪)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq]; exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma mk_quotLift {I : Ideal (SInt 𝔪)} (y : SInt 𝔪 ⧸ I) :
    Ideal.Quotient.mk I (quotLift y) = y :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective _

/-- `e(x / gen 𝔞)` depends only on `x mod 𝔞 R`. -/
lemma sAddChar_div_congr (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (hx : x - x' ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 ((x : F) / (g.gen 𝔞 : F)) = sAddChar 𝔪 ((x' : F) / (g.gen 𝔞 : F)) := by
  have : (x : F) / (g.gen 𝔞 : F) =
      (x' : F) / (g.gen 𝔞 : F) + ((x - x' : SInt 𝔪) : F) / (g.gen 𝔞 : F) := by
    rw [Subalgebra.coe_sub]; ring
  rw [this, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g 𝔞 h𝔞 _ hx)]

/-- The additive character `y ↦ e(y / gen P)` of `L`. -/
noncomputable def psi (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) :
    AddChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun y := sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F))
  map_zero_eq_one' := by
    have h0 : quotLift (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_quotLift]
    exact C3B.sAddChar_of_mem _ (C3B.div_gen_mem g _ h.ext _ h0)
  map_add_eq_mul' := by
    intro a b
    have hab : quotLift (a + b) - (quotLift a + quotLift b) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift, mk_quotLift]
    rw [sAddChar_div_congr g _ h.ext hab, Subalgebra.coe_add, add_div,
      sAddChar_div_gen_add g _ h.ext]

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

lemma psi_isPrimitive (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) : (psi g h).IsPrimitive := by
  intro a ha hone
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ∉ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one]; rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨r, hr⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff le_rfl x hx
  apply hr
  have := congrArg (fun φ => φ (Ideal.Quotient.mk _ r)) hone
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this
  rw [← map_mul, psi_mk, Subalgebra.coe_mul] at this
  rw [pow_one]
  exact this

/-! ### Characters on the finite field `L` -/

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma card_L : Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, natCard_L h]

lemma chi_pow_mod (n : ℕ) : chi ι h hω ^ n = chi ι h hω ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, chi_pow_six h hω, one_pow, one_mul]

variable (g : AllowedGen ι 𝔪)

end field

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3I_HD: the bundle's `γ_j`, `Λ`, `G` through Gauss and Jacobi sums; `Ḡ⁶ = 1` and
`γ₁ γ₂ Λ̄ Ḡ = −1` at a good prime

* `gaussPhase_eq`: `γ_j(P) = (N P)^{-1/2} g(χ^j, ψ)` (`j ≥ 1`);
* `gaussG_eq`: `G(P) = conj(χ(4)) γ₃(P)`;
* `cubicResidueChar_eq`: `ρ_P(x) = χ²(x)` through `𝓞/P ≃ L`; `gaussLambda_eq`:
  `Λ(P) = −(N P)^{-1/2} J(χ², χ²)`;
* `conj_gaussG_pow_six` and `hd_good`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma normalizedFactors_v (v : HeightOneSpectrum (𝓞 F)) :
    normalizedFactors v.asIdeal = {v.asIdeal} := by
  have hirr : Irreducible v.asIdeal := (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  rw [normalizedFactors_irreducible hirr, normalize_eq]

lemma residueSymbol_v (x : SInt 𝔪) :
    residueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal x := by
  simp [residueSymbol, normalizedFactors_v]

lemma sqrt_sq_C : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ^ 2 = Ideal.absNorm v.asIdeal := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

lemma chi_mk_quotLift (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = chi ι h hω y := by
  rw [← chi_mk h hω, mk_quotLift]

/-- `γ_j(P) = (N P)^{-1/2} g(χ^j, ψ)`. -/
lemma gaussPhase_eq (g : AllowedGen ι 𝔪) {j : ℕ} (hj : j ≠ 0) :
    gaussPhase g j v.asIdeal =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)⁻¹ *
        gaussSum (chi ι h hω ^ j) (psi g h) := by
  unfold gaussPhase
  congr 1
  rw [finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [residueSymbol_v, chi_mk_quotLift h hω, MulChar.pow_apply' _ hj, psi_apply]

end field

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3I_Loc: generators of prime powers and their valuations

* `SixEq 𝔪 x y`: `x = μ⁶ y` for a unit `μ` of `R`; `gen_mul_sixEq`, `gen_top_sixEq`,
  `gen_pow_add`, `gen_pow_mul`.
* `val_gen`: `v(gen(P^j)) = exp(-j)`; `val_unit`; `mul_mem_iff`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

/-- `x = μ⁶ y` for a unit `μ` of `R`. -/
def SixEq (𝔪 : Ideal (𝓞 F)) (x y : SInt 𝔪) : Prop := ∃ μ : (SInt 𝔪)ˣ, x = (μ : SInt 𝔪) ^ 6 * y

lemma SixEq.refl (x : SInt 𝔪) : SixEq 𝔪 x x := ⟨1, by simp⟩

lemma SixEq.trans {x y z : SInt 𝔪} (h1 : SixEq 𝔪 x y) (h2 : SixEq 𝔪 y z) : SixEq 𝔪 x z := by
  obtain ⟨μ, rfl⟩ := h1
  obtain ⟨ν, rfl⟩ := h2
  exact ⟨μ * ν, by rw [Units.val_mul, mul_pow]; ring⟩

lemma SixEq.mul {x y x' y' : SInt 𝔪} (h1 : SixEq 𝔪 x y) (h2 : SixEq 𝔪 x' y') :
    SixEq 𝔪 (x * x') (y * y') := by
  obtain ⟨μ, rfl⟩ := h1
  obtain ⟨ν, rfl⟩ := h2
  exact ⟨μ * ν, by rw [Units.val_mul, mul_pow]; ring⟩

/-- `gen(IJ) = μ⁶ gen(I) gen(J)`. -/
lemma gen_mul_sixEq (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) : SixEq 𝔪 (g.gen (I * J)) (g.gen I * g.gen J) := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, hε, mul_assoc]
  rfl

lemma isExterior_top' : IsExterior 𝔪 (⊤ : Ideal (𝓞 F)) := ⟨top_ne_bot, top_sup_eq _⟩

/-- `gen ⊤` is a sixth power of a unit. -/
lemma gen_top_sixEq (g : AllowedGen ι 𝔪) : SixEq 𝔪 (g.gen ⊤) 1 := by
  obtain ⟨μ, hμ⟩ := C3B.isUnit_gen_top g
  have h := gen_mul_sixEq g (isExterior_top' (𝔪 := 𝔪)) isExterior_top'
  rw [Ideal.top_mul] at h
  obtain ⟨ν, hν⟩ := h
  refine ⟨ν⁻¹, ?_⟩
  rw [mul_one, ← hμ]
  rw [← hμ] at hν
  have h2 : (ν : SInt 𝔪) ^ 6 * μ = 1 := by
    apply mul_left_cancel₀ μ.ne_zero
    linear_combination (-1 : SInt 𝔪) * hν
  calc (μ : SInt 𝔪) = ((ν⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * ((ν : SInt 𝔪) ^ 6 * μ) := by
        rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    _ = _ := by rw [h2, mul_one]

section prime

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma ext_pow (j : ℕ) : IsExterior 𝔪 (v.asIdeal ^ j) := isExterior_pow h.ext j

lemma gen_pow_add (a b : ℕ) :
    SixEq 𝔪 (g.gen (v.asIdeal ^ (a + b))) (g.gen (v.asIdeal ^ a) * g.gen (v.asIdeal ^ b)) := by
  rw [pow_add]; exact gen_mul_sixEq g (ext_pow h a) (ext_pow h b)

lemma gen_pow_zero : SixEq 𝔪 (g.gen (v.asIdeal ^ 0)) 1 := by
  rw [pow_zero, Ideal.one_eq_top]; exact gen_top_sixEq g

/-- `gen(P^j) ~ π^j`. -/
lemma gen_pow_sixEq (j : ℕ) : SixEq 𝔪 (g.gen (v.asIdeal ^ j)) (g.gen v.asIdeal ^ j) := by
  induction j with
  | zero => have := gen_pow_zero g h; simp only [pow_zero] at this ⊢; exact this
  | succ k ih =>
    have := gen_pow_add g h k 1
    rw [pow_one] at this
    exact this.trans (by rw [pow_succ (g.gen v.asIdeal)]; exact ih.mul (SixEq.refl (𝔪 := 𝔪) _))

/-- `gen(P^(m j)) ~ gen(P^m)^j`. -/
lemma gen_pow_mul (m j : ℕ) :
    SixEq 𝔪 (g.gen (v.asIdeal ^ (m * j))) (g.gen (v.asIdeal ^ m) ^ j) := by
  induction j with
  | zero =>
    rw [mul_zero, pow_zero (g.gen (v.asIdeal ^ m))]; exact gen_pow_zero g h
  | succ k ih =>
    rw [mul_add, mul_one, pow_succ (g.gen (v.asIdeal ^ m))]
    exact (gen_pow_add g h _ _).trans (ih.mul (SixEq.refl (𝔪 := 𝔪) _))

/-! ### Valuations -/

lemma val_unit (μ : (SInt 𝔪)ˣ) : v.valuation F ((μ : SInt 𝔪) : F) = 1 := by
  have h1 := val_le_one h.notS (μ : SInt 𝔪)
  have h2 := val_le_one h.notS ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have h3 : v.valuation F ((μ : SInt 𝔪) : F) * v.valuation F (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

lemma val_sixEq {x y : SInt 𝔪} (hxy : SixEq 𝔪 x y) :
    v.valuation F (x : F) = v.valuation F (y : F) := by
  obtain ⟨μ, rfl⟩ := hxy
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, map_pow, val_unit h, one_pow, one_mul]

lemma gen_mem (j : ℕ) :
    g.gen (v.asIdeal ^ j) ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen _ (ext_pow h j)]; exact Ideal.mem_span_singleton_self _

lemma val_pi : v.valuation F (g.gen v.asIdeal : F) = exp (-1 : ℤ) := by
  have hmem := gen_mem g h 1
  rw [pow_one] at hmem
  apply le_antisymm
  · have := val_le_of_mem h.notS 1 (by rw [pow_one]; exact hmem)
    simpa using this
  · obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : algebraMap (𝓞 F) (SInt 𝔪) p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      apply Ideal.mem_map_of_mem
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    rw [← g.span_gen _ h.ext, Ideal.mem_span_singleton'] at hpm
    obtain ⟨r, hr⟩ := hpm
    have := congrArg (fun z : SInt 𝔪 => v.valuation F (z : F)) hr
    simp only [Subalgebra.coe_mul, map_mul, coe_alg, hp] at this
    rw [← this]
    calc v.valuation F (r : F) * v.valuation F (g.gen v.asIdeal : F)
        ≤ 1 * v.valuation F (g.gen v.asIdeal : F) := mul_le_mul_left (val_le_one h.notS r) _
      _ = _ := one_mul _

/-- `v(gen(P^j)) = exp(-j)`. -/
lemma val_gen (j : ℕ) : v.valuation F (g.gen (v.asIdeal ^ j) : F) = exp (-(j : ℤ)) := by
  rw [val_sixEq h (gen_pow_sixEq g h j), Subalgebra.coe_pow, map_pow, val_pi g h, ← exp_nsmul]
  congr 1; simp

/-- `x y ∈ P^(a+j)` iff `y ∈ P^j` when `v(x) = exp(-a)`. -/
lemma mul_mem_iff {x : SInt 𝔪} {a : ℕ} (hx : v.valuation F (x : F) = exp (-(a : ℤ))) (j : ℕ)
    (y : SInt 𝔪) :
    x * y ∈ (v.asIdeal ^ (a + j)).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      y ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [mem_map_pow_iff h.notS, mem_map_pow_iff h.notS, Subalgebra.coe_mul, map_mul, hx]
  have e : (exp (-((a + j : ℕ) : ℤ)) : ℤᵐ⁰) = exp (-(a : ℤ)) * exp (-(j : ℤ)) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [e]
  constructor
  · intro h1
    have h1' : v.valuation F (y : F) * exp (-(a : ℤ)) ≤ exp (-(j : ℤ)) * exp (-(a : ℤ)) := by
      rw [mul_comm, mul_comm (exp (-(j : ℤ)))]; exact h1
    exact le_of_mul_le_mul_ne h1' exp_ne_zero
  · intro h1
    exact mul_le_mul' le_rfl h1

end prime

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3I_GP: Gauss sums modulo prime powers

For `t ≥ 1`, `A = gen(P^t)`, `r ∈ R`, `G_t(r) = gaussSumAt g (P^t) r`:
* `gsat_eq_zero`: `G_t(r) = 0` if `r ∉ P^(t-1) R`;
* `gsat_eq_fibre`: `G_t(r) = Q^(t-1) ∑_{a ∈ L} χ(a)^t e(r a / A)` if `r ∈ P^(t-1) R`;
* `exists_c`: then `r / A = c / π` with `c ∈ R`, `c ∈ P R ↔ r ∈ P^t R`;
* `lsum_eq`: the `L`-sum is `∑_a χ^t(a) ψ(c a)`; `ram_sum` (`6 ∣ t`), `gauss_shift` (`6 ∤ t`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma finsum_quot_congr {I J : Ideal (SInt 𝔪)} (hIJ : I = J) (f : SInt 𝔪 → ℂ) :
    ∑ᶠ y : SInt 𝔪 ⧸ I, f (quotLift y) = ∑ᶠ y : SInt 𝔪 ⧸ J, f (quotLift y) := by
  subst hIJ; rfl

lemma normalizedFactors_v_pow (v : HeightOneSpectrum (𝓞 F)) (t : ℕ) :
    normalizedFactors (v.asIdeal ^ t) = Multiset.replicate t v.asIdeal := by
  rw [normalizedFactors_pow, normalizedFactors_v, Multiset.nsmul_singleton]

lemma residueSymbol_pow (t : ℕ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (v.asIdeal ^ t) x = sexticResidueSymbol ι 𝔪 v.asIdeal x ^ t := by
  rw [residueSymbol, normalizedFactors_v_pow v t, Multiset.map_replicate,
    Multiset.prod_replicate]

lemma map_pow_mul (a b : ℕ) {x y : SInt 𝔪}
    (hx : x ∈ (v.asIdeal ^ a).map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hy : y ∈ (v.asIdeal ^ b).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    x * y ∈ (v.asIdeal ^ (a + b)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [pow_add, Ideal.map_mul]; exact Ideal.mul_mem_mul hx hy

lemma map_pow_anti {a b : ℕ} (hab : a ≤ b) :
    (v.asIdeal ^ b).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      (v.asIdeal ^ a).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.map_mono (Ideal.pow_le_pow_right hab)

lemma mem_one_iff (x : SInt 𝔪) :
    x ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      x ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by rw [pow_one]

section gauss

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include h

/-- The summand of `G_t(r)` as a function on `R`. -/
noncomputable def gsF (t : ℕ) (r : SInt 𝔪) (x : SInt 𝔪) : ℂ :=
  sexticResidueSymbol ι 𝔪 v.asIdeal x ^ t *
    sAddChar 𝔪 ((r : F) * (x : F) / (g.gen (v.asIdeal ^ t) : F))

omit h in
lemma gsat_eq_finsum (t : ℕ) (r : SInt 𝔪) :
    gaussSumAt g (v.asIdeal ^ t) (r : F) =
      ∑ᶠ y : SInt 𝔪 ⧸ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)),
        gsF (ι := ι) (v := v) g t r (quotLift y) := by
  unfold gaussSumAt gsF
  refine finsum_congr fun y => ?_
  rw [residueSymbol_pow]

lemma sext_congr {x y : SInt 𝔪} (hxy : x - y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal y :=
  C3B.sexticResidueSymbol_eq_of_mk_eq ι _ x y (Ideal.Quotient.eq.mpr hxy)

/-- `G_t(r) = 0` for `r ∉ P^(t-1) R`. -/
theorem gsat_eq_zero {t : ℕ} (ht : 1 ≤ t) (r : SInt 𝔪)
    (hr : r ∉ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    gaussSumAt g (v.asIdeal ^ t) (r : F) = 0 := by
  set π := g.gen v.asIdeal
  set A := g.gen (v.asIdeal ^ t)
  have hext := ext_pow h t
  -- `π r ∉ P^t R`
  have hπr : π * r ∉ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := mul_mem_iff h (x := π) (a := 1) (by rw [val_pi g h]; simp) (t - 1) r
    rw [Nat.add_sub_cancel' ht] at this
    rwa [this]
  obtain ⟨r', hr'⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff ht _ hπr
  set b : SInt 𝔪 := π * r'
  set c := sAddChar 𝔪 ((r : F) * (b : F) / (A : F))
  have hc : c ≠ 1 := by
    simp only [c, b, Subalgebra.coe_mul] at hr' ⊢
    rwa [show (r : F) * ((π : F) * (r' : F)) = (π : F) * (r : F) * (r' : F) by ring]
  have hb : b ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := gen_mem g h 1; rw [pow_one] at this
    exact Ideal.mul_mem_right _ _ this
  have haveFin := finite_quot (𝔪 := 𝔪) h.notS t
  set I := (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪))
  have hshift : ∀ y : SInt 𝔪 ⧸ I,
      gsF (ι := ι) (v := v) g t r (quotLift (y + Ideal.Quotient.mk I b)) =
        gsF (ι := ι) (v := v) g t r (quotLift y) * c := by
    intro y
    set q := quotLift y
    set q' := quotLift (y + Ideal.Quotient.mk I b)
    have hδ : q' - (q + b) ∈ I := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift]
    have hδ1 : q' - q ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      have h1 : q' - q = (q' - (q + b)) + b := by ring
      rw [h1]
      have hI1 : I ≤ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        have := map_pow_anti (𝔪 := 𝔪) (v := v) ht; rwa [pow_one] at this
      exact add_mem (hI1 hδ) hb
    unfold gsF
    rw [sext_congr h hδ1, mul_assoc]
    congr 1
    have hrδ : r * q' - (r * q + r * b) ∈ I := by
      rw [show r * q' - (r * q + r * b) = r * (q' - (q + b)) by ring]
      exact Ideal.mul_mem_left _ _ hδ
    rw [show (r : F) * (q' : F) = ((r * q' : SInt 𝔪) : F) by rw [Subalgebra.coe_mul],
      sAddChar_div_congr g _ hext hrδ, Subalgebra.coe_add, add_div,
      sAddChar_div_gen_add g _ hext, Subalgebra.coe_mul, Subalgebra.coe_mul]
  have hsum : (∑ᶠ y : SInt 𝔪 ⧸ I, gsF (ι := ι) (v := v) g t r (quotLift y)) =
      (∑ᶠ y : SInt 𝔪 ⧸ I, gsF (ι := ι) (v := v) g t r (quotLift y)) * c := by
    rw [finsum_mul]
    rw [← finsum_comp_equiv (Equiv.addRight (Ideal.Quotient.mk I b))]
    exact finsum_congr fun y => hshift y
  rw [gsat_eq_finsum]
  have : (∑ᶠ y : SInt 𝔪 ⧸ I, gsF (ι := ι) (v := v) g t r (quotLift y)) * (1 - c) = 0 := by
    rw [mul_sub, mul_one, ← hsum, sub_self]
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hc.symm)

/-- `G_t(r) = Q^(t-1) ∑_{a ∈ L} χ_P(a)^t e(r a / A)` for `r ∈ P^(t-1) R`. -/
theorem gsat_eq_fibre {t : ℕ} (ht : 1 ≤ t) (r : SInt 𝔪)
    (hr : r ∈ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    gaussSumAt g (v.asIdeal ^ t) (r : F) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) *
        ∑ᶠ a : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
          gsF (ι := ι) (v := v) g t r (quotLift a) := by
  have hext := ext_pow h t
  rw [gsat_eq_finsum, finsum_quot_fibre h.notS ht]
  · rw [finsum_quot_congr (by rw [pow_one] : (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) =
      v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
  · intro x y hxy
    unfold gsF
    rw [sext_congr h ((mem_one_iff _).1 hxy)]
    congr 1
    apply sAddChar_div_congr g _ hext (x := r * x) (x' := r * y)
    rw [show r * x - r * y = r * (x - y) by ring]
    have := map_pow_mul (v := v) (t - 1) 1 hr hxy
    rwa [Nat.sub_add_cancel ht] at this

/-- For `r ∈ P^(t-1) R`: `r / gen(P^t) = c / π` with `c ∈ R`, and `c ∈ P R ↔ r ∈ P^t R`. -/
theorem exists_c {t : ℕ} (ht : 1 ≤ t) (r : SInt 𝔪)
    (hr : r ∈ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ c : SInt 𝔪, (r : F) / (g.gen (v.asIdeal ^ t) : F) = (c : F) / (g.gen v.asIdeal : F) ∧
      (c ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
        r ∈ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have hadd := gen_pow_add g h (t - 1) 1
  rw [Nat.sub_add_cancel ht, pow_one] at hadd
  obtain ⟨μ, hμ⟩ := hadd
  obtain ⟨r', hr'⟩ := (C3B.mem_map_iff g _ (ext_pow h (t - 1)) r).1 hr
  set B := g.gen (v.asIdeal ^ (t - 1))
  set π := g.gen v.asIdeal
  refine ⟨r' * ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6, ?_, ?_⟩
  · have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ (ext_pow h (t - 1))
    have hπ0 : (π : F) ≠ 0 := C3B.gen_ne_zero g _ h.ext
    have hμμ : (((μ : SInt 𝔪) : F)) ^ 6 * (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) ^ 6 = 1 :=
      C3B.coe_unit_pow_mul_inv μ
    have hμ0 : ((μ : SInt 𝔪) : F) ≠ 0 := by
      intro h0; rw [h0] at hμμ; simp at hμμ
    rw [div_eq_div_iff (C3B.gen_ne_zero g _ (ext_pow h t)) hπ0, hμ, hr']
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    linear_combination (-((r' : F) * (B : F) * (π : F))) * hμμ
  · have hval := val_gen g h (t - 1)
    rw [hr']
    have key := mul_mem_iff h hval 1 r'
    rw [Nat.sub_add_cancel ht, pow_one] at key
    rw [key]
    constructor
    · intro hm
      have := Ideal.mul_mem_right ((μ : SInt 𝔪) ^ 6) _ hm
      rwa [mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one] at this
    · intro hm
      exact Ideal.mul_mem_right _ _ hm

end gauss

section lsum

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

/-- The `L`-sum as a twisted Gauss sum. -/
theorem lsum_eq {t : ℕ} (ht : t ≠ 0) (r c : SInt 𝔪)
    (hrc : (r : F) / (g.gen (v.asIdeal ^ t) : F) = (c : F) / (g.gen v.asIdeal : F)) :
    ∑ᶠ a : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
        gsF (ι := ι) (v := v) g t r (quotLift a) =
      ∑ a, (chi ι h hω ^ t) a * psi g h (Ideal.Quotient.mk _ c * a) := by
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold gsF
  rw [chi_mk_quotLift h hω, MulChar.pow_apply' _ ht]
  congr 1
  rw [← mk_quotLift (I := v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) a, ← map_mul, psi_mk,
    mk_quotLift, mul_comm (r : F), mul_div_assoc, hrc, Subalgebra.coe_mul]
  ring_nf

/-- The Ramanujan sum: `∑_a χ^t(a) ψ(b a) = [b = 0] Q − 1` for `6 ∣ t`. -/
theorem ram_sum [DecidableEq (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))] {t : ℕ}
    (h6 : 6 ∣ t) (b : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∑ a, (chi ι h hω ^ t) a * psi g h (b * a) =
      (if b = 0 then (Ideal.absNorm v.asIdeal : ℂ) else 0) - 1 := by
  have hψ := psi_isPrimitive g h
  have hcard := card_L h hω
  have h1 : chi ι h hω ^ t = 1 := by
    rw [chi_pow_mod h hω, Nat.eq_zero_of_dvd_of_lt (Nat.dvd_mod_iff h6 |>.2 dvd_rfl |> fun _ =>
      (Nat.dvd_mod_iff (dvd_refl 6)).2 h6) (Nat.mod_lt _ (by norm_num)), pow_zero]
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hs := AddChar.sum_mulShift b hψ
  have e1 : ∀ a, (chi ι h hω ^ t) a * psi g h (b * a) =
      psi g h (a * b) - if a = 0 then 1 else 0 := by
    intro a
    rw [h1, mul_comm b a]
    by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul,
        AddChar.map_zero_eq_one, sub_self]
    · rw [if_neg ha, sub_zero, MulChar.one_apply (Ne.isUnit ha), one_mul]
  rw [Finset.sum_congr rfl (fun a _ => e1 a), Finset.sum_sub_distrib, hs, hcard,
    Finset.sum_ite_eq' Finset.univ (0 : SInt 𝔪 ⧸ _)]
  simp

/-- `∑_a χ^t(a) ψ(b a) = χ^t(b)⁻¹ g(χ^t)` for `b ≠ 0`. -/
theorem gauss_shift {t : ℕ}
    {b : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hb : b ≠ 0) :
    ∑ a, (chi ι h hω ^ t) a * psi g h (b * a) =
      ((chi ι h hω ^ t) b)⁻¹ * gaussSum (chi ι h hω ^ t) (psi g h) := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hu : IsUnit b := Ne.isUnit hb
  have key := gaussSum_mulShift (chi ι h hω ^ t) (psi g h) hu.unit
  have hne : (chi ι h hω ^ t) b ≠ 0 := by
    intro h0
    have h6 : ((chi ι h hω ^ t) b) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' _ (by norm_num), ← pow_mul, mul_comm, pow_mul, chi_pow_six h hω,
        one_pow, MulChar.one_apply hu]
    rw [h0] at h6; norm_num at h6
  rw [← key, IsUnit.unit_spec, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, gaussSum]
  rfl

theorem gauss_zero_shift {t : ℕ} (h6 : ¬ 6 ∣ t) :
    ∑ a, (chi ι h hω ^ t) a * psi g h (0 * a) = 0 := by
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one (chi_pow_ne_one h hω h6)

end lsum

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3I_F: the local Poisson factor `F(P^k, P^t, gen(P^m)⁶)`

Case analysis following (7.15)–(7.17), with `H = gen(P^m)⁶`, `A = gen(P^t)`, `s = gen(P^k)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

/-- A unique solution of a linear congruence. -/
lemma finsum_unique {I : Ideal (SInt 𝔪)} (u : (SInt 𝔪)ˣ) (b : SInt 𝔪) (f : SInt 𝔪 → ℂ)
    (hf : ∀ x y, x - y ∈ I → f x = f y) (p : SInt 𝔪 → Prop) [DecidablePred p]
    (hp : ∀ x, p x ↔ b - (u : SInt 𝔪) * x ∈ I) :
    ∑ᶠ d : SInt 𝔪 ⧸ I, (if p (quotLift d) then f (quotLift d) else 0) =
      f (((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * b) := by
  set x₀ := ((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * b
  have key : ∀ x, b - (u : SInt 𝔪) * x ∈ I ↔ x - x₀ ∈ I := by
    intro x
    have e1 : x - x₀ = -((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * (b - (u : SInt 𝔪) * x) := by
      simp only [x₀]
      have : ((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * (u : SInt 𝔪) = 1 := Units.inv_mul u
      linear_combination (-x) * this
    have e2 : b - (u : SInt 𝔪) * x = -(u : SInt 𝔪) * (x - x₀) := by
      simp only [x₀]
      have : (u : SInt 𝔪) * ((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) = 1 := Units.mul_inv u
      linear_combination (-b) * this
    constructor
    · intro h; rw [e1]; exact Ideal.mul_mem_left _ _ h
    · intro h; rw [e2]; exact Ideal.mul_mem_left _ _ h
  rw [finsum_eq_single _ (Ideal.Quotient.mk I x₀)]
  · have h0 : quotLift (Ideal.Quotient.mk I x₀) - x₀ ∈ I := quotLift_mk_sub x₀
    rw [if_pos ((hp _).2 ((key _).2 h0)), hf _ _ h0]
  · intro d hd
    rw [if_neg]
    intro hpd
    apply hd
    rw [← mk_quotLift d]
    exact Ideal.Quotient.eq.mpr ((key _).1 ((hp _).1 hpd))

lemma mem_iff_of_val {x : SInt 𝔪} {a : ℕ} (hv : v ∉ placesOf 𝔪)
    (hx : v.valuation F (x : F) = exp (-(a : ℤ))) (j : ℕ) :
    x ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ j ≤ a := by
  rw [mem_map_pow_iff hv, hx, exp_le_exp]; omega

section main

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma val_H (m : ℕ) :
    v.valuation F ((g.gen (v.asIdeal ^ m) ^ 6 : SInt 𝔪) : F) = exp (-((6 * m : ℕ) : ℤ)) := by
  rw [Subalgebra.coe_pow, map_pow, val_gen g h, ← exp_nsmul]; congr 1; push_cast; ring

lemma H_mem_iff (m j : ℕ) :
    g.gen (v.asIdeal ^ m) ^ 6 ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ j ≤ 6 * m :=
  mem_iff_of_val h.notS (val_H g h m) j

lemma goodP_v : C3B.GoodP 𝔪 v.asIdeal :=
  ⟨v.isPrime, v.ne_bot, h.notS, Nat.dvd_trans (by norm_num) h.twelve⟩

lemma goodP_pow (t : ℕ) : ∀ Q ∈ normalizedFactors (v.asIdeal ^ t), C3B.GoodP 𝔪 Q := by
  intro Q hQ
  rw [normalizedFactors_v_pow, Multiset.mem_replicate] at hQ
  rw [hQ.2]; exact goodP_v h

lemma sext_zero_of_mem {q : SInt 𝔪} (hq : q ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal q = 0 := by
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr hq)]

/-- `k = 0`: `F(1, P^t, H) = G_t(H)`. -/
theorem pf_k0 (t m : ℕ) :
    poissonFactor g (v.asIdeal ^ 0) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ m) ^ 6) =
      gaussSumAt g (v.asIdeal ^ t) ((g.gen (v.asIdeal ^ m) ^ 6 : SInt 𝔪) : F) := by
  have hext := ext_pow h t
  rw [pow_zero, Ideal.one_eq_top, poissonFactor, C3B.finsum_quot_top,
    if_pos (by rw [Ideal.map_top]; exact Submodule.mem_top), C3B.residueSymbol_top, one_mul]
  obtain ⟨μ, hμ⟩ := gen_top_sixEq g (𝔪 := 𝔪)
  rw [mul_one] at hμ
  set H := g.gen (v.asIdeal ^ m) ^ 6
  set A := g.gen (v.asIdeal ^ t)
  set q₀ := (quotLift (0 : SInt 𝔪 ⧸ (⊤ : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪))))
  set ν := ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have hμν : ((μ : SInt 𝔪) : F) ^ 6 * (ν : F) ^ 6 = 1 := C3B.coe_unit_pow_mul_inv μ
  have harg : ((H - A * q₀ : SInt 𝔪) : F) / (g.gen ⊤ : F) =
      ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * (H : F) + ((A * (-(q₀ * ν ^ 6)) : SInt 𝔪) : F) := by
    have hμ0 : ((μ : SInt 𝔪) : F) ^ 6 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hμν; exact zero_ne_one hμν
    rw [hμ, div_eq_iff (by rw [Subalgebra.coe_pow]; exact hμ0)]
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg]
    linear_combination (-(H : F) + (A : F) * (q₀ : F)) * hμν
  rw [harg, C3B.gaussSumAt_add_mem g _ hext _ _ (Ideal.mul_mem_right _ _ (gen_mem g h t)),
    C3B.gaussSumAt_unit_pow_six g _ hext (goodP_pow h t) μ⁻¹ _ H.2]

open Classical in
/-- `F(P^k, P^t, H)` as a sum over `R/P^k R`. -/
lemma pf_eq_sum (k t : ℕ) (H : SInt 𝔪) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) H =
      ∑ᶠ d : SInt 𝔪 ⧸ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)),
        if H - g.gen (v.asIdeal ^ t) * quotLift d ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))
        then sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) ^ k *
          gaussSumAt g (v.asIdeal ^ t)
            (((H - g.gen (v.asIdeal ^ t) * quotLift d : SInt 𝔪) : F) /
              (g.gen (v.asIdeal ^ k) : F))
        else 0 := by
  unfold poissonFactor
  refine finsum_congr fun d => ?_
  split_ifs <;> simp only [residueSymbol_pow]

/-- The quotient `(H - A q)/s` when `s ∣ H - A q`. -/
lemma exists_arg (k : ℕ) (x : SInt 𝔪)
    (hx : x ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, (x : F) / (g.gen (v.asIdeal ^ k) : F) = (r : F) ∧
      ∀ j, (r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
        x ∈ (v.asIdeal ^ (k + j)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  obtain ⟨r, hr⟩ := (C3B.mem_map_iff g _ (ext_pow h k) x).1 hx
  refine ⟨r, ?_, fun j => ?_⟩
  · rw [hr, Subalgebra.coe_mul, mul_div_cancel_left₀ _ (C3B.gen_ne_zero g _ (ext_pow h k))]
  · rw [hr, mul_mem_iff h (val_gen g h k)]

lemma gsat_top' (k : SInt 𝔪) : gaussSumAt g (v.asIdeal ^ 0) (k : F) = 1 := by
  rw [pow_zero, Ideal.one_eq_top]; exact C3B.gaussSumAt_top g _ k.2

lemma unit_not_mem (μ : (SInt 𝔪)ˣ) :
    (μ : SInt 𝔪) ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  intro hm
  have := val_le_of_mem h.notS 1 (by rw [pow_one]; exact hm)
  rw [val_unit h] at this
  exact absurd this (by rw [not_le]; exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero)

lemma sext_one {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : sexticResidueSymbol ι 𝔪 v.asIdeal 1 = 1 := by
  rw [← chi_mk h hω, map_one, MulChar.map_one]

lemma sext_unit_six {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (μ : (SInt 𝔪)ˣ) :
    sexticResidueSymbol ι 𝔪 v.asIdeal ((μ : SInt 𝔪) ^ 6) = 1 := by
  have := C3B.sexticResidueSymbol_unit_pow_six ι v.asIdeal (goodP_v h) μ 1
  rw [mul_one] at this; rw [this, sext_one h hω]

/-- `t = 0`, `k ≥ 1`. -/
theorem pf_t0 {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ 0) (g.gen (v.asIdeal ^ m) ^ 6) =
      if m = 0 then 1 else 0 := by
  classical
  rw [pf_eq_sum g h]
  obtain ⟨α, hα⟩ := gen_pow_zero g h
  rw [mul_one] at hα
  set A := g.gen (v.asIdeal ^ 0)
  set H := g.gen (v.asIdeal ^ m) ^ 6
  have hk1 : (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := map_pow_anti (𝔪 := 𝔪) (v := v) hk; rwa [pow_one] at this
  have hterm : ∀ q : SInt 𝔪, (if H - A * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))
      then sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k *
        gaussSumAt g (v.asIdeal ^ 0) (((H - A * q : SInt 𝔪) : F) / (g.gen (v.asIdeal ^ k) : F))
      else 0) = if H - A * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))
      then sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k else 0 := by
    intro q
    split_ifs with hc
    · obtain ⟨r, hr, -⟩ := exists_arg g h k _ hc
      rw [hr, gsat_top' g h, mul_one]
    · rfl
  rw [finsum_congr fun d => hterm (quotLift d)]
  by_cases hm : m = 0
  · rw [if_pos hm]
    -- unique solution `q ≡ A⁻¹ H`
    obtain ⟨β, hβ⟩ := gen_pow_zero g h
    rw [mul_one] at hβ
    have hH : H = ((β ^ 6 : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 := by
      simp only [H, hm, hβ, Units.val_pow_eq_pow_val]
    rw [finsum_unique (α ^ 6) H (fun q => sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k)
      (fun x y hxy => by rw [sext_congr h (hk1 hxy)])
      (fun q => H - A * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))) (fun x => by
        rw [Units.val_pow_eq_pow_val, ← hα])]
    have e : (((α ^ 6)⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) * H =
        (((α⁻¹ * β ^ 6 : (SInt 𝔪)ˣ)) : SInt 𝔪) ^ 6 := by
      rw [hH, ← inv_pow]; simp only [Units.val_pow_eq_pow_val, Units.val_mul]; ring
    rw [e, sext_unit_six h hω, one_pow]
  · rw [if_neg hm]
    have hHm : H ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      have := (H_mem_iff g h m 1).2 (by omega); rwa [pow_one] at this
    refine (finsum_congr fun d => ?_).trans finsum_zero
    split_ifs with hc
    · have hAq : A * quotLift d ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        have := sub_mem hHm (hk1 hc); rwa [sub_sub_cancel] at this
      have hq : quotLift d ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hα] at hAq
        have := Ideal.mul_mem_left _ (((α⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6) hAq
        rwa [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] at this
      rw [sext_zero_of_mem h hq, zero_pow (by omega)]
    · rfl

lemma mem_one' {x : SInt 𝔪} (hx : x ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    x ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by rwa [pow_one] at hx

/-- `m = 0`, `t, k ≥ 1`. -/
theorem pf_m0 {t k : ℕ} (ht : 1 ≤ t) (hk : 1 ≤ k) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ 0) ^ 6) = 0 := by
  rw [pf_eq_sum g h]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  rw [if_neg]
  intro hc
  have hA : g.gen (v.asIdeal ^ t) * quotLift d ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mul_mem_right _ _ (map_pow_anti ht (gen_mem g h t))
  have := add_mem (map_pow_anti hk hc) hA
  rw [sub_add_cancel, H_mem_iff g h] at this
  omega

/-- `6m < t`, `k ≥ 1`. -/
theorem pf_lt {t k m : ℕ} (ht : 1 ≤ t) (hk : 1 ≤ k) (hmt : 6 * m < t) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ m) ^ 6) = 0 := by
  rw [pf_eq_sum g h]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  split_ifs with hc
  · obtain ⟨r, hr, hrj⟩ := exists_arg g h k _ hc
    rw [hr, gsat_eq_zero g h ht r, mul_zero]
    intro hr1
    have h1 := (hrj (t - 1)).1 hr1
    have h2 : g.gen (v.asIdeal ^ t) * quotLift d ∈
        (v.asIdeal ^ (6 * m + 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.mul_mem_right _ _ (map_pow_anti (by omega) (gen_mem g h t))
    have := add_mem (map_pow_anti (by omega) h1) h2
    rw [sub_add_cancel, H_mem_iff g h] at this
    omega
  · rfl

/-- `t < 6m`, `k ≥ 2`. -/
theorem pf_gt2 {t k m : ℕ} (ht : 1 ≤ t) (hk : 2 ≤ k) (hmt : t < 6 * m) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ m) ^ 6) = 0 := by
  rw [pf_eq_sum g h]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  split_ifs with hc
  · by_cases hq : quotLift d ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
    · rw [sext_zero_of_mem h hq, zero_pow (by omega), zero_mul]
    obtain ⟨r, hr, hrj⟩ := exists_arg g h k _ hc
    rw [hr, gsat_eq_zero g h ht r, mul_zero]
    intro hr1
    have h1 := (hrj (t - 1)).1 hr1
    have hH : g.gen (v.asIdeal ^ m) ^ 6 ∈ (v.asIdeal ^ (t + 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      (H_mem_iff g h m _).2 (by omega)
    have := sub_mem hH (map_pow_anti (by omega) h1)
    rw [sub_sub_cancel, mul_mem_iff h (val_gen g h t)] at this
    exact hq (mem_one' h this)
  · rfl

section fin

variable {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include hω

open Classical in
/-- `G_t(r) = Q^t [r ∈ P^t] − Q^(t−1) [r ∈ P^(t−1)]` for `6 ∣ t`. -/
theorem G6 {t : ℕ} (ht : 1 ≤ t) (h6 : 6 ∣ t) (r : SInt 𝔪) :
    gaussSumAt g (v.asIdeal ^ t) (r : F) =
      (if r ∈ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        (Ideal.absNorm v.asIdeal : ℂ) ^ t else 0) -
      (if r ∈ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) else 0) := by
  have hQt : (Ideal.absNorm v.asIdeal : ℂ) ^ t =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) * (Ideal.absNorm v.asIdeal : ℂ) := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  by_cases hr : r ∈ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [gsat_eq_fibre g h ht r hr]
    obtain ⟨c, hrc, hc⟩ := exists_c g h ht r hr
    rw [lsum_eq g h hω (by omega) r c hrc, ram_sum g h hω h6, if_pos hr]
    by_cases hrt : r ∈ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪))
    · rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 (hc.2 hrt)), if_pos hrt, hQt]; ring
    · rw [if_neg (fun h0 => hrt (hc.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0))), if_neg hrt]; ring
  · rw [gsat_eq_zero g h ht r hr, if_neg hr,
      if_neg (fun h' => hr (map_pow_anti (by omega) h'))]
    ring

/-- `k = 0`, `t ≥ 1`. -/
theorem pf_k0_val {t : ℕ} (ht : 1 ≤ t) (m : ℕ) :
    poissonFactor g (v.asIdeal ^ 0) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ m) ^ 6) =
      if 6 ∣ t then
        (if t ≤ 6 * m then (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) *
          ((Ideal.absNorm v.asIdeal : ℂ) - 1) else 0)
      else if 6 * m + 1 = t then
        (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) * gaussSum (chi ι h hω) (psi g h)
      else 0 := by
  classical
  rw [pf_k0 g h]
  set H := g.gen (v.asIdeal ^ m) ^ 6
  have hQt : (Ideal.absNorm v.asIdeal : ℂ) ^ t =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) * (Ideal.absNorm v.asIdeal : ℂ) := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  by_cases h6 : 6 ∣ t
  · rw [if_pos h6, G6 g h hω ht h6, H_mem_iff g h, H_mem_iff g h]
    obtain ⟨s, rfl⟩ := h6
    by_cases hsm : 6 * s ≤ 6 * m
    · rw [if_pos hsm, if_pos hsm, if_pos (by omega), hQt]; ring
    · rw [if_neg hsm, if_neg hsm, if_neg (by omega)]; ring
  rw [if_neg h6]
  by_cases hH1 : H ∈ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))
  · have hH1' := (H_mem_iff g h m _).1 hH1
    rw [gsat_eq_fibre g h ht H hH1]
    obtain ⟨c, hrc, hc⟩ := exists_c g h ht H hH1
    rw [lsum_eq g h hω (by omega) H c hrc]
    by_cases hHt : H ∈ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪))
    · have hHt' := (H_mem_iff g h m _).1 hHt
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (hc.2 hHt), gauss_zero_shift g h hω h6, mul_zero,
        if_neg (by omega)]
    · have hHt' : ¬ t ≤ 6 * m := fun h' => hHt ((H_mem_iff g h m _).2 h')
      have htm : 6 * m + 1 = t := by omega
      rw [if_pos htm]
      have hne : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) c ≠ 0 :=
        fun h0 => hHt (hc.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0))
      rw [gauss_shift g h hω hne, chi_pow_mod h hω t,
        show t % 6 = 1 by omega, pow_one]
      -- `c` is a sixth power of a unit
      have hA : SixEq 𝔪 (g.gen (v.asIdeal ^ t)) (H * g.gen v.asIdeal) := by
        have h1 := gen_pow_add g h (m * 6) 1
        rw [pow_one, show m * 6 + 1 = t by omega] at h1
        exact h1.trans ((gen_pow_mul g h m 6).mul (SixEq.refl (𝔪 := 𝔪) _))
      obtain ⟨ν, hν⟩ := hA
      have hH0 : (H : F) ≠ 0 := by
        rw [Subalgebra.coe_pow]
        exact pow_ne_zero _ (C3B.gen_ne_zero g _ (ext_pow h m))
      have hπ0 : (g.gen v.asIdeal : F) ≠ 0 := C3B.gen_ne_zero g _ h.ext
      have hcν : (c : F) * ((ν : SInt 𝔪) : F) ^ 6 = 1 := by
        rw [div_eq_div_iff (C3B.gen_ne_zero g _ (ext_pow h t)) hπ0, hν] at hrc
        simp only [Subalgebra.coe_mul, Subalgebra.coe_pow] at hrc
        apply mul_left_cancel₀ (mul_ne_zero hH0 hπ0)
        linear_combination -hrc
      have hcR : c = ((ν⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 := by
        apply Subtype.ext
        have hμμ := C3B.coe_unit_pow_mul_inv ν
        rw [Subalgebra.coe_pow]
        linear_combination (((ν⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) ^ 6 * hcν - (c : F) * hμμ
      have hχc : chi ι h hω (Ideal.Quotient.mk _ c) = 1 := by
        have hne' : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
            ((ν⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ≠ 0 := fun h0 =>
          unit_not_mem h ν⁻¹ (Ideal.Quotient.eq_zero_iff_mem.1 h0)
        rw [hcR, map_pow, map_pow]
        exact chi_pow_six_apply h hω hne'
      rw [hχc, inv_one, one_mul]
  · have hH1' : ¬ t - 1 ≤ 6 * m := fun h' => hH1 ((H_mem_iff g h m _).2 h')
    rw [gsat_eq_zero g h ht H hH1, if_neg (by omega)]

omit hω in
lemma A_eq_H (m : ℕ) : ∃ μ : (SInt 𝔪)ˣ,
    g.gen (v.asIdeal ^ (6 * m)) = (μ : SInt 𝔪) ^ 6 * g.gen (v.asIdeal ^ m) ^ 6 := by
  have := gen_pow_mul g h m 6
  rw [mul_comm m 6] at this
  exact this

omit h hω in
lemma mem_zero_pow (x : SInt 𝔪) : x ∈ (v.asIdeal ^ 0).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; exact Submodule.mem_top

omit hω in
lemma Hy_mem_iff (m i : ℕ) (y : SInt 𝔪) (j : ℕ) (hj : j = 6 * m + i) :
    g.gen (v.asIdeal ^ m) ^ 6 * y ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      y ∈ (v.asIdeal ^ i).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  subst hj; exact mul_mem_iff h (val_H g h m) i y

/-- `t = 6m`, `k = 1`. -/
theorem pf_eq1 {m : ℕ} (hm : 1 ≤ m) :
    poissonFactor g (v.asIdeal ^ 1) (v.asIdeal ^ (6 * m)) (g.gen (v.asIdeal ^ m) ^ 6) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (6 * m) := by
  classical
  haveI := finite_L h
  have hfin1 := finite_quot (𝔪 := 𝔪) h.notS 1
  have ht : 1 ≤ 6 * m := by omega
  have h6 : 6 ∣ 6 * m := ⟨m, rfl⟩
  obtain ⟨μ, hμ⟩ := A_eq_H g h m
  set H := g.gen (v.asIdeal ^ m) ^ 6
  set A := g.gen (v.asIdeal ^ (6 * m))
  set Q := (Ideal.absNorm v.asIdeal : ℂ)
  rw [pf_eq_sum g h]
  have hterm : ∀ q : SInt 𝔪,
      (if H - A * q ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        sexticResidueSymbol ι 𝔪 v.asIdeal q ^ 1 *
          gaussSumAt g (v.asIdeal ^ (6 * m)) (((H - A * q : SInt 𝔪) : F) / (g.gen (v.asIdeal ^ 1) : F))
        else 0) =
      (if 1 - (μ : SInt 𝔪) ^ 6 * q ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        sexticResidueSymbol ι 𝔪 v.asIdeal q * Q ^ (6 * m) else 0) -
        sexticResidueSymbol ι 𝔪 v.asIdeal q * Q ^ (6 * m - 1) := by
    intro q
    have hHAq : H - A * q = H * (1 - (μ : SInt 𝔪) ^ 6 * q) := by rw [hμ]; ring
    have hc : H - A * q ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [hHAq]
      exact map_pow_anti (by omega) ((Hy_mem_iff g h m 0 _ (6 * m) (by omega)).2 (mem_zero_pow _))
    rw [if_pos hc]
    obtain ⟨r, hr, hrj⟩ := exists_arg g h 1 _ hc
    rw [hr, G6 g h hω ht h6 r, pow_one, hrj, hrj, hHAq, Hy_mem_iff g h m 1 _ _ (by omega),
      Hy_mem_iff g h m 0 _ _ (by omega), if_pos (mem_zero_pow _)]
    split_ifs <;> ring
  rw [finsum_congr fun d => hterm (quotLift d), finsum_sub_distrib (Set.toFinite _)
    (Set.toFinite _)]
  rw [finsum_unique (μ ^ 6) 1 (fun q => sexticResidueSymbol ι 𝔪 v.asIdeal q * Q ^ (6 * m))
    (fun x y hxy => by rw [sext_congr h (mem_one' h hxy)])
    (fun q => 1 - (μ : SInt 𝔪) ^ 6 * q ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)))
    (fun x => by rw [Units.val_pow_eq_pow_val])]
  have hs : ∑ᶠ d : SInt 𝔪 ⧸ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)),
      sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift d) * Q ^ (6 * m - 1) = 0 := by
    rw [← finsum_mul, finsum_quot_congr (by rw [pow_one]) (fun q =>
      sexticResidueSymbol ι 𝔪 v.asIdeal q), finsum_eq_sum_of_fintype]
    simp_rw [chi_mk_quotLift h hω]
    have hχ : chi ι h hω ≠ 1 := by
      have := chi_pow_ne_one (ι := ι) h hω (j := 1) (by norm_num); rwa [pow_one] at this
    rw [MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]
  rw [hs, sub_zero, mul_one, ← inv_pow, Units.val_pow_eq_pow_val, sext_unit_six h hω, one_mul]

/-- `t = 6m`, `k ≥ 2`. -/
theorem pf_eq2 {m k : ℕ} (hm : 1 ≤ m) (hk : 2 ≤ k) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ (6 * m)) (g.gen (v.asIdeal ^ m) ^ 6) = 0 := by
  classical
  have hfk := finite_quot (𝔪 := 𝔪) h.notS k
  have hfk1 := finite_quot (𝔪 := 𝔪) h.notS (k - 1)
  have ht : 1 ≤ 6 * m := by omega
  have h6 : 6 ∣ 6 * m := ⟨m, rfl⟩
  obtain ⟨μ, hμ⟩ := A_eq_H g h m
  set H := g.gen (v.asIdeal ^ m) ^ 6
  set A := g.gen (v.asIdeal ^ (6 * m))
  set Q := (Ideal.absNorm v.asIdeal : ℂ)
  rw [pf_eq_sum g h]
  have hterm : ∀ q : SInt 𝔪,
      (if H - A * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k *
          gaussSumAt g (v.asIdeal ^ (6 * m))
            (((H - A * q : SInt 𝔪) : F) / (g.gen (v.asIdeal ^ k) : F))
        else 0) =
      (if 1 - (μ : SInt 𝔪) ^ 6 * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k * Q ^ (6 * m) else 0) -
      (if 1 - (μ : SInt 𝔪) ^ 6 * q ∈ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k * Q ^ (6 * m - 1) else 0) := by
    intro q
    have hHAq : H - A * q = H * (1 - (μ : SInt 𝔪) ^ 6 * q) := by rw [hμ]; ring
    by_cases hc : H - A * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪))
    · rw [if_pos hc]
      obtain ⟨r, hr, hrj⟩ := exists_arg g h k _ hc
      rw [hr, G6 g h hω ht h6 r, hrj, hrj, hHAq, Hy_mem_iff g h m k _ _ (by omega),
        Hy_mem_iff g h m (k - 1) _ _ (by omega)]
      split_ifs <;> ring
    · rw [if_neg hc]
      have h1 : 1 - (μ : SInt 𝔪) ^ 6 * q ∉ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        intro hy
        apply hc
        rw [hHAq]
        exact map_pow_anti (by omega) ((Hy_mem_iff g h m (k - 1) _ (6 * m + (k - 1)) rfl).2 hy)
      rw [if_neg h1, if_neg (fun hy => h1 (map_pow_anti (by omega) hy))]
      ring
  rw [finsum_congr fun d => hterm (quotLift d), finsum_sub_distrib (Set.toFinite _)
    (Set.toFinite _)]
  have hk1 : (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := map_pow_anti (𝔪 := 𝔪) (v := v) (a := 1) (b := k - 1) (by omega); rwa [pow_one] at this
  have hkk : (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
      v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    le_trans (map_pow_anti (by omega)) hk1
  rw [finsum_unique (μ ^ 6) 1 (fun q => sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k * Q ^ (6 * m))
    (fun x y hxy => by rw [sext_congr h (hkk hxy)])
    (fun q => 1 - (μ : SInt 𝔪) ^ 6 * q ∈ (v.asIdeal ^ k).map (algebraMap (𝓞 F) (SInt 𝔪)))
    (fun x => by rw [Units.val_pow_eq_pow_val])]
  rw [finsum_quot_fibre h.notS (i := k - 1) (j := k) (by omega) (fun x =>
    if 1 - (μ : SInt 𝔪) ^ 6 * x ∈ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) then
      sexticResidueSymbol ι 𝔪 v.asIdeal x ^ k * Q ^ (6 * m - 1) else 0)]
  · rw [finsum_unique (μ ^ 6) 1
      (fun q => sexticResidueSymbol ι 𝔪 v.asIdeal q ^ k * Q ^ (6 * m - 1))
      (fun x y hxy => by rw [sext_congr h (hk1 hxy)])
      (fun q => 1 - (μ : SInt 𝔪) ^ 6 * q ∈ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)))
      (fun x => by rw [Units.val_pow_eq_pow_val])]
    rw [mul_one, ← inv_pow, Units.val_pow_eq_pow_val, sext_unit_six h hω, one_pow, one_mul,
      one_mul, show k - (k - 1) = 1 by omega, pow_one, ← pow_succ',
      Nat.sub_add_cancel ht, sub_self]
  · intro x y hxy
    have hcond : (1 - (μ : SInt 𝔪) ^ 6 * x ∈ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
        (1 - (μ : SInt 𝔪) ^ 6 * y ∈ (v.asIdeal ^ (k - 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
      have e : 1 - (μ : SInt 𝔪) ^ 6 * x = (1 - (μ : SInt 𝔪) ^ 6 * y) - (μ : SInt 𝔪) ^ 6 * (x - y) := by
        ring
      rw [e]
      constructor
      · intro hh
        have := add_mem hh (Ideal.mul_mem_left _ ((μ : SInt 𝔪) ^ 6) hxy)
        rwa [sub_add_cancel] at this
      · intro hh
        exact sub_mem hh (Ideal.mul_mem_left _ _ hxy)
    rw [sext_congr h (hk1 hxy)]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hcond.1 h1) h2
    · exact absurd (hcond.2 h2) h1
    · rfl

/-- `∑_a χ^n(a) = [6 ∣ n] (Q − 1)`. -/
lemma sum_chi_pow (n : ℕ) :
    ∑ a, (chi ι h hω ^ n) a =
      if 6 ∣ n then (Ideal.absNorm v.asIdeal : ℂ) - 1 else 0 := by
  classical
  have hcard := card_L h hω
  by_cases h6 : 6 ∣ n
  · rw [if_pos h6, chi_pow_mod h hω, Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_mod_iff (dvd_refl 6)).2 h6)
      (Nat.mod_lt _ (by norm_num)), pow_zero]
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    have e : ∀ a : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
        (1 : MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ) a =
          1 - if a = 0 then 1 else 0 := by
      intro a
      by_cases ha : a = 0
      · rw [if_pos ha, ha, MulChar.map_nonunit _ not_isUnit_zero, sub_self]
      · rw [if_neg ha, sub_zero, MulChar.one_apply (Ne.isUnit ha)]
    rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ (0 : SInt 𝔪 ⧸ _), Finset.sum_const, Finset.card_univ,
      hcard, if_pos (Finset.mem_univ _)]
    simp
  · rw [if_neg h6]
    exact MulChar.sum_eq_zero_of_ne_one (chi_pow_ne_one h hω h6)

/-- `t < 6m`, `k = 1`. -/
theorem pf_gt1 {t m : ℕ} (ht : 1 ≤ t) (hmt : t < 6 * m) :
    poissonFactor g (v.asIdeal ^ 1) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ m) ^ 6) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (t - 1) *
        (if 6 ∣ t - 1 then (Ideal.absNorm v.asIdeal : ℂ) - 1 else 0) *
          gaussSum (chi ι h hω) (psi g h) := by
  classical
  have hfin1 := finite_quot (𝔪 := 𝔪) h.notS 1
  set H := g.gen (v.asIdeal ^ m) ^ 6
  set A := g.gen (v.asIdeal ^ t)
  set π := g.gen v.asIdeal
  set Q := (Ideal.absNorm v.asIdeal : ℂ)
  set mk1 := Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [pf_eq_sum g h]
  -- `H = w π A`
  obtain ⟨w, hw⟩ : ∃ w : SInt 𝔪, (H : F) = (w : F) * (π : F) * (A : F) := by
    have hH : H ∈ (v.asIdeal ^ (t + 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      (H_mem_iff g h m _).2 (by omega)
    obtain ⟨z, hz⟩ := (C3B.mem_map_iff g _ (ext_pow h (t + 1)) H).1 hH
    have hadd := gen_pow_add g h t 1
    rw [pow_one] at hadd
    obtain ⟨ν, hν⟩ := hadd
    refine ⟨(ν : SInt 𝔪) ^ 6 * z, ?_⟩
    rw [hz, hν]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    ring
  have hπ0 : (π : F) ≠ 0 := C3B.gen_ne_zero g _ h.ext
  have hA0 : (A : F) ≠ 0 := C3B.gen_ne_zero g _ (ext_pow h t)
  have hterm : ∀ q : SInt 𝔪,
      (if H - A * q ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) then
        sexticResidueSymbol ι 𝔪 v.asIdeal q ^ 1 *
          gaussSumAt g (v.asIdeal ^ t) (((H - A * q : SInt 𝔪) : F) / (g.gen (v.asIdeal ^ 1) : F))
        else 0) =
      sexticResidueSymbol ι 𝔪 v.asIdeal q *
        (Q ^ (t - 1) * ∑ a, (chi ι h hω ^ t) a * psi g h (-mk1 q * a)) := by
    intro q
    have hHt : H ∈ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      (H_mem_iff g h m _).2 (by omega)
    have hAq : A * q ∈ (v.asIdeal ^ t).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.mul_mem_right _ _ (gen_mem g h t)
    have hc : H - A * q ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      map_pow_anti ht (sub_mem hHt hAq)
    rw [if_pos hc, pow_one]
    obtain ⟨r, hr, hrj⟩ := exists_arg g h 1 _ hc
    have hr1 : r ∈ (v.asIdeal ^ (t - 1)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [hrj, show 1 + (t - 1) = t by omega]; exact sub_mem hHt hAq
    rw [hr, gsat_eq_fibre g h ht r hr1]
    set c : SInt 𝔪 := w * π - q
    have hrc : (r : F) / (A : F) = (c : F) / (π : F) := by
      rw [← hr, pow_one, show g.gen v.asIdeal = π from rfl]
      simp only [c, Subalgebra.coe_sub, Subalgebra.coe_mul]
      rw [hw, div_div, div_eq_div_iff (mul_ne_zero hπ0 hA0) hπ0]
      ring
    rw [lsum_eq g h hω (by omega) r c hrc]
    have hmc : mk1 c = -mk1 q := by
      simp only [c, map_sub, map_mul]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by have := gen_mem g h 1; rwa [pow_one] at this :
        π ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))), mul_zero, zero_sub]
    rw [hmc]
  rw [finsum_congr fun d => hterm (quotLift d)]
  rw [finsum_quot_congr (by rw [pow_one]) (fun q => sexticResidueSymbol ι 𝔪 v.asIdeal q *
    (Q ^ (t - 1) * ∑ a, (chi ι h hω ^ t) a * psi g h (-mk1 q * a))), finsum_eq_sum_of_fintype]
  simp_rw [chi_mk_quotLift h hω, mk1, mk_quotLift]
  -- reorganize
  have e1 : ∀ d : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      chi ι h hω d * (Q ^ (t - 1) * ∑ a, (chi ι h hω ^ t) a * psi g h (-d * a)) =
        Q ^ (t - 1) * ∑ a, (chi ι h hω ^ t) a * (chi ι h hω d * psi g h (-a * d)) := by
    intro d
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show -a * d = -d * a by ring]; ring
  rw [Finset.sum_congr rfl (fun d _ => e1 d), ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  -- the inner Gauss sums
  have e2 : ∀ a : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      (chi ι h hω ^ t) a * ∑ d, chi ι h hω d * psi g h (-a * d) =
        (chi ι h hω ^ (t - 1)) a * gaussSum (chi ι h hω) (psi g h) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      haveI := isMaximal_v h
      letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
      rw [MulChar.map_nonunit _ not_isUnit_zero, MulChar.map_nonunit _ not_isUnit_zero, zero_mul,
        zero_mul]
    have hna : -a ≠ 0 := neg_ne_zero.2 ha
    have hgs := gauss_shift g h hω (t := 1) hna
    rw [pow_one] at hgs
    rw [hgs]
    have hneg : chi ι h hω (-a) = chi ι h hω a := by
      rw [show -a = -1 * a by ring, map_mul, chi_neg_one h hω, one_mul]
    have hca : chi ι h hω a ≠ 0 := by
      intro h0
      have := chi_pow_six_apply (ι := ι) h hω ha
      rw [h0] at this; norm_num at this
    rw [hneg, MulChar.pow_apply' _ (by omega)]
    rcases Nat.eq_zero_or_pos (t - 1) with h0 | hpos
    · have ht1 : t = 1 := by omega
      subst ht1
      rw [h0, pow_zero]
      haveI := isMaximal_v h
      letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
      rw [MulChar.one_apply (Ne.isUnit ha), pow_one, ← mul_assoc, mul_inv_cancel₀ hca]
    · rw [MulChar.pow_apply' _ hpos.ne', ← mul_assoc]
      congr 1
      rw [show t = (t - 1) + 1 by omega, pow_succ, mul_assoc, mul_inv_cancel₀ hca, mul_one]
      rfl
  simp_rw [e2, ← Finset.sum_mul, sum_chi_pow h hω]
  ring

lemma sqrt_mul_gaussPhase_one :
    (Real.sqrt (Ideal.absNorm v.asIdeal) : ℂ) * gaussPhase g 1 v.asIdeal =
      gaussSum (chi ι h hω) (psi g h) := by
  rw [gaussPhase_eq h hω g (j := 1) (by norm_num), pow_one, ← mul_assoc]
  have hs := sqrt_sq_C (v := v)
  have hQ : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (absNorm_pos v).ne'
  have hs0 : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ≠ 0 := by
    intro h0; rw [h0] at hs; exact hQ (by rw [← hs]; ring)
  rw [mul_inv_cancel₀ hs0, one_mul]

/-- The value of `F(P^k, P^t, gen(P^m)⁶)`. -/
noncomputable def pfVal' (Q G : ℂ) (t k m : ℕ) : ℂ :=
  if t = 0 then (if k = 0 ∨ m = 0 then 1 else 0)
  else if k = 0 then
    (if 6 ∣ t then (if t ≤ 6 * m then Q ^ (t - 1) * (Q - 1) else 0)
     else if 6 * m + 1 = t then Q ^ (t - 1) * G else 0)
  else if m = 0 then 0
  else if 6 * m < t then 0
  else if 6 * m = t then (if k = 1 then Q ^ t else 0)
  else if k = 1 then Q ^ (t - 1) * (if 6 ∣ t - 1 then Q - 1 else 0) * G else 0

/-- `F(P^k, P^t, gen(P^m)⁶)` at a good prime. -/
theorem pf_eval (t k m : ℕ) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ t) (g.gen (v.asIdeal ^ m) ^ 6) =
      pfVal' (Ideal.absNorm v.asIdeal : ℂ) (gaussSum (chi ι h hω) (psi g h)) t k m := by
  unfold pfVal'
  by_cases ht0 : t = 0
  · subst ht0
    rw [if_pos rfl]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pf_k0 g h, gsat_top' g h, if_pos (Or.inl rfl)]
    · rw [pf_t0 g h hω hk m]
      by_cases hm : m = 0
      · rw [if_pos hm, if_pos (Or.inr hm)]
      · rw [if_neg hm, if_neg (by omega)]
  rw [if_neg ht0]
  have ht : 1 ≤ t := by omega
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl, pf_k0_val g h hω ht m]
  rw [if_neg hk0]
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_pos rfl, pf_m0 g h ht (by omega)]
  rw [if_neg hm0]
  by_cases hlt : 6 * m < t
  · rw [if_pos hlt, pf_lt g h ht (by omega) hlt]
  rw [if_neg hlt]
  by_cases heq : 6 * m = t
  · rw [if_pos heq, ← heq]
    by_cases hk1 : k = 1
    · subst hk1
      rw [if_pos rfl, pf_eq1 g h hω (by omega)]
    · rw [if_neg hk1, pf_eq2 g h hω (by omega) (by omega)]
  rw [if_neg heq]
  have hgt : t < 6 * m := by omega
  by_cases hk1 : k = 1
  · subst hk1
    rw [if_pos rfl, pf_gt1 g h hω ht hgt]
  · rw [if_neg hk1, pf_gt2 g h ht (by omega) hgt]

omit h hω in
lemma pfVal'_eq (Qn : ℕ) (hQ : (Qn : ℂ) ≠ 0) (γ : ℂ) (e₀ l k m : ℕ) (he : e₀ ≤ 1) :
    pfVal' (Qn : ℂ) ((Real.sqrt Qn : ℂ) * γ) (e₀ + 3 * l) k m = poissonLocal Qn γ e₀ l k m := by
  have hpow : ∀ n : ℕ, 1 ≤ n → (Qn : ℂ) ^ n = (Qn : ℂ) ^ (n - 1) * Qn := by
    intro n hn; rw [← pow_succ, Nat.sub_add_cancel hn]
  unfold pfVal' poissonLocal
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · simp only [Nat.even_iff, zero_add, if_true]
    split_ifs <;> first | rfl | (exfalso; omega) | skip
    · rw [hpow (3 * l) (by omega)]; field_simp
    · ring
    · ring
  · simp only [Nat.even_iff, one_ne_zero, if_false, true_and]
    split_ifs <;> first | rfl | (exfalso; omega) | skip
    · rw [show 1 + 3 * l - 1 = 3 * l by omega]; ring
    · rw [show 1 + 3 * l - 1 = 3 * l by omega]; ring
    · ring

/-- **The local Poisson table** (7.15), (7.17) at a good prime. -/
theorem pf_table (e₀ l k m : ℕ) (he : e₀ ≤ 1) :
    poissonFactor g (v.asIdeal ^ k) (v.asIdeal ^ e₀ * (v.asIdeal ^ l) ^ 3)
        (g.gen (v.asIdeal ^ m) ^ 6) =
      poissonLocal (Ideal.absNorm v.asIdeal) (gaussPhase g 1 v.asIdeal) e₀ l k m := by
  have hQ : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (absNorm_pos v).ne'
  rw [← pow_mul, ← pow_add, show e₀ + l * 3 = e₀ + 3 * l by ring, pf_eval g h hω,
    ← sqrt_mul_gaussPhase_one g h hω, pfVal'_eq _ hQ _ e₀ l k m he]

end fin

end main

end C3I

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

end C3B

end ArtinPrimitiveRoots
end

section
/-! # C3I_Cut: the cutoff — exterior primes of `ℚ(μ_n)`, `12 ∣ n`, are good

`N₀ = max(3^[F:ℚ], N 𝔇)`: an exterior prime has norm `> N₀`, so it lies over neither `2` nor `3`
(`12 ∣ N P − 1`) and does not divide the different. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F] (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hQ1 : Q ≠ 1 := by
    have : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk hQ1 hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- A primitive sixth root of unity in `𝓞 F`. -/
theorem exists_prim_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] :
    ∃ ω : 𝓞 F, IsPrimitiveRoot ω 6 := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  exact ⟨hζ6.toInteger, hζ6.toInteger_isPrimitiveRoot⟩

/-- The cutoff. -/
noncomputable def cutN (F : Type*) [Field F] [NumberField F] : ℕ :=
  max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))

/-- Exterior primes are good once `N₀ ≥ cutN F`. -/
theorem good_of_exterior (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : cutN F ≤ N₀) {𝔪 : Ideal (𝓞 F)} (hsm : SmallPrimesDvd N₀ 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hext : IsExterior 𝔪 P) :
    Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)) := by
  have hbig : N₀ < Ideal.absNorm P := by
    by_contra hcon
    apply hP.ne_top
    rw [eq_top_iff, ← hext.2]
    exact sup_le le_rfl (hsm P hP hext.1 (by omega))
  have h1 : 3 ^ Module.finrank ℤ (𝓞 F) ≤ cutN F := le_max_left _ _
  have h2 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≤ cutN F := le_max_right _ _
  refine ⟨hext.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hext.1 (by omega), ?_⟩
  intro hD
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hD
  have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
  change Ideal.absNorm P ≤ _ at this
  omega

end C3I

open NumberField

end ArtinPrimitiveRoots

end

section
/-! # C3I_CutF: the cut `exists_cutoff_poissonFactor_prime_pow_eq_poissonLocal` -/

set_option linter.style.haveILetI false

namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots

end

section
set_option linter.style.haveILetI false
open ArtinPrimitiveRoots
open NumberField
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
        poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (g.gen (P ^ m) ^ 6) =
          poissonLocal (Ideal.absNorm P) (gaussPhase g 1 P) e₀ l k m := by
  refine ⟨C3I.cutN F, fun 𝔪 _ hsm g P hP hext e₀ l k m he => ?_⟩
  have h := C3I.good_of_exterior n hn0 hn le_rfl hsm hP hext
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six (F := F) n hn0 hn
  haveI := C3I.finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)))
  exact C3I.pf_table g h hω e₀ l k m he
end
