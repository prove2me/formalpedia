-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_additiveFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T21:08:27.296987+00:00
-- url     : https://prove2.me/submissions/6ff241b6-4762-45bb-ae33-925eadda8b98

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

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

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

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

lemma hasWit_neg {x : F} (h : HasWit 𝔪 x) : HasWit 𝔪 (-x) := by
  obtain ⟨y, hy1, hy2⟩ := h
  refine ⟨-y, by rw [show -x - -y = -(x - y) by ring]; exact neg_mem hy1, fun v hv => ?_⟩
  rw [Valuation.map_neg]; exact hy2 v hv

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

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

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

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

end roots

section chi

variable {ι : F →+* ℂ}

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

/-! ### Characters on the finite field `L` -/

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

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

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

end field

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
/-!
# L2A_FSLS: the large sieve on `ℤ^d` for sup-norm separated points

`Σ_{n ∈ [0,H)^d} |Σ_j b_j e(n·θ_j)|² ≤ C_d H^d Σ |b_j|²` for points `θ_j ∈ ℝ^d` that are
`δ`-separated modulo `ℤ^d` in the sup norm, when `1 ≤ δ H`. Proof by the Fejér square kernel
(`Σ_{a,c ∈ [0,2H)^d} |S(a − c)|²`), no Poisson summation.
-/

namespace ArtinPrimitiveRoots.L2A

open Complex Finset

/-- `e(x) = exp(2πi x)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_int (k : ℤ) : ee k = 1 := by
  unfold ee
  have : (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = k * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma conj_ee (x : ℝ) : starRingEnd ℂ (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; push_cast; ring

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum]

/-- `‖e(z) − 1‖ ≥ 4|z|` for `|z| ≤ 1/2`. -/
lemma four_abs_le_norm_ee_sub_one {z : ℝ} (hz : |z| ≤ 1 / 2) : 4 * |z| ≤ ‖ee z - 1‖ := by
  unfold ee
  have : (2 * Real.pi * Complex.I * (z : ℂ)) = Complex.I * ((2 * Real.pi * z : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hpi := Real.pi_pos
  rw [show 2 * Real.pi * z / 2 = Real.pi * z by ring, abs_mul, abs_two]
  -- |sin(π z)| ≥ 2|z|
  have key : 2 * |z| ≤ |Real.sin (Real.pi * z)| := by
    rcases le_total 0 z with h | h
    · have h1 : Real.pi * z ≤ Real.pi / 2 := by
        rw [abs_of_nonneg h] at hz; nlinarith
      have := Real.mul_le_sin (by positivity) h1
      rw [abs_of_nonneg h, abs_of_nonneg (le_trans (by positivity) this)]
      calc 2 * z = 2 / Real.pi * (Real.pi * z) := by field_simp
        _ ≤ _ := this
    · have h1 : Real.pi * (-z) ≤ Real.pi / 2 := by
        rw [abs_of_nonpos h] at hz; nlinarith
      have := Real.mul_le_sin (by nlinarith) h1
      rw [abs_of_nonpos h, show Real.pi * z = -(Real.pi * -z) by ring, Real.sin_neg, abs_neg,
        abs_of_nonneg (le_trans (mul_nonneg (by positivity) (by nlinarith)) this)]
      calc 2 * -z = 2 / Real.pi * (Real.pi * -z) := by field_simp
        _ ≤ _ := this
  linarith

/-- The geometric sum `g_K(y) = Σ_{t<K} e(t y)`. -/
noncomputable def geomE (K : ℕ) (y : ℝ) : ℂ := ∑ t ∈ range K, ee (t * y)

lemma norm_geomE_le (K : ℕ) (y : ℝ) : ‖geomE K y‖ ≤ K := by
  unfold geomE
  calc ‖∑ t ∈ range K, ee (t * y)‖ ≤ ∑ t ∈ range K, ‖ee (t * y)‖ := norm_sum_le _ _
    _ = K := by simp [norm_ee]

lemma geomE_mul (K : ℕ) (y : ℝ) : geomE K y * (ee y - 1) = ee (K * y) - 1 := by
  unfold geomE
  have : ∀ t : ℕ, ee (t * y) = ee y ^ t := by
    intro t; induction t with
    | zero => simp [ee]
    | succ t ih => rw [pow_succ, ← ih, ← ee_add]; congr 1; push_cast; ring
  simp_rw [this]; rw [geom_sum_mul]

lemma norm_geomE_mul_abs_le (K : ℕ) {y : ℝ} (k : ℤ) (hz : |y - k| ≤ 1 / 2) :
    ‖geomE K y‖ * (4 * |y - k|) ≤ 2 := by
  have h1 : ee (y - k) = ee y := by
    rw [sub_eq_add_neg, ee_add, ← Int.cast_neg, ee_int, mul_one]
  have h2 := four_abs_le_norm_ee_sub_one hz
  rw [h1] at h2
  calc ‖geomE K y‖ * (4 * |y - k|) ≤ ‖geomE K y‖ * ‖ee y - 1‖ :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖ee (K * y) - 1‖ := by rw [← norm_mul, geomE_mul]
    _ ≤ ‖ee (K * y)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_ee, norm_one]; norm_num

/-- `‖g_{2H}(y)‖² (1 + 4 H² z²) ≤ 5 H²` for `z = y − k`, `|z| ≤ 1/2`. -/
lemma norm_geomE_sq_mul_le (H : ℕ) {y : ℝ} (k : ℤ) (hz : |y - k| ≤ 1 / 2) :
    ‖geomE (2 * H) y‖ ^ 2 * (1 + 4 * H ^ 2 * (y - k) ^ 2) ≤ 8 * H ^ 2 := by
  have a := norm_geomE_le (2 * H) y
  have b := norm_geomE_mul_abs_le (2 * H) k hz
  have hn := norm_nonneg (geomE (2 * H) y)
  have hab : ‖geomE (2 * H) y‖ * |y - k| ≤ 1 / 2 := by linarith
  have h2 : (‖geomE (2 * H) y‖ * |y - k|) ^ 2 ≤ 1 / 4 := by
    have := mul_nonneg hn (abs_nonneg (y - k))
    nlinarith
  push_cast at a
  have : ‖geomE (2 * H) y‖ ^ 2 ≤ 4 * H ^ 2 := by nlinarith
  have hsq : (y - k) ^ 2 = |y - k| ^ 2 := (sq_abs _).symm
  rw [hsq]
  nlinarith [sq_nonneg (H : ℝ)]

variable {d : ℕ} {ι : Type*}

/-- The box `[0,K)^d` in `ℤ^d`. -/
noncomputable def boxZ (d K : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Ico (0 : ℤ) K

/-- The trigonometric polynomial `S(n) = Σ_j b_j e(n·θ_j)`. -/
noncomputable def trigS {ι : Type*} (J : Finset ι) (b : ι → ℂ) (θ : ι → Fin d → ℝ)
    (n : Fin d → ℤ) : ℂ :=
  ∑ j ∈ J, b j * ee (∑ i, (n i : ℝ) * θ j i)

/-- `Σ_{a ∈ [0,K)^d} e(a·x) = ∏_i g_K(x_i)`. -/
lemma sum_boxZ_ee (K : ℕ) (x : Fin d → ℝ) :
    ∑ a ∈ boxZ d K, ee (∑ i, (a i : ℝ) * x i) = ∏ i, geomE K (x i) := by
  unfold boxZ geomE
  have : ∀ i : Fin d, ∑ t ∈ range K, ee (t * x i) = ∑ t ∈ Ico (0 : ℤ) K, ee (t * x i) := by
    intro i
    have hm : (range K).map Nat.castEmbedding = Ico (0 : ℤ) K := by
      ext t; simp only [mem_map, mem_range, Nat.castEmbedding_apply, mem_Ico]
      constructor
      · rintro ⟨a, ha, rfl⟩; omega
      · rintro ⟨h1, h2⟩; exact ⟨t.toNat, by omega, by omega⟩
    rw [← hm, Finset.sum_map]; rfl
  simp_rw [this]
  rw [Finset.prod_univ_sum]
  simp_rw [ee_sum]

lemma norm_sq_trigS (J : Finset ι) (b : ι → ℂ) (θ : ι → Fin d → ℝ) (n : Fin d → ℤ) :
    ((‖trigS J b θ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ J, ∑ j' ∈ J, b j * starRingEnd ℂ (b j') *
        ee (∑ i, (n i : ℝ) * (θ j i - θ j' i)) := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hz, trigS, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [map_mul, conj_ee]
  have : ee (∑ i, (n i : ℝ) * (θ j i - θ j' i)) =
      ee (∑ i, (n i : ℝ) * θ j i) * ee (-∑ i, (n i : ℝ) * θ j' i) := by
    rw [← ee_add]; congr 1; rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [this]; ring

/-- The Fejér square identity: `Σ_{a,c ∈ [0,K)^d} |S(a − c)|² = Σ_{j,j'} b_j b̄_{j'} |G(θ_j − θ_{j'})|²`. -/
lemma sum_sum_norm_sq_trigS (K : ℕ) (J : Finset ι) (b : ι → ℂ) (θ : ι → Fin d → ℝ) :
    ((∑ a ∈ boxZ d K, ∑ c ∈ boxZ d K, ‖trigS J b θ (a - c)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ J, ∑ j' ∈ J, b j * starRingEnd ℂ (b j') *
        ((∏ i, ‖geomE K (θ j i - θ j' i)‖ ^ 2 : ℝ) : ℂ) := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [Complex.ofReal_sum, norm_sq_trigS]
  -- reorder the four sums
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  simp_rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
    (Finset.sum_comm (s := boxZ d K) (t := J))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp_rw [← Finset.mul_sum]
  congr 1
  set x : Fin d → ℝ := fun i => θ j i - θ j' i
  have hsplit : ∀ a c : Fin d → ℤ, ee (∑ i, (((a - c) i : ℤ) : ℝ) * (θ j i - θ j' i)) =
      ee (∑ i, (a i : ℝ) * x i) * starRingEnd ℂ (ee (∑ i, (c i : ℝ) * x i)) := by
    intro a c
    rw [conj_ee, ← ee_add]; congr 1
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Int.cast_sub, x]; ring
  simp_rw [hsplit, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul, sum_boxZ_ee]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, ← Finset.prod_pow]

/-- The shifted-box lower bound: `K^d Σ_{n ∈ [0,K)^d} |S(n)|² ≤ Σ_{a,c ∈ [0,2K)^d} |S(a − c)|²`. -/
lemma pow_mul_sum_le (K : ℕ) (f : (Fin d → ℤ) → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (K : ℝ) ^ d * ∑ n ∈ boxZ d K, f n ≤
      ∑ a ∈ boxZ d (2 * K), ∑ c ∈ boxZ d (2 * K), f (a - c) := by
  have hcard : (boxZ d K).card = K ^ d := by
    simp [boxZ, Fintype.card_piFinset, Int.card_Ico]
  have h1 : (K : ℝ) ^ d * ∑ n ∈ boxZ d K, f n = ∑ c ∈ boxZ d K, ∑ n ∈ boxZ d K, f n := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  rw [h1, Finset.sum_comm (s := boxZ d (2 * K))]
  have hsub : boxZ d K ⊆ boxZ d (2 * K) := by
    intro c hc
    simp only [boxZ, Fintype.mem_piFinset, mem_Ico] at hc ⊢
    intro i; have := hc i; push_cast; omega
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ =>
    Finset.sum_nonneg fun a _ => hf _)
  refine Finset.sum_le_sum fun c hc => ?_
  have hinj : Set.InjOn (fun n : Fin d → ℤ => n + c) (boxZ d K) := fun x _ y _ h => by
    simpa using h
  calc ∑ n ∈ boxZ d K, f n = ∑ n ∈ boxZ d K, f ((n + c) - c) := by simp
    _ = ∑ a ∈ (boxZ d K).image (fun n => n + c), f (a - c) :=
        (Finset.sum_image (f := fun a => f (a - c)) hinj).symm
    _ ≤ ∑ a ∈ boxZ d (2 * K), f (a - c) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hf _
      intro a ha
      simp only [mem_image] at ha
      obtain ⟨n, hn, rfl⟩ := ha
      simp only [boxZ, Fintype.mem_piFinset, mem_Ico] at hn hc ⊢
      intro i; have := hn i; have := hc i; simp only [Pi.add_apply]; push_cast; omega

/-- The constant `Σ_{k ∈ ℤ} 4/(1 + k²)`. -/
noncomputable def cK : ℝ := ∑' k : ℤ, 4 / (1 + (k : ℝ) ^ 2)

lemma summable_cK : Summable fun k : ℤ => 4 / (1 + (k : ℝ) ^ 2) := by
  have h2 : Summable fun k : ℤ => 1 / (k : ℝ) ^ 2 := Real.summable_one_div_int_pow.2 (by norm_num)
  have h3 : Summable fun k : ℤ => (if k = 0 then (4 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [hk])
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) ((h2.mul_left 4).add h3)
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, if_false, add_zero]
    have : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    calc 4 / (1 + (k : ℝ) ^ 2) ≤ 4 / (k : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) this (by linarith)
      _ = 4 * (1 / (k : ℝ) ^ 2) := by ring

/-- The cell bound: for `|z| ≤ 1/2`, `k = ⌊2z/δ⌋`, `1 ≤ δH`:
`‖g_{2H}(y)‖² ≤ 32 H² /(1 + k²)` where `z = y − r`. -/
lemma norm_geomE_sq_le_cell (H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδH : 1 ≤ δ * H) {y : ℝ} (r : ℤ)
    (hz : |y - r| ≤ 1 / 2) :
    ‖geomE (2 * H) y‖ ^ 2 ≤ 8 * H ^ 2 * (4 / (1 + (⌊2 * (y - r) / δ⌋ : ℝ) ^ 2)) := by
  set z := y - r
  set k := ⌊2 * z / δ⌋
  have main := norm_geomE_sq_mul_le H r hz
  -- (max(|k| − 1, 0))·δ/2 ≤ |z|
  have hk1 : (|(k : ℝ)| - 1) * δ / 2 ≤ |z| := by
    have hf1 := Int.floor_le (2 * z / δ)
    have hf2 := Int.lt_floor_add_one (2 * z / δ)
    rcases le_total 0 (k : ℝ) with h | h
    · rw [abs_of_nonneg h]
      have : (k : ℝ) * δ ≤ 2 * z := by rw [le_div_iff₀ hδ] at hf1; linarith
      have := le_abs_self z; nlinarith
    · rw [abs_of_nonpos h]
      have : 2 * z < ((k : ℝ) + 1) * δ := by rw [div_lt_iff₀ hδ] at hf2; linarith
      have := neg_abs_le z; nlinarith
  have hkey : (1 + (k : ℝ) ^ 2) / 4 ≤ 1 + 4 * H ^ 2 * z ^ 2 := by
    have hk' : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
    rw [hk', show z ^ 2 = |z| ^ 2 from (sq_abs _).symm]
    set t := |(k : ℝ)|
    have ht : 0 ≤ t := abs_nonneg _
    rcases le_or_gt t 1 with h | h
    · nlinarith [sq_nonneg (H * |z|)]
    · -- (t − 1) ≤ 2|z|/δ ≤ 2 H |z|
      have h2 : t - 1 ≤ 2 * H * |z| := by
        have hH : (0 : ℝ) < H := by
          rcases Nat.eq_zero_or_pos H with h0 | h0
          · subst h0; simp at hδH; linarith
          · exact_mod_cast h0
        have : (t - 1) * δ ≤ 2 * |z| := by linarith
        have : (t - 1) * δ * H ≤ 2 * |z| * H := by nlinarith
        nlinarith
      have h3 : (t - 1) ^ 2 ≤ 4 * H ^ 2 * |z| ^ 2 := by
        have : 0 ≤ t - 1 := by linarith
        nlinarith
      nlinarith
  have hpos : 0 < 1 + (k : ℝ) ^ 2 := by positivity
  rw [mul_div_assoc', le_div_iff₀ hpos]
  have hn := sq_nonneg ‖geomE (2 * H) y‖
  nlinarith

lemma geomE_neg (K : ℕ) (y : ℝ) : geomE K (-y) = starRingEnd ℂ (geomE K y) := by
  unfold geomE; rw [map_sum]; refine Finset.sum_congr rfl fun t _ => ?_
  rw [conj_ee]; congr 1; ring

lemma norm_geomE_neg (K : ℕ) (y : ℝ) : ‖geomE K (-y)‖ = ‖geomE K y‖ := by
  rw [geomE_neg, Complex.norm_conj]

/-- The kernel `K(x) = ∏_i ‖g_{2H}(x_i)‖²`. -/
noncomputable def kerF (H : ℕ) (x : Fin d → ℝ) : ℝ := ∏ i, ‖geomE (2 * H) (x i)‖ ^ 2

lemma kerF_nonneg (H : ℕ) (x : Fin d → ℝ) : 0 ≤ kerF H x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

lemma sum_Icc_le_cK (M : ℕ) : ∑ t ∈ Icc (-(M : ℤ)) M, 4 / (1 + (t : ℝ) ^ 2) ≤ cK :=
  summable_cK.sum_le_tsum _ (fun _ _ => by positivity)

lemma cK_nonneg : 0 ≤ cK := tsum_nonneg fun _ => by positivity

/-- The row-sum bound: `Σ_{j'} K(θ_j − θ_{j'}) ≤ (8 H² c_K)^d` for separated points. -/
lemma row_sum_le {ι : Type*} (J : Finset ι) (θ : ι → Fin d → ℝ) (H : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hδH : 1 ≤ δ * H)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ k : Fin d → ℤ, ∃ i, δ ≤ |θ j i - θ j' i - k i|)
    (j : ι) :
    ∑ j' ∈ J, kerF H (fun i => θ j i - θ j' i) ≤ (8 * H ^ 2 * cK) ^ d := by
  classical
  set r : ι → Fin d → ℤ := fun j' i => round (θ j i - θ j' i)
  set z : ι → Fin d → ℝ := fun j' i => θ j i - θ j' i - r j' i
  set k : ι → Fin d → ℤ := fun j' i => ⌊2 * z j' i / δ⌋
  set f : ℤ → ℝ := fun t => 8 * H ^ 2 * (4 / (1 + (t : ℝ) ^ 2))
  have hf0 : ∀ t, 0 ≤ f t := fun t => by positivity
  have hz : ∀ j' i, |z j' i| ≤ 1 / 2 := fun j' i => abs_sub_round _
  have hK : ∀ j', kerF H (fun i => θ j i - θ j' i) ≤ ∏ i, f (k j' i) := by
    intro j'
    refine Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun i _ => ?_
    exact norm_geomE_sq_le_cell H hδ hδH (r j' i) (hz j' i)
  have hHpos : (0 : ℝ) < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · subst h0; simp at hδH; linarith
    · exact_mod_cast h0
  have hinv : 1 / δ ≤ H := by rw [div_le_iff₀ hδ]; linarith
  -- the cells lie in [-(H+1), H+1]^d
  set M : ℕ := H + 1
  have hrange : ∀ j', k j' ∈ Fintype.piFinset fun _ : Fin d => Icc (-(M : ℤ)) M := by
    intro j'
    simp only [Fintype.mem_piFinset, mem_Icc]
    intro i
    have h1 : |2 * z j' i / δ| ≤ H := by
      rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ, abs_mul, abs_two]
      have := hz j' i
      have : 1 ≤ H * δ := by linarith
      nlinarith
    have h2 := abs_le.1 h1
    have hf1 := Int.floor_le (2 * z j' i / δ)
    have hf2 := Int.lt_floor_add_one (2 * z j' i / δ)
    constructor
    · have : (-(M : ℤ) : ℝ) ≤ (k j' i : ℝ) := by
        simp only [M, k]; push_cast; linarith
      exact_mod_cast this
    · have : (k j' i : ℝ) ≤ ((M : ℤ) : ℝ) := by
        simp only [M, k]; push_cast; linarith
      exact_mod_cast this
  -- injectivity of the cell map on J
  have hinj : Set.InjOn k J := by
    intro j' hj' j'' hj'' heq
    by_contra hne
    obtain ⟨i, hi⟩ := hsep j' hj' j'' hj'' hne (r j'' - r j')
    have hfl : ⌊2 * z j' i / δ⌋ = ⌊2 * z j'' i / δ⌋ := congrFun heq i
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    have h2 : |z j' i - z j'' i| < δ / 2 := by
      rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ, ← mul_sub, abs_mul, abs_two] at h1
      linarith
    have h3 : θ j' i - θ j'' i - ((r j'' - r j') i : ℤ) = -(z j' i - z j'' i) := by
      simp only [z, Pi.sub_apply, Int.cast_sub]; ring
    rw [h3, abs_neg] at hi
    linarith
  calc ∑ j' ∈ J, kerF H (fun i => θ j i - θ j' i) ≤ ∑ j' ∈ J, ∏ i, f (k j' i) :=
        Finset.sum_le_sum fun j' _ => hK j'
    _ = ∑ κ ∈ J.image k, ∏ i, f (κ i) :=
        (Finset.sum_image (f := fun κ : Fin d → ℤ => ∏ i, f (κ i)) hinj).symm
    _ ≤ ∑ κ ∈ Fintype.piFinset (fun _ : Fin d => Icc (-(M : ℤ)) M), ∏ i, f (κ i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
          Finset.prod_nonneg fun _ _ => hf0 _
        intro κ hκ; obtain ⟨j', _, rfl⟩ := Finset.mem_image.1 hκ; exact hrange j'
    _ = ∏ _i : Fin d, ∑ t ∈ Icc (-(M : ℤ)) M, f t := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : Fin d, (8 * H ^ 2 * cK) := by
        refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => hf0 _) fun _ _ => ?_
        simp only [f]; rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_Icc_le_cK M) (by positivity)
    _ = (8 * H ^ 2 * cK) ^ d := by simp

/-- **The large sieve on `ℤ^d`.** For points `θ_j` that are `δ`-separated modulo `ℤ^d` in the sup
norm and `1 ≤ δ H`: `Σ_{n ∈ [0,H)^d} |Σ_j b_j e(n·θ_j)|² ≤ (8 c_K)^d H^d Σ_j |b_j|²`. -/
theorem largeSieveZ {ι : Type*} (J : Finset ι) (b : ι → ℂ) (θ : ι → Fin d → ℝ) (H : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδH : 1 ≤ δ * H)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ k : Fin d → ℤ, ∃ i, δ ≤ |θ j i - θ j' i - k i|) :
    ∑ n ∈ boxZ d H, ‖trigS J b θ n‖ ^ 2 ≤ (8 * cK) ^ d * H ^ d * ∑ j ∈ J, ‖b j‖ ^ 2 := by
  have hHpos : (0 : ℝ) < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · subst h0; simp at hδH; linarith
    · exact_mod_cast h0
  set Kj : ι → ι → ℝ := fun j j' => kerF H (fun i => θ j i - θ j' i)
  have hKsymm : ∀ j j', Kj j j' = Kj j' j := by
    intro j j'; simp only [Kj, kerF]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show θ j' i - θ j i = -(θ j i - θ j' i) by ring, norm_geomE_neg]
  have hA := pow_mul_sum_le H (fun n => ‖trigS J b θ n‖ ^ 2) (fun _ => sq_nonneg _)
  have hB : ∑ a ∈ boxZ d (2 * H), ∑ c ∈ boxZ d (2 * H), ‖trigS J b θ (a - c)‖ ^ 2 ≤
      ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * Kj j j' := by
    set L := ∑ a ∈ boxZ d (2 * H), ∑ c ∈ boxZ d (2 * H), ‖trigS J b θ (a - c)‖ ^ 2
    have hid := sum_sum_norm_sq_trigS (2 * H) J b θ
    calc L ≤ |L| := le_abs_self _
      _ = ‖(L : ℂ)‖ := (Complex.norm_real L).symm
      _ = ‖∑ j ∈ J, ∑ j' ∈ J, b j * starRingEnd ℂ (b j') *
            ((∏ i, ‖geomE (2 * H) (θ j i - θ j' i)‖ ^ 2 : ℝ) : ℂ)‖ := by rw [hid]
      _ ≤ ∑ j ∈ J, ‖∑ j' ∈ J, b j * starRingEnd ℂ (b j') *
            ((∏ i, ‖geomE (2 * H) (θ j i - θ j' i)‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, ∑ j' ∈ J, ‖b j * starRingEnd ℂ (b j') *
            ((∏ i, ‖geomE (2 * H) (θ j i - θ j' i)‖ ^ 2 : ℝ) : ℂ)‖ :=
          Finset.sum_le_sum fun _ _ => norm_sum_le _ _
      _ = ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * Kj j j' := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
          have := kerF_nonneg H (fun i => θ j i - θ j' i)
          simp only [kerF] at this
          rw [abs_of_nonneg this]; rfl
  have hC : ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * Kj j j' ≤
      ∑ j ∈ J, ‖b j‖ ^ 2 * ∑ j' ∈ J, Kj j j' := by
    have h1 : ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ * ‖b j'‖ * Kj j j' ≤
        ∑ j ∈ J, ∑ j' ∈ J, ((‖b j‖ ^ 2 + ‖b j'‖ ^ 2) / 2) * Kj j j' := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (kerF_nonneg H _)
      nlinarith [sq_nonneg (‖b j‖ - ‖b j'‖)]
    have h2 : ∑ j ∈ J, ∑ j' ∈ J, ‖b j'‖ ^ 2 * Kj j j' =
        ∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ ^ 2 * Kj j j' := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      rw [hKsymm]
    have h3 : ∑ j ∈ J, ∑ j' ∈ J, ((‖b j‖ ^ 2 + ‖b j'‖ ^ 2) / 2) * Kj j j' =
        (∑ j ∈ J, ∑ j' ∈ J, ‖b j‖ ^ 2 * Kj j j' + ∑ j ∈ J, ∑ j' ∈ J, ‖b j'‖ ^ 2 * Kj j j') / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [h3, h2] at h1
    refine h1.trans (le_of_eq ?_)
    rw [add_self_div_two]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hD : ∑ j ∈ J, ‖b j‖ ^ 2 * ∑ j' ∈ J, Kj j j' ≤
      (8 * H ^ 2 * cK) ^ d * ∑ j ∈ J, ‖b j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (row_sum_le J θ H hδ hδH hsep j) (sq_nonneg _)
  have hfin := hA.trans (hB.trans (hC.trans hD))
  have hHd : (0 : ℝ) < (H : ℝ) ^ d := pow_pos hHpos d
  have : (8 * (H : ℝ) ^ 2 * cK) ^ d = (H : ℝ) ^ d * ((8 * cK) ^ d * H ^ d) := by
    rw [show 8 * (H : ℝ) ^ 2 * cK = H * ((8 * cK) * H) by ring, mul_pow, mul_pow]
  rw [this, mul_assoc] at hfin
  exact le_of_mul_le_mul_left hfin hHd

lemma trigS_add (J : Finset ι) (b : ι → ℂ) (θ : ι → Fin d → ℝ) (n c : Fin d → ℤ) :
    trigS J b θ n = trigS J (fun j => b j * ee (-∑ i, (c i : ℝ) * θ j i)) θ (n + c) := by
  unfold trigS
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, ← ee_add]; congr 2
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add]; ring

/-- **The large sieve on `ℤ^d`, symmetric box form.** For a finite set `A` of lattice points with
`|n_i| ≤ B` and `2B + 1 ≤ H`, `1 ≤ δ H`. -/
theorem largeSieveZ_box {ι : Type*} (J : Finset ι) (b : ι → ℂ) (θ : ι → Fin d → ℝ)
    (A : Finset (Fin d → ℤ)) (B H : ℕ) (hA : ∀ n ∈ A, ∀ i, |n i| ≤ B) (hBH : 2 * B + 1 ≤ H)
    {δ : ℝ} (hδ : 0 < δ) (hδH : 1 ≤ δ * H)
    (hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ k : Fin d → ℤ, ∃ i, δ ≤ |θ j i - θ j' i - k i|) :
    ∑ n ∈ A, ‖trigS J b θ n‖ ^ 2 ≤ (8 * cK) ^ d * H ^ d * ∑ j ∈ J, ‖b j‖ ^ 2 := by
  set c : Fin d → ℤ := fun _ => B
  set b' : ι → ℂ := fun j => b j * ee (-∑ i, (c i : ℝ) * θ j i)
  have hb' : ∀ j, ‖b' j‖ = ‖b j‖ := fun j => by simp [b', norm_ee]
  have hinj : Set.InjOn (fun n : Fin d → ℤ => n + c) A := fun x _ y _ h => by simpa using h
  calc ∑ n ∈ A, ‖trigS J b θ n‖ ^ 2 = ∑ n ∈ A, ‖trigS J b' θ (n + c)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_; rw [trigS_add J b θ n c]
    _ = ∑ m ∈ A.image (fun n => n + c), ‖trigS J b' θ m‖ ^ 2 :=
        (Finset.sum_image (f := fun m => ‖trigS J b' θ m‖ ^ 2) hinj).symm
    _ ≤ ∑ m ∈ boxZ d H, ‖trigS J b' θ m‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        simp only [boxZ, Fintype.mem_piFinset, mem_Ico]
        intro i; have := abs_le.1 (hA n hn i); simp only [Pi.add_apply, c]; omega
    _ ≤ (8 * cK) ^ d * H ^ d * ∑ j ∈ J, ‖b' j‖ ^ 2 := largeSieveZ J b' θ H hδ hδH hsep
    _ = (8 * cK) ^ d * H ^ d * ∑ j ∈ J, ‖b j‖ ^ 2 := by simp_rw [hb']

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_FSChar: the S-adelic character on the lattice `𝓞 F`, and separation of fractions

The lattice model of `F_S`: on `𝓞 F` (a lattice in `F ⊗ ℝ`, coordinates in the integral basis
`ω`), the character `a ↦ e(a β)` is the trace character `ee(Σ_i a_i θ_i)` with
`θ_i = −Tr(ω_i ξ)`, for any `S_f`-integral `ξ ≡ β (mod R)` (`sAddChar_mul_eq_ee`).

`sep_of_mul_mem`: two such points whose difference is not in `R` but has denominator ideal `J`
are `δ`-separated modulo `ℤ^d` in the sup norm once `(δ C)^d N(J) N(𝔇) < 1` (the norm argument
of Lemma 7.1, (7.5)).
-/

open NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F]

/-- The index type of the integral basis. -/
abbrev BI (F : Type*) [Field F] [NumberField F] : Type _ := Module.Free.ChooseBasisIndex ℤ (𝓞 F)

/-- Integral-basis coordinates of `a ∈ 𝓞 F`. -/
noncomputable def coordZ (a : 𝓞 F) (i : BI F) : ℤ := (RingOfIntegers.basis F).repr a i

lemma coe_eq_sum_coordZ (a : 𝓞 F) :
    (a : F) = ∑ i, coordZ a i • integralBasis F i := by
  have h := congrArg (algebraMap (𝓞 F) F) ((RingOfIntegers.basis F).sum_repr a)
  rw [map_sum] at h
  show algebraMap (𝓞 F) F a = _
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integralBasis_apply, map_zsmul]
  rfl

/-- `Tr(a ξ) = Σ_i a_i Tr(ω_i ξ)`. -/
lemma trace_mul_eq (a : 𝓞 F) (ξ : F) :
    Algebra.trace ℚ F ((a : F) * ξ) =
      ∑ i, (coordZ a i : ℚ) * Algebra.trace ℚ F (integralBasis F i * ξ) := by
  rw [coe_eq_sum_coordZ a, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_zsmul, zsmul_eq_mul]

/-- The torus point `θ_i = −Tr(ω_i ξ)` of `ξ`. -/
noncomputable def thetaOf (ξ : F) (i : BI F) : ℝ :=
  -((Algebra.trace ℚ F (integralBasis F i * ξ) : ℚ) : ℝ)

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_mem_integer (a : 𝓞 F) : (a : F) ∈ (placesOf 𝔪).integer F :=
  (algebraMap (𝓞 F) (SInt 𝔪) a).2

/-- **The character on the lattice.** For `ξ ≡ β (mod R)` integral at `S_f`,
`e(a β) = ee(Σ_i a_i θ_i(ξ))` for every `a ∈ 𝓞 F`. -/
theorem sAddChar_mul_eq_ee {β ξ : F} (h1 : β - ξ ∈ (placesOf 𝔪).integer F)
    (h2 : ∀ v ∈ placesOf 𝔪, v.valuation F ξ ≤ 1) (a : 𝓞 F) :
    sAddChar 𝔪 ((a : F) * β) = ee (∑ i, (coordZ a i : ℝ) * thetaOf ξ i) := by
  have hw1 : (a : F) * β - (a : F) * ξ ∈ (placesOf 𝔪).integer F := by
    rw [← mul_sub]; exact mul_mem (coe_mem_integer a) h1
  have hw2 : ∀ v ∈ placesOf 𝔪, v.valuation F ((a : F) * ξ) ≤ 1 := by
    intro v hv
    rw [map_mul]
    exact mul_le_one' (v.valuation_le_one a) (h2 v hv)
  rw [C3I.sAddChar_eq_of_wit hw1 hw2, trace_mul_eq, ee]
  congr 1
  simp only [thetaOf, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast, Complex.ofReal_ratCast,
    Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-! ### The dual basis and the separation of fractions -/

variable (F) in
/-- The trace-dual basis `ω^∨` of the integral basis. -/
noncomputable def dualB : Module.Basis (BI F) ℚ F :=
  (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F)

lemma trace_dualB_mul (i j : BI F) :
    Algebra.trace ℚ F (dualB F i * integralBasis F j) = if j = i then 1 else 0 := by
  have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ F)
    (integralBasis F) i j
  simpa [dualB, Algebra.traceForm_apply] using this

lemma eq_sum_trace_dualB (x : F) :
    x = ∑ j, Algebra.trace ℚ F (x * integralBasis F j) • dualB F j := by
  conv_lhs => rw [← (dualB F).sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dualB, LinearMap.BilinForm.dualBasis_repr_apply]
  rfl

variable (F) in
/-- The archimedean size constant of the dual basis. -/
noncomputable def cDual : ℝ := 1 + ∑ w : InfinitePlace F, ∑ j, w (dualB F j)

lemma cDual_pos : 0 < cDual F := by
  unfold cDual
  have : 0 ≤ ∑ w : InfinitePlace F, ∑ j, w (dualB F j) :=
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun j _ => apply_nonneg w _
  linarith

lemma infinitePlace_ratCast_smul (w : InfinitePlace F) (q : ℚ) (y : F) : w (q • y) = |(q : ℝ)| * w y := by
  rw [Algebra.smul_def, map_mul, eq_ratCast, InfinitePlace.map_ratCast, ← Rat.norm_cast_real,
    Real.norm_eq_abs]

/-- An element with all dual traces `< δ` is archimedean-small: `w(x) ≤ δ C`. -/
lemma place_le_of_trace_small (x : F) {δ : ℝ}
    (hx : ∀ j, |((Algebra.trace ℚ F (x * integralBasis F j) : ℚ) : ℝ)| ≤ δ)
    (w : InfinitePlace F) : w x ≤ δ * cDual F := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hx (Classical.arbitrary _))
  conv_lhs => rw [eq_sum_trace_dualB x]
  calc w (∑ j, Algebra.trace ℚ F (x * integralBasis F j) • dualB F j)
      ≤ ∑ j, w (Algebra.trace ℚ F (x * integralBasis F j) • dualB F j) :=
        AbsoluteValue.sum_le w.1 _ _
    _ = ∑ j, |((Algebra.trace ℚ F (x * integralBasis F j) : ℚ) : ℝ)| * w (dualB F j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [infinitePlace_ratCast_smul]
    _ ≤ ∑ j, δ * w (dualB F j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hx j) (apply_nonneg w _)
    _ = δ * ∑ j, w (dualB F j) := by rw [Finset.mul_sum]
    _ ≤ δ * cDual F := by
        refine mul_le_mul_of_nonneg_left ?_ hδ
        unfold cDual
        have := Finset.single_le_sum (f := fun w : InfinitePlace F => ∑ j, w (dualB F j))
          (fun w _ => Finset.sum_nonneg fun j _ => apply_nonneg w _) (Finset.mem_univ w)
        linarith

lemma abs_norm_le_of_trace_small (x : F) {δ : ℝ}
    (hx : ∀ j, |((Algebra.trace ℚ F (x * integralBasis F j) : ℚ) : ℝ)| ≤ δ) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| ≤ (δ * cDual F) ^ Module.finrank ℚ F := by
  rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  have := InfinitePlace.prod_eq_abs_norm x
  rw [← Rat.cast_abs, ← this]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg (apply_nonneg w _) _)
    fun w _ => pow_le_pow_left₀ (apply_nonneg w _) (place_le_of_trace_small x hx w) _

lemma fi_one_ne_zero : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero

/-- An element `y` of the trace dual of `𝓞 F` satisfies `y p ∈ 𝓞` for `p ∈ 𝔇`. -/
lemma exists_mul_eq_of_trace_int (y : F) (hy : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n)
    (p : 𝓞 F) (hp : p ∈ differentIdeal ℤ (𝓞 F)) :
    ∃ a : 𝓞 F, y * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a := by
  have hdual : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual fi_one_ne_zero]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := hy a'
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; rfl⟩
  have hp' : algebraMap (𝓞 F) F p ∈
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩
  rw [coeIdeal_differentIdeal ℤ ℚ] at hp'
  have h1 := FractionalIdeal.mul_mem_mul hdual hp'
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ fi_one_ne_zero)] at h1
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  exact ⟨a, ha.symm⟩

/-- Elements of the trace dual of `𝓞 F` lie in `R` when no prime outside `S` divides `𝔇`. -/
lemma mem_integer_of_trace_int
    (hD : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (y : F) (hy : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n) :
    y ∈ (placesOf 𝔪).integer F := by
  intro v hv
  obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp (hD v hv)
  obtain ⟨a, ha⟩ := exists_mul_eq_of_trace_int y hy p hp
  have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
  have := v.valuation_le_one (K := F) a
  change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
  rw [← ha, map_mul, h1, mul_one] at this
  exact this

/-- The norm lower bound: if `x ≠ 0` and `x I ⊆ 𝓞` for a nonzero ideal `I`, then
`1 ≤ |N x| N(I)`. -/
lemma one_le_abs_norm_mul (x : F) (hx : x ≠ 0) (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥)
    (hint : ∀ z ∈ I, ∃ a : 𝓞 F, x * algebraMap (𝓞 F) F z = algebraMap (𝓞 F) F a) :
    1 ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm I : ℝ) := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ x *
      (I : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_mul_le_iff]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨a, ha⟩ := hint z hz
    rw [ha]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩
  obtain ⟨K, hK⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hK0 : K ≠ ⊥ := by
    intro h0
    rw [h0, FractionalIdeal.coeIdeal_bot (S := (𝓞 F)⁰) (P := F)] at hK
    have := hK.symm
    rw [mul_eq_zero, FractionalIdeal.spanSingleton_eq_zero_iff,
      FractionalIdeal.coeIdeal_eq_zero] at this
    rcases this with h | h
    · exact hx h
    · exact hI0 h
  have hnorm : (Ideal.absNorm K : ℚ) = |Algebra.norm ℚ x| * (Ideal.absNorm I : ℚ) := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := F), hK, map_mul,
      FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm]
  have hK1 : (1 : ℝ) ≤ Ideal.absNorm K := by
    have : Ideal.absNorm K ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hnorm' : (Ideal.absNorm K : ℝ) = |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm I : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hnorm
    push_cast at this
    exact this
  linarith

/-- **Separation of fractions** ((7.5) of Lemma 7.1 in the lattice model). Let `ξ, ξ'` be integral
at `S_f`, with `ξ − ξ' ∉ R` but `(ξ − ξ') J ⊆ R` for a nonzero ideal `J`. If
`(δ C)^d N(J) N(𝔇) < 1`, then `θ(ξ) − θ(ξ')` is at sup-distance `≥ δ` from `ℤ^d`. -/
theorem sep_of_mul_mem
    (hD : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (J : Ideal (𝓞 F)) (hJ0 : J ≠ ⊥) (ξ ξ' : F)
    (hξ : ∀ v ∈ placesOf 𝔪, v.valuation F ξ ≤ 1) (hξ' : ∀ v ∈ placesOf 𝔪, v.valuation F ξ' ≤ 1)
    (hJ : ∀ z ∈ J, (ξ - ξ') * algebraMap (𝓞 F) F z ∈ (placesOf 𝔪).integer F)
    (hne : ξ - ξ' ∉ (placesOf 𝔪).integer F) {δ : ℝ}
    (hsmall : (δ * cDual F) ^ Module.finrank ℚ F *
      ((Ideal.absNorm J : ℝ) * Ideal.absNorm (differentIdeal ℤ (𝓞 F))) < 1)
    (k : BI F → ℤ) : ∃ i, δ ≤ |thetaOf ξ i - thetaOf ξ' i - k i| := by
  classical
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  set lam : F := ∑ i, (k i : ℚ) • dualB F i with hlam
  -- traces of `lam`
  have htrlam : ∀ j, Algebra.trace ℚ F (lam * integralBasis F j) = k j := by
    intro j
    simp only [hlam, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, trace_dualB_mul,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have htrlam' : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (lam * a) = n := by
    intro a
    refine ⟨∑ j, k j * coordZ a j, ?_⟩
    rw [mul_comm, trace_mul_eq]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (integralBasis F j), htrlam]; ring
  have htrx' : ∀ j, |((Algebra.trace ℚ F ((ξ - ξ' + lam) * integralBasis F j) : ℚ) : ℝ)| ≤ δ := by
    intro j
    have : ((Algebra.trace ℚ F ((ξ - ξ' + lam) * integralBasis F j) : ℚ) : ℝ) =
        -(thetaOf ξ j - thetaOf ξ' j - k j) := by
      simp only [add_mul, sub_mul, map_add, map_sub, Rat.cast_add, Rat.cast_sub, htrlam,
        Rat.cast_intCast, thetaOf, mul_comm (integralBasis F j)]
      ring
    rw [this, abs_neg]; exact (hcon j).le
  -- `lam ∈ R`, hence `x' ≠ 0`
  have hlamR : lam ∈ (placesOf 𝔪).integer F := mem_integer_of_trace_int hD lam htrlam'
  have hx'0 : ξ - ξ' + lam ≠ 0 := by
    intro h0
    apply hne
    rw [show ξ - ξ' = -lam from eq_neg_of_add_eq_zero_left h0]
    exact neg_mem hlamR
  -- upper bound on the norm
  have hup := abs_norm_le_of_trace_small _ htrx'
  -- lower bound: `x' (J 𝔇) ⊆ 𝓞`
  have hD0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hint : ∀ z ∈ J * differentIdeal ℤ (𝓞 F),
      ∃ a : 𝓞 F, (ξ - ξ' + lam) * algebraMap (𝓞 F) F z = algebraMap (𝓞 F) F a := by
    intro z hz
    have hzJ : z ∈ J := (Ideal.mul_le_left : J * differentIdeal ℤ (𝓞 F) ≤ J) hz
    have hzD : z ∈ differentIdeal ℤ (𝓞 F) :=
      (Ideal.mul_le_right : J * differentIdeal ℤ (𝓞 F) ≤ differentIdeal ℤ (𝓞 F)) hz
    obtain ⟨a1, ha1⟩ := exists_mul_eq_of_trace_int lam htrlam' z hzD
    have h2 : (ξ - ξ') * algebraMap (𝓞 F) F z ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ (fun v => ?_)
      by_cases hv : v ∈ placesOf 𝔪
      · rw [map_mul]
        refine mul_le_one' ?_ (v.valuation_le_one z)
        exact (Valuation.map_sub _ _ _).trans (max_le (hξ v hv) (hξ' v hv))
      · exact hJ z hzJ v hv
    obtain ⟨a2, ha2⟩ := h2
    exact ⟨a2 + a1, by rw [map_add, ← ha1, ha2]; ring⟩
  have hJD0 : J * differentIdeal ℤ (𝓞 F) ≠ ⊥ := mul_ne_zero hJ0 hD0
  have hlow := one_le_abs_norm_mul _ hx'0 _ hJD0 hint
  rw [map_mul, Nat.cast_mul] at hlow
  have hJDpos : (0 : ℝ) ≤ (Ideal.absNorm J : ℝ) * Ideal.absNorm (differentIdeal ℤ (𝓞 F)) := by
    positivity
  have := mul_le_mul_of_nonneg_right hup hJDpos
  linarith

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_FSBal: balanced representatives modulo sixth powers of units

Archimedean part (Dirichlet's unit theorem through Mathlib's fundamental cone): every nonzero
`x ∈ 𝓞 F` has a multiple `η⁶ x`, `η ∈ 𝓞ˣ`, with `‖mixedEmbedding (η⁶ x)‖ ≤ C |N x|^{1/d}`
(`exists_unit_pow_six_balanced`). Coordinates in the integral basis are bounded by the mixed
embedding (`abs_coordZ_le`).
-/

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units IsDedekindDomain
open scoped Classical

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F]

/-- Integral-basis coordinates are bounded by the mixed embedding. -/
theorem exists_abs_coordZ_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : 𝓞 F) (i : BI F),
    |(coordZ a i : ℝ)| ≤ C * ‖mixedEmbedding F (a : F)‖ := by
  classical
  set B := latticeBasis F
  -- coordinate functionals are continuous
  have hcont : ∀ i, ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ y : mixedSpace F, |B.coord i y| ≤ Ci * ‖y‖ := by
    intro i
    let L : mixedSpace F →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.coord i)
    refine ⟨‖L‖, norm_nonneg _, fun y => ?_⟩
    have := L.le_opNorm y
    rwa [Real.norm_eq_abs] at this
  choose Ci hCi0 hCi using hcont
  refine ⟨∑ i, Ci i, Finset.sum_nonneg fun i _ => hCi0 i, fun a i => ?_⟩
  have hrepr : B.coord i (mixedEmbedding F (a : F)) = coordZ a i := by
    have h1 : mixedEmbedding F (a : F) = ∑ j, (coordZ a j : ℝ) • B j := by
      rw [coe_eq_sum_coordZ a, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, latticeBasis_apply, ← Int.cast_smul_eq_zsmul ℝ]
    rw [h1, map_sum]
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply]
    simp
  rw [← hrepr]
  refine (hCi i _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact Finset.single_le_sum (f := Ci) (fun j _ => hCi0 j) (Finset.mem_univ i)

/-- Elements of the fundamental cone are bounded by `C · norm^{1/d}`. -/
theorem exists_norm_le_of_mem_fundamentalCone : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ fundamentalCone F,
    ‖y‖ ≤ C * mixedEmbedding.norm y ^ ((1 : ℝ) / Module.finrank ℚ F) := by
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.1 (isBounded_normLeOne F))
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  set d := Module.finrank ℚ F
  have hd : (0 : ℝ) < d := by exact_mod_cast Module.finrank_pos
  have hN : 0 < mixedEmbedding.norm y := (norm_pos_of_mem hy)
  set c : ℝ := mixedEmbedding.norm y ^ (-(1 : ℝ) / d)
  have hc : 0 < c := Real.rpow_pos_of_pos hN _
  have hcy : c • y ∈ normLeOne F := by
    rw [mem_normLeOne]
    refine ⟨smul_mem_of_mem hy hc.ne', ?_⟩
    rw [mixedEmbedding.norm_smul, abs_of_pos hc, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    rw [show -(1 : ℝ) / d * d = -1 by field_simp, Real.rpow_neg_one, inv_mul_cancel₀ hN.ne']
  have h1 := hC _ hcy
  rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h1
  have h2 : ‖y‖ ≤ C * c⁻¹ := by
    rw [le_mul_inv_iff₀ hc]; linarith
  have h3 : c⁻¹ = mixedEmbedding.norm y ^ ((1 : ℝ) / d) := by
    rw [← Real.rpow_neg hN.le]; congr 1; ring
  rw [h3] at h2
  refine h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- Units mod sixth powers have a bounded set of representatives. -/
theorem exists_unit_decomp : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (𝓞 F)ˣ, ∃ η τ : (𝓞 F)ˣ,
    u = τ * η ^ 6 ∧ ‖mixedEmbedding F (((τ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)‖ ≤ C := by
  classical
  set r := rank F
  let f : torsion F × (Fin r → Fin 6) → ℝ := fun p =>
    ‖mixedEmbedding F ((((p.1 : (𝓞 F)ˣ) * ∏ i, (fundSystem F i) ^ ((p.2 i : ℕ) : ℤ))⁻¹ :
      (𝓞 F)ˣ) : F)‖
  have hfin : (Set.range f).Finite := Set.finite_range f
  obtain ⟨C, hC⟩ := hfin.bddAbove
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  obtain ⟨⟨ζ, e⟩, he, -⟩ := exist_unique_eq_mul_prod (K := F) u
  simp only at he
  set η : (𝓞 F)ˣ := ∏ i, (fundSystem F i) ^ (e i / 6)
  let p : torsion F × (Fin r → Fin 6) := (ζ, fun i => ⟨(e i % 6).toNat, by
    have h1 := Int.emod_nonneg (e i) (by norm_num : (6 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos (e i) (by norm_num : (0 : ℤ) < 6)
    omega⟩)
  set τ : (𝓞 F)ˣ := (ζ : (𝓞 F)ˣ) * ∏ i, (fundSystem F i) ^ (((p.2 i : ℕ) : ℤ))
  refine ⟨η, τ, ?_, ?_⟩
  · rw [he]
    simp only [τ, η, p]
    rw [mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    have h1 := Int.emod_nonneg (e i) (by norm_num : (6 : ℤ) ≠ 0)
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv (e i) 6
    push_cast
    linarith
  · have : f p ≤ C := hC ⟨p, rfl⟩
    exact this.trans (le_max_left _ _)

/-- **Archimedean balance.** Every nonzero `x ∈ 𝓞 F` has a multiple `η⁶ x` (`η ∈ 𝓞ˣ`) with
`‖mixedEmbedding (η⁶ x)‖ ≤ C |N x|^{1/d}`. -/
theorem exists_unit_pow_six_balanced : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : 𝓞 F, x ≠ 0 →
    ∃ η : (𝓞 F)ˣ, ‖mixedEmbedding F (((η : 𝓞 F) ^ 6 * x : 𝓞 F) : F)‖ ≤
      C * |((Algebra.norm ℚ (x : F) : ℚ) : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ F) := by
  obtain ⟨C₀, hC₀, hcone⟩ := exists_norm_le_of_mem_fundamentalCone (F := F)
  obtain ⟨CT, hCT, hdec⟩ := exists_unit_decomp (F := F)
  refine ⟨CT * C₀, mul_nonneg hCT hC₀, fun x hx => ?_⟩
  have hx' : (x : F) ≠ 0 := by exact_mod_cast hx
  have hN : mixedEmbedding.norm (mixedEmbedding F (x : F)) ≠ 0 := by
    rw [norm_eq_norm]
    simp [hx']
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hN
  obtain ⟨η, τ, huη, hτ⟩ := hdec u
  refine ⟨η, ?_⟩
  have hux := hcone _ hu
  rw [norm_unit_smul, norm_eq_norm] at hux
  rw [unitSMul_smul] at hux
  -- `η⁶ x = τ⁻¹ (u x)`
  have hkey : mixedEmbedding F (((η : 𝓞 F) ^ 6 * x : 𝓞 F) : F) =
      mixedEmbedding F (((τ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) *
        (mixedEmbedding F ((u : 𝓞 F) : F) * mixedEmbedding F (x : F)) := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [huη]
    push_cast
    have hinv : (((τ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (((τ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) (Units.inv_mul τ)
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
  rw [hkey]
  refine (norm_mul_le _ _).trans ?_
  calc ‖mixedEmbedding F (((τ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)‖ *
        ‖mixedEmbedding F ((u : 𝓞 F) : F) * mixedEmbedding F (x : F)‖
      ≤ CT * (C₀ * |((Algebra.norm ℚ (x : F) : ℚ) : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ F)) := by
        refine mul_le_mul hτ ?_ (norm_nonneg _) hCT
        convert hux using 3
        · push_cast; rfl
        · exact (Rat.cast_abs _).symm
    _ = CT * C₀ * |((Algebra.norm ℚ (x : F) : ℚ) : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ F) := by ring

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_FSSf: normalizing the `S_f`-valuations by sixth powers of `S`-units

`exists_Sf_normal`: for `m ∈ R` generating `𝔟 R` (`𝔟 ≠ 0`), some `μ ∈ R^×` has
`μ⁶ m ∈ 𝓞 F` and `|N(μ⁶ m)| ≤ C_S N 𝔟`. The units are powers of generators `π_v` of
`v^h` (`h` the class number) for the finitely many `v ∈ S_f`.
-/

open NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma finite_placesOf (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite :=
  (Ideal.finite_factors h𝔪).subset fun v hv => Ideal.dvd_iff_le.2 hv

/-- `v^h` is principal, `h` the class number. -/
lemma exists_span_eq_pow (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, Ideal.span {π} = v.asIdeal ^ classNumber F := by
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have h1 : ClassGroup.mk0 (⟨v.asIdeal, hv0⟩ ^ classNumber F) = 1 := by
    rw [map_pow, classNumber]; exact pow_card_eq_one
  rw [SubmonoidClass.mk_pow, ClassGroup.mk0_eq_one_iff] at h1
  obtain ⟨π, hπ⟩ := h1.principal
  exact ⟨π, hπ.symm⟩

lemma pi_ne_zero {v : HeightOneSpectrum (𝓞 F)} {π : 𝓞 F}
    (hπ : Ideal.span {π} = v.asIdeal ^ classNumber F) : π ≠ 0 := by
  intro h0
  rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at hπ
  exact pow_ne_zero _ v.ne_bot hπ.symm

lemma val_pi_other {v v' : HeightOneSpectrum (𝓞 F)} (hvv' : v ≠ v') {π : 𝓞 F}
    (hπ : Ideal.span {π} = v.asIdeal ^ classNumber F) :
    v'.valuation F (algebraMap (𝓞 F) F π) = 1 := by
  rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  have h1 : v.asIdeal ^ classNumber F ≤ v'.asIdeal := by
    rw [← hπ, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  have h2 : v.asIdeal ≤ v'.asIdeal := v'.isPrime.le_of_pow_le h1
  apply hvv'
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top h2)

lemma val_pi_self {v : HeightOneSpectrum (𝓞 F)} {π : 𝓞 F}
    (hπ : Ideal.span {π} = v.asIdeal ^ classNumber F) :
    v.valuation F (algebraMap (𝓞 F) F π) = exp (-(classNumber F : ℤ)) := by
  rw [C3I.val_alg]
  apply le_antisymm
  · rw [v.intValuation_le_pow_iff_mem, ← hπ]; exact Ideal.mem_span_singleton_self π
  · have hnot : π ∉ v.asIdeal ^ (classNumber F + 1) := by
      intro hmem
      have : v.asIdeal ^ classNumber F ≤ v.asIdeal ^ (classNumber F + 1) := by
        rw [← hπ, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
      exact (not_le_of_gt (Ideal.pow_succ_lt_pow v.ne_bot _)) this
    rw [← v.intValuation_le_pow_iff_mem, not_le] at hnot
    apply C3I.exp_le_of_lt
    convert hnot using 2
    push_cast; ring

/-- The `S`-unit `π_v` for `v ∈ S_f`. -/
noncomputable def piUnit (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ placesOf 𝔪) (π : 𝓞 F)
    (hπ : Ideal.span {π} = v.asIdeal ^ classNumber F) : (placesOf 𝔪).unit F :=
  ⟨Units.mk0 (algebraMap (𝓞 F) F π) (by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact pi_ne_zero hπ),
    fun v' hv' => by
      have : v ≠ v' := fun h => hv' (h ▸ hv)
      exact val_pi_other this hπ⟩

lemma coe_piUnit (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ placesOf 𝔪) (π : 𝓞 F)
    (hπ : Ideal.span {π} = v.asIdeal ^ classNumber F) :
    (((piUnit v hv π hπ : (placesOf 𝔪).unit F) : Fˣ) : F) = algebraMap (𝓞 F) F π := rfl

/-- **`S_f`-normalization.** -/
theorem exists_Sf_normal (h𝔪 : 𝔪 ≠ ⊥) : ∃ CS : ℝ, 0 < CS ∧ ∀ (m : SInt 𝔪) (𝔟 : Ideal (𝓞 F)),
    𝔟 ≠ ⊥ → Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪)) →
      ∃ μ : (SInt 𝔪)ˣ, ∃ x : 𝓞 F, (x : F) = ((μ : SInt 𝔪) : F) ^ 6 * (m : F) ∧ x ≠ 0 ∧
        |((Algebra.norm ℚ (x : F) : ℚ) : ℝ)| ≤ CS * Ideal.absNorm 𝔟 := by
  classical
  set Sf := (finite_placesOf h𝔪).toFinset
  have hSf : ∀ v, v ∈ Sf ↔ v ∈ placesOf 𝔪 := fun v => Set.Finite.mem_toFinset _
  set h := classNumber F
  have hh : 0 < h := classNumber_pos F
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => exists_span_eq_pow v
  set CS : ℝ := ∏ v ∈ Sf, ((Ideal.absNorm v.asIdeal : ℝ) ^ (6 * h))
  have hCS : 0 < CS := Finset.prod_pos fun v _ => by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    positivity
  refine ⟨CS, hCS, fun m 𝔟 h𝔟 hm => ?_⟩
  -- `m ≠ 0`
  have hm0 : (m : F) ≠ 0 := by
    intro h0
    have hm0' : m = 0 := Subtype.ext h0
    rw [hm0', Ideal.span_singleton_eq_bot.2 rfl] at hm
    apply h𝔟
    rw [eq_bot_iff]
    intro a ha
    have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.mem_map_of_mem _ ha
    rw [← hm, Ideal.mem_bot] at this
    have := congrArg (fun z : SInt 𝔪 => (z : F)) this
    simp only [C3I.coe_alg, ZeroMemClass.coe_zero] at this
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 this
  -- exponents
  set t : HeightOneSpectrum (𝓞 F) → ℤ := fun v => log (v.valuation F (m : F))
  have ht : ∀ v, v.valuation F (m : F) = exp (t v) := fun v => by
    simp only [t]; rw [exp_log]; rw [Ne, map_eq_zero]; exact hm0
  set k : HeightOneSpectrum (𝓞 F) → ℤ := fun v => t v / (6 * h) + 1
  -- the unit
  set U : (placesOf 𝔪).unit F := ∏ v ∈ Sf.attach,
    (piUnit v.1 ((hSf v.1).1 v.2) (π v.1) (hπ v.1)) ^ (k v.1)
  set μ : (SInt 𝔪)ˣ := Set.unitEquivUnitsInteger (placesOf 𝔪) F U
  have hμ : ((μ : SInt 𝔪) : F) = ∏ v ∈ Sf.attach, (algebraMap (𝓞 F) F (π v.1)) ^ (k v.1) := by
    have h1 : ((μ : SInt 𝔪) : F) = ((U : Fˣ) : F) := rfl
    rw [h1]
    simp only [U]
    simp [coe_piUnit]
  -- valuations of the unit
  have hvalU : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F ((μ : SInt 𝔪) : F) =
      if w ∈ placesOf 𝔪 then exp (-(h : ℤ) * k w) else 1 := by
    intro w
    rw [hμ, map_prod]
    simp_rw [map_zpow₀]
    split_ifs with hw
    · rw [Finset.prod_eq_single (⟨w, (hSf w).2 hw⟩ : Sf)]
      · rw [val_pi_self (hπ w), ← exp_zsmul]; congr 1; simp [smul_eq_mul]; ring
      · intro b _ hb
        have : b.1 ≠ w := fun h' => hb (Subtype.ext h')
        rw [val_pi_other this (hπ b.1), one_zpow]
      · intro h'; exact absurd (Finset.mem_attach _ _) h'
    · refine Finset.prod_eq_one fun b _ => ?_
      have : b.1 ≠ w := fun h' => hw (h' ▸ (hSf b.1).1 b.2)
      rw [val_pi_other this (hπ b.1), one_zpow]
  set y : F := ((μ : SInt 𝔪) : F) ^ 6 * (m : F)
  have hy0 : y ≠ 0 := by
    have : ((μ : SInt 𝔪) : F) ≠ 0 := by
      intro h0
      have := congrArg (fun z : F => z * ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)) h0
      simp only [zero_mul] at this
      rw [← Subalgebra.coe_mul, Units.mul_inv] at this
      exact one_ne_zero this
    exact mul_ne_zero (pow_ne_zero _ this) hm0
  have hvaly : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F y =
      if w ∈ placesOf 𝔪 then exp (t w - 6 * h * k w) else w.valuation F (m : F) := by
    intro w
    simp only [y, map_mul, map_pow, hvalU]
    split_ifs with hw
    · rw [ht w, ← exp_nsmul, ← exp_add]; congr 1; simp [nsmul_eq_mul]; ring
    · rw [one_pow, one_mul]
  have hrange : ∀ w, -(6 * (h : ℤ)) ≤ t w - 6 * h * k w ∧ t w - 6 * h * k w ≤ -1 := by
    intro w
    have h6 : (0 : ℤ) < 6 * h := by positivity
    have h1 := Int.emod_nonneg (t w) h6.ne'
    have h2 := Int.emod_lt_of_pos (t w) h6
    have h3 := Int.emod_add_mul_ediv (t w) (6 * h)
    simp only [k]
    constructor <;> nlinarith
  -- `y ∈ 𝓞`
  have hyint : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F y ≤ 1 := by
    intro w
    rw [hvaly]
    split_ifs with hw
    · rw [← exp_zero, exp_le_exp]; linarith [(hrange w).2]
    · exact m.2 w hw
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
  have hxy : (x : F) = y := hx
  have hx0 : x ≠ 0 := by
    intro h0; apply hy0; rw [← hxy, h0]; rfl
  refine ⟨μ, x, hxy, hx0, ?_⟩
  -- the norm bound: `J = 𝔟 ∏ v^{6h} ≤ (x)`
  set J : Ideal (𝓞 F) := 𝔟 * ∏ v ∈ Sf, v.asIdeal ^ (6 * h)
  have hJ0 : J ≠ ⊥ := by
    refine mul_ne_zero h𝔟 ?_
    rw [Finset.prod_ne_zero_iff]
    intro v _; exact pow_ne_zero _ v.ne_bot
  have hJle : J ≤ Ideal.span {x} := by
    intro z hz
    rw [Ideal.mem_span_singleton']
    -- `z / x` is integral
    have hzx : ∀ w : HeightOneSpectrum (𝓞 F),
        w.valuation F (algebraMap (𝓞 F) F z / y) ≤ 1 := by
      intro w
      have hyw : w.valuation F y ≠ 0 := by rw [Ne, map_eq_zero]; exact hy0
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hyw)]
      by_cases hw : w ∈ placesOf 𝔪
      · have hzw : z ∈ w.asIdeal ^ (6 * h) := by
          have h1 : J ≤ ∏ v ∈ Sf, v.asIdeal ^ (6 * h) := Ideal.mul_le_right
          have h2 : ∏ v ∈ Sf, v.asIdeal ^ (6 * h) ≤ w.asIdeal ^ (6 * h) := by
            rw [← Finset.prod_erase_mul _ _ ((hSf w).2 hw)]
            exact Ideal.mul_le_right
          exact h2 (h1 hz)
        rw [← w.intValuation_le_pow_iff_mem] at hzw
        rw [C3I.val_alg, hvaly, if_pos hw]
        refine hzw.trans ?_
        rw [exp_le_exp]; push_cast; linarith [(hrange w).1]
      · have hz𝔟 : z ∈ 𝔟 := Ideal.mul_le_left hz
        have : algebraMap (𝓞 F) (SInt 𝔪) z ∈ Ideal.span {m} := by
          rw [hm]; exact Ideal.mem_map_of_mem _ hz𝔟
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 this
        have hzF : algebraMap (𝓞 F) F z = (r : F) * (m : F) := by
          rw [← C3I.coe_alg (𝔪 := 𝔪), ← hr]; rfl
        rw [hzF, map_mul, hvaly, if_neg hw]
        calc w.valuation F (r : F) * w.valuation F (m : F) ≤ 1 * w.valuation F (m : F) :=
              mul_le_mul_of_nonneg_right (r.2 w hw) zero_le'
          _ = _ := one_mul _
    obtain ⟨q, hq⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hzx
    refine ⟨q, ?_⟩
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, hq]
    change _ * (x : F) = _
    rw [hxy, div_mul_cancel₀ _ hy0]
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hJle
  have hJn : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hJn) hdvd
  -- `absNorm (x) = |N x|`
  have hnx : (Ideal.absNorm (Ideal.span {x}) : ℝ) = |((Algebra.norm ℚ (x : F) : ℚ) : ℝ)| := by
    have := FractionalIdeal.coeIdeal_absNorm (K := F) (Ideal.span {x})
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.absNorm_span_singleton] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    push_cast at h2
    rw [← h2]
  have hJnorm : (Ideal.absNorm J : ℝ) = Ideal.absNorm 𝔟 * CS := by
    simp only [J, CS, map_mul, map_prod, map_pow, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  rw [← hnx]
  calc (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Ideal.absNorm J := by exact_mod_cast hle
    _ = CS * Ideal.absNorm 𝔟 := by rw [hJnorm, mul_comm]

/-- **Balanced box representatives** (Lemma 3.2's balanced generators, in the lattice model):
every `m ∈ R` generating `𝔟 R` has a multiple `μ⁶ m ∈ 𝓞 F` (`μ ∈ R^×`) whose integral-basis
coordinates are `≤ C (N 𝔟)^{1/d}`. -/
theorem exists_box_rep (h𝔪 : 𝔪 ≠ ⊥) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : SInt 𝔪) (𝔟 : Ideal (𝓞 F)),
    𝔟 ≠ ⊥ → Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪)) →
      ∃ μ : (SInt 𝔪)ˣ, ∃ a : 𝓞 F, (a : F) = ((μ : SInt 𝔪) : F) ^ 6 * (m : F) ∧
        ∀ i, |(coordZ a i : ℝ)| ≤ C * (Ideal.absNorm 𝔟 : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ F) := by
  classical
  obtain ⟨CS, hCS, hSf⟩ := exists_Sf_normal h𝔪
  obtain ⟨C₁, hC₁, hbal⟩ := exists_unit_pow_six_balanced (F := F)
  obtain ⟨C₂, hC₂, hcoord⟩ := exists_abs_coordZ_le (F := F)
  set e : ℝ := (1 : ℝ) / Module.finrank ℚ F
  have he : 0 ≤ e := by positivity
  refine ⟨C₂ * C₁ * CS ^ e, by positivity, fun m 𝔟 h𝔟 hm => ?_⟩
  obtain ⟨μ₁, x, hx, hx0, hxn⟩ := hSf m 𝔟 h𝔟 hm
  obtain ⟨η, hη⟩ := hbal x hx0
  set ηR : (SInt 𝔪)ˣ := Units.map (algebraMap (𝓞 F) (SInt 𝔪)).toMonoidHom η
  have hηR : ((ηR : SInt 𝔪) : F) = ((η : 𝓞 F) : F) := rfl
  refine ⟨μ₁ * ηR, (η : 𝓞 F) ^ 6 * x, ?_, fun i => ?_⟩
  · have h1 : ((((η : 𝓞 F) ^ 6 * x : 𝓞 F)) : F) = ((η : 𝓞 F) : F) ^ 6 * (x : F) := by
      push_cast; ring
    rw [h1, hx, Units.val_mul, Subalgebra.coe_mul, hηR]
    ring
  · refine (hcoord _ i).trans ?_
    calc C₂ * ‖mixedEmbedding F (((η : 𝓞 F) ^ 6 * x : 𝓞 F) : F)‖
        ≤ C₂ * (C₁ * |((Algebra.norm ℚ (x : F) : ℚ) : ℝ)| ^ e) :=
          mul_le_mul_of_nonneg_left hη hC₂
      _ ≤ C₂ * (C₁ * (CS * Ideal.absNorm 𝔟) ^ e) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC₁) hC₂
          exact Real.rpow_le_rpow (abs_nonneg _) hxn he
      _ = C₂ * C₁ * CS ^ e * (Ideal.absNorm 𝔟 : ℝ) ^ e := by
          rw [Real.mul_rpow hCS.le (Nat.cast_nonneg _)]; ring

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_FSQuot: exterior ideals of `𝓞 F` and of `R`

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,
  `natCard_quot_map_le : #(R / I R) ≤ N I`.
-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Every `r ∈ R` has `𝔪^N r ⊆ 𝓞` for some `N`. -/
lemma exists_pow_mul_mem (r : SInt 𝔪) : ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ c : 𝓞 F,
    algebraMap (𝓞 F) (SInt 𝔪) w * r = algebraMap (𝓞 F) (SInt 𝔪) c := by
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (r : F)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set N := Ideal.absNorm (Ideal.span {d}) with hN
  refine ⟨N, fun w hw => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      v.valuation F (algebraMap (𝓞 F) F w * (r : F)) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · have hvm : 𝔪 ≤ v.asIdeal := hv
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
        rw [C3I.val_alg, ← not_le, v.intValuation_le_pow_iff_mem]; exact hdN
      have hvw : v.valuation F (algebraMap (𝓞 F) F w) ≤ exp (-(N : ℤ)) := by
        rw [C3I.val_alg, v.intValuation_le_pow_iff_mem]
        exact Ideal.pow_right_mono hvm N hw
      have hdpos : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := ne_zero_of_lt hvd
      have hxd : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F b := by
        rw [← hbd, div_mul_cancel₀]
        exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
      have key : v.valuation F (algebraMap (𝓞 F) F w * (r : F)) *
          v.valuation F (algebraMap (𝓞 F) F d) ≤ 1 * v.valuation F (algebraMap (𝓞 F) F d) := by
        rw [← map_mul, show algebraMap (𝓞 F) F w * (r : F) * algebraMap (𝓞 F) F d =
          algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F w by rw [mul_assoc, hxd]; ring, map_mul]
        exact mul_le_mul' (v.valuation_le_one b) (hvw.trans hvd.le)
      exact C3I.le_of_mul_le_mul_ne key hdpos
    · rw [map_mul]
      exact mul_le_one' (v.valuation_le_one w) (r.2 v hv)
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint
  refine ⟨c, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, C3I.coe_alg, C3I.coe_alg, hc]

/-- `I R ∩ 𝓞 = I` for an ideal `I` coprime to `𝔪`. -/
lemma mem_of_map_mem (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (a : 𝓞 F)
    (ha : algebraMap (𝓞 F) (SInt 𝔪) a ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) : a ∈ I := by
  set φ := algebraMap (𝓞 F) (SInt 𝔪)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hxy
    simp only [φ, C3I.coe_alg] at this
    exact IsFractionRing.injective (𝓞 F) F this
  -- the predicate
  have hQ : ∀ x ∈ I.map φ, ∃ N : ℕ, ∀ w ∈ 𝔪 ^ N, ∃ i ∈ I, φ w * x = φ i := by
    intro x hx
    rw [Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i0, hi0, rfl⟩ := hx
      exact ⟨0, fun w _ => ⟨w * i0, I.mul_mem_left _ hi0, by rw [map_mul]⟩⟩
    | zero => exact ⟨0, fun w _ => ⟨0, I.zero_mem, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨max N1 N2, fun w hw => ?_⟩
      obtain ⟨i1, hi1, e1⟩ := h1 w (Ideal.pow_le_pow_right (le_max_left _ _) hw)
      obtain ⟨i2, hi2, e2⟩ := h2 w (Ideal.pow_le_pow_right (le_max_right _ _) hw)
      exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [mul_add, e1, e2, map_add]⟩
    | smul r x _ hx =>
      obtain ⟨Nx, hNx⟩ := hx
      obtain ⟨Nr, hNr⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
      refine ⟨Nr + Nx, fun w hw => ?_⟩
      rw [pow_add] at hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro w1 hw1 w2 hw2
        obtain ⟨c, hc⟩ := hNr w1 hw1
        obtain ⟨i, hi, ei⟩ := hNx w2 hw2
        refine ⟨c * i, I.mul_mem_left _ hi, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, ← hc, ← ei]; ring
      · rintro w1 w2 ⟨i1, hi1, e1⟩ ⟨i2, hi2, e2⟩
        exact ⟨i1 + i2, I.add_mem hi1 hi2, by rw [map_add, add_mul, e1, e2, map_add]⟩
  obtain ⟨N, hN⟩ := hQ _ ha
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨i, hi, ei⟩ := hN w hw
  have : w * a = i := hinj (by rw [map_mul, ei])
  have ha' : a = u * a + w * a := by rw [← add_mul, huw, one_mul]
  rw [ha', this]
  exact I.add_mem (I.mul_mem_right _ hu) hi

/-- `𝓞 → R / I R` is onto for `I` coprime to `𝔪`. -/
lemma exists_sub_mem_map (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) (r : SInt 𝔪) :
    ∃ c : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) c ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem (𝔪 := 𝔪) r
  have hcop : IsCoprime I (𝔪 ^ N) := (Ideal.isCoprime_iff_sup_eq.mpr hI).pow_right
  obtain ⟨u, hu, w, hw, huw⟩ := hcop.exists
  obtain ⟨c, hc⟩ := hN w hw
  refine ⟨c, ?_⟩
  have : r - algebraMap (𝓞 F) (SInt 𝔪) c = algebraMap (𝓞 F) (SInt 𝔪) u * r := by
    rw [← hc]
    have : algebraMap (𝓞 F) (SInt 𝔪) u + algebraMap (𝓞 F) (SInt 𝔪) w = 1 := by
      rw [← map_add, huw, map_one]
    linear_combination (-r) * this
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu)

lemma quotHom_surjective (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) :
    Function.Surjective (C3I.quotHom 𝔪 I) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_map I hI r
  exact ⟨Ideal.Quotient.mk _ c, by rw [C3I.quotHom_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩

lemma finite_quot_map (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Finite (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_surjective _ (quotHom_surjective I hI)

lemma natCard_quot_map_le (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Nat.card (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) ≤ Ideal.absNorm I := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_le_card_of_surjective _ (quotHom_surjective I hI)

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_FSDist: reduced fractions with distinct data are distinct modulo `R`

`frac_eq_of_sub_mem`: if `a/s − a'/s' ∈ R` for allowed generators `s, s'` of exterior `𝔰, 𝔰'`
and numerators with nonzero residue symbols (so reduced), then `𝔰 = 𝔰'` and `a ≡ a' (mod 𝔰 R)`.
This is the first paragraph of the proof of Lemma 7.1 (p. 43).
-/

open NumberField IsDedekindDomain WithZero UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-- A nonzero residue symbol forces the numerator off every prime factor. -/
lemma not_mem_of_residueSymbol_ne_zero {𝔰 : Ideal (𝓞 F)} {a : SInt 𝔪}
    (ha : residueSymbol ι 𝔪 𝔰 a ≠ 0) {P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors 𝔰) :
    a ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  intro hmem
  apply ha
  unfold residueSymbol
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  refine ⟨P, hP, ?_⟩
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 hmem)]

lemma val_le_exp_neg_one_of_lt_one {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (h : v.valuation F x < 1) : v.valuation F x ≤ exp (-1 : ℤ) := by
  by_contra hc
  rw [not_le] at hc
  have := C3I.exp_le_of_lt (j := 0) (by simpa using hc)
  rw [exp_zero] at this
  exact absurd h (not_lt.2 this)

/-- A prime outside `S` containing the allowed generator divides the ideal. -/
lemma mem_normalizedFactors_of_gen_mem (g : AllowedGen ι 𝔪) {𝔰 : Ideal (𝓞 F)}
    (h𝔰 : IsExterior 𝔪 𝔰) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ placesOf 𝔪)
    (hs : g.gen 𝔰 ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.asIdeal ∈ normalizedFactors 𝔰 := by
  have hvm : v.asIdeal ⊔ 𝔪 = ⊤ := by
    have hmax := v.isMaximal
    by_contra hne
    apply hv
    have h1 : v.asIdeal = v.asIdeal ⊔ 𝔪 := hmax.eq_of_le hne le_sup_left
    show 𝔪 ≤ v.asIdeal
    rw [h1]; exact le_sup_right
  have hle : 𝔰 ≤ v.asIdeal := by
    intro b hb
    apply mem_of_map_mem v.asIdeal hvm b
    have : algebraMap (𝓞 F) (SInt 𝔪) b ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.mem_map_of_mem _ hb
    rw [← g.span_gen 𝔰 h𝔰, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [hc]
    exact Ideal.mul_mem_right _ _ hs
  have hdvd : v.asIdeal ∣ 𝔰 := Ideal.dvd_iff_le.2 hle
  have hirr : Irreducible v.asIdeal :=
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd h𝔰.1 hirr hdvd
  rw [associated_iff_eq] at hassoc
  rwa [hassoc]

/-- One inequality of the valuation comparison. -/
lemma val_gen_le (g : AllowedGen ι 𝔪) {𝔰 𝔰' : Ideal (𝓞 F)} (h𝔰 : IsExterior 𝔪 𝔰)
    (h𝔰' : IsExterior 𝔪 𝔰') {a a' : SInt 𝔪} (ha : residueSymbol ι 𝔪 𝔰 a ≠ 0)
    (h : (a : F) / (g.gen 𝔰 : F) - (a' : F) / (g.gen 𝔰' : F) ∈ (placesOf 𝔪).integer F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ placesOf 𝔪) :
    v.valuation F (g.gen 𝔰' : F) ≤ v.valuation F (g.gen 𝔰 : F) := by
  by_contra hlt
  rw [not_le] at hlt
  set s : F := (g.gen 𝔰 : F)
  set s' : F := (g.gen 𝔰' : F)
  have hs0 : s ≠ 0 := C3B.gen_ne_zero g 𝔰 h𝔰
  have hs'0 : s' ≠ 0 := C3B.gen_ne_zero g 𝔰' h𝔰'
  have hvs0 : v.valuation F s ≠ 0 := by rw [Ne, map_eq_zero]; exact hs0
  have hvs'0 : v.valuation F s' ≠ 0 := by rw [Ne, map_eq_zero]; exact hs'0
  have hs1 : v.valuation F s < 1 := lt_of_lt_of_le hlt ((g.gen 𝔰').2 v hv)
  -- `s ∈ v R`, so `v ∣ 𝔰` and `v(a) = 1`
  have hsmem : g.gen 𝔰 ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have := C3I.mem_of_val_le hv 1 (g.gen 𝔰) (by simpa using val_le_exp_neg_one_of_lt_one hs1)
    rwa [pow_one] at this
  have hvf := mem_normalizedFactors_of_gen_mem g h𝔰 hv hsmem
  have hanot := not_mem_of_residueSymbol_ne_zero ha hvf
  have hva : v.valuation F (a : F) = 1 := by
    apply le_antisymm (a.2 v hv)
    have := C3I.exp_le_val_of_not_mem hv 0 a (by rwa [zero_add, pow_one])
    simpa using this
  set x := (a : F) / s
  set y := (a' : F) / s'
  have hx : v.valuation F x * v.valuation F s = 1 := by
    rw [← map_mul, div_mul_cancel₀ _ hs0, hva]
  have hy : v.valuation F y * v.valuation F s' ≤ 1 := by
    rw [← map_mul, div_mul_cancel₀ _ hs'0]; exact a'.2 v hv
  have hx0 : v.valuation F x ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hx; exact zero_ne_one hx
  -- `v(y) < v(x)`
  have hyx : v.valuation F y < v.valuation F x := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : v.valuation F x * v.valuation F s' ≤ v.valuation F x * v.valuation F s := by
      calc v.valuation F x * v.valuation F s' ≤ v.valuation F y * v.valuation F s' :=
            mul_le_mul_of_nonneg_right hc zero_le
        _ ≤ 1 := hy
        _ = _ := hx.symm
    rw [mul_comm (v.valuation F x), mul_comm (v.valuation F x)] at h1
    exact absurd (C3I.le_of_mul_le_mul_ne h1 hx0) (not_le.2 hlt)
  have hxgt : 1 < v.valuation F x := by
    by_contra hc
    rw [not_lt] at hc
    have : v.valuation F x * v.valuation F s ≤ 1 * v.valuation F s :=
      mul_le_mul_of_nonneg_right hc zero_le
    rw [hx, one_mul] at this
    exact absurd hs1 (not_lt.2 this)
  have hsub := Valuation.map_sub_eq_of_lt_left (v.valuation F) hyx
  have := h v hv
  rw [hsub] at this
  exact absurd hxgt (not_lt.2 this)

/-- **Distinct reduced fractions are distinct modulo `R`.** -/
theorem frac_eq_of_sub_mem (g : AllowedGen ι 𝔪) {𝔰 𝔰' : Ideal (𝓞 F)} (h𝔰 : IsExterior 𝔪 𝔰)
    (h𝔰' : IsExterior 𝔪 𝔰') {a a' : SInt 𝔪} (ha : residueSymbol ι 𝔪 𝔰 a ≠ 0)
    (ha' : residueSymbol ι 𝔪 𝔰' a' ≠ 0)
    (h : (a : F) / (g.gen 𝔰 : F) - (a' : F) / (g.gen 𝔰' : F) ∈ (placesOf 𝔪).integer F) :
    𝔰 = 𝔰' ∧ a - a' ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have h' : (a' : F) / (g.gen 𝔰' : F) - (a : F) / (g.gen 𝔰 : F) ∈ (placesOf 𝔪).integer F := by
    rw [← neg_sub]; exact neg_mem h
  set s : F := (g.gen 𝔰 : F)
  set s' : F := (g.gen 𝔰' : F)
  have hs0 : s ≠ 0 := C3B.gen_ne_zero g 𝔰 h𝔰
  have hs'0 : s' ≠ 0 := C3B.gen_ne_zero g 𝔰' h𝔰'
  have heqv : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      v.valuation F s = v.valuation F s' := fun v hv =>
    le_antisymm (val_gen_le g h𝔰' h𝔰 ha' h' v hv) (val_gen_le g h𝔰 h𝔰' ha h v hv)
  -- `s / s'` and `s' / s` are in `R`
  have hu : s / s' ∈ (placesOf 𝔪).integer F := fun v hv => by
    rw [map_div₀, heqv v hv, div_self]
    rw [Ne, map_eq_zero]; exact hs'0
  have hu' : s' / s ∈ (placesOf 𝔪).integer F := fun v hv => by
    rw [map_div₀, heqv v hv, div_self]
    rw [Ne, map_eq_zero]; exact hs'0
  have hspan : 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) = 𝔰'.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen 𝔰 h𝔰, ← g.span_gen 𝔰' h𝔰']
    apply le_antisymm
    · rw [Ideal.span_singleton_le_span_singleton]
      refine ⟨⟨s / s', hu⟩, Subtype.ext ?_⟩
      change s = s' * (s / s')
      field_simp
    · rw [Ideal.span_singleton_le_span_singleton]
      refine ⟨⟨s' / s, hu'⟩, Subtype.ext ?_⟩
      change s' = s * (s' / s)
      field_simp
  have heq : 𝔰 = 𝔰' := by
    apply le_antisymm
    · intro b hb
      apply mem_of_map_mem 𝔰' h𝔰'.2 b
      rw [← hspan]; exact Ideal.mem_map_of_mem _ hb
    · intro b hb
      apply mem_of_map_mem 𝔰 h𝔰.2 b
      rw [hspan]; exact Ideal.mem_map_of_mem _ hb
  refine ⟨heq, ?_⟩
  subst heq
  -- `(a − a') / s ∈ R`
  have hmem : ((a - a' : SInt 𝔪) : F) / s ∈ (placesOf 𝔪).integer F := by
    rw [Subalgebra.coe_sub, sub_div]; exact h
  rw [← g.span_gen 𝔰 h𝔰, Ideal.mem_span_singleton']
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  change ((a - a' : SInt 𝔪) : F) / s * s = _
  rw [div_mul_cancel₀ _ hs0]

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_Pts: the additive fractions `d/s` as points of the dual torus

* `PIdx 𝔪`: pairs `(𝔰, d mod 𝔰R)`; `fracWit g p`: an `S_f`-integral `ξ ≡ −d/s (mod R)`;
  `thetaP g p = θ(ξ)`.
* `gaussSumAt_eq_finsum_ee`: `g_𝔰(−m) = Σ_d χ_𝔰(d) ee(a·θ_{𝔰,d})` for any `a = μ⁶ m ∈ 𝓞`.
* `thetaP_sep`: distinct reduced fractions are `δ`-separated.
* `span_rowElt`, `rowClass_eq_of_box`: row classes are determined by any `μ⁶`-multiple of their
  element.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- Pairs `(𝔰, d mod 𝔰 R)`, indexing the fractions `d/s`. -/
abbrev PIdx (𝔪 : Ideal (𝓞 F)) : Type _ :=
  Σ 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}, SInt 𝔪 ⧸ 𝔰.1.map (algebraMap (𝓞 F) (SInt 𝔪))

lemma hasWit_frac (g : AllowedGen ι 𝔪) (p : PIdx 𝔪) :
    C3I.HasWit 𝔪 (-((quotLift p.2 : SInt 𝔪) : F) / (g.gen p.1.1 : F)) := by
  rw [neg_div]
  exact C3I.hasWit_neg (C3I.hasWit_div_gen g p.1.1 p.1.2 (quotLift p.2))

/-- An `S_f`-integral representative of `−d/s` modulo `R`. -/
noncomputable def fracWit (g : AllowedGen ι 𝔪) (p : PIdx 𝔪) : F := (hasWit_frac g p).choose

lemma fracWit_spec (g : AllowedGen ι 𝔪) (p : PIdx 𝔪) :
    -((quotLift p.2 : SInt 𝔪) : F) / (g.gen p.1.1 : F) - fracWit g p ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F (fracWit g p) ≤ 1 :=
  (hasWit_frac g p).choose_spec

/-- The torus point of the fraction `p`. -/
noncomputable def thetaP (g : AllowedGen ι 𝔪) (p : PIdx 𝔪) : BI F → ℝ := thetaOf (fracWit g p)

/-- **`g_𝔰(−m)` as a trigonometric polynomial on the lattice.** -/
theorem gaussSumAt_eq_finsum_ee (g : AllowedGen ι 𝔪) (𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰})
    (hgood : ∀ P ∈ normalizedFactors 𝔰.1, C3B.GoodP 𝔪 P) (m : SInt 𝔪) (μ : (SInt 𝔪)ˣ)
    (a : 𝓞 F) (ha : (a : F) = ((μ : SInt 𝔪) : F) ^ 6 * (m : F)) :
    gaussSumAt g 𝔰.1 (-(m : F)) = ∑ᶠ x : SInt 𝔪 ⧸ 𝔰.1.map (algebraMap (𝓞 F) (SInt 𝔪)),
      residueSymbol ι 𝔪 𝔰.1 (quotLift x) *
        ee (∑ i, (coordZ a i : ℝ) * thetaP g ⟨𝔰, x⟩ i) := by
  have h1 : -(a : F) = ((μ : SInt 𝔪) : F) ^ 6 * (-(m : F)) := by rw [ha]; ring
  have hm : -(m : F) ∈ (placesOf 𝔪).integer F := neg_mem m.2
  rw [← C3B.gaussSumAt_unit_pow_six g 𝔰.1 𝔰.2 hgood μ (-(m : F)) hm, ← h1]
  unfold gaussSumAt
  refine finsum_congr fun x => ?_
  congr 1
  have hs := fracWit_spec g ⟨𝔰, x⟩
  have := sAddChar_mul_eq_ee hs.1 hs.2 a
  rw [show -(a : F) * ((quotLift x : SInt 𝔪) : F) / (g.gen 𝔰.1 : F) =
    (a : F) * (-((quotLift x : SInt 𝔪) : F) / (g.gen 𝔰.1 : F)) by ring]
  exact this

/-- **Separation of the fraction points.** -/
theorem thetaP_sep (g : AllowedGen ι 𝔪)
    (hD : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (p p' : PIdx 𝔪) (hp : residueSymbol ι 𝔪 p.1.1 (quotLift p.2) ≠ 0)
    (hp' : residueSymbol ι 𝔪 p'.1.1 (quotLift p'.2) ≠ 0) (hne : p ≠ p') {δ : ℝ}
    (hsmall : (δ * cDual F) ^ Module.finrank ℚ F *
      ((Ideal.absNorm (p.1.1 * p'.1.1) : ℝ) * Ideal.absNorm (differentIdeal ℤ (𝓞 F))) < 1)
    (k : BI F → ℤ) : ∃ i, δ ≤ |thetaP g p i - thetaP g p' i - k i| := by
  obtain ⟨hs1, hs2⟩ := fracWit_spec g p
  obtain ⟨hs1', hs2'⟩ := fracWit_spec g p'
  set β := -((quotLift p.2 : SInt 𝔪) : F) / (g.gen p.1.1 : F)
  set β' := -((quotLift p'.2 : SInt 𝔪) : F) / (g.gen p'.1.1 : F)
  set ξ := fracWit g p
  set ξ' := fracWit g p'
  have hdecomp : ξ - ξ' = (β - β') - (β - ξ) + (β' - ξ') := by ring
  apply sep_of_mul_mem hD (p.1.1 * p'.1.1) (mul_ne_zero p.1.2.1 p'.1.2.1) ξ ξ' hs2 hs2'
  · intro z hz
    have hz1 : z ∈ p.1.1 := Ideal.mul_le_left hz
    have hz2 : z ∈ p'.1.1 := Ideal.mul_le_right hz
    have hzR : algebraMap (𝓞 F) F z ∈ (placesOf 𝔪).integer F := coe_mem_integer z
    have hβz : β * algebraMap (𝓞 F) F z ∈ (placesOf 𝔪).integer F := by
      have := C3B.div_gen_mem g p.1.1 p.1.2 (algebraMap (𝓞 F) (SInt 𝔪) z)
        (Ideal.mem_map_of_mem _ hz1)
      rw [C3I.coe_alg] at this
      rw [show β * algebraMap (𝓞 F) F z = -((quotLift p.2 : SInt 𝔪) : F) *
        (algebraMap (𝓞 F) F z / (g.gen p.1.1 : F)) by simp only [β]; ring]
      exact mul_mem (neg_mem (quotLift p.2).2) this
    have hβz' : β' * algebraMap (𝓞 F) F z ∈ (placesOf 𝔪).integer F := by
      have := C3B.div_gen_mem g p'.1.1 p'.1.2 (algebraMap (𝓞 F) (SInt 𝔪) z)
        (Ideal.mem_map_of_mem _ hz2)
      rw [C3I.coe_alg] at this
      rw [show β' * algebraMap (𝓞 F) F z = -((quotLift p'.2 : SInt 𝔪) : F) *
        (algebraMap (𝓞 F) F z / (g.gen p'.1.1 : F)) by simp only [β']; ring]
      exact mul_mem (neg_mem (quotLift p'.2).2) this
    rw [hdecomp, add_mul, sub_mul, sub_mul]
    exact add_mem (sub_mem (sub_mem hβz hβz') (mul_mem hs1 hzR)) (mul_mem hs1' hzR)
  · intro hmem
    apply hne
    have hββ : β - β' ∈ (placesOf 𝔪).integer F := by
      rw [show β - β' = (ξ - ξ') + (β - ξ) - (β' - ξ') by ring]
      exact sub_mem (add_mem hmem hs1) hs1'
    have h2 : ((quotLift p'.2 : SInt 𝔪) : F) / (g.gen p'.1.1 : F) -
        ((quotLift p.2 : SInt 𝔪) : F) / (g.gen p.1.1 : F) ∈ (placesOf 𝔪).integer F := by
      convert hββ using 1; simp only [β, β']; ring
    obtain ⟨heq, hmod⟩ := frac_eq_of_sub_mem g p'.1.2 p.1.2 hp' hp h2
    obtain ⟨⟨𝔰, h𝔰⟩, x⟩ := p
    obtain ⟨⟨𝔰', h𝔰'⟩, x'⟩ := p'
    simp only at heq hmod
    subst heq
    have hx : x' = x := by
      rw [← Function.surjInv_eq Ideal.Quotient.mk_surjective x',
        ← Function.surjInv_eq Ideal.Quotient.mk_surjective x]
      exact Ideal.Quotient.eq.2 hmod
    rw [hx]
  · exact hsmall

/-- The element of a row class generates its ideal. -/
lemma span_rowElt (g : AllowedGen ι 𝔪) (r : RowClass 𝔪) :
    Ideal.span {rowElt g r} = r.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [rowElt, SClass.rep, Ideal.span_singleton_mul_left_unit (Units.isUnit _), g.span_gen _ r.1.2]

/-- **Row classes are determined by a sixth-power multiple of their element.** -/
theorem rowClass_eq_of_box (g : AllowedGen ι 𝔪) (r r' : RowClass 𝔪) (μ μ' : (SInt 𝔪)ˣ)
    (h : ((μ : SInt 𝔪) : F) ^ 6 * (rowElt g r : F) = ((μ' : SInt 𝔪) : F) ^ 6 * (rowElt g r' : F)) :
    r = r' := by
  set ν : (SInt 𝔪)ˣ := μ⁻¹ * μ'
  have hμinv : ((μ : SInt 𝔪) : F) * (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have hR : rowElt g r = (ν : SInt 𝔪) ^ 6 * rowElt g r' := by
    apply Subtype.ext
    simp only [ν, Units.val_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, mul_pow]
    have : (rowElt g r : F) = (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) ^ 6 *
        (((μ : SInt 𝔪) : F) ^ 6 * (rowElt g r : F)) := by
      rw [← mul_assoc, ← mul_pow, mul_comm (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) ((μ : SInt 𝔪) : F),
        hμinv, one_pow, one_mul]
    rw [this, h]; ring
  -- the ideals agree
  have hspan : r.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) = r'.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← span_rowElt g r, ← span_rowElt g r', hR,
      Ideal.span_singleton_mul_left_unit ((Units.isUnit ν).pow 6)]
  have h1 : r.1.1 = r'.1.1 := by
    apply le_antisymm
    · intro b hb
      apply mem_of_map_mem r'.1.1 r'.1.2.2 b
      rw [← hspan]; exact Ideal.mem_map_of_mem _ hb
    · intro b hb
      apply mem_of_map_mem r.1.1 r.1.2.2 b
      rw [hspan]; exact Ideal.mem_map_of_mem _ hb
  have h1' : r.1 = r'.1 := Subtype.ext h1
  obtain ⟨𝔟, ε⟩ := r
  obtain ⟨𝔟', ε'⟩ := r'
  simp only at h1'
  subst h1'
  -- the unit classes agree
  have hgen0 : (g.gen 𝔟.1 : F) ≠ 0 := C3B.gen_ne_zero g 𝔟.1 𝔟.2
  set u := Function.surjInv QuotientGroup.mk_surjective ε
  set u' := Function.surjInv QuotientGroup.mk_surjective ε'
  have hrep : ∀ e : SClass 𝔪, ((SClass.rep e : SInt 𝔪) : F) =
      (((Function.surjInv QuotientGroup.mk_surjective e : (placesOf 𝔪).unit F) : Fˣ) : F) :=
    fun e => rfl
  have hF : ((u : Fˣ) : F) = (((ν : SInt 𝔪) : F)) ^ 6 * ((u' : Fˣ) : F) := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) hR
    simp only [rowElt, Subalgebra.coe_mul, Subalgebra.coe_pow, hrep] at this
    apply mul_right_cancel₀ hgen0
    rw [this]; ring
  set ν' : (placesOf 𝔪).unit F := (Set.unitEquivUnitsInteger (placesOf 𝔪) F).symm ν
  have hν' : ((ν' : Fˣ) : F) = ((ν : SInt 𝔪) : F) := by
    have : Set.unitEquivUnitsInteger (placesOf 𝔪) F ν' = ν := by simp [ν']
    rw [← this]; rfl
  have hu : u = ν' ^ 6 * u' := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hν']
    exact hF
  have hε : ε = ε' := by
    rw [← Function.surjInv_eq QuotientGroup.mk_surjective ε,
      ← Function.surjInv_eq QuotientGroup.mk_surjective ε']
    change (QuotientGroup.mk u : SClass 𝔪) = QuotientGroup.mk u'
    rw [hu, QuotientGroup.mk_mul]
    have : (QuotientGroup.mk (ν' ^ 6) : SClass 𝔪) = 1 := by
      rw [QuotientGroup.eq_one_iff]; exact ⟨ν', rfl⟩
    rw [this]; exact one_mul (QuotientGroup.mk u' : SClass 𝔪)
  rw [hε]

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_Four: absolutely convergent Fourier series of a compactly supported `C²` function

`exists_fourier_expansion`: for `B : ℝ → ℂ` of class `C²` vanishing outside `[−R, R]` and any
window `[w₀, w₁]`, there are `L > 0` and `β : ℤ → ℂ` with `Σ ‖β_k‖ < ∞` and
`B w = Σ_k β_k ee(k w / L)` for `w ∈ [w₀, w₁]` (the "Fourier series in log v" of the proof of
Proposition 7.2, p. 44).
-/

namespace ArtinPrimitiveRoots.L2A

open Complex Set intervalIntegral

lemma norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (n : ℤ) : ‖fourierCoeffOn hab f n‖ ≤ M := by
  haveI : Fact (0 < b - a) := ⟨by linarith⟩
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h := norm_integral_le_of_norm_le_const (a := a) (b := b) (C := M)
    (f := fun x => fourier (-n) (x : AddCircle (b - a)) • f x) (fun x _ => by
      rw [norm_smul]
      have h1 : ‖fourier (-n) (x : AddCircle (b - a))‖ ≤ 1 := by
        have := ContinuousMap.norm_coe_le_norm (fourier (T := b - a) (-n)) (x : AddCircle (b - a))
        rwa [fourier_norm] at this
      calc ‖fourier (-n) (x : AddCircle (b - a))‖ * ‖f x‖ ≤ 1 * M :=
            mul_le_mul h1 (hM x) (norm_nonneg _) zero_le_one
        _ = M := one_mul M)
  rw [abs_of_pos (by linarith : 0 < b - a)] at h
  have hba : 0 < b - a := by linarith
  calc ‖(1 / (b - a) : ℝ)‖ * ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x‖
      ≤ ‖(1 / (b - a) : ℝ)‖ * (M * (b - a)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = M := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp

/-- A function vanishing outside `[−R, R]` has vanishing derivative outside `[−R, R]`. -/
lemma deriv_eq_zero_of_vanish {B : ℝ → ℂ} {R : ℝ} (hR : ∀ w, R < |w| → B w = 0) (w : ℝ)
    (hw : R < |w|) : deriv B w = 0 := by
  have hev : B =ᶠ[nhds w] fun _ => 0 := by
    have hopen : IsOpen {x : ℝ | R < |x|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hw] with x hx
    exact hR x hx
  rw [hev.deriv_eq]; simp

/-- **Fourier separation.** -/
theorem exists_fourier_expansion (B : ℝ → ℂ) (hB : ContDiff ℝ 2 B) (R : ℝ)
    (hR : ∀ w, R < |w| → B w = 0) (w0 w1 : ℝ) :
    ∃ (L : ℝ) (β : ℤ → ℂ), 0 < L ∧ Summable (fun k => ‖β k‖) ∧
      ∀ w ∈ Icc w0 w1, HasSum (fun k : ℤ => β k * ee (k * w / L)) (B w) := by
  classical
  set A : ℝ := min (-|R|) w0 - 1
  set L : ℝ := (max |R| w1 + 1) - A
  have hL : 0 < L := by
    simp only [L, A]
    have := min_le_left (-|R|) w0; have := le_max_left |R| w1; have := abs_nonneg R; linarith
  have : Fact (0 < L) := ⟨hL⟩
  have hAL : A < A + L := by linarith
  -- derivatives
  have hd1 : Differentiable ℝ B := hB.differentiable (by norm_num)
  have hB1 : ContDiff ℝ 1 (deriv B) := hB.iterate_deriv' 1 1
  have hd2 : Differentiable ℝ (deriv B) := hB1.differentiable (by norm_num)
  have hB2c : Continuous (deriv (deriv B)) := (hB.iterate_deriv' 0 2).continuous
  have hR1 : ∀ w, R < |w| → deriv B w = 0 := deriv_eq_zero_of_vanish hR
  have hR2 : ∀ w, R < |w| → deriv (deriv B) w = 0 := deriv_eq_zero_of_vanish hR1
  -- `B''` is bounded
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖deriv (deriv B) x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -|R|) (b := |R|)).exists_bound_of_continuousOn
      hB2c.continuousOn
    refine ⟨max M 0, fun x => ?_⟩
    by_cases hx : R < |x|
    · rw [hR2 x hx, norm_zero]; exact le_max_right _ _
    · have : x ∈ Icc (-|R|) |R| := by
        have := le_abs_self R
        constructor <;> [linarith [neg_abs_le x, (not_lt.1 hx)]; linarith [le_abs_self x,
          (not_lt.1 hx)]]
      exact (hM x this).trans (le_max_left _ _)
  -- vanishing at the window ends
  have hAout : R < |A| := by
    have h1 : A < -|R| := by simp only [A]; have := min_le_left (-|R|) w0; linarith
    have h2 : |R| < |A| := by rw [abs_of_neg (by linarith [abs_nonneg R] : A < 0)]; linarith
    linarith [le_abs_self R]
  have hBout : R < |A + L| := by
    have : A + L = max |R| w1 + 1 := by simp only [L]; ring
    rw [this, abs_of_pos (by have := le_max_left |R| w1; linarith [abs_nonneg R])]
    have := le_max_left |R| w1; linarith [le_abs_self R]
  set β : ℤ → ℂ := fun k => fourierCoeffOn hAL B k
  -- coefficient bound
  have hβ : ∀ k : ℤ, k ≠ 0 → ‖β k‖ ≤ (L / (2 * Real.pi)) ^ 2 * M / (k : ℝ) ^ 2 := by
    intro k hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have e1 := fourierCoeffOn_of_hasDerivAt hAL hk (f := B) (f' := deriv B)
      (fun x _ => (hd1 x).hasDerivAt) (hB1.continuous.intervalIntegrable _ _)
    have e2 := fourierCoeffOn_of_hasDerivAt hAL hk (f := deriv B) (f' := deriv (deriv B))
      (fun x _ => (hd2 x).hasDerivAt) (hB2c.intervalIntegrable _ _)
    rw [hR A hAout, hR (A + L) hBout, sub_self, mul_zero, zero_sub] at e1
    rw [hR1 A hAout, hR1 (A + L) hBout, sub_self, mul_zero, zero_sub] at e2
    rw [show ((A + L : ℝ) : ℂ) - (A : ℂ) = (L : ℂ) by push_cast; ring] at e1 e2
    have hc2 := norm_fourierCoeffOn_le hAL (deriv (deriv B)) hM k
    have hfac : ‖(1 / (-2 * Real.pi * I * k) : ℂ) * (-(L : ℂ))‖ = L / (2 * Real.pi * |(k : ℝ)|) := by
      rw [norm_mul, norm_div, norm_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hL]
      rw [show (-2 * (Real.pi : ℂ) * I * (k : ℂ)) = ((-2 * Real.pi * k : ℝ) : ℂ) * I by
        push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
      field_simp
    simp only [β]
    rw [e1, show (1 / (-2 * Real.pi * I * k) : ℂ) * -(L * fourierCoeffOn hAL (deriv B) k) =
      ((1 / (-2 * Real.pi * I * k) : ℂ) * (-(L : ℂ))) * fourierCoeffOn hAL (deriv B) k by ring,
      e2, show (1 / (-2 * Real.pi * I * k) : ℂ) * -(L * fourierCoeffOn hAL (deriv (deriv B)) k) =
      ((1 / (-2 * Real.pi * I * k) : ℂ) * (-(L : ℂ))) * fourierCoeffOn hAL (deriv (deriv B)) k by
        ring]
    set c : ℂ := (1 / (-2 * Real.pi * I * k) : ℂ) * (-(L : ℂ)) with hc
    rw [norm_mul c, norm_mul c, hfac]
    have hk2 : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 hkR
    have hpi := Real.pi_pos
    calc L / (2 * Real.pi * |(k : ℝ)|) * (L / (2 * Real.pi * |(k : ℝ)|) *
          ‖fourierCoeffOn hAL (deriv (deriv B)) k‖)
        ≤ L / (2 * Real.pi * |(k : ℝ)|) * (L / (2 * Real.pi * |(k : ℝ)|) * M) := by
          gcongr
      _ = (L / (2 * Real.pi)) ^ 2 * M / (k : ℝ) ^ 2 := by
          rw [show (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 from (sq_abs _).symm]
          field_simp
  have hsum : Summable (fun k => ‖β k‖) := by
    have h2 : Summable fun k : ℤ => (L / (2 * Real.pi)) ^ 2 * M * (1 / (k : ℝ) ^ 2) :=
      (Real.summable_one_div_int_pow.2 (by norm_num)).mul_left _
    have h3 : Summable fun k : ℤ => (if k = 0 then ‖β 0‖ else 0) :=
      summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp at hk; simp [hk])
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (h2.add h3)
    by_cases hk : k = 0
    · subst hk; simp
    · simp only [hk, if_false, add_zero]
      rw [mul_one_div]; exact hβ k hk
  refine ⟨L, β, hL, hsum, fun w hw => ?_⟩
  -- the continuous periodic lift
  have hcont : Continuous (AddCircle.liftIco L A B) :=
    AddCircle.liftIco_continuous (by rw [hR A hAout, hR (A + L) hBout]) hd1.continuous.continuousOn
  set f : C(AddCircle L, ℂ) := ⟨AddCircle.liftIco L A B, hcont⟩
  have hcoef : ∀ k, fourierCoeff f k = β k := fun k => fourierCoeff_liftIco_eq B k
  have hsf : Summable (fourierCoeff f) := by
    have : fourierCoeff f = β := funext hcoef
    rw [this]; exact hsum.of_norm
  have hp := has_pointwise_sum_fourier_series_of_summable hsf (w : AddCircle L)
  have hwin : w ∈ Ico A (A + L) := by
    constructor
    · simp only [A]; have := min_le_right (-|R|) w0; linarith [hw.1]
    · have : A + L = max |R| w1 + 1 := by simp only [L]; ring
      rw [this]; have := le_max_right |R| w1; linarith [hw.2]
  have hfw : f (w : AddCircle L) = B w := AddCircle.liftIco_coe_apply hwin
  rw [hfw] at hp
  convert hp using 1
  funext k
  rw [hcoef, smul_eq_mul, fourier_coe_apply, ee]
  congr 2
  push_cast; ring

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_Anal: analytic inputs for C1a

* `exists_card_absNorm_le`: `#{I : N I ≤ x} ≤ C x` for `x ≥ 1` (Mathlib's ideal asymptotics).
* `IsProbeWeight.exists_support`, `IsProbeWeight.exists_bound`.
* `sq_tsum_le`, `norm_sq_tsum_le`: weighted Cauchy–Schwarz for series.
* `exists_fourier_V`: the Fourier separation of `V(T/v)` in `log T` and `log v` (p. 44).
-/

open NumberField

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F]

variable (F) in
/-- **Ideal count.** -/
theorem exists_card_absNorm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x} : ℝ) ≤ C * x := by
  have ht := NumberField.Ideal.tendsto_norm_le_div_atTop F
  set ρ := (2 ^ NumberField.InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces F * NumberField.Units.regulator F *
    classNumber F) / (NumberField.Units.torsionOrder F * Real.sqrt |NumberField.discr F|)
  have hev := ht.eventually (Iic_mem_nhds (lt_add_one ρ))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨s₀, hs₀⟩ := hev
  set s₁ := max s₀ 1
  have hfinS : ∀ y : ℝ, ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ y}).Finite := by
    intro y
    exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊y⌋₊).subset
      (fun I (hI : (Ideal.absNorm I : ℝ) ≤ y) => (show Ideal.absNorm I ≤ ⌊y⌋₊ from
        Nat.le_floor hI))
  have hmono : ∀ y z : ℝ, y ≤ z → Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ y} ≤
      Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ z} := by
    intro y z hyz
    exact Nat.card_mono (hfinS z) (fun I (hI : (Ideal.absNorm I : ℝ) ≤ y) =>
      (show (Ideal.absNorm I : ℝ) ≤ z from hI.trans hyz))
  refine ⟨(|ρ| + 1) * s₁, by positivity, fun x hx => ?_⟩
  by_cases hxs : s₁ ≤ x
  · have h1 := hs₀ x (le_trans (le_max_left _ _) hxs)
    have hxpos : 0 < x := by linarith
    rw [div_le_iff₀ hxpos] at h1
    calc (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x} : ℝ) ≤ (ρ + 1) * x := h1
      _ ≤ (|ρ| + 1) * x := by gcongr; exact le_abs_self ρ
      _ ≤ (|ρ| + 1) * s₁ * x := by
          rw [mul_assoc]; gcongr
          calc x = 1 * x := (one_mul x).symm
            _ ≤ s₁ * x := by gcongr; exact le_max_right _ _
  · rw [not_le] at hxs
    have h1 := hs₀ s₁ (le_max_left _ _)
    have hs₁pos : 0 < s₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [div_le_iff₀ hs₁pos] at h1
    have h2 : (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x} : ℝ) ≤
        Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s₁} := by
      exact_mod_cast hmono x s₁ hxs.le
    calc (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x} : ℝ)
        ≤ (ρ + 1) * s₁ := h2.trans h1
      _ ≤ (|ρ| + 1) * s₁ := by gcongr; exact le_abs_self ρ
      _ ≤ (|ρ| + 1) * s₁ * x := by
          calc (|ρ| + 1) * s₁ = (|ρ| + 1) * s₁ * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr

/-- The support of a probe weight lies in a compact interval of `(0, ∞)`. -/
lemma isProbeWeight_exists_support {W : ℝ → ℝ} (hW : IsProbeWeight W) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x, W x ≠ 0 → a ≤ x ∧ x ≤ b := by
  obtain ⟨-, hc, hpos⟩ := hW
  by_cases hne : (tsupport W).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hc.isCompact.exists_isLeast hne
    obtain ⟨x₁, hx₁, hmax⟩ := hc.isCompact.exists_isGreatest hne
    refine ⟨x₀, x₁, hpos hx₀, hmax hx₀, fun x hx => ?_⟩
    have hxs : x ∈ tsupport W := subset_tsupport W hx
    exact ⟨hmin hxs, hmax hxs⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, 1, one_pos, le_rfl, fun x hx => ?_⟩
    have : x ∈ tsupport W := subset_tsupport W hx
    rw [hne] at this; exact absurd this (Set.notMem_empty x)

/-- A probe weight is bounded. -/
lemma isProbeWeight_exists_bound {W : ℝ → ℝ} (hW : IsProbeWeight W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |W x| ≤ M := by
  obtain ⟨hd, hc, -⟩ := hW
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn hd.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport W
  · have := hM x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]; exact le_max_right _ _

/-- Weighted Cauchy–Schwarz for real series. -/
lemma sq_tsum_le {w t : ℤ → ℝ} (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (hwt : Summable fun k => w k * t k) (hwt2 : Summable fun k => w k * t k ^ 2) :
    (∑' k, w k * t k) ^ 2 ≤ (∑' k, w k) * ∑' k, w k * t k ^ 2 := by
  set W := ∑' k, w k
  set A := ∑' k, w k * t k
  set B := ∑' k, w k * t k ^ 2
  have hW0 : 0 ≤ W := tsum_nonneg hw
  rcases hW0.eq_or_lt with h0 | hpos
  · -- all weights vanish
    have hz : ∀ k, w k = 0 := by
      intro k
      have := hws.le_tsum k (fun j _ => hw j)
      have hW' : ∑' i, w i = 0 := h0.symm
      rw [hW'] at this; exact le_antisymm this (hw k)
    have hA : A = 0 := by simp only [A, hz, zero_mul, tsum_zero]
    rw [hA, ← h0]; simp
  · set m := A / W
    have hnn : 0 ≤ ∑' k, w k * (t k - m) ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (hw k) (sq_nonneg _)
    have hexp : ∑' k, w k * (t k - m) ^ 2 = B - 2 * m * A + m ^ 2 * W := by
      have h1 : (fun k => w k * (t k - m) ^ 2) =
          fun k => (w k * t k ^ 2 - 2 * m * (w k * t k)) + m ^ 2 * w k := by
        funext k; ring
      rw [h1, Summable.tsum_add (hwt2.sub (hwt.mul_left _)) (hws.mul_left _),
        Summable.tsum_sub hwt2 (hwt.mul_left _), tsum_mul_left, tsum_mul_left]
    rw [hexp] at hnn
    have hmA : m * A = A ^ 2 / W := by simp only [m]; ring
    have hm2W : m ^ 2 * W = A ^ 2 / W := by simp only [m]; field_simp
    rw [show B - 2 * m * A + m ^ 2 * W = B - A ^ 2 / W by rw [mul_assoc, hmA, hm2W]; ring] at hnn
    have : A ^ 2 / W ≤ B := by linarith
    rw [div_le_iff₀ hpos] at this
    linarith

/-- Weighted Cauchy–Schwarz for complex series with bounded terms. -/
lemma norm_sq_tsum_le {β x : ℤ → ℂ} (hβ : Summable fun k => ‖β k‖) {X₀ : ℝ}
    (hx : ∀ k, ‖x k‖ ≤ X₀) :
    ‖∑' k, β k * x k‖ ^ 2 ≤ (∑' k, ‖β k‖) * ∑' k, ‖β k‖ * ‖x k‖ ^ 2 := by
  have hX₀ : 0 ≤ X₀ := le_trans (norm_nonneg _) (hx 0)
  have hs1 : Summable fun k => ‖β k‖ * ‖x k‖ :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_left (hx k) (norm_nonneg _)) (hβ.mul_right X₀)
  have hs2 : Summable fun k => ‖β k‖ * ‖x k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hx k) 2)
        (norm_nonneg _)) (hβ.mul_right (X₀ ^ 2))
  have hs0 : Summable fun k => β k * x k := by
    refine Summable.of_norm ?_
    simpa [norm_mul] using hs1
  have h1 : ‖∑' k, β k * x k‖ ≤ ∑' k, ‖β k‖ * ‖x k‖ := by
    refine (norm_tsum_le_tsum_norm (by simpa [norm_mul] using hs1)).trans (le_of_eq ?_)
    simp [norm_mul]
  have h2 := sq_tsum_le (w := fun k => ‖β k‖) (t := fun k => ‖x k‖) (fun k => norm_nonneg _)
    hβ hs1 hs2
  calc ‖∑' k, β k * x k‖ ^ 2 ≤ (∑' k, ‖β k‖ * ‖x k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **Fourier separation of `V(T/v)`.** -/
theorem exists_fourier_V {V : ℝ → ℝ} (hV : IsProbeWeight V) (T1 T2 a1 b1 : ℝ) (hT1 : 0 < T1)
    (ha1 : 0 < a1) :
    ∃ (L : ℝ) (β : ℤ → ℂ), 0 < L ∧ Summable (fun k => ‖β k‖) ∧
      ∀ T v : ℝ, T1 ≤ T → T ≤ T2 → a1 ≤ v → v ≤ b1 →
        HasSum (fun k : ℤ => β k * ee (k * Real.log T / L) * ee (-(k * Real.log v / L)))
          ((V (T / v) : ℝ) : ℂ) := by
  obtain ⟨a2, b2, ha2, hab2, hsupp⟩ := isProbeWeight_exists_support hV
  set B : ℝ → ℂ := fun w => ((V (Real.exp w) : ℝ) : ℂ)
  have hB : ContDiff ℝ 2 B := by
    have h1 : ContDiff ℝ 2 V := hV.1.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
    exact Complex.ofRealCLM.contDiff.comp (h1.comp Real.contDiff_exp)
  set R := max |Real.log a2| |Real.log b2|
  have hR : ∀ w, R < |w| → B w = 0 := by
    intro w hw
    simp only [B]
    by_contra hne
    have hne' : V (Real.exp w) ≠ 0 := by exact_mod_cast hne
    obtain ⟨h1, h2⟩ := hsupp _ hne'
    have hl1 : Real.log a2 ≤ w := by
      rw [← Real.log_exp w]; exact Real.log_le_log ha2 h1
    have hl2 : w ≤ Real.log b2 := by
      rw [← Real.log_exp w]; exact Real.log_le_log (Real.exp_pos w) h2
    have : |w| ≤ R := by
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log a2); have := le_max_left |Real.log a2| |Real.log b2|
        linarith
      · have := le_abs_self (Real.log b2); have := le_max_right |Real.log a2| |Real.log b2|
        linarith
    linarith
  obtain ⟨L, β, hL, hβ, hexp⟩ := exists_fourier_expansion B hB R hR
    (Real.log T1 - Real.log b1) (Real.log T2 - Real.log a1)
  refine ⟨L, β, hL, hβ, fun T v hT1' hT2' hv1 hv2 => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le hT1 hT1'
  have hvpos : 0 < v := lt_of_lt_of_le ha1 hv1
  have hw : Real.log T - Real.log v ∈ Set.Icc (Real.log T1 - Real.log b1)
      (Real.log T2 - Real.log a1) := by
    constructor
    · have := Real.log_le_log hT1 hT1'; have := Real.log_le_log hvpos hv2; linarith
    · have := Real.log_le_log hTpos hT2'; have := Real.log_le_log ha1 hv1; linarith
  have h := hexp _ hw
  have hBw : B (Real.log T - Real.log v) = ((V (T / v) : ℝ) : ℂ) := by
    simp only [B]
    rw [Real.exp_sub, Real.exp_log hTpos, Real.exp_log hvpos]
  rw [hBw] at h
  convert h using 1
  funext k
  rw [mul_assoc, ← ee_add]
  congr 2
  ring

end ArtinPrimitiveRoots.L2A
end

section
/-!
# L2A_Main: the additive-factor mass bound (C1a), modulo the cutoff

`tsum_norm_sq_additiveFactor_le_core`: under the conclusions of the cutoff (`𝔇` and the primes
above `6` lie in `S`), `Σ_r ‖additiveFactor‖² ≤ C / Y` for `1 ≤ Y ≤ X`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L2A

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The real coefficient `Y⁻¹ W₁(q/Y) (q X)^{-1/2} q^{-1/2}` of the additive factor. -/
noncomputable def cS (W₁ : ℝ → ℝ) (X Y : ℝ) (𝔰 : Ideal (𝓞 F)) : ℝ :=
  Y⁻¹ * W₁ (Ideal.absNorm 𝔰 / Y) / Real.sqrt (Ideal.absNorm 𝔰 * X) /
    Real.sqrt (Ideal.absNorm 𝔰)

lemma finite_extSet (𝔪 : Ideal (𝓞 F)) (x : ℝ) :
    ({𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰} | (Ideal.absNorm 𝔰.1 : ℝ) ≤ x}).Finite := by
  have h := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊x⌋₊)
  refine (h.preimage (Subtype.val_injective.injOn)).subset ?_
  intro 𝔰 h𝔰
  exact Nat.le_floor h𝔰

/-- Exterior ideals of norm `≤ x`. -/
noncomputable def extFin (𝔪 : Ideal (𝓞 F)) (x : ℝ) : Finset {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰} :=
  (finite_extSet 𝔪 x).toFinset

lemma mem_extFin {x : ℝ} {𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}} :
    𝔰 ∈ extFin 𝔪 x ↔ (Ideal.absNorm 𝔰.1 : ℝ) ≤ x := Set.Finite.mem_toFinset _

/-- All residues modulo an exterior ideal. -/
noncomputable def qFin (𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}) :
    Finset (SInt 𝔪 ⧸ 𝔰.1.map (algebraMap (𝓞 F) (SInt 𝔪))) :=
  (Set.finite_univ_iff.2 (finite_quot_map 𝔰.1 𝔰.2.1 𝔰.2.2)).toFinset

lemma mem_qFin (𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰})
    (x : SInt 𝔪 ⧸ 𝔰.1.map (algebraMap (𝓞 F) (SInt 𝔪))) : x ∈ qFin 𝔰 := by
  simp [qFin]

/-- The reduced fractions with denominator norm `≤ x`. -/
noncomputable def jFin (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : ℝ) : Finset (PIdx 𝔪) :=
  ((extFin 𝔪 x).sigma qFin).filter fun p => residueSymbol ι 𝔪 p.1.1 (quotLift p.2) ≠ 0

lemma absNorm_pos_of_ext (𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}) :
    (0 : ℝ) < Ideal.absNorm 𝔰.1 := by
  have : Ideal.absNorm 𝔰.1 ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔰.2.1
  exact_mod_cast Nat.pos_of_ne_zero this

/-- **The additive factor as a finite sum.** -/
lemma additiveFactor_eq_sum (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ) {b1 : ℝ}
    (hsupp : ∀ x, W₁ x ≠ 0 → x ≤ b1) {X Y : ℝ} (hY : 0 < Y) (r : RowClass 𝔪) :
    additiveFactor g W₁ V X Y r = ∑ 𝔰 ∈ extFin 𝔪 (b1 * Y),
      ((cS W₁ X Y 𝔰.1 * V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) : ℝ) : ℂ) *
        gaussSumAt g 𝔰.1 (-((rowElt g r : SInt 𝔪) : F)) := by
  unfold additiveFactor
  rw [tsum_eq_sum]
  · rfl
  · intro 𝔰 h𝔰
    rw [mem_extFin, not_le] at h𝔰
    have h1 : W₁ (Ideal.absNorm 𝔰.1 / Y) = 0 := by
      by_contra hne
      have := hsupp _ hne
      rw [div_le_iff₀ hY] at this
      linarith
    simp [h1]

/-- Outside the window `a₁a₂ ≤ N𝔟/(XY) ≤ b₁b₂` the additive factor vanishes. -/
lemma additiveFactor_eq_zero (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ) {a1 b1 a2 b2 : ℝ}
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hW : ∀ x, W₁ x ≠ 0 → a1 ≤ x ∧ x ≤ b1)
    (hV : ∀ x, V x ≠ 0 → a2 ≤ x ∧ x ≤ b2) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (r : RowClass 𝔪)
    (hT : ¬ (a1 * a2 ≤ Ideal.absNorm r.1.1 / (X * Y) ∧ Ideal.absNorm r.1.1 / (X * Y) ≤ b1 * b2)) :
    additiveFactor g W₁ V X Y r = 0 := by
  rw [additiveFactor_eq_sum g W₁ V (fun x hx => (hW x hx).2) hY r]
  refine Finset.sum_eq_zero fun 𝔰 _ => ?_
  have hq := absNorm_pos_of_ext 𝔰
  have hz : cS W₁ X Y 𝔰.1 * V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) = 0 := by
    by_contra hne
    have hw : W₁ (Ideal.absNorm 𝔰.1 / Y) ≠ 0 := by
      intro h0; apply hne; simp [cS, h0]
    have hv : V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    obtain ⟨w1, w2⟩ := hW _ hw
    obtain ⟨v1, v2⟩ := hV _ hv
    apply hT
    have heq : (Ideal.absNorm r.1.1 : ℝ) / (X * Y) =
        (Ideal.absNorm 𝔰.1 / Y) * (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) := by
      field_simp
    rw [heq]
    exact ⟨mul_le_mul w1 v1 ha2.le (le_trans ha1.le w1),
      mul_le_mul w2 v2 (le_trans ha2.le v1) (le_trans (le_trans ha1.le w1) w2)⟩
  rw [hz]; simp

/-- The coefficient of the fraction `p` in the `k`-th Fourier mode. -/
noncomputable def bCoef (ι : F →+* ℂ) (W₁ : ℝ → ℝ) (X Y L : ℝ) (k : ℤ) (p : PIdx 𝔪) : ℂ :=
  ((cS W₁ X Y p.1.1 : ℝ) : ℂ) * ee (-(k * Real.log (Ideal.absNorm p.1.1 / Y) / L)) *
    residueSymbol ι 𝔪 p.1.1 (quotLift p.2)

/-- The torus point of `p` in `Fin d` coordinates. -/
noncomputable def thF (g : AllowedGen ι 𝔪) {d : ℕ} (eB : BI F ≃ Fin d) (p : PIdx 𝔪) :
    Fin d → ℝ := fun i => thetaP g p (eB.symm i)

/-- **The Fourier–lattice expansion of the additive factor.** -/
lemma additiveFactor_hasSum (g : AllowedGen ι 𝔪)
    (hgood : ∀ 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}, ∀ P ∈ normalizedFactors 𝔰.1,
      C3B.GoodP 𝔪 P)
    (W₁ V : ℝ → ℝ) {a1 b1 : ℝ} (hW : ∀ x, W₁ x ≠ 0 → a1 ≤ x ∧ x ≤ b1) {T1 T2 L : ℝ}
    {β : ℤ → ℂ}
    (hexp : ∀ T v : ℝ, T1 ≤ T → T ≤ T2 → a1 ≤ v → v ≤ b1 →
      HasSum (fun k : ℤ => β k * ee (k * Real.log T / L) * ee (-(k * Real.log v / L)))
        ((V (T / v) : ℝ) : ℂ))
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (r : RowClass 𝔪)
    (hT1 : T1 ≤ Ideal.absNorm r.1.1 / (X * Y)) (hT2 : Ideal.absNorm r.1.1 / (X * Y) ≤ T2)
    (μ : (SInt 𝔪)ˣ) (a : 𝓞 F) (ha : (a : F) = ((μ : SInt 𝔪) : F) ^ 6 * (rowElt g r : F))
    {d : ℕ} (eB : BI F ≃ Fin d) :
    HasSum (fun k : ℤ => β k * ee (k * Real.log (Ideal.absNorm r.1.1 / (X * Y)) / L) *
      trigS (jFin ι 𝔪 (b1 * Y)) (bCoef ι W₁ X Y L k) (thF g eB) (fun i => coordZ a (eB.symm i)))
      (additiveFactor g W₁ V X Y r) := by
  classical
  set T : ℝ := Ideal.absNorm r.1.1 / (X * Y)
  rw [additiveFactor_eq_sum g W₁ V (fun x hx => (hW x hx).2) hY r]
  set G : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰} → ℂ :=
    fun 𝔰 => gaussSumAt g 𝔰.1 (-((rowElt g r : SInt 𝔪) : F))
  have hG : ∀ 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}, G 𝔰 = ∑ x ∈ qFin 𝔰,
      residueSymbol ι 𝔪 𝔰.1 (quotLift x) * ee (∑ i, (coordZ a i : ℝ) * thetaP g ⟨𝔰, x⟩ i) := by
    intro 𝔰
    simp only [G]
    rw [gaussSumAt_eq_finsum_ee g 𝔰 (hgood 𝔰) (rowElt g r) μ a ha]
    apply finsum_eq_sum_of_support_subset
    intro x _
    exact mem_qFin 𝔰 x
  have hper : ∀ 𝔰 ∈ extFin 𝔪 (b1 * Y), HasSum (fun k : ℤ => ((cS W₁ X Y 𝔰.1 : ℝ) : ℂ) *
      (β k * ee (k * Real.log T / L) * ee (-(k * Real.log (Ideal.absNorm 𝔰.1 / Y) / L))) * G 𝔰)
      (((cS W₁ X Y 𝔰.1 * V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) : ℝ) : ℂ) * G 𝔰) := by
    intro 𝔰 _
    by_cases hw : W₁ (Ideal.absNorm 𝔰.1 / Y) = 0
    · have h0 : cS W₁ X Y 𝔰.1 = 0 := by simp [cS, hw]
      simp only [h0, Complex.ofReal_zero, zero_mul]
      exact hasSum_zero
    · obtain ⟨h1, h2⟩ := hW _ hw
      have hq := absNorm_pos_of_ext 𝔰
      have h := hexp T (Ideal.absNorm 𝔰.1 / Y) hT1 hT2 h1 h2
      have hTv : T / (Ideal.absNorm 𝔰.1 / Y) = Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X) := by
        simp only [T]; field_simp
      rw [hTv] at h
      have h' := (h.mul_left ((cS W₁ X Y 𝔰.1 : ℝ) : ℂ)).mul_right (G 𝔰)
      have hval : ((cS W₁ X Y 𝔰.1 * V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) : ℝ) :
          ℂ) * G 𝔰 = ((cS W₁ X Y 𝔰.1 : ℝ) : ℂ) *
          ((V (Ideal.absNorm r.1.1 / (Ideal.absNorm 𝔰.1 * X)) : ℝ) : ℂ) * G 𝔰 := by
        push_cast; ring
      rw [hval]
      exact h'
  have hsum := hasSum_sum hper
  have key : ∀ k : ℤ, (∑ 𝔰 ∈ extFin 𝔪 (b1 * Y), ((cS W₁ X Y 𝔰.1 : ℝ) : ℂ) *
      (β k * ee (k * Real.log T / L) * ee (-(k * Real.log (Ideal.absNorm 𝔰.1 / Y) / L))) * G 𝔰) =
      β k * ee (k * Real.log T / L) *
        trigS (jFin ι 𝔪 (b1 * Y)) (bCoef ι W₁ X Y L k) (thF g eB)
          (fun i => coordZ a (eB.symm i)) := by
    intro k
    unfold trigS
    have hinner : ∀ p : PIdx 𝔪, (∑ i : Fin d, ((coordZ a (eB.symm i) : ℤ) : ℝ) * thF g eB p i) =
        ∑ j, (coordZ a j : ℝ) * thetaP g p j := by
      intro p
      exact Equiv.sum_comp eB.symm (fun j => (coordZ a j : ℝ) * thetaP g p j)
    simp_rw [hinner]
    have hfilt : ∑ p ∈ jFin ι 𝔪 (b1 * Y),
        bCoef ι W₁ X Y L k p * ee (∑ j, (coordZ a j : ℝ) * thetaP g p j) =
        ∑ p ∈ (extFin 𝔪 (b1 * Y)).sigma qFin,
          bCoef ι W₁ X Y L k p * ee (∑ j, (coordZ a j : ℝ) * thetaP g p j) := by
      apply Finset.sum_filter_of_ne
      intro p _ hp
      intro h0
      apply hp
      simp [bCoef, h0]
    rw [hfilt, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔰 _ => ?_
    rw [hG 𝔰, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [bCoef]
    ring
  simp only [key] at hsum
  exact hsum

lemma norm_sexticResidueSymbol_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have hζ := h2.choose_spec.1
    have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow]
      have : ((h2.choose : 𝓞 F) : F) ^ 6 = 1 := by exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) hζ
      rw [this, map_one]
    have hn : ‖ι (h2.choose : F)‖ ^ 6 = 1 := by rw [← norm_pow, h6, norm_one]
    have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 hn
    rw [this]
  · simp

lemma norm_residueSymbol_le (𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    calc ‖sexticResidueSymbol ι 𝔪 P x‖ * ‖((s.map fun P => sexticResidueSymbol ι 𝔪 P x).prod)‖
        ≤ 1 * 1 := mul_le_mul (norm_sexticResidueSymbol_le P x) ih (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

lemma norm_bCoef_le (W₁ : ℝ → ℝ) (X Y L : ℝ) (k : ℤ) (p : PIdx 𝔪) :
    ‖bCoef ι W₁ X Y L k p‖ ≤ |cS W₁ X Y p.1.1| := by
  unfold bCoef
  rw [norm_mul, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc |cS W₁ X Y p.1.1| * ‖residueSymbol ι 𝔪 p.1.1 (quotLift p.2)‖ ≤ |cS W₁ X Y p.1.1| * 1 :=
        mul_le_mul_of_nonneg_left (norm_residueSymbol_le _ _) (abs_nonneg _)
    _ = _ := mul_one _

/-- The trigonometric sums are bounded independently of the Fourier mode. -/
lemma norm_trigS_le (W₁ : ℝ → ℝ) (X Y L x : ℝ) (k : ℤ) {d : ℕ} (θ : PIdx 𝔪 → Fin d → ℝ)
    (n : Fin d → ℤ) :
    ‖trigS (jFin ι 𝔪 x) (bCoef ι W₁ X Y L k) θ n‖ ≤
      ∑ p ∈ jFin ι 𝔪 x, |cS W₁ X Y p.1.1| := by
  unfold trigS
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, norm_ee, mul_one]
  exact norm_bCoef_le W₁ X Y L k p

/-- The coefficient mass: `Σ_p ‖b_p‖² ≤ Σ_𝔰 N𝔰 c_𝔰²`. -/
lemma sum_norm_sq_bCoef_le (W₁ : ℝ → ℝ) (X Y L x : ℝ) (k : ℤ) :
    ∑ p ∈ jFin ι 𝔪 x, ‖bCoef ι W₁ X Y L k p‖ ^ 2 ≤
      ∑ 𝔰 ∈ extFin 𝔪 x, (Ideal.absNorm 𝔰.1 : ℝ) * cS W₁ X Y 𝔰.1 ^ 2 := by
  classical
  calc ∑ p ∈ jFin ι 𝔪 x, ‖bCoef ι W₁ X Y L k p‖ ^ 2
      ≤ ∑ p ∈ (extFin 𝔪 x).sigma qFin, ‖bCoef ι W₁ X Y L k p‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => sq_nonneg _
    _ ≤ ∑ p ∈ (extFin 𝔪 x).sigma qFin, cS W₁ X Y p.1.1 ^ 2 := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← sq_abs (cS W₁ X Y p.1.1)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_bCoef_le W₁ X Y L k p) 2
    _ = ∑ 𝔰 ∈ extFin 𝔪 x, ((qFin 𝔰).card : ℝ) * cS W₁ X Y 𝔰.1 ^ 2 := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun 𝔰 _ => ?_
        show ∑ _s ∈ qFin 𝔰, cS W₁ X Y 𝔰.1 ^ 2 = _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ 𝔰 ∈ extFin 𝔪 x, (Ideal.absNorm 𝔰.1 : ℝ) * cS W₁ X Y 𝔰.1 ^ 2 := by
        refine Finset.sum_le_sum fun 𝔰 _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h1 : (qFin 𝔰).card = Nat.card (SInt 𝔪 ⧸ 𝔰.1.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
          have : Finite (SInt 𝔪 ⧸ 𝔰.1.map (algebraMap (𝓞 F) (SInt 𝔪))) :=
            finite_quot_map 𝔰.1 𝔰.2.1 𝔰.2.2
          rw [qFin, ← Set.ncard_eq_toFinset_card _, Set.ncard_univ]
        rw [h1]
        exact_mod_cast natCard_quot_map_le 𝔰.1 𝔰.2.1 𝔰.2.2

lemma card_extFin_le {Cid : ℝ}
    (hcount : ∀ x : ℝ, 1 ≤ x → (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x} : ℝ) ≤
      Cid * x) {x x' : ℝ} (hxx' : x ≤ x') (hx' : 1 ≤ x') :
    ((extFin 𝔪 x).card : ℝ) ≤ Cid * x' := by
  classical
  have hfinS : ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ x'}).Finite :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊x'⌋₊).subset
      (fun I (hI : (Ideal.absNorm I : ℝ) ≤ x') => (show Ideal.absNorm I ≤ ⌊x'⌋₊ from
        Nat.le_floor hI))
  have h1 : (extFin 𝔪 x).card ≤ hfinS.toFinset.card := by
    rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
    refine Finset.card_le_card fun I hI => ?_
    rw [Finset.mem_map] at hI
    obtain ⟨𝔰, h𝔰, rfl⟩ := hI
    rw [Set.Finite.mem_toFinset]
    exact (mem_extFin.1 h𝔰).trans hxx'
  have h2 : hfinS.toFinset.card =
      Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x'} := by
    rw [← Set.ncard_eq_toFinset_card _ hfinS, ← Nat.card_coe_set_eq]; rfl
  calc ((extFin 𝔪 x).card : ℝ) ≤ hfinS.toFinset.card := by exact_mod_cast h1
    _ = _ := by rw [h2]
    _ ≤ Cid * x' := hcount x' hx'

/-- **The coefficient mass bound** `Σ_𝔰 N𝔰 c_𝔰² ≪ (X Y²)⁻¹`. -/
lemma sum_absNorm_cS_sq_le {W₁ : ℝ → ℝ} {a1 b1 M₁ Cid : ℝ} (ha1 : 0 < a1)
    (hW : ∀ x, W₁ x ≠ 0 → a1 ≤ x ∧ x ≤ b1) (hM : ∀ x, |W₁ x| ≤ M₁) (hCid : 0 ≤ Cid)
    (hcount : ∀ x : ℝ, 1 ≤ x → (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ x} : ℝ) ≤
      Cid * x) {X Y : ℝ} (hX : 0 < X) (hY : 1 ≤ Y) :
    ∑ 𝔰 ∈ extFin 𝔪 (b1 * Y), (Ideal.absNorm 𝔰.1 : ℝ) * cS W₁ X Y 𝔰.1 ^ 2 ≤
      Cid * max b1 1 * M₁ ^ 2 / a1 / (X * Y ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hterm : ∀ 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰},
      (Ideal.absNorm 𝔰.1 : ℝ) * cS W₁ X Y 𝔰.1 ^ 2 ≤ M₁ ^ 2 / (a1 * X * Y ^ 3) := by
    intro 𝔰
    have hq := absNorm_pos_of_ext 𝔰
    set q : ℝ := (Ideal.absNorm 𝔰.1 : ℝ)
    have hcs : q * cS W₁ X Y 𝔰.1 ^ 2 = W₁ (q / Y) ^ 2 / (Y ^ 2 * (q * X)) := by
      simp only [cS, q]
      rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      field_simp
    rw [hcs]
    by_cases hw : W₁ (q / Y) = 0
    · rw [hw]; simp; positivity
    · have hqa : a1 * Y ≤ q := by
        have := (hW _ hw).1; rwa [le_div_iff₀ hY0] at this
      have hW2 : W₁ (q / Y) ^ 2 ≤ M₁ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : a1 * Y * (X * Y ^ 2) ≤ q * (X * Y ^ 2) :=
        mul_le_mul_of_nonneg_right hqa (by positivity)
      have h3 : a1 * X * Y ^ 3 ≤ Y ^ 2 * (q * X) := by nlinarith
      exact mul_le_mul hW2 h3 (by positivity) (sq_nonneg _)
  have hx1 : (1 : ℝ) ≤ max b1 1 * Y := by nlinarith [le_max_right b1 1]
  have hcard : ((extFin 𝔪 (b1 * Y)).card : ℝ) ≤ Cid * (max b1 1 * Y) :=
    card_extFin_le hcount (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) hx1
  calc ∑ 𝔰 ∈ extFin 𝔪 (b1 * Y), (Ideal.absNorm 𝔰.1 : ℝ) * cS W₁ X Y 𝔰.1 ^ 2
      ≤ ∑ t ∈ extFin 𝔪 (b1 * Y), M₁ ^ 2 / (a1 * X * Y ^ 3) :=
        Finset.sum_le_sum fun 𝔰 _ => hterm 𝔰
    _ = (extFin 𝔪 (b1 * Y)).card * (M₁ ^ 2 / (a1 * X * Y ^ 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cid * (max b1 1 * Y)) * (M₁ ^ 2 / (a1 * X * Y ^ 3)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = Cid * max b1 1 * M₁ ^ 2 / a1 / (X * Y ^ 2) := by
        field_simp

lemma pow_le_two_pow_mul_add {d : ℕ} {A B H : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hH0 : 0 ≤ H)
    (hH : H ≤ A + B) : H ^ d ≤ 2 ^ d * (A ^ d + B ^ d) := by
  have h1 : A + B ≤ 2 * max A B := by
    have := le_max_left A B; have := le_max_right A B; linarith
  have h2 : H ^ d ≤ (2 * max A B) ^ d := pow_le_pow_left₀ hH0 (hH.trans h1) d
  rw [mul_pow] at h2
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases le_total A B with h | h
  · rw [max_eq_right h]; have := pow_nonneg hA d; linarith
  · rw [max_eq_left h]; have := pow_nonneg hB d; linarith

lemma rpow_one_div_pow {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : d ≠ 0) :
    (x ^ ((1 : ℝ) / d)) ^ d = x := by
  rw [one_div, Real.rpow_inv_natCast_pow hx hd]

set_option maxHeartbeats 4000000 in
/-- **C1a, modulo the cutoff.** -/
theorem tsum_bound_core (h𝔪 : 𝔪 ≠ ⊥)
    (hD : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (hgood : ∀ 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}, ∀ P ∈ normalizedFactors 𝔰.1,
      C3B.GoodP 𝔪 P)
    (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ) (hW₁ : IsProbeWeight W₁) (hV : IsProbeWeight V) :
    ∃ C : ℝ, ∀ X Y : ℝ, 1 ≤ Y → Y ≤ X →
      ∃ σ : ℝ, HasSum (fun r : RowClass 𝔪 => ‖additiveFactor g W₁ V X Y r‖ ^ 2) σ ∧
        σ ≤ C / Y := by
  classical
  set d := Module.finrank ℚ F with hd_def
  have hd : 0 < d := Module.finrank_pos
  have hcardBI : Fintype.card (BI F) = d := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let eB : BI F ≃ Fin d := Fintype.equivFinOfCardEq hcardBI
  obtain ⟨a1, b1, ha1, hab1, hW⟩ := isProbeWeight_exists_support hW₁
  obtain ⟨a2, b2, ha2, hab2, hVs⟩ := isProbeWeight_exists_support hV
  obtain ⟨M₁, hM₁0, hM₁⟩ := isProbeWeight_exists_bound hW₁
  obtain ⟨L, β, hL, hβ, hexp⟩ :=
    exists_fourier_V hV (a1 * a2) (b1 * b2) a1 b1 (mul_pos ha1 ha2) ha1
  obtain ⟨Cbox, hCbox0, hbox⟩ := exists_box_rep (𝔪 := 𝔪) h𝔪
  obtain ⟨Cid, hCid0, hcount⟩ := exists_card_absNorm_le F
  set Bβ := ∑' k, ‖β k‖ with hBβ_def
  have hBβ : 0 ≤ Bβ := tsum_nonneg fun k => norm_nonneg _
  set ND : ℝ := (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) with hND_def
  have hND : 1 ≤ ND := by
    have : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
    rw [hND_def]; exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  set cD := cDual F
  have hcD : 0 < cD := cDual_pos
  set e : ℝ := (1 : ℝ) / d with he_def
  have he : 0 ≤ e := by positivity
  set b1' := max b1 1
  have hb1' : 1 ≤ b1' := le_max_right _ _
  have hb1pos : 0 < b1 := lt_of_lt_of_le ha1 hab1
  have hb2pos : 0 < b2 := lt_of_lt_of_le ha2 hab2
  set K1 : ℝ := 2 * Cbox * (b1 * b2) ^ e + 4
  set K2 : ℝ := cD * (2 * b1' ^ 2 * ND) ^ e
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  set KJ : ℝ := Cid * b1' * M₁ ^ 2 / a1
  have hKJ : 0 ≤ KJ := by positivity
  set C : ℝ := Bβ ^ 2 * (8 * cK) ^ d * 2 ^ d * KJ * (K1 ^ d + K2 ^ d)
  refine ⟨C, fun X Y hY hYX => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hX0 : 0 < X := by linarith
  have hXY : 1 ≤ X * Y := by nlinarith
  -- balanced box representatives
  choose μ a ha hab using fun r : RowClass 𝔪 =>
    hbox (rowElt g r) r.1.1 r.1.2.1 (span_rowElt g r)
  set nfun : RowClass 𝔪 → Fin d → ℤ := fun r i => coordZ (a r) (eB.symm i) with hnfun
  set J := jFin ι 𝔪 (b1 * Y) with hJ
  set Vm : ℝ := b1' * Y with hVm
  have hVm1 : 1 ≤ Vm := by rw [hVm]; nlinarith
  set Q : ℝ := 2 * Vm ^ 2 * ND with hQ
  have hQ0 : 0 < Q := by positivity
  have hQe : 0 < Q ^ e := Real.rpow_pos_of_pos hQ0 _
  set δ : ℝ := 1 / (cD * Q ^ e) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδcD : (δ * cD) ^ d = 1 / Q := by
    have : δ * cD = (Q ^ e)⁻¹ := by rw [hδ_def]; field_simp
    rw [this, inv_pow, he_def, rpow_one_div_pow hQ0.le hd.ne', one_div]
  set Bn : ℕ := ⌈Cbox * (b1 * b2 * (X * Y)) ^ e⌉₊ with hBn
  set H : ℕ := 2 * Bn + 1 + ⌈1 / δ⌉₊ with hH
  have hδH : 1 ≤ δ * H := by
    have h1 := Nat.le_ceil (1 / δ)
    have h2 : ((⌈1 / δ⌉₊ : ℕ) : ℝ) ≤ H := by
      rw [hH]; push_cast; have := (Nat.cast_nonneg Bn : (0 : ℝ) ≤ Bn); linarith
    have h3 : 1 / δ ≤ (H : ℝ) := h1.trans h2
    rw [div_le_iff₀ hδ] at h3; linarith
  have hsep : ∀ p ∈ J, ∀ p' ∈ J, p ≠ p' → ∀ k : Fin d → ℤ,
      ∃ i, δ ≤ |thF g eB p i - thF g eB p' i - k i| := by
    intro p hp p' hp' hne k
    rw [hJ, jFin, Finset.mem_filter, Finset.mem_sigma, mem_extFin] at hp hp'
    have hbV : b1 * Y ≤ Vm := by rw [hVm]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le
    have hn1 : (Ideal.absNorm p.1.1 : ℝ) ≤ Vm := hp.1.1.trans hbV
    have hn2 : (Ideal.absNorm p'.1.1 : ℝ) ≤ Vm := hp'.1.1.trans hbV
    have hsmall : (δ * cD) ^ d * ((Ideal.absNorm (p.1.1 * p'.1.1) : ℝ) * ND) < 1 := by
      rw [hδcD, map_mul, Nat.cast_mul]
      have h3 : (Ideal.absNorm p.1.1 : ℝ) * Ideal.absNorm p'.1.1 * ND ≤ Vm ^ 2 * ND := by
        have := mul_le_mul hn1 hn2 (Nat.cast_nonneg _) (by linarith)
        nlinarith
      rw [one_div, inv_mul_lt_iff₀ hQ0, hQ]
      nlinarith
    obtain ⟨j, hj⟩ := thetaP_sep g hD p p' hp.2 hp'.2 hne hsmall (fun j => k (eB j))
    refine ⟨eB j, ?_⟩
    simpa [thF] using hj
  -- the large sieve for each Fourier mode
  have hcoef : ∀ k : ℤ, ∑ p ∈ J, ‖bCoef ι W₁ X Y L k p‖ ^ 2 ≤ KJ / (X * Y ^ 2) := by
    intro k
    exact (sum_norm_sq_bCoef_le W₁ X Y L (b1 * Y) k).trans
      (sum_absNorm_cS_sq_le ha1 hW hM₁ hCid0 hcount hX0 hY)
  have hLS : ∀ (k : ℤ) (s' : Finset (RowClass 𝔪)),
      (∀ r ∈ s', (Ideal.absNorm r.1.1 : ℝ) / (X * Y) ≤ b1 * b2) →
      ∑ r ∈ s', ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2 ≤
        (8 * cK) ^ d * (H : ℝ) ^ d * (KJ / (X * Y ^ 2)) := by
    intro k s' hs'
    have hinj : Set.InjOn nfun s' := by
      intro r _ r' _ heq
      have hcoord : ∀ j, coordZ (a r) j = coordZ (a r') j := fun j => by
        have := congrFun heq (eB j); simpa [nfun] using this
      have haa : a r = a r' := by
        apply (RingOfIntegers.basis F).repr.injective
        ext j; exact hcoord j
      apply rowClass_eq_of_box g r r' (μ r) (μ r')
      rw [← ha r, ← ha r', haa]
    have hbound : ∀ n ∈ s'.image nfun, ∀ i, |n i| ≤ Bn := by
      intro n hn i
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hn
      have h1 := hab r (eB.symm i)
      have h2 : (Ideal.absNorm r.1.1 : ℝ) ≤ b1 * b2 * (X * Y) := by
        have := hs' r hr; rwa [div_le_iff₀ (by positivity)] at this
      have h3 : Cbox * (Ideal.absNorm r.1.1 : ℝ) ^ ((1 : ℝ) / d) ≤
          Cbox * (b1 * b2 * (X * Y)) ^ e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) h2 he) hCbox0
      have h4 := Nat.le_ceil (Cbox * (b1 * b2 * (X * Y)) ^ e)
      have : (|nfun r i| : ℝ) ≤ Bn := by
        simp only [nfun]; push_cast; rw [hBn]; linarith
      exact_mod_cast this
    have hBH : 2 * Bn + 1 ≤ H := by rw [hH]; omega
    calc ∑ r ∈ s', ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2
        = ∑ n ∈ s'.image nfun, ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) n‖ ^ 2 :=
          (Finset.sum_image (f := fun n => ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) n‖ ^ 2)
            hinj).symm
      _ ≤ (8 * cK) ^ d * (H : ℝ) ^ d * ∑ p ∈ J, ‖bCoef ι W₁ X Y L k p‖ ^ 2 :=
          largeSieveZ_box J _ (thF g eB) (s'.image nfun) Bn H hbound hBH hδ hδH hsep
      _ ≤ (8 * cK) ^ d * (H : ℝ) ^ d * (KJ / (X * Y ^ 2)) :=
          mul_le_mul_of_nonneg_left (hcoef k) (by have := cK_nonneg; positivity)
  -- the size of the box
  have hHd : (H : ℝ) ^ d ≤ 2 ^ d * (K1 ^ d * (X * Y) + K2 ^ d * Y ^ 2) := by
    set u := (X * Y) ^ e with hu_def
    set w := (Y ^ 2) ^ e with hw_def
    have hu1 : 1 ≤ u := Real.one_le_rpow hXY he
    have hw0 : 0 ≤ w := by positivity
    have hHle : (H : ℝ) ≤ K1 * u + K2 * w := by
      have hB : (Bn : ℝ) ≤ Cbox * (b1 * b2 * (X * Y)) ^ e + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have hC : ((⌈1 / δ⌉₊ : ℕ) : ℝ) ≤ 1 / δ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      have h1 : (b1 * b2 * (X * Y)) ^ e = (b1 * b2) ^ e * u :=
        Real.mul_rpow (by positivity) (by positivity)
      have h2 : 1 / δ = K2 * w := by
        rw [hδ_def, one_div_one_div, hQ, hVm]
        rw [show 2 * (b1' * Y) ^ 2 * ND = (2 * b1' ^ 2 * ND) * Y ^ 2 by ring,
          Real.mul_rpow (by positivity) (by positivity)]
        ring
      have hHc : (H : ℝ) = 2 * Bn + 1 + ⌈1 / δ⌉₊ := by rw [hH]; push_cast; ring
      rw [hHc]
      have h5 : 2 * Cbox * (b1 * b2) ^ e * u + 4 ≤ K1 * u := by
        have : (4 : ℝ) ≤ 4 * u := by linarith
        have hK1e : K1 * u = 2 * Cbox * (b1 * b2) ^ e * u + 4 * u := by ring
        linarith
      rw [h1] at hB
      have hC' : ((⌈1 / δ⌉₊ : ℕ) : ℝ) ≤ K2 * w + 1 := by rw [← h2]; exact hC
      linarith
    have := pow_le_two_pow_mul_add (d := d) (mul_nonneg hK1 (by linarith)) (mul_nonneg hK2 hw0)
      (Nat.cast_nonneg H) hHle
    have hud : u ^ d = X * Y := rpow_one_div_pow (by positivity) hd.ne'
    have hwd : w ^ d = Y ^ 2 := rpow_one_div_pow (by positivity) hd.ne'
    rw [mul_pow, mul_pow, hud, hwd] at this
    exact this
  -- Cauchy–Schwarz in the Fourier modes
  set X₀ : ℝ := ∑ p ∈ J, |cS W₁ X Y p.1.1| with hX₀
  have hS : ∀ (k : ℤ) (r : RowClass 𝔪),
      ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ≤ X₀ := fun k r =>
    norm_trigS_le W₁ X Y L (b1 * Y) k (thF g eB) (nfun r)
  have hCS : ∀ r : RowClass 𝔪, a1 * a2 ≤ (Ideal.absNorm r.1.1 : ℝ) / (X * Y) →
      (Ideal.absNorm r.1.1 : ℝ) / (X * Y) ≤ b1 * b2 →
      ‖additiveFactor g W₁ V X Y r‖ ^ 2 ≤
        Bβ * ∑' k, ‖β k‖ * ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2 := by
    intro r h1 h2
    have hs := additiveFactor_hasSum g hgood W₁ V hW hexp hX0 hY0 r h1 h2 (μ r) (a r) (ha r) eB
    rw [← hs.tsum_eq]
    set x : ℤ → ℂ := fun k => ee (k * Real.log ((Ideal.absNorm r.1.1 : ℝ) / (X * Y)) / L) *
      trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)
    have hxn : ∀ k, ‖x k‖ = ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ := fun k => by
      simp only [x]; rw [norm_mul, norm_ee, one_mul]
    have hcs := norm_sq_tsum_le (β := β) (x := x) hβ (X₀ := X₀) (fun k => (hxn k).le.trans (hS k r))
    have hfun : (fun k => β k * ee (k * Real.log ((Ideal.absNorm r.1.1 : ℝ) / (X * Y)) / L) *
        trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)) = fun k => β k * x k := by
      funext k; simp only [x]; ring
    rw [hfun]
    refine hcs.trans (le_of_eq ?_)
    rw [hBβ_def]
    simp_rw [hxn]
  -- finite partial sums
  have hC_def : C = Bβ ^ 2 * (8 * cK) ^ d * 2 ^ d * KJ * (K1 ^ d + K2 ^ d) := rfl
  clear_value X₀ H Bn δ Q Vm nfun J C KJ K1 K2 b1' e cD ND Bβ
  obtain ⟨LSB, hLSB⟩ : ∃ x : ℝ, x = (8 * cK) ^ d * (H : ℝ) ^ d * (KJ / (X * Y ^ 2)) := ⟨_, rfl⟩
  have hcK := cK_nonneg
  have hLSB0 : 0 ≤ LSB := by
    rw [hLSB]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) d) (pow_nonneg (Nat.cast_nonneg _) d))
      (div_nonneg hKJ (by positivity))
  have hLS' : ∀ (k : ℤ) (s' : Finset (RowClass 𝔪)),
      (∀ r ∈ s', (Ideal.absNorm r.1.1 : ℝ) / (X * Y) ≤ b1 * b2) →
      ∑ r ∈ s', ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2 ≤ LSB := by
    intro k s' hs'; rw [hLSB]; exact hLS k s' hs'
  have hfin : ∀ s : Finset (RowClass 𝔪),
      ∑ r ∈ s, ‖additiveFactor g W₁ V X Y r‖ ^ 2 ≤ C / Y := by
    intro s
    set s' := s.filter (fun r => a1 * a2 ≤ (Ideal.absNorm r.1.1 : ℝ) / (X * Y) ∧
      (Ideal.absNorm r.1.1 : ℝ) / (X * Y) ≤ b1 * b2) with hs'
    have hzero : ∑ r ∈ s, ‖additiveFactor g W₁ V X Y r‖ ^ 2 =
        ∑ r ∈ s', ‖additiveFactor g W₁ V X Y r‖ ^ 2 := by
      rw [hs']; symm
      apply Finset.sum_filter_of_ne
      intro r _ hr
      by_contra hc
      apply hr
      rw [additiveFactor_eq_zero g W₁ V ha1 ha2 hW hVs hX0 hY0 r hc]; simp
    have hs'T : ∀ r ∈ s', (Ideal.absNorm r.1.1 : ℝ) / (X * Y) ≤ b1 * b2 :=
      fun r hr => (Finset.mem_filter.1 hr).2.2
    have hsumm : ∀ r ∈ s', Summable (fun k : ℤ =>
        ‖β k‖ * ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2) := by
      intro r _
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hβ.mul_right (X₀ ^ 2))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hS k r) 2) (norm_nonneg _)
    have hsumm2 : Summable (fun k : ℤ => ‖β k‖ *
        ∑ r ∈ s', ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hβ.mul_right LSB)
      exact mul_le_mul_of_nonneg_left (hLS' k s' hs'T) (norm_nonneg _)
    have hmain : Bβ ^ 2 * LSB ≤ C / Y := by
      have hA : (H : ℝ) ^ d * (KJ / (X * Y ^ 2)) ≤ 2 ^ d * KJ * (K1 ^ d + K2 ^ d) / Y := by
        calc (H : ℝ) ^ d * (KJ / (X * Y ^ 2))
            ≤ 2 ^ d * (K1 ^ d * (X * Y) + K2 ^ d * Y ^ 2) * (KJ / (X * Y ^ 2)) :=
              mul_le_mul_of_nonneg_right hHd (by positivity)
          _ = 2 ^ d * KJ * (K1 ^ d / Y + K2 ^ d / X) := by field_simp
          _ ≤ 2 ^ d * KJ * (K1 ^ d / Y + K2 ^ d / Y) := by
              gcongr
          _ = 2 ^ d * KJ * (K1 ^ d + K2 ^ d) / Y := by ring
      calc Bβ ^ 2 * LSB = Bβ ^ 2 * (8 * cK) ^ d * ((H : ℝ) ^ d * (KJ / (X * Y ^ 2))) := by
            rw [hLSB]; ring
        _ ≤ Bβ ^ 2 * (8 * cK) ^ d * (2 ^ d * KJ * (K1 ^ d + K2 ^ d) / Y) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = C / Y := by rw [hC_def]; ring
    calc ∑ r ∈ s, ‖additiveFactor g W₁ V X Y r‖ ^ 2
        = ∑ r ∈ s', ‖additiveFactor g W₁ V X Y r‖ ^ 2 := hzero
      _ ≤ ∑ r ∈ s', Bβ * ∑' k, ‖β k‖ *
            ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2 :=
          Finset.sum_le_sum fun r hr =>
            hCS r (Finset.mem_filter.1 hr).2.1 (Finset.mem_filter.1 hr).2.2
      _ = Bβ * ∑' k, ‖β k‖ *
            ∑ r ∈ s', ‖trigS J (bCoef ι W₁ X Y L k) (thF g eB) (nfun r)‖ ^ 2 := by
          rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsumm]
          congr 1
          refine tsum_congr fun k => ?_
          rw [Finset.mul_sum]
      _ ≤ Bβ * ∑' k : ℤ, ‖β k‖ * LSB := by
          refine mul_le_mul_of_nonneg_left ?_ hBβ
          exact Summable.tsum_le_tsum
            (fun k => mul_le_mul_of_nonneg_left (hLS' k s' hs'T) (norm_nonneg _)) hsumm2
            (hβ.mul_right _)
      _ = Bβ ^ 2 * LSB := by rw [tsum_mul_right, ← hBβ_def]; ring
      _ ≤ C / Y := hmain
  exact ⟨_, (summable_of_sum_le (fun r => sq_nonneg _) hfin).hasSum,
    Real.tsum_le_of_sum_le (fun r => sq_nonneg _) hfin⟩

end ArtinPrimitiveRoots.L2A
end

section
/-! # L2A_Chk: C1a `exists_cutoff_tsum_norm_sq_additiveFactor_le` (02b132d6), stub verbatim -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

lemma L2A.sup_eq_top_of_not_le {F : Type*} [Field F] [NumberField F] {𝔪 P : Ideal (𝓞 F)}
    (hP : P.IsMaximal) (h : ¬ 𝔪 ≤ P) : P ⊔ 𝔪 = ⊤ := by
  by_contra hne
  apply h
  have h1 : P = P ⊔ 𝔪 := hP.eq_of_le hne le_sup_left
  rw [h1]; exact le_sup_right

end ArtinPrimitiveRoots
end

section
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open ArtinPrimitiveRoots
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (W₁ V : ℝ → ℝ), IsProbeWeight W₁ → IsProbeWeight V →
        ∃ C : ℝ, ∀ X Y : ℝ, 1 ≤ Y → Y ≤ X →
          ∃ σ : ℝ, HasSum (fun r : RowClass 𝔪 => ‖additiveFactor g W₁ V X Y r‖ ^ 2) σ ∧
            σ ≤ C / Y := by
  refine ⟨C3I.cutN F, fun 𝔪 h𝔪 hsm g W₁ V hW₁ hV => ?_⟩
  have hD : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
    intro v hv
    have hext : IsExterior 𝔪 v.asIdeal := ⟨v.ne_bot, L2A.sup_eq_top_of_not_le v.isMaximal hv⟩
    exact (C3I.good_of_exterior n hn0 hn le_rfl hsm v.isPrime hext).diff
  have hgood : ∀ 𝔰 : {𝔰 : Ideal (𝓞 F) // IsExterior 𝔪 𝔰}, ∀ P ∈ normalizedFactors 𝔰.1,
      C3B.GoodP 𝔪 P := by
    intro 𝔰 P hP
    have hPp : Prime P := prime_of_normalized_factor P hP
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp
    have hP0 : P ≠ ⊥ := hPp.ne_zero
    have hle : 𝔰.1 ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
    have hnot : ¬ 𝔪 ≤ P := fun h => hPprime.ne_top (eq_top_iff.2 (𝔰.2.2 ▸ sup_le hle h))
    have hext : IsExterior 𝔪 P := ⟨hP0, L2A.sup_eq_top_of_not_le (hPprime.isMaximal hP0) hnot⟩
    have hgd := C3I.good_of_exterior n hn0 hn le_rfl hsm hPprime hext
    exact ⟨hPprime, hP0, hnot, Nat.dvd_trans (by norm_num : 6 ∣ 12) hgd.twelve⟩
  exact L2A.tsum_bound_core h𝔪 hD hgood g W₁ V hW₁ hV
end
