-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:43:17.492221+00:00
-- url     : https://prove2.me/submissions/b94d557a-973d-4681-8910-bd9f2c0a6014

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
import Mathlib

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

/-- An exterior prime is good. -/
theorem goodP_of_exterior (n : ℕ) (hn0 : 0 < n) (hn : 6 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : 3 ^ Module.finrank ℤ (𝓞 F) ≤ N₀) {𝔪 : Ideal (𝓞 F)}
    (hsm : SmallPrimesDvd N₀ 𝔪) {P : Ideal (𝓞 F)} (hPi : P.IsPrime) (hP : IsExterior 𝔪 P) :
    GoodP 𝔪 P := by
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hPi.ne_top
    rw [eq_top_iff, ← hP.2]
    exact sup_le le_rfl h
  refine ⟨hPi, hP.1, h𝔪, six_dvd_absNorm_sub_one n hn0 hn P hPi hP.1 ?_⟩
  by_contra hcon
  exact h𝔪 (hsm P hPi hP.1 (by omega))

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

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

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

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3H_Core: finite bilinear-form bounds and the row-multiplication step (GL Lemma 4.4)

`SBf χ R Cs v`: for every coefficient vector `z`, `∑_{a ∈ R} |∑_{c ∈ Cs} z c χ a c|² ≤ v ∑ |z c|²`.

* `SBf.mono_rows`, `SBf.union`, `SBf.biUnion`: row-set bookkeeping.
* `SBf.of_inj`: rows that map injectively into `R'` with `χ a c = w c χ (f a) c`, `‖w c‖ ≤ 1`.
* `SBf.lift`: Heath-Brown's Lemma 9 (GL Lemma 4.4) in abstract form: if rows can be multiplied by
  any of a family `P` of "primes", each row or column being divisible by at most `ω` of them and
  `8 ω ≤ #P`, then a bound `W` for the multiplied rows gives the bound `8 W`.
-/

namespace L3H

open Finset

variable {I : Type*}

/-- The finite sieve-form bound. -/
def SBf (χ : I → I → ℂ) (R Cs : Finset I) (v : ℝ) : Prop :=
  ∀ z : I → ℂ, ∑ a ∈ R, ‖∑ c ∈ Cs, z c * χ a c‖ ^ 2 ≤ v * ∑ c ∈ Cs, ‖z c‖ ^ 2

variable {χ : I → I → ℂ}

theorem SBf.mono_v {R Cs : Finset I} {v v' : ℝ} (h : SBf χ R Cs v) (hv : v ≤ v') :
    SBf χ R Cs v' := fun z =>
  (h z).trans (mul_le_mul_of_nonneg_right hv (sum_nonneg fun _ _ => by positivity))

theorem SBf.mono_rows {R R' Cs : Finset I} {v : ℝ} (h : SBf χ R' Cs v) (hR : R ⊆ R') :
    SBf χ R Cs v := fun z =>
  le_trans (sum_le_sum_of_subset_of_nonneg hR fun _ _ _ => by positivity) (h z)

theorem SBf.union [DecidableEq I] {R₁ R₂ Cs : Finset I} {v₁ v₂ : ℝ} (h₁ : SBf χ R₁ Cs v₁)
    (h₂ : SBf χ R₂ Cs v₂) : SBf χ (R₁ ∪ R₂) Cs (v₁ + v₂) := fun z => by
  refine (sum_union_le_of_nonneg ?_).trans ?_
  · intro _ _; positivity
  · rw [add_mul]; exact add_le_add (h₁ z) (h₂ z)
where
  sum_union_le_of_nonneg {f : I → ℝ} (hf : ∀ a ∈ R₁ ∪ R₂, 0 ≤ f a) :
      ∑ a ∈ R₁ ∪ R₂, f a ≤ ∑ a ∈ R₁, f a + ∑ a ∈ R₂, f a := by
    rw [← sum_union_inter]
    exact le_add_of_nonneg_right (sum_nonneg fun a ha => hf a (mem_union_left _
      (mem_inter.1 ha).1))

theorem SBf.biUnion [DecidableEq I] {J : Type*} (s : Finset J) (R : J → Finset I) (Cs : Finset I)
    (v : J → ℝ) (h : ∀ j ∈ s, SBf χ (R j) Cs (v j)) :
    SBf χ (s.biUnion R) Cs (∑ j ∈ s, v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro z; simp
  | insert j s hj ih =>
    rw [biUnion_insert, sum_insert hj]
    exact (h j (mem_insert_self _ _)).union (ih fun k hk => h k (mem_insert_of_mem hk))

/-- Cauchy–Schwarz: some bound always holds. -/
theorem SBf.trivial (R Cs : Finset I) :
    SBf χ R Cs (∑ a ∈ R, ∑ c ∈ Cs, ‖χ a c‖ ^ 2) := fun z => by
  rw [sum_mul]
  refine sum_le_sum fun a _ => ?_
  calc ‖∑ c ∈ Cs, z c * χ a c‖ ^ 2 ≤ (∑ c ∈ Cs, ‖z c‖ * ‖χ a c‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans ?_
        exact le_of_eq (sum_congr rfl fun c _ => norm_mul _ _)
    _ ≤ (∑ c ∈ Cs, ‖z c‖ ^ 2) * ∑ c ∈ Cs, ‖χ a c‖ ^ 2 := inner_mul_le_norm_mul_norm_sq' _ _ _
    _ = (∑ c ∈ Cs, ‖χ a c‖ ^ 2) * ∑ c ∈ Cs, ‖z c‖ ^ 2 := mul_comm _ _
where
  inner_mul_le_norm_mul_norm_sq' (s : Finset I) (f g : I → ℝ) :
      (∑ c ∈ s, f c * g c) ^ 2 ≤ (∑ c ∈ s, f c ^ 2) * ∑ c ∈ s, g c ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s f g

theorem SBf.nonneg_of {R Cs : Finset I} {v : ℝ} (h : SBf χ R Cs v) (c₀ : I) (hc₀ : c₀ ∈ Cs) :
    0 ≤ v := by
  classical
  have := h (fun c => if c = c₀ then 1 else 0)
  have hs : ∑ c ∈ Cs, ‖(if c = c₀ then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    rw [sum_eq_single c₀ (fun b _ hb => by simp [hb]) (fun h => absurd hc₀ h)]; simp
  rw [hs, mul_one] at this
  exact le_trans (sum_nonneg fun _ _ => by positivity) this

/-- Re-indexing rows through an injective map. -/
theorem SBf.of_inj {R R' Cs : Finset I} {W : ℝ} (hW : SBf χ R' Cs W) (f : I → I)
    (hf : Set.InjOn f R) (hfR : ∀ a ∈ R, f a ∈ R') (w : I → ℂ) (hw : ∀ c ∈ Cs, ‖w c‖ ≤ 1)
    (hχ : ∀ a ∈ R, ∀ c ∈ Cs, χ a c = w c * χ (f a) c) : SBf χ R Cs W := by
  classical
  intro z
  have h1 : ∑ a ∈ R, ‖∑ c ∈ Cs, z c * χ a c‖ ^ 2 =
      ∑ r ∈ R.image f, ‖∑ c ∈ Cs, (z c * w c) * χ r c‖ ^ 2 := by
    rw [sum_image hf]
    refine sum_congr rfl fun a ha => ?_
    congr 2
    refine sum_congr rfl fun c hc => ?_
    rw [hχ a ha c hc]; ring
  rw [h1]
  have hsub : R.image f ⊆ R' := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hr
    exact hfR a ha
  refine le_trans (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) ?_
  refine (hW _).trans ?_
  have hW0 : 0 ≤ W ∨ Cs = ∅ := by
    by_cases hC : Cs = ∅
    · exact Or.inr hC
    · obtain ⟨c₀, hc₀⟩ := nonempty_iff_ne_empty.2 hC
      exact Or.inl (hW.nonneg_of c₀ hc₀)
  rcases hW0 with hW0 | hC
  · refine mul_le_mul_of_nonneg_left (sum_le_sum fun c hc => ?_) hW0
    rw [norm_mul, mul_pow]
    have := hw c hc
    have h0 : 0 ≤ ‖w c‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z c‖, pow_le_one₀ h0 this (n := 2)]
  · simp [hC]

theorem SBf.mono_cols {R Cs Cs' : Finset I} {v : ℝ} (h : SBf χ R Cs v) (hC : Cs' ⊆ Cs) :
    SBf χ R Cs' v := by
  classical
  intro z
  have := h (fun c => if c ∈ Cs' then z c else 0)
  have e1 : ∀ a, ∑ c ∈ Cs, (if c ∈ Cs' then z c else 0) * χ a c = ∑ c ∈ Cs', z c * χ a c := by
    intro a
    rw [← sum_subset hC (f := fun c => (if c ∈ Cs' then z c else 0) * χ a c)]
    · exact sum_congr rfl fun c hc => by rw [if_pos hc]
    · intro c _ hc; rw [if_neg hc, zero_mul]
  have e2 : ∑ c ∈ Cs, ‖(if c ∈ Cs' then z c else 0)‖ ^ 2 = ∑ c ∈ Cs', ‖z c‖ ^ 2 := by
    rw [← sum_subset hC (f := fun c => ‖(if c ∈ Cs' then z c else 0)‖ ^ 2)]
    · exact sum_congr rfl fun c hc => by rw [if_pos hc]
    · intro c _ hc; simp [hc]
  simp only [e1, e2] at this
  exact this

lemma norm_add_sq_le_two (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h0 : 0 ≤ ‖x + y‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

lemma sum_filter_card_le [DecidableEq I] (P S : Finset I) (dvd : I → I → Prop) [DecidableRel dvd]
    (g : I → ℝ) (hg : ∀ a ∈ S, 0 ≤ g a) (ω : ℕ)
    (hc : ∀ a ∈ S, (P.filter (fun p => dvd p a)).card ≤ ω) :
    ∑ p ∈ P, ∑ a ∈ S.filter (fun a => dvd p a), g a ≤ ω * ∑ a ∈ S, g a := by
  have : ∑ p ∈ P, ∑ a ∈ S.filter (fun a => dvd p a), g a =
      ∑ a ∈ S, (P.filter (fun p => dvd p a)).card * g a := by
    simp_rw [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [card_filter, Nat.cast_sum, sum_mul]
    exact sum_congr rfl fun p _ => by split_ifs <;> simp
  rw [this, mul_sum]
  exact sum_le_sum fun a ha => mul_le_mul_of_nonneg_right (by exact_mod_cast hc a ha) (hg a ha)

/-- One step of Heath-Brown's Lemma 9: `v ↦ (8/3) W + (2/3) v`. -/
theorem SBf.lift_step [DecidableEq I] {R R' Cs P : Finset I} {W v : ℝ} (hW0 : 0 ≤ W)
    (hW : SBf χ R' Cs W) (hv0 : 0 ≤ v) (hv : SBf χ R Cs v)
    (dvd : I → I → Prop) [DecidableRel dvd] (mul : I → I → I) (w : I → I → ℂ)
    (ω : ℕ) (hP : 8 * ω ≤ P.card) (hPne : P.Nonempty)
    (hcR : ∀ a ∈ R, (P.filter (fun p => dvd p a)).card ≤ ω)
    (hcC : ∀ c ∈ Cs, (P.filter (fun p => dvd p c)).card ≤ ω)
    (hmulR : ∀ p ∈ P, ∀ a ∈ R, ¬ dvd p a → mul a p ∈ R')
    (hinj : ∀ p ∈ P, Set.InjOn (fun a => mul a p) (R.filter (fun a => ¬ dvd p a)))
    (hw : ∀ p ∈ P, ∀ c ∈ Cs, ‖w p c‖ ≤ 1)
    (hχ : ∀ p ∈ P, ∀ a ∈ R, ¬ dvd p a → ∀ c ∈ Cs, ¬ dvd p c →
      χ a c = w p c * χ (mul a p) c) :
    SBf χ R Cs (8 / 3 * W + 2 / 3 * v) := by
  intro z
  set S : I → ℂ := fun a => ∑ c ∈ Cs, z c * χ a c with hS
  set T := ∑ a ∈ R, ‖S a‖ ^ 2 with hT
  set Z := ∑ c ∈ Cs, ‖z c‖ ^ 2 with hZ
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => by positivity
  have hZ0 : 0 ≤ Z := sum_nonneg fun _ _ => by positivity
  change T ≤ (8 / 3 * W + 2 / 3 * v) * Z
  by_cases hTz : T = 0
  · rw [hTz]; positivity
  have hTp : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hTz)
  have hZp : 0 < Z := by
    rcases lt_or_eq_of_le hZ0 with h | h
    · exact h
    exfalso
    have hz : ∀ c ∈ Cs, z c = 0 := by
      intro c hc
      have := (sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)).1 h.symm c hc
      simpa using this
    apply hTz
    refine sum_eq_zero fun a _ => ?_
    have : S a = 0 := sum_eq_zero fun c hc => by rw [hz c hc, zero_mul]
    rw [this]; simp
  -- choose a good prime
  set f : I → ℝ := fun p => (∑ a ∈ R.filter (fun a => dvd p a), ‖S a‖ ^ 2) * Z +
    (∑ c ∈ Cs.filter (fun c => dvd p c), ‖z c‖ ^ 2) * T with hf
  have hsumf : ∑ p ∈ P, f p ≤ ∑ p ∈ P, T * Z / 4 := by
    have h1 := sum_filter_card_le P R dvd (fun a => ‖S a‖ ^ 2) (fun _ _ => by positivity) ω hcR
    have h2 := sum_filter_card_le P Cs dvd (fun c => ‖z c‖ ^ 2) (fun _ _ => by positivity) ω hcC
    rw [sum_const, nsmul_eq_mul]
    simp only [hf, sum_add_distrib, ← sum_mul]
    have hP' : (8 * ω : ℝ) ≤ P.card := by exact_mod_cast hP
    have hTZ : 0 ≤ T * Z := mul_nonneg hT0 hZ0
    calc (∑ p ∈ P, ∑ a ∈ R.filter (fun a => dvd p a), ‖S a‖ ^ 2) * Z +
          (∑ p ∈ P, ∑ c ∈ Cs.filter (fun c => dvd p c), ‖z c‖ ^ 2) * T
        ≤ (ω * T) * Z + (ω * Z) * T := by gcongr
      _ = (8 * ω) * (T * Z / 4) := by ring
      _ ≤ P.card * (T * Z / 4) := by gcongr
  obtain ⟨p, hp, hfp⟩ := exists_le_of_sum_le hPne hsumf
  set Rb := ∑ a ∈ R.filter (fun a => dvd p a), ‖S a‖ ^ 2 with hRb
  set Cb := ∑ c ∈ Cs.filter (fun c => dvd p c), ‖z c‖ ^ 2 with hCb
  have hRb0 : 0 ≤ Rb := sum_nonneg fun _ _ => by positivity
  have hCb0 : 0 ≤ Cb := sum_nonneg fun _ _ => by positivity
  have hRb4 : Rb ≤ T / 4 := by
    have : Rb * Z ≤ T * Z / 4 := by
      have := hfp; simp only [hf] at this; nlinarith [mul_nonneg hCb0 hT0]
    have h := (mul_le_mul_iff_of_pos_right hZp).1 (show Rb * Z ≤ (T / 4) * Z by linarith)
    exact h
  have hCb4 : Cb ≤ Z / 4 := by
    have : Cb * T ≤ T * Z / 4 := by
      have := hfp; simp only [hf] at this; nlinarith [mul_nonneg hRb0 hZ0]
    exact (mul_le_mul_iff_of_pos_right hTp).1 (show Cb * T ≤ (Z / 4) * T by linarith)
  -- good rows carry 3/4 of the mass
  set Rg := R.filter (fun a => ¬ dvd p a) with hRg
  set Cg := Cs.filter (fun c => ¬ dvd p c) with hCg
  have hsplit : T = (∑ a ∈ Rg, ‖S a‖ ^ 2) + Rb := by
    rw [hT, hRg, hRb, add_comm]; exact (sum_filter_add_sum_filter_not R _ _).symm
  -- columns split
  have hSa : ∀ a, S a = (∑ c ∈ Cg, z c * χ a c) +
      ∑ c ∈ Cs, (if dvd p c then z c else 0) * χ a c := by
    intro a
    rw [hS, hCg, sum_filter]
    simp only
    rw [← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  have hgood : ∑ a ∈ Rg, ‖∑ c ∈ Cg, z c * χ a c‖ ^ 2 ≤ W * Z := by
    have hW' : SBf χ R' Cg W := hW.mono_cols (filter_subset _ _)
    have hRgs : SBf χ Rg Cg W := by
      refine hW'.of_inj (fun a => mul a p) (hinj p hp) (fun a ha => ?_) (w p)
        (fun c hc => hw p hp c (mem_filter.1 hc).1) (fun a ha c hc => ?_)
      · exact hmulR p hp a (mem_filter.1 ha).1 (mem_filter.1 ha).2
      · exact hχ p hp a (mem_filter.1 ha).1 (mem_filter.1 ha).2 c (mem_filter.1 hc).1
          (mem_filter.1 hc).2
    refine (hRgs z).trans (mul_le_mul_of_nonneg_left ?_ hW0)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have hbad : ∑ a ∈ Rg, ‖∑ c ∈ Cs, (if dvd p c then z c else 0) * χ a c‖ ^ 2 ≤ v * Cb := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun _ _ _ => by positivity) ?_
    refine (hv _).trans (le_of_eq ?_)
    rw [hCb, sum_filter]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    split_ifs <;> simp
  have hRg_le : ∑ a ∈ Rg, ‖S a‖ ^ 2 ≤ 2 * (W * Z) + 2 * (v * Cb) := by
    calc ∑ a ∈ Rg, ‖S a‖ ^ 2 ≤ ∑ a ∈ Rg, (2 * ‖∑ c ∈ Cg, z c * χ a c‖ ^ 2 +
          2 * ‖∑ c ∈ Cs, (if dvd p c then z c else 0) * χ a c‖ ^ 2) := by
          refine sum_le_sum fun a _ => ?_
          rw [hSa a]; exact norm_add_sq_le_two _ _
      _ = 2 * ∑ a ∈ Rg, ‖∑ c ∈ Cg, z c * χ a c‖ ^ 2 +
          2 * ∑ a ∈ Rg, ‖∑ c ∈ Cs, (if dvd p c then z c else 0) * χ a c‖ ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ 2 * (W * Z) + 2 * (v * Cb) := by gcongr
  have hvCb : v * Cb ≤ v * (Z / 4) := mul_le_mul_of_nonneg_left hCb4 hv0
  nlinarith

/-- Heath-Brown's Lemma 9 (GL Lemma 4.4), abstract form. -/
theorem SBf.lift [DecidableEq I] {R R' Cs P : Finset I} {W : ℝ} (hW0 : 0 ≤ W)
    (hW : SBf χ R' Cs W)
    (dvd : I → I → Prop) [DecidableRel dvd] (mul : I → I → I) (w : I → I → ℂ)
    (ω : ℕ) (hP : 8 * ω ≤ P.card) (hPne : P.Nonempty)
    (hcR : ∀ a ∈ R, (P.filter (fun p => dvd p a)).card ≤ ω)
    (hcC : ∀ c ∈ Cs, (P.filter (fun p => dvd p c)).card ≤ ω)
    (hmulR : ∀ p ∈ P, ∀ a ∈ R, ¬ dvd p a → mul a p ∈ R')
    (hinj : ∀ p ∈ P, Set.InjOn (fun a => mul a p) (R.filter (fun a => ¬ dvd p a)))
    (hw : ∀ p ∈ P, ∀ c ∈ Cs, ‖w p c‖ ≤ 1)
    (hχ : ∀ p ∈ P, ∀ a ∈ R, ¬ dvd p a → ∀ c ∈ Cs, ¬ dvd p c →
      χ a c = w p c * χ (mul a p) c) :
    SBf χ R Cs (8 * W) := by
  set v₀ := max (∑ a ∈ R, ∑ c ∈ Cs, ‖χ a c‖ ^ 2) (8 * W) with hv₀
  have hd : 0 ≤ v₀ - 8 * W := sub_nonneg.2 (le_max_right _ _)
  have hk : ∀ k : ℕ, SBf χ R Cs (8 * W + (2 / 3) ^ k * (v₀ - 8 * W)) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul, add_sub_cancel]
      exact (SBf.trivial R Cs).mono_v (le_max_left _ _)
    | succ k ih =>
      have h0 : 0 ≤ 8 * W + (2 / 3) ^ k * (v₀ - 8 * W) := by positivity
      have := SBf.lift_step hW0 hW h0 ih dvd mul w ω hP hPne hcR hcC hmulR hinj hw hχ
      refine this.mono_v (le_of_eq ?_)
      ring
  intro z
  have hlim : Filter.Tendsto (fun k : ℕ => (8 * W + (2 / 3 : ℝ) ^ k * (v₀ - 8 * W)) *
      ∑ c ∈ Cs, ‖z c‖ ^ 2) Filter.atTop (nhds ((8 * W + 0 * (v₀ - 8 * W)) *
        ∑ c ∈ Cs, ‖z c‖ ^ 2)) := by
    refine Filter.Tendsto.mul_const _ (Filter.Tendsto.const_add _ (Filter.Tendsto.mul_const _ ?_))
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp only [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun k => hk k z

end L3H

end
end

section
section
/-! # L3H_NT: the quadratic family `χ_𝔠(𝔡) = residueSymbol 𝔡 (gen 𝔠)³` as a finite kernel

* `rowsF 𝔪 lo hi`: exterior squarefree ideals with `lo < N 𝔡 ≤ hi`, as a `Finset`.
* `chiK ι 𝔪 g 𝔡 𝔠 = residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3`.
* `chiK_mul_row`: `χ(a) = w · χ(a p)` with `‖w‖ = 1` for an exterior good prime `p ∤ 𝔠`.
* `sb_iff_dyadic`, `sb_of_SBf`: the `tsum`-over-subtypes statements against `SBf`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

/-! ### Residue symbols -/

lemma rs_mul {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma rs_prime {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (x : SInt 𝔪) : residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [normalizedFactors_irreducible hirr, normalize_eq]
  simp

lemma gen_not_mem {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {P c : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hPm : ¬ 𝔪 ≤ P) (hc : IsExterior 𝔪 c) (hcP : ¬ c ≤ P) :
    Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (g.gen c) ≠ 0 := by
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem] at h
  apply hcP
  intro a ha
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hP0⟩
  have hv : v ∉ placesOf 𝔪 := hPm
  have h1 : algebraMap (𝓞 F) (SInt 𝔪) a ∈ c.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ ha
  rw [← g.span_gen c hc, Ideal.mem_span_singleton'] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 : algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one, ← hr]; exact Ideal.mul_mem_left _ _ h
  have := (C3I.alg_mem_map_pow_iff (𝔪 := 𝔪) hv 1 a).1 h2
  rwa [pow_one] at this

lemma coprime_six_of_dvd {N : ℕ} (hN : 1 ≤ N) (h6 : 6 ∣ N - 1) : N.Coprime 6 := by
  obtain ⟨k, hk⟩ := h6
  have : N = 6 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (6 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

lemma norm_sext_eq_one (ι : F →+* ℂ) {𝔪 P : Ideal (𝓞 F)} (hP : C3B.GoodP 𝔪 P) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪)
    (hx : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ = 1 := by
  classical
  obtain ⟨hPp, hP0, h𝔪, h6⟩ := hP
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hP0⟩
  have hv : v ∉ placesOf 𝔪 := h𝔪
  haveI : (P.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := C3I.isMaximal_map (v := v) hv
  letI := Ideal.Quotient.field (P.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hN : 1 ≤ Ideal.absNorm P := by
    rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hP0
  have hferm := C3B.pow_absNorm_eq P hPp hP0 h𝔪
    (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x)
  have hy1 : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^
      (Ideal.absNorm P - 1) = 1 := by
    have : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^ (Ideal.absNorm P - 1) *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x =
        1 * Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x := by
      rw [← pow_succ, Nat.sub_add_cancel hN, hferm, one_mul]
    exact mul_right_cancel₀ hx this
  have hz6 : (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^
      ((Ideal.absNorm P - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel h6, hy1]
  have hcop : (Ideal.absNorm P).Coprime 6 := coprime_six_of_dvd hN h6
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
  have hωP : IsPrimitiveRoot (Ideal.Quotient.mk P ω) 6 := hω.idealQuotient_mk hN1 hcop
  have hinj : Function.Injective (C3I.quotHom 𝔪 P) := by
    have := (C3I.quotHom_bijective (𝔪 := 𝔪) hv 1).1
    rw [pow_one] at this
    exact this
  have hωL := hωP.map_of_injective hinj
  rw [C3I.quotHom_mk] at hωL
  obtain ⟨i, -, hi⟩ := hωL.eq_pow_of_pow_eq_one hz6
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) ζ) =
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^
          ((Ideal.absNorm P - 1) / 6) := by
    refine ⟨ω ^ i, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    · rw [map_pow, map_pow, hi]
  unfold sexticResidueSymbol
  rw [if_neg hx, dif_pos hex]
  have h6' : (ι (hex.choose : F)) ^ 6 = 1 := by
    rw [← map_pow, ← map_pow, hex.choose_spec.1]; simp
  exact Complex.norm_eq_one_of_pow_eq_one h6' (by norm_num)

/-! ### Multiplicativity of the symbol (without `C3I.chi`) -/

/-- The image of `ω` in `R / P R` is a primitive sixth root of unity. -/
lemma omegaL_prim {𝔪 P : Ideal (𝓞 F)} (hP : C3B.GoodP 𝔪 P) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪)))
      (algebraMap (𝓞 F) (SInt 𝔪) ω)) 6 := by
  obtain ⟨hPp, hP0, h𝔪, h6⟩ := hP
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hP0⟩
  have hv : v ∉ placesOf 𝔪 := h𝔪
  have hN : 1 ≤ Ideal.absNorm P := by
    rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hP0
  have hcop : (Ideal.absNorm P).Coprime 6 := coprime_six_of_dvd hN h6
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
  have hωP : IsPrimitiveRoot (Ideal.Quotient.mk P ω) 6 := hω.idealQuotient_mk hN1 hcop
  have hinj : Function.Injective (C3I.quotHom 𝔪 P) := by
    have := (C3I.quotHom_bijective (𝔪 := 𝔪) hv 1).1
    rw [pow_one] at this
    exact this
  have hωL := hωP.map_of_injective hinj
  rwa [C3I.quotHom_mk] at hωL

/-- Sixth roots of unity of `𝓞 F` are determined by their images in `R / P R`. -/
lemma mu6_inj {𝔪 P : Ideal (𝓞 F)} (hP : C3B.GoodP 𝔪 P) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {ζ ζ' : 𝓞 F} (h : ζ ^ 6 = 1) (h' : ζ' ^ 6 = 1)
    (himg : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) ζ) =
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) ζ')) :
    ζ = ζ' := by
  obtain ⟨a, ha, rfl⟩ := hω.eq_pow_of_pow_eq_one h
  obtain ⟨b, hb, rfl⟩ := hω.eq_pow_of_pow_eq_one h'
  have hωL := omegaL_prim hP hω
  rw [map_pow, map_pow, map_pow, map_pow] at himg
  rw [hωL.pow_inj ha hb himg]

/-- The value of the symbol at a unit: `ι ζ` for the sixth root of unity `ζ ≡ x^((N P − 1)/6)`. -/
lemma sext_spec (ι : F →+* ℂ) {𝔪 P : Ideal (𝓞 F)} (hP : C3B.GoodP 𝔪 P) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪)
    (hx : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0) :
    ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) ζ) =
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^ ((Ideal.absNorm P - 1) / 6) ∧
      sexticResidueSymbol ι 𝔪 P x = ι (ζ : F) := by
  classical
  obtain ⟨hPp, hP0, h𝔪, h6⟩ := hP
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hP0⟩
  have hv : v ∉ placesOf 𝔪 := h𝔪
  haveI : (P.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := C3I.isMaximal_map (v := v) hv
  letI := Ideal.Quotient.field (P.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hN : 1 ≤ Ideal.absNorm P := by
    rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hP0
  have hferm := C3B.pow_absNorm_eq P hPp hP0 h𝔪
    (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x)
  have hy1 : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^
      (Ideal.absNorm P - 1) = 1 := by
    have : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^ (Ideal.absNorm P - 1) *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x =
        1 * Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x := by
      rw [← pow_succ, Nat.sub_add_cancel hN, hferm, one_mul]
    exact mul_right_cancel₀ hx this
  have hz6 : (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^
      ((Ideal.absNorm P - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel h6, hy1]
  have hωL := omegaL_prim ⟨hPp, hP0, h𝔪, h6⟩ hω
  obtain ⟨i, -, hi⟩ := hωL.eq_pow_of_pow_eq_one hz6
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) ζ) =
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ^
          ((Ideal.absNorm P - 1) / 6) := by
    refine ⟨ω ^ i, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    · rw [map_pow, map_pow, hi]
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold sexticResidueSymbol
  rw [if_neg hx, dif_pos hex]

lemma sext_mul (ι : F →+* ℂ) {𝔪 P : Ideal (𝓞 F)} (hP : C3B.GoodP 𝔪 P) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) (x y : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y := by
  classical
  obtain ⟨hPp, hP0, h𝔪, h6⟩ := hP
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hP0⟩
  have hv : v ∉ placesOf 𝔪 := h𝔪
  haveI : (P.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := C3I.isMaximal_map (v := v) hv
  letI := Ideal.Quotient.field (P.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have zero_case : ∀ z : SInt 𝔪,
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) z = 0 →
        sexticResidueSymbol ι 𝔪 P z = 0 := by
    intro z hz; unfold sexticResidueSymbol; rw [if_pos hz]
  by_cases hx : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x = 0
  · rw [zero_case x hx, zero_case (x * y) (by rw [map_mul, hx, zero_mul]), zero_mul]
  by_cases hy : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y = 0
  · rw [zero_case y hy, zero_case (x * y) (by rw [map_mul, hy, mul_zero]), mul_zero]
  have hxy : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) (x * y) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hx hy
  have hP : C3B.GoodP 𝔪 P := ⟨hPp, hP0, h𝔪, h6⟩
  obtain ⟨ζx, hx6, hxi, hxv⟩ := sext_spec ι hP hω x hx
  obtain ⟨ζy, hy6, hyi, hyv⟩ := sext_spec ι hP hω y hy
  obtain ⟨ζ, h6', hi, hv'⟩ := sext_spec ι hP hω (x * y) hxy
  have heq : ζ = ζx * ζy := by
    refine mu6_inj hP hω h6' (by rw [mul_pow, hx6, hy6, one_mul]) ?_
    rw [hi, map_mul, mul_pow, map_mul, map_mul, hxi, hyi]
  rw [hv', hxv, hyv, heq]
  push_cast
  exact map_mul ι _ _

lemma rs_mul_x (ι : F →+* ℂ) {𝔪 𝔞 : Ideal (𝓞 F)}
    (h𝔞 : ∀ P ∈ normalizedFactors 𝔞, C3B.GoodP 𝔪 P) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    (x y : SInt 𝔪) : residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun P hP => sext_mul ι (h𝔞 P hP) hω x y)

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul_units {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)}
    (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

/-! ### The kernel -/

/-- `χ_𝔠(𝔡)`, the quadratic symbol of the family. -/
noncomputable def chiK (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (𝔡 𝔠 : Ideal (𝓞 F)) : ℂ :=
  residueSymbol ι 𝔪 𝔡 (g.gen 𝔠) ^ 3

/-- Row multiplication by a good prime `p ∤ 𝔠`: `χ_𝔠(a) = w · χ_𝔠(a p)`, `‖w‖ = 1`. -/
lemma chiK_mul_row (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) {p a c : Ideal (𝓞 F)} (hp : C3B.GoodP 𝔪 p) (ha : a ≠ ⊥)
    (hc : IsExterior 𝔪 c) (hcp : ¬ c ≤ p) :
    chiK ι 𝔪 g a c =
      (starRingEnd ℂ (sexticResidueSymbol ι 𝔪 p (g.gen c))) ^ 3 * chiK ι 𝔪 g (a * p) c := by
  have hs := norm_sext_eq_one ι hp hω (g.gen c) (gen_not_mem g hp.1 hp.2.1 hp.2.2.1 hc hcp)
  unfold chiK
  rw [rs_mul a p ha hp.2.1, rs_prime p hp.1 hp.2.1]
  set s := sexticResidueSymbol ι 𝔪 p (g.gen c)
  set A := residueSymbol ι 𝔪 a (g.gen c)
  have hss : starRingEnd ℂ s * s = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hs]; simp
  calc A ^ 3 = A ^ 3 * (starRingEnd ℂ s * s) ^ 3 := by rw [hss, one_pow, mul_one]
    _ = starRingEnd ℂ s ^ 3 * (A * s) ^ 3 := by ring

lemma norm_conj_sext_pow_le (ι : F →+* ℂ) (𝔪 p : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖(starRingEnd ℂ (sexticResidueSymbol ι 𝔪 p x)) ^ 3‖ ≤ 1 := by
  rw [norm_pow, Complex.norm_conj]
  have h : ‖sexticResidueSymbol ι 𝔪 p x‖ ≤ 1 := by
    unfold sexticResidueSymbol
    split_ifs with h1 h2
    · simp
    · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
        rw [← map_pow, ← map_pow, h2.choose_spec.1]; simp
      rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
    · simp
  exact pow_le_one₀ (norm_nonneg _) h

/-- `χ_{𝔤 𝔠}(a) = χ_𝔤(a) χ_𝔠(a)` when the prime factors of `a` are good. -/
lemma chiK_mul_col (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) {a 𝔤 c : Ideal (𝓞 F)}
    (ha : ∀ P ∈ normalizedFactors a, C3B.GoodP 𝔪 P) (h𝔤 : IsExterior 𝔪 𝔤)
    (hc : IsExterior 𝔪 c) : chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c := by
  obtain ⟨ε, hε⟩ := gen_mul_units g h𝔤 hc
  unfold chiK
  rw [hε, mul_assoc, C3B.residueSymbol_unit_pow_six ι a ha ε, rs_mul_x ι ha hω, mul_pow]

/-! ### Ideal facts -/

lemma squarefree_mul_prime {a p : Ideal (𝓞 F)} (ha : Squarefree a) (hp : p.IsPrime) (hp0 : p ≠ ⊥)
    (hap : ¬ a ≤ p) : Squarefree (a * p) := by
  have hpr : Prime p := Ideal.prime_of_isPrime hp0 hp
  refine squarefree_mul_iff.2 ⟨?_, ha, hpr.irreducible.squarefree⟩
  have := (hpr.irreducible.isRelPrime_iff_not_dvd (n := a)).2 (fun h => hap (Ideal.le_of_dvd h))
  exact this.symm

lemma exterior_mul_prime {𝔪 a p : Ideal (𝓞 F)} (ha : IsExterior 𝔪 a) (hp : p.IsMaximal)
    (hp0 : p ≠ ⊥) (hpm : ¬ 𝔪 ≤ p) : IsExterior 𝔪 (a * p) := by
  have hpe : IsExterior 𝔪 p := by
    refine ⟨hp0, ?_⟩
    by_contra h
    exact hpm (le_trans le_sup_right ((hp.eq_of_le (Ne.symm (Ne.symm h)) le_sup_left).symm.le))
  exact C3I.isExterior_mul ha hpe

lemma exterior_of_maximal {𝔪 p : Ideal (𝓞 F)} (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    (hpm : ¬ 𝔪 ≤ p) : IsExterior 𝔪 p := by
  refine ⟨hp0, ?_⟩
  by_contra h
  exact hpm (le_trans le_sup_right ((hp.eq_of_le h le_sup_left).symm.le))

/-! ### Row and column sets -/

lemma fin_set (𝔪 : Ideal (𝓞 F)) (lo hi : ℝ) :
    {𝔡 : Ideal (𝓞 F) | IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ lo < (Ideal.absNorm 𝔡 : ℝ) ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ hi}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊hi⌋₊).subset
    (fun 𝔡 h => Nat.le_floor h.2.2.2)

/-- Exterior squarefree ideals with `lo < N 𝔡 ≤ hi`. -/
noncomputable def rowsF (𝔪 : Ideal (𝓞 F)) (lo hi : ℝ) : Finset (Ideal (𝓞 F)) :=
  (fin_set 𝔪 lo hi).toFinset

lemma mem_rowsF {𝔪 : Ideal (𝓞 F)} {lo hi : ℝ} {𝔡 : Ideal (𝓞 F)} :
    𝔡 ∈ rowsF 𝔪 lo hi ↔ IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ lo < (Ideal.absNorm 𝔡 : ℝ) ∧
      (Ideal.absNorm 𝔡 : ℝ) ≤ hi := by
  unfold rowsF; rw [Set.Finite.mem_toFinset]; rfl

lemma one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (1 : ℝ) ≤ Ideal.absNorm I := by
  have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

lemma mem_rowsF_zero {𝔪 : Ideal (𝓞 F)} {hi : ℝ} {𝔡 : Ideal (𝓞 F)} :
    𝔡 ∈ rowsF 𝔪 0 hi ↔ IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧ (Ideal.absNorm 𝔡 : ℝ) ≤ hi := by
  rw [mem_rowsF]
  constructor
  · rintro ⟨h1, h2, -, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨h1, h2, lt_of_lt_of_le zero_lt_one (one_le_absNorm h1.1), h4⟩

/-! ### `tsum` over subtypes -/

lemma tsum_subtype_eq {β E : Type*} [AddCommMonoid E] [TopologicalSpace E] (p : β → Prop)
    (S : Finset β) (hS : ∀ x, x ∈ S ↔ p x) (f : β → E) :
    ∑' x : {x // p x}, f x.1 = ∑ x ∈ S, f x := by
  rw [← Finset.tsum_subtype S f]
  exact (Equiv.subtypeEquivRight (fun x => (hS x).symm)).tsum_eq (fun x => f x.1)

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)

/-- The `SBf` bound gives the statement's `tsum` form (rows of norm `≤ D`). -/
lemma sb_of_SBf {C D v : ℝ} (h : SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C) v) :
    ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
        (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
      ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
          (Ideal.absNorm 𝔡 : ℝ) ≤ D},
          ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
        v * ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  classical
  intro z
  set z' : Ideal (𝓞 F) → ℂ := fun c =>
    if hc : IsExterior 𝔪 c ∧ Squarefree c ∧ (Ideal.absNorm c : ℝ) ≤ C then z ⟨c, hc⟩ else 0
  have hz : ∀ c : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, z c = z' c.1 := fun c => by simp [z', c.2]
  have hin : ∀ 𝔡 : Ideal (𝓞 F), ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, z 𝔠 * residueSymbol ι 𝔪 𝔡 (g.gen 𝔠.1) ^ 3 =
      ∑ c ∈ rowsF 𝔪 0 C, z' c * chiK ι 𝔪 g 𝔡 c := by
    intro 𝔡
    simp_rw [hz]
    exact tsum_subtype_eq _ _ (fun x => mem_rowsF_zero) (fun c => z' c * chiK ι 𝔪 g 𝔡 c)
  have hn : ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, ‖z 𝔠‖ ^ 2 = ∑ c ∈ rowsF 𝔪 0 C, ‖z' c‖ ^ 2 := by
    simp_rw [hz]
    exact tsum_subtype_eq _ _ (fun x => mem_rowsF_zero) (fun c => ‖z' c‖ ^ 2)
  simp_rw [hin, hn]
  rw [tsum_subtype_eq _ _ (fun x => mem_rowsF_zero)
    (fun 𝔡 => ‖∑ c ∈ rowsF 𝔪 0 C, z' c * chiK ι 𝔪 g 𝔡 c‖ ^ 2)]
  exact h z'

end L3H

end
end

section
section
/-! # L3H_Prime: a supply of prime ideals of controlled norm, and the divisor count

* `exists_primes`: for `𝔪 ≠ ⊥` and `y ≥ 1`, at least `L` maximal ideals `p ∤ 𝔪` with
  `y < N p ≤ (2^(L + N 𝔪) y)^[F:ℚ]` (Bertrand's postulate `L + N 𝔪` times, one prime above each).
* `card_filter_le`: an ideal `x ≠ ⊥` with `N x < y^(k+1)` lies in at most `k` distinct maximal
  ideals of norm `> y`.
-/

open NumberField

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

open Classical in
theorem card_filter_le (P : Finset (Ideal (𝓞 F))) (hP : ∀ p ∈ P, p.IsMaximal) {y : ℝ}
    (hy : 1 < y) (hPn : ∀ p ∈ P, y < (Ideal.absNorm p : ℝ)) {x : Ideal (𝓞 F)} (hx : x ≠ ⊥)
    {k : ℕ} (hk : (Ideal.absNorm x : ℝ) < y ^ (k + 1)) :
    (P.filter (fun p => x ≤ p)).card ≤ k := by
  classical
  set Q := P.filter (fun p => x ≤ p)
  have hdvd : (∏ p ∈ Q, p) ∣ x := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hp q hq hpq
      have hpM := hP p (Finset.mem_filter.1 hp).1
      have hqM := hP q (Finset.mem_filter.1 hq).1
      rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      by_contra h
      have h1 : p ⊔ q = p := (hpM.eq_of_le h le_sup_left).symm
      have h2 : q ≤ p := h1 ▸ le_sup_right
      exact hpq ((hqM.eq_of_le hpM.ne_top h2).symm)
    · intro p hp
      exact Ideal.dvd_iff_le.2 (Finset.mem_filter.1 hp).2
  have hN : Ideal.absNorm (∏ p ∈ Q, p) ∣ Ideal.absNorm x := by
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, map_mul]; exact dvd_mul_right _ _
  have hx0 : Ideal.absNorm x ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hx
  have hle : (Ideal.absNorm (∏ p ∈ Q, p) : ℝ) ≤ Ideal.absNorm x :=
    by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hN
  rw [map_prod, Nat.cast_prod] at hle
  have hlow : y ^ Q.card ≤ ∏ p ∈ Q, (Ideal.absNorm p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith) fun p hp =>
      (hPn p (Finset.mem_filter.1 hp).1).le
  by_contra hc
  push Not at hc
  have : y ^ (k + 1) ≤ y ^ Q.card := pow_le_pow_right₀ hy.le hc
  linarith

/-- Bertrand chain: distinct primes `q i ∈ (2^i y, 2^(i+1) y]`. -/
lemma bertrand_chain (y : ℕ) (hy : 1 ≤ y) (i : ℕ) :
    ∃ q, Nat.Prime q ∧ 2 ^ i * y < q ∧ q ≤ 2 ^ (i + 1) * y := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ i * y)
    (by positivity)
  exact ⟨q, hq, h1, by rw [pow_succ]; linarith⟩

theorem exists_primes (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (L y : ℕ) (hy : 1 ≤ y) :
    ∃ P : Finset (Ideal (𝓞 F)), L ≤ P.card ∧ ∀ p ∈ P, p.IsMaximal ∧ p ≠ ⊥ ∧ ¬ 𝔪 ≤ p ∧
      y < Ideal.absNorm p ∧
      Ideal.absNorm p ≤ (2 ^ (L + Ideal.absNorm 𝔪) * y) ^ Module.finrank ℤ (𝓞 F) := by
  classical
  set K := L + Ideal.absNorm 𝔪
  set d := Module.finrank ℤ (𝓞 F)
  have hd : 0 < d := Module.finrank_pos
  choose q hqp hq1 hq2 using bertrand_chain y hy
  have hqinj : Set.InjOn q (Finset.range K : Set ℕ) := by
    intro i _ j _ hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : 2 ^ (i + 1) * y ≤ 2 ^ j * y :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)
      have := hq2 i; have := hq1 j; omega
    · have : 2 ^ (j + 1) * y ≤ 2 ^ i * y :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)
      have := hq2 j; have := hq1 i; omega
  set Q₀ := (Finset.range K).image q
  have hQ₀ : Q₀.card = K := by rw [Finset.card_image_of_injOn hqinj, Finset.card_range]
  set Q := Q₀.filter (fun r => ¬ r ∣ Ideal.absNorm 𝔪)
  have hm0 : Ideal.absNorm 𝔪 ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔪
  have hQcard : L ≤ Q.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Q₀) (fun r => ¬ r ∣ Ideal.absNorm 𝔪)
    have hbad : (Q₀.filter (fun r => ¬ ¬ r ∣ Ideal.absNorm 𝔪)).card ≤ Ideal.absNorm 𝔪 := by
      calc (Q₀.filter (fun r => ¬ ¬ r ∣ Ideal.absNorm 𝔪)).card
          ≤ (Finset.Icc 1 (Ideal.absNorm 𝔪)).card := by
            refine Finset.card_le_card fun r hr => ?_
            rw [Finset.mem_filter, not_not] at hr
            rw [Finset.mem_Icc]
            exact ⟨Nat.pos_of_dvd_of_pos hr.2 (Nat.pos_of_ne_zero hm0), Nat.le_of_dvd
              (Nat.pos_of_ne_zero hm0) hr.2⟩
        _ = Ideal.absNorm 𝔪 := by simp
    have hQ : Q.card + (Q₀.filter (fun r => ¬ ¬ r ∣ Ideal.absNorm 𝔪)).card = K := by
      rw [← hQ₀]; exact hsplit
    have hK : K = L + Ideal.absNorm 𝔪 := rfl
    omega
  have hQprime : ∀ r ∈ Q, Nat.Prime r ∧ y < r ∧ r ≤ 2 ^ K * y ∧ ¬ r ∣ Ideal.absNorm 𝔪 := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr.1
    refine ⟨hqp i, ?_, ?_, hr.2⟩
    · have := hq1 i
      have : y ≤ 2 ^ i * y := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    · have := hq2 i
      have : 2 ^ (i + 1) * y ≤ 2 ^ K * y :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
          (Nat.succ_le_of_lt (Finset.mem_range.1 hi)))
      omega
  -- a maximal ideal above each rational prime
  have hex : ∀ r : ℕ, Nat.Prime r → ∃ p : Ideal (𝓞 F), p.IsMaximal ∧ (r : 𝓞 F) ∈ p := by
    intro r hr
    have hne : Ideal.span {(r : 𝓞 F)} ≠ ⊤ := by
      intro h
      have := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_top, Ideal.absNorm_span_singleton] at this
      have hn : Algebra.norm ℤ (r : 𝓞 F) = (r : ℤ) ^ d := by
        rw [show (r : 𝓞 F) = algebraMap ℤ (𝓞 F) r by simp, Algebra.norm_algebraMap]
      rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at this
      have := (Nat.pow_eq_one.1 this)
      rcases this with h1 | h1
      · exact hr.one_lt.ne' h1
      · omega
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨p, hp, hle (Ideal.mem_span_singleton_self _)⟩
  choose! pr hprM hprmem using hex
  have hnorm : ∀ r ∈ Q, ∃ f, 1 ≤ f ∧ f ≤ d ∧ Ideal.absNorm (pr r) = r ^ f := by
    intro r hr
    have hrp := (hQprime r hr).1
    have hM := hprM r hrp
    have hle : Ideal.span {(r : 𝓞 F)} ≤ pr r :=
      (Ideal.span_singleton_le_iff_mem _).2 (hprmem r hrp)
    have hdv := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_singleton] at hdv
    have hn : Algebra.norm ℤ (r : 𝓞 F) = (r : ℤ) ^ d := by
      rw [show (r : 𝓞 F) = algebraMap ℤ (𝓞 F) r by simp, Algebra.norm_algebraMap]
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdv
    obtain ⟨f, hf, hfe⟩ := (Nat.dvd_prime_pow hrp).1 hdv
    refine ⟨f, ?_, hf, hfe⟩
    by_contra h0
    have : f = 0 := by omega
    rw [this, pow_zero, Ideal.absNorm_eq_one_iff] at hfe
    exact hM.ne_top hfe
  have hinj : Set.InjOn pr (Q : Set ℕ) := by
    intro r hr r' hr' h
    by_contra hne
    have hrp := (hQprime r hr).1
    have hrp' := (hQprime r' hr').1
    have hcop : Nat.Coprime r r' := (Nat.coprime_primes hrp hrp').2 hne
    obtain ⟨u, v, huv⟩ : IsCoprime (r : ℤ) (r' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    have hmem : (1 : 𝓞 F) ∈ pr r := by
      have h1 : ((u * r + v * r' : ℤ) : 𝓞 F) = 1 := by rw [huv]; simp
      rw [← h1]
      push_cast
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hprmem r hrp)) ?_
      rw [h]; exact Ideal.mul_mem_left _ _ (hprmem r' hrp')
    exact (hprM r hrp).ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  refine ⟨Q.image pr, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj]; exact hQcard
  intro p hp
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨hrp, hyr, hrK, hrm⟩ := hQprime r hr
  obtain ⟨f, hf1, hfd, hfe⟩ := hnorm r hr
  have hM := hprM r hrp
  refine ⟨hM, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, Ideal.absNorm_bot] at hfe
    exact pow_ne_zero f hrp.ne_zero hfe.symm
  · intro hle
    have hdv := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hfe] at hdv
    exact hrm (dvd_trans (dvd_pow_self r (by omega)) hdv)
  · rw [hfe]
    calc y < r := hyr
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ f := Nat.pow_le_pow_right hrp.pos hf1
  · rw [hfe]
    calc r ^ f ≤ r ^ d := Nat.pow_le_pow_right hrp.pos hfd
      _ ≤ (2 ^ K * y) ^ d := Nat.pow_le_pow_left hrK d

end L3H

end
end

section
section
/-! # L3H_Aux: shared helpers (dyadic covers, `log₂` bounds, trivial bounds, `rpow` facts) -/

open NumberField ArtinPrimitiveRoots Real

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma dyadic_cover {b t : ℝ} (hb : 0 < b) (hbt : b < t) :
    ∀ J : ℕ, t ≤ b * 2 ^ J → ∃ j < J, b * 2 ^ j < t ∧ t ≤ 2 * (b * 2 ^ j) := by
  intro J
  induction J with
  | zero => intro h; simp at h; linarith
  | succ J ih =>
    intro h
    by_cases hJ : t ≤ b * 2 ^ J
    · obtain ⟨j, hj, h1, h2⟩ := ih hJ
      exact ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩
    · push Not at hJ
      refine ⟨J, Nat.lt_succ_self J, hJ, ?_⟩
      rw [pow_succ] at h; linarith

lemma rows_le_subset (𝔪 : Ideal (𝓞 F)) {D : ℝ} (hD : 1 ≤ D) :
    rowsF 𝔪 0 D ⊆ (Finset.range (Nat.log 2 ⌊D⌋₊ + 2)).biUnion
      (fun i => rowsF 𝔪 ((2 : ℝ) ^ i / 2) (2 * ((2 : ℝ) ^ i / 2))) := by
  intro 𝔡 h𝔡
  obtain ⟨h1, h2, -, h4⟩ := mem_rowsF.1 h𝔡
  have hN1 : (1 : ℝ) ≤ Ideal.absNorm 𝔡 := one_le_absNorm h1.1
  have hbig : D ≤ (1 / 2 : ℝ) * 2 ^ (Nat.log 2 ⌊D⌋₊ + 2) := by
    have hfl : ⌊D⌋₊ < 2 ^ (Nat.log 2 ⌊D⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hfl' : (⌊D⌋₊ : ℝ) + 1 ≤ 2 ^ (Nat.log 2 ⌊D⌋₊ + 1) := by exact_mod_cast hfl
    have hD' : D < ⌊D⌋₊ + 1 := Nat.lt_floor_add_one D
    rw [pow_succ]; nlinarith
  obtain ⟨j, hj, hj1, hj2⟩ := dyadic_cover (b := 1 / 2) (t := (Ideal.absNorm 𝔡 : ℝ))
    (by norm_num) (by linarith) _ (h4.trans hbig)
  refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, mem_rowsF.2 ⟨h1, h2, ?_, ?_⟩⟩
  · linarith
  · linarith

lemma natlog_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (Nat.log 2 n : ℝ) ≤ (n : ℝ) ^ δ / (δ * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hδ.ne']
  · have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
    have h2' : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast h2
    have hl : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2'
    have hl2 : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div (by positivity) hδ
    rw [le_div_iff₀ (by positivity)]
    have : (Nat.log 2 n : ℝ) * Real.log 2 * δ ≤ (n : ℝ) ^ δ / δ * δ :=
      mul_le_mul_of_nonneg_right (hl.trans hl2) hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at this
    linarith

lemma norm_chiK_le (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (a c : Ideal (𝓞 F)) :
    ‖chiK ι 𝔪 g a c‖ ≤ 1 := by
  unfold chiK residueSymbol
  rw [norm_pow]
  refine pow_le_one₀ (norm_nonneg _) ?_
  induction (UniqueFactorizationMonoid.normalizedFactors a) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ih
    unfold sexticResidueSymbol
    split_ifs with h1 h2
    · simp
    · have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
        rw [← map_pow, ← map_pow, h2.choose_spec.1]; simp
      rw [Complex.norm_eq_one_of_pow_eq_one h6 (by norm_num)]
    · simp

lemma SBf_card (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (R Cs : Finset (Ideal (𝓞 F))) :
    SBf (chiK ι 𝔪 g) R Cs (R.card * Cs.card) := by
  refine (SBf.trivial R Cs).mono_v ?_
  calc ∑ a ∈ R, ∑ c ∈ Cs, ‖chiK ι 𝔪 g a c‖ ^ 2 ≤ ∑ a ∈ R, ∑ c ∈ Cs, (1 : ℝ) := by
        gcongr with a _ c _
        exact pow_le_one₀ (norm_nonneg _) (norm_chiK_le ι 𝔪 g a c)
    _ = R.card * Cs.card := by simp

/-- Real-variable bookkeeping for the big case. -/
lemma rpow_mono_exp {X a b : ℝ} (hX : 1 ≤ X) (hab : a ≤ b) : X ^ a ≤ X ^ b :=
  Real.rpow_le_rpow_of_exponent_le hX hab

lemma one_le_rpow' {X a : ℝ} (hX : 1 ≤ X) (ha : 0 ≤ a) : 1 ≤ X ^ a := Real.one_le_rpow hX ha

lemma pow_rpow_eq {X η : ℝ} (hX : 0 ≤ X) (k : ℕ) : (X ^ η) ^ k = X ^ (η * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]

end L3H

end
end

section
section
/-! # L3H_Lift: GL Lemma 4.4 (Heath-Brown Lemma 9) for the family `chiK`

`lift_dyadic`: the dyadic rows `M < N 𝔡 ≤ 2M` are bounded by `8 ∑_j v_j` when the dyadic rows
`M y 2^j < N 𝔡 ≤ 2 M y 2^j` (`j < J`) are bounded by `v_j`, given a family `P` of exterior primes
of norm in `(y, Y]`, `2 M Y ≤ M y 2^J`, each ideal of norm `≤ X` lying in at most `ω` of them,
and `8 ω ≤ #P`. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

open Classical in
theorem lift_dyadic (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6)
    (hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p)
    (P : Finset (Ideal (𝓞 F))) {y Y X : ℝ}
    (hP : ∀ p ∈ P, p.IsMaximal ∧ p ≠ ⊥ ∧ ¬ 𝔪 ≤ p ∧ y < (Ideal.absNorm p : ℝ) ∧
      (Ideal.absNorm p : ℝ) ≤ Y)
    (w : ℕ) (hcard : 8 * w ≤ P.card) (hne : P.Nonempty)
    (hcount : ∀ x : Ideal (𝓞 F), x ≠ ⊥ → (Ideal.absNorm x : ℝ) ≤ X →
      (P.filter (fun p => x ≤ p)).card ≤ w)
    {M C : ℝ} (hM : 0 < M) (h2M : 2 * M ≤ X) (hC : C ≤ X) (hy : 0 < y)
    (J : ℕ) (hJ : 2 * M * Y ≤ M * y * 2 ^ J)
    (v : ℕ → ℝ) (hv0 : ∀ j, 0 ≤ v j)
    (hv : ∀ j < J, SBf (chiK ι 𝔪 g) (rowsF 𝔪 (M * y * 2 ^ j) (2 * (M * y * 2 ^ j)))
      (rowsF 𝔪 0 C) (v j)) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C) (8 * ∑ j ∈ Finset.range J, v j) := by
  set R' := (Finset.range J).biUnion (fun j => rowsF 𝔪 (M * y * 2 ^ j) (2 * (M * y * 2 ^ j)))
  have hR' : SBf (chiK ι 𝔪 g) R' (rowsF 𝔪 0 C) (∑ j ∈ Finset.range J, v j) :=
    SBf.biUnion _ _ _ _ fun j hj => hv j (Finset.mem_range.1 hj)
  refine SBf.lift (Finset.sum_nonneg fun j _ => hv0 j) hR' (fun p x => x ≤ p) (fun a p => a * p)
    (fun p c => (starRingEnd ℂ (sexticResidueSymbol ι 𝔪 p (g.gen c))) ^ 3) w hcard hne
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨h1, -, -, h4⟩ := mem_rowsF.1 ha
    exact hcount a h1.1 (h4.trans h2M)
  · intro c hc
    obtain ⟨h1, -, h4⟩ := mem_rowsF_zero.1 hc
    exact hcount c h1.1 (h4.trans hC)
  · intro p hp a ha hpa
    obtain ⟨hpM, hp0, hpm, hpy, hpY⟩ := hP p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_rowsF.1 ha
    have hN : (Ideal.absNorm (a * p) : ℝ) = Ideal.absNorm a * Ideal.absNorm p := by
      rw [map_mul, Nat.cast_mul]
    have hlo : M * y < (Ideal.absNorm (a * p) : ℝ) := by
      rw [hN]; exact mul_lt_mul'' h3 hpy hM.le hy.le
    have hhi : (Ideal.absNorm (a * p) : ℝ) ≤ M * y * 2 ^ J := by
      rw [hN]
      calc (Ideal.absNorm a : ℝ) * Ideal.absNorm p ≤ (2 * M) * Y :=
            mul_le_mul h4 hpY (Nat.cast_nonneg _) (by linarith)
        _ ≤ M * y * 2 ^ J := hJ
    obtain ⟨j, hj, hj1, hj2⟩ := dyadic_cover (by positivity) hlo J hhi
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, ?_⟩
    refine mem_rowsF.2 ⟨exterior_mul_prime h1 hpM hp0 hpm,
      squarefree_mul_prime h2 hpM.isPrime hp0 hpa, by simpa [mul_assoc] using hj1,
      by simpa [mul_assoc] using hj2⟩
  · intro p hp a ha b hb hab
    have hp0 := (hP p hp).2.1
    exact mul_right_cancel₀ hp0 hab
  · intro p _ c _
    exact norm_conj_sext_pow_le ι 𝔪 p (g.gen c)
  · intro p hp a ha _ c hc hcp
    obtain ⟨hpM, hp0, hpm, -, -⟩ := hP p hp
    exact chiK_mul_row ι g hω (hgood p hpM hp0 hpm) (mem_rowsF.1 ha).1.1
      (mem_rowsF_zero.1 hc).1 hcp

end L3H

end
end

section
section
/-! # L3H_Climb: pushing dyadic rows up to a target window by repeated row multiplication

`climb`: if every dyadic row block at a scale in `[Mt, Mt y 2^J]` is bounded by `Φ`, then a block at
any scale `M ≤ Mt y 2^J` with `Mt ≤ M y^k` is bounded by `(8 J)^k Φ`. Each step applies
`lift_dyadic` (GL Lemma 4.4) with primes of norm in `(y, Y]`. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

open Classical in
theorem climb (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6)
    (hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p)
    (P : Finset (Ideal (𝓞 F))) {y Y X : ℝ}
    (hP : ∀ p ∈ P, p.IsMaximal ∧ p ≠ ⊥ ∧ ¬ 𝔪 ≤ p ∧ y < (Ideal.absNorm p : ℝ) ∧
      (Ideal.absNorm p : ℝ) ≤ Y)
    (w : ℕ) (hcard : 8 * w ≤ P.card) (hne : P.Nonempty)
    (hcount : ∀ x : Ideal (𝓞 F), x ≠ ⊥ → (Ideal.absNorm x : ℝ) ≤ X →
      (P.filter (fun p => x ≤ p)).card ≤ w)
    {C : ℝ} (hC : C ≤ X) (hy : 1 ≤ y) (J : ℕ) (hJ1 : 1 ≤ J) (hJ : 2 * Y ≤ y * 2 ^ J)
    {Mt Φ : ℝ} (hMt : 0 < Mt) (hΦ : 0 ≤ Φ) (hX : 2 * (Mt * y * 2 ^ J) ≤ X)
    (hbase : ∀ M, Mt ≤ M → M ≤ Mt * y * 2 ^ J →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C) Φ) :
    ∀ k : ℕ, ∀ M, 0 < M → M ≤ Mt * y * 2 ^ J → Mt ≤ M * y ^ k →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C) ((8 * J) ^ k * Φ) := by
  have h8J : (1 : ℝ) ≤ 8 * J := by
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    linarith
  intro k
  induction k with
  | zero =>
    intro M _ hMtop hk
    simp only [pow_zero, mul_one, one_mul] at hk ⊢
    exact hbase M hk hMtop
  | succ k ih =>
    intro M hM hMtop hk
    by_cases hMt' : Mt ≤ M
    · refine (hbase M hMt' hMtop).mono_v ?_
      exact le_mul_of_one_le_left hΦ (one_le_pow₀ h8J)
    push Not at hMt'
    have hy0 : 0 < y := by linarith
    have hpieces : ∀ j < J, SBf (chiK ι 𝔪 g) (rowsF 𝔪 (M * y * 2 ^ j) (2 * (M * y * 2 ^ j)))
        (rowsF 𝔪 0 C) ((8 * J) ^ k * Φ) := by
      intro j hj
      refine ih _ (by positivity) ?_ ?_
      · have h2j : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj.le
        have := mul_le_mul (mul_le_mul_of_nonneg_right hMt'.le hy0.le) h2j (by positivity)
          (by positivity)
        linarith
      · calc Mt ≤ M * y ^ (k + 1) := hk
          _ = (M * y) * y ^ k := by ring
          _ ≤ (M * y * 2 ^ j) * y ^ k := by
              have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
              have h2 : 0 ≤ M * y := by positivity
              have h3 : 0 ≤ y ^ k := by positivity
              have h4 : M * y ≤ M * y * 2 ^ j := le_mul_of_one_le_right h2 h1
              exact mul_le_mul_of_nonneg_right h4 h3
    have h2M : 2 * M ≤ X := by
      have : M ≤ Mt * y * 2 ^ J := hMtop
      linarith
    have := lift_dyadic ι 𝔪 g hω hgood P hP w hcard hne hcount hM h2M hC hy0 J
      (by nlinarith) (fun _ => (8 * J) ^ k * Φ) (fun _ => by positivity) hpieces
    refine this.mono_v (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
    ring

end L3H

end
end

section
section
/-! # L3H_Asm: rows of norm `≤ D` from dyadic blocks pushed into a window

`assemble`: split the rows `N 𝔡 ≤ D` into the dyadic blocks `(2^i/2, 2^i]`, `i < log₂ ⌊D⌋ + 2`,
and bound each one by `climb`. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

open Classical in
theorem assemble (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6)
    (hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p)
    (P : Finset (Ideal (𝓞 F))) {y Y X : ℝ}
    (hP : ∀ p ∈ P, p.IsMaximal ∧ p ≠ ⊥ ∧ ¬ 𝔪 ≤ p ∧ y < (Ideal.absNorm p : ℝ) ∧
      (Ideal.absNorm p : ℝ) ≤ Y)
    (w : ℕ) (hcard : 8 * w ≤ P.card) (hne : P.Nonempty)
    (hcount : ∀ x : Ideal (𝓞 F), x ≠ ⊥ → (Ideal.absNorm x : ℝ) ≤ X →
      (P.filter (fun p => x ≤ p)).card ≤ w)
    {C D : ℝ} (hD : 1 ≤ D) (hC : C ≤ X) (hy : 1 ≤ y) (J : ℕ) (hJ1 : 1 ≤ J)
    (hJ : 2 * Y ≤ y * 2 ^ J)
    {Mt Φ : ℝ} (hMt : 0 < Mt) (hΦ : 0 ≤ Φ) (hX : 2 * (Mt * y * 2 ^ J) ≤ X)
    (hbase : ∀ M, Mt ≤ M → M ≤ Mt * y * 2 ^ J →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C) Φ)
    (k₀ : ℕ) (hk₀ : Mt ≤ (1 / 2) * y ^ k₀) (hDtop : 2 * D ≤ Mt * y * 2 ^ J) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C)
      ((Nat.log 2 ⌊D⌋₊ + 2 : ℕ) * ((8 * J) ^ k₀ * Φ)) := by
  have hcl := climb ι 𝔪 g hω hgood P hP w hcard hne hcount hC hy J hJ1 hJ hMt hΦ hX hbase k₀
  have hpieces : ∀ i ∈ Finset.range (Nat.log 2 ⌊D⌋₊ + 2),
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 ((2 : ℝ) ^ i / 2) (2 * ((2 : ℝ) ^ i / 2))) (rowsF 𝔪 0 C)
        ((8 * J) ^ k₀ * Φ) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    refine hcl _ (by positivity) ?_ ?_
    · -- 2^i/2 ≤ D... ≤ top
      have hfl : (2 : ℝ) ^ i / 2 ≤ 2 * D := by
        have h1 : 2 ^ i ≤ 2 ^ (Nat.log 2 ⌊D⌋₊ + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ Nat.log 2 ⌊D⌋₊ ≤ ⌊D⌋₊ :=
          Nat.pow_log_le_self 2 (by
            have : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hD)
            omega)
        have h3 : ((2 : ℕ) : ℝ) ^ i ≤ 2 * ⌊D⌋₊ := by
          rw [pow_succ] at h1; exact_mod_cast (by omega : 2 ^ i ≤ 2 * ⌊D⌋₊)
        have h4 : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le (by linarith)
        push_cast at h3
        linarith
      linarith
    · have : (1 / 2 : ℝ) ≤ 2 ^ i / 2 := by
        have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        linarith
      calc Mt ≤ (1 / 2) * y ^ k₀ := hk₀
        _ ≤ (2 ^ i / 2) * y ^ k₀ := by gcongr
  have hU := SBf.biUnion _ _ (rowsF 𝔪 0 C) _ hpieces
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hU
  exact hU.mono_rows (rows_le_subset 𝔪 hD)

end L3H

end
end

section
section
/-! # L3H_Big: the main case `C D ≥ X₀` of `up` (all constants as parameters) -/

open NumberField ArtinPrimitiveRoots Real

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

set_option maxHeartbeats 4000000 in
open Classical in
theorem big (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6)
    (hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p)
    (α : ℝ) (hα : 1 ≤ α) (d : ℕ) (hd : Module.finrank ℤ (𝓞 F) = d) (hd1 : 1 ≤ d)
    (ε η ε₁ δ : ℝ) (k₀ w : ℕ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hε₁0 : 0 < ε₁)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hηda : η * (d + α) ≤ ε / 8) (hε₁d : ε₁ * (1 + d) ≤ ε / 8)
    (hδk : δ * (k₀ + 1) ≤ ε / 8) (hk₀ : 2 ≤ η * k₀) (hw : 2 + (d : ℝ) ≤ η * w)
    (K₁ : ℝ) (hK₁ : ∀ C M : ℝ, 1 ≤ C → 1 ≤ M →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
        (K₁ * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε₁))
    (K' : ℕ) (hK' : K' = 8 * w + 8 + Ideal.absNorm 𝔪)
    (c₁ : ℝ) (hc₁ : c₁ = (2 : ℝ) ^ (1 + K' * d + (d - 1)) * 2 ^ d)
    (C D : ℝ) (hC : 1 ≤ C) (hD : 1 ≤ D) (hX₀ : 2 * c₁ + 2 ≤ C * D) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C)
      ((1 / (δ * Real.log 2) + 2) *
        (8 * (((1 + K' * d + (d - 1) : ℕ) : ℝ) + ((d - 1 : ℕ) : ℝ) * 2 / (δ * Real.log 2))) ^ k₀ *
        (max K₁ 0 * (c₁ + 1 + 2 ^ (α - 1)) * c₁ ^ ε₁) *
        (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε) := by
  obtain ⟨dm, hdm⟩ : ∃ dm, dm = d - 1 := ⟨_, rfl⟩
  rw [← hdm]
  have hddm : d = dm + 1 := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc₁1 : 1 ≤ c₁ := by
    rw [hc₁]; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by norm_num))
  obtain ⟨X, hXd⟩ : ∃ X, X = C * D := ⟨_, rfl⟩
  rw [← hXd] at hX₀ ⊢
  have hX1 : 1 ≤ X := hXd ▸ one_le_mul_of_one_le_of_one_le hC hD
  have hX0 : 0 < X := by linarith
  have hDX : D ≤ X := hXd ▸ le_mul_of_one_le_left (by linarith) hC
  have hCX : C ≤ X := hXd ▸ le_mul_of_one_le_right (by linarith) hD
  have hX2 : 2 ≤ X := by linarith
  -- the scale y
  obtain ⟨y, hyd⟩ : ∃ y : ℕ, y = ⌈X ^ η⌉₊ := ⟨_, rfl⟩
  have hXη1' : 1 < X ^ η := Real.one_lt_rpow (by linarith) hη0
  have hyX : X ^ η ≤ y := hyd ▸ Nat.le_ceil _
  have hy2 : (y : ℝ) ≤ 2 * X ^ η := by
    have := Nat.ceil_lt_add_one (show 0 ≤ X ^ η by linarith); rw [← hyd] at this; linarith
  have hy1 : 1 ≤ y := by
    have : 0 < y := hyd ▸ Nat.ceil_pos.2 (by linarith); omega
  have hyR : (1 : ℝ) < y := lt_of_lt_of_le hXη1' hyX
  have hyR1 : (1 : ℝ) ≤ y := hyR.le
  have hy0 : (0 : ℝ) < y := by linarith
  obtain ⟨P, hPc, hPp⟩ := exists_primes 𝔪 h𝔪 (8 * w + 8) y hy1
  rw [hd, ← hK'] at hPp
  obtain ⟨Yn, hYn⟩ : ∃ Yn : ℕ, Yn = (2 ^ K' * y) ^ d := ⟨_, rfl⟩
  obtain ⟨J, hJd⟩ : ∃ J : ℕ, J = 1 + K' * d + dm * (Nat.log 2 y + 1) := ⟨_, rfl⟩
  have hJ1 : 1 ≤ J := by omega
  have hyl : y < 2 ^ (Nat.log 2 y + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
  have hJn : 2 * Yn ≤ y * 2 ^ J := by
    have h1 : y ^ dm ≤ (2 ^ (Nat.log 2 y + 1)) ^ dm := Nat.pow_le_pow_left hyl.le _
    calc 2 * Yn = 2 * 2 ^ (K' * d) * y ^ dm * y := by
          rw [hYn, mul_pow, ← pow_mul, hddm, pow_succ]; ring
      _ ≤ 2 * 2 ^ (K' * d) * (2 ^ (Nat.log 2 y + 1)) ^ dm * y := by gcongr
      _ = y * 2 ^ J := by
          rw [hJd, ← pow_mul, pow_add, pow_add, pow_one]; ring
  have hJR : 2 * (Yn : ℝ) ≤ y * 2 ^ J := by exact_mod_cast hJn
  have hP' : ∀ p ∈ P, p.IsMaximal ∧ p ≠ ⊥ ∧ ¬ 𝔪 ≤ p ∧ (y : ℝ) < (Ideal.absNorm p : ℝ) ∧
      (Ideal.absNorm p : ℝ) ≤ (Yn : ℝ) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hPp p hp
    exact ⟨h1, h2, h3, by exact_mod_cast h4, by rw [hYn]; exact_mod_cast h5⟩
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hPcard : 8 * w ≤ P.card := by omega
  -- the window
  obtain ⟨Mt, hMtd⟩ : ∃ Mt : ℝ, Mt = max 1 (D / y) := ⟨_, rfl⟩
  have hMt0 : 0 < Mt := hMtd ▸ lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMt1 : 1 ≤ Mt := hMtd ▸ le_max_left _ _
  have hMtD : Mt ≤ D := hMtd ▸ max_le hD (div_le_self (by linarith) hyR1)
  have hMty : D ≤ Mt * y := by
    have : D / y ≤ Mt := hMtd ▸ le_max_right _ _
    rwa [div_le_iff₀ hy0] at this
  have hMtlow : D / (2 * X ^ η) ≤ Mt := by
    refine le_trans ?_ (hMtd ▸ le_max_right _ _)
    exact div_le_div_of_nonneg_left (by linarith) hy0 hy2
  obtain ⟨Mtop, hMtopd⟩ : ∃ Mtop : ℝ, Mtop = Mt * y * 2 ^ J := ⟨_, rfl⟩
  have hMtop0 : 0 ≤ Mtop := by rw [hMtopd]; positivity
  have h2J : (2 : ℝ) ^ J ≤ 2 ^ (1 + K' * d + dm) * (y : ℝ) ^ dm := by
    have hpl : (2 : ℝ) ^ Nat.log 2 y ≤ y := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : y ≠ 0)
    calc (2 : ℝ) ^ J = 2 ^ (1 + K' * d) * (2 * 2 ^ Nat.log 2 y) ^ dm := by
          rw [hJd, ← pow_succ', ← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (1 + K' * d) * (2 * y) ^ dm := by gcongr
      _ = 2 ^ (1 + K' * d + dm) * (y : ℝ) ^ dm := by rw [mul_pow, pow_add]; ring
  have hyd' : (y : ℝ) ^ d ≤ 2 ^ d * X ^ ((d : ℝ) * η) := by
    calc (y : ℝ) ^ d ≤ (2 * X ^ η) ^ d := by gcongr
      _ = 2 ^ d * X ^ ((d : ℝ) * η) := by rw [mul_pow, pow_rpow_eq hX0.le, mul_comm η]
  have hMtop : Mtop ≤ c₁ * D * X ^ ((d : ℝ) * η) := by
    calc Mtop = Mt * y * 2 ^ J := hMtopd
      _ ≤ D * y * (2 ^ (1 + K' * d + dm) * (y : ℝ) ^ dm) := by gcongr
      _ = 2 ^ (1 + K' * d + dm) * D * (y : ℝ) ^ d := by rw [hddm, pow_succ]; ring
      _ ≤ 2 ^ (1 + K' * d + dm) * D * (2 ^ d * X ^ ((d : ℝ) * η)) := by gcongr
      _ = c₁ * D * X ^ ((d : ℝ) * η) := by rw [hc₁, hdm]; ring
  -- the count
  obtain ⟨X', hX'd⟩ : ∃ X' : ℝ, X' = 2 * Mtop + C := ⟨_, rfl⟩
  have hcount : ∀ x : Ideal (𝓞 F), x ≠ ⊥ → (Ideal.absNorm x : ℝ) ≤ X' →
      (P.filter (fun p => x ≤ p)).card ≤ w := by
    intro x hx hxX
    refine card_filter_le P (fun p hp => (hPp p hp).1) hyR (fun p hp => (hP' p hp).2.2.2.1) hx ?_
    have hge : 1 ≤ X ^ ((d : ℝ) * η) := one_le_rpow' hX1 (by positivity)
    have hb1 : X ^ (1 + (d : ℝ) * η) = X * X ^ ((d : ℝ) * η) := by
      rw [Real.rpow_add hX0, Real.rpow_one]
    have h1 : X' ≤ (2 * c₁ + 1) * X ^ (1 + (d : ℝ) * η) := by
      rw [hb1, hX'd]
      have e1 : 2 * Mtop ≤ 2 * (c₁ * X * X ^ ((d : ℝ) * η)) := by
        have : c₁ * D * X ^ ((d : ℝ) * η) ≤ c₁ * X * X ^ ((d : ℝ) * η) := by gcongr
        linarith
      have e2 : C ≤ X * X ^ ((d : ℝ) * η) := le_trans hCX (le_mul_of_one_le_right (by linarith) hge)
      linarith
    have h2 : X ^ (2 + (d : ℝ) * η) ≤ (y : ℝ) ^ (w + 1) := by
      calc X ^ (2 + (d : ℝ) * η) ≤ X ^ (η * ((w + 1 : ℕ) : ℝ)) := by
            refine rpow_mono_exp hX1 ?_
            push_cast
            have : (d : ℝ) * η ≤ d := mul_le_of_le_one_right (by positivity) hη1
            linarith
        _ = (X ^ η) ^ (w + 1) := (pow_rpow_eq hX0.le (w + 1)).symm
        _ ≤ (y : ℝ) ^ (w + 1) := by gcongr
    have h3 : (2 * c₁ + 1) * X ^ (1 + (d : ℝ) * η) < X ^ (2 + (d : ℝ) * η) := by
      have hb : X ^ (2 + (d : ℝ) * η) = X * X ^ (1 + (d : ℝ) * η) := by
        rw [show (2 : ℝ) + d * η = 1 + (1 + d * η) by ring, Real.rpow_add hX0, Real.rpow_one]
      rw [hb]
      have : 0 < X ^ (1 + (d : ℝ) * η) := by positivity
      exact mul_lt_mul_of_pos_right (by linarith) this
    linarith
  -- the base window bound
  obtain ⟨K₁', hK₁'d⟩ : ∃ K₁' : ℝ, K₁' = max K₁ 0 := ⟨_, rfl⟩
  have hK₁'0 : 0 ≤ K₁' := hK₁'d ▸ le_max_right _ _
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : ℝ,
      Φ = K₁' * (Mtop + C + C ^ (2 * α - 1) * Mt ^ (1 - α)) * (C * Mtop) ^ ε₁ := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ := by rw [hΦd]; positivity
  have hbase : ∀ M, Mt ≤ M → M ≤ Mt * y * 2 ^ J →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C) Φ := by
    intro M hM1 hM2
    rw [← hMtopd] at hM2
    have hM1' : 1 ≤ M := le_trans hMt1 hM1
    refine (hK₁ C M hC hM1').mono_v ?_
    have hA : M + C + C ^ (2 * α - 1) * M ^ (1 - α) ≤
        Mtop + C + C ^ (2 * α - 1) * Mt ^ (1 - α) := by
      have h1 : M ^ (1 - α) ≤ Mt ^ (1 - α) := Real.rpow_le_rpow_of_nonpos hMt0 hM1 (by linarith)
      have h2 : C ^ (2 * α - 1) * M ^ (1 - α) ≤ C ^ (2 * α - 1) * Mt ^ (1 - α) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have hB : (C * M) ^ ε₁ ≤ (C * Mtop) ^ ε₁ :=
      Real.rpow_le_rpow (by positivity) (by gcongr) hε₁0.le
    have hA0 : 0 ≤ M + C + C ^ (2 * α - 1) * M ^ (1 - α) := by positivity
    have hK : K₁ ≤ K₁' := hK₁'d ▸ le_max_left _ _
    rw [hΦd]
    calc K₁ * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε₁
        ≤ K₁' * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε₁ := by gcongr
      _ ≤ K₁' * (Mtop + C + C ^ (2 * α - 1) * Mt ^ (1 - α)) * (C * Mtop) ^ ε₁ := by gcongr
  have hk₀' : Mt ≤ (1 / 2) * (y : ℝ) ^ k₀ := by
    have h1 : X ^ (2 : ℝ) ≤ (y : ℝ) ^ k₀ := by
      calc X ^ (2 : ℝ) ≤ X ^ (η * k₀) := rpow_mono_exp hX1 hk₀
        _ = (X ^ η) ^ k₀ := (pow_rpow_eq hX0.le k₀).symm
        _ ≤ (y : ℝ) ^ k₀ := by gcongr
    rw [Real.rpow_two] at h1
    have h2 : 2 * X ≤ X * X := mul_le_mul_of_nonneg_right hX2 hX0.le
    linarith
  have hDtop : 2 * D ≤ Mt * y * 2 ^ J := by
    have : (2 : ℝ) ≤ 2 ^ J := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hJ1
    calc 2 * D ≤ (Mt * y) * 2 := by linarith
      _ ≤ (Mt * y) * 2 ^ J := by gcongr
  have hXtop : 2 * (Mt * y * 2 ^ J) ≤ X' := by rw [hX'd, ← hMtopd]; linarith
  have hCX' : C ≤ X' := by rw [hX'd]; linarith
  have hA := assemble ι 𝔪 g hω hgood P hP' w hPcard hPne hcount hD hCX' hyR1 J hJ1 hJR hMt0 hΦ0
    hXtop hbase k₀ hk₀' hDtop
  refine hA.mono_v ?_
  -- final inequality
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = D + C + C ^ (2 * α - 1) * D ^ (1 - α) := ⟨_, rfl⟩
  rw [← hT]
  have hT0 : 0 ≤ C ^ (2 * α - 1) * D ^ (1 - α) := by positivity
  have hT1 : 1 ≤ T := by rw [hT]; linarith
  have hI : ((Nat.log 2 ⌊D⌋₊ + 2 : ℕ) : ℝ) ≤ (1 / (δ * Real.log 2) + 2) * X ^ δ := by
    have h1 := natlog_le hδ0 ⌊D⌋₊
    have h2 : ((⌊D⌋₊ : ℕ) : ℝ) ^ δ ≤ X ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.floor_le (by linarith)).trans hDX) hδ0.le
    have h3 : 1 ≤ X ^ δ := one_le_rpow' hX1 hδ0.le
    have h4 : (⌊D⌋₊ : ℝ) ^ δ / (δ * Real.log 2) ≤ X ^ δ / (δ * Real.log 2) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    push_cast
    rw [add_mul, div_mul_eq_mul_div, one_mul]
    linarith
  have hJb : (J : ℝ) ≤ (((1 + K' * d + dm : ℕ) : ℝ) + (dm : ℝ) * 2 / (δ * Real.log 2)) *
      X ^ δ := by
    have h1 := natlog_le hδ0 y
    have h2 : (y : ℝ) ^ δ ≤ 2 * X ^ δ := by
      calc (y : ℝ) ^ δ ≤ (2 * X ^ η) ^ δ := Real.rpow_le_rpow (by positivity) hy2 hδ0.le
        _ = 2 ^ δ * X ^ (η * δ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX0.le]
        _ ≤ 2 ^ (1 : ℝ) * X ^ δ :=
            mul_le_mul (rpow_mono_exp (by norm_num) hδ1)
              (rpow_mono_exp hX1 (mul_le_of_le_one_left hδ0.le hη1)) (by positivity)
              (by positivity)
        _ = 2 * X ^ δ := by rw [Real.rpow_one]
    have h3 : 1 ≤ X ^ δ := one_le_rpow' hX1 hδ0.le
    have hlog : (Nat.log 2 y : ℝ) ≤ 2 * X ^ δ / (δ * Real.log 2) :=
      h1.trans (div_le_div_of_nonneg_right h2 (by positivity))
    have hJe : (J : ℝ) = ((1 + K' * d + dm : ℕ) : ℝ) + dm * (Nat.log 2 y : ℝ) := by
      rw [hJd]; push_cast; ring
    rw [hJe, add_mul]
    have hdm0 : (0 : ℝ) ≤ dm := Nat.cast_nonneg _
    have e1 : ((1 + K' * d + dm : ℕ) : ℝ) ≤ ((1 + K' * d + dm : ℕ) : ℝ) * X ^ δ :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) h3
    have e2 : (dm : ℝ) * (Nat.log 2 y : ℝ) ≤ dm * 2 / (δ * Real.log 2) * X ^ δ := by
      calc (dm : ℝ) * (Nat.log 2 y : ℝ) ≤ dm * (2 * X ^ δ / (δ * Real.log 2)) :=
            mul_le_mul_of_nonneg_left hlog hdm0
        _ = dm * 2 / (δ * Real.log 2) * X ^ δ := by ring
    linarith
  obtain ⟨cJ, hcJ⟩ : ∃ cJ : ℝ,
      cJ = ((1 + K' * d + dm : ℕ) : ℝ) + (dm : ℝ) * 2 / (δ * Real.log 2) := ⟨_, rfl⟩
  rw [← hcJ] at hJb ⊢
  have hcJ0 : 0 ≤ cJ := by rw [hcJ]; positivity
  have h8J : (8 * (J : ℝ)) ^ k₀ ≤ (8 * cJ) ^ k₀ * X ^ (δ * k₀) := by
    calc (8 * (J : ℝ)) ^ k₀ ≤ (8 * (cJ * X ^ δ)) ^ k₀ := by gcongr
      _ = (8 * cJ) ^ k₀ * X ^ (δ * k₀) := by rw [← pow_rpow_eq hX0.le]; ring
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = X ^ (η * (d + α)) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := hE ▸ one_le_rpow' hX1 (by positivity)
  have hTm : Mtop + C + C ^ (2 * α - 1) * Mt ^ (1 - α) ≤ (c₁ + 1 + 2 ^ (α - 1)) * E * T := by
    have hMtα : Mt ^ (1 - α) ≤ 2 ^ (α - 1) * E * D ^ (1 - α) := by
      have h0 : 0 < 2 * X ^ η := by positivity
      have h1 : Mt ^ (1 - α) ≤ (D / (2 * X ^ η)) ^ (1 - α) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hMtlow (by linarith)
      have h2 : (D / (2 * X ^ η)) ^ (1 - α) = D ^ (1 - α) * (2 * X ^ η) ^ (α - 1) := by
        rw [Real.div_rpow (by linarith) h0.le, div_eq_mul_inv, ← Real.rpow_neg h0.le]
        congr 2; ring
      have h3 : (2 * X ^ η) ^ (α - 1) = 2 ^ (α - 1) * X ^ (η * (α - 1)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX0.le]
      have h4 : X ^ (η * (α - 1)) ≤ E := hE ▸ rpow_mono_exp hX1
        (mul_le_mul_of_nonneg_left (by linarith) hη0.le)
      rw [h2, h3] at h1
      have h5 : D ^ (1 - α) * (2 ^ (α - 1) * X ^ (η * (α - 1))) ≤
          D ^ (1 - α) * (2 ^ (α - 1) * E) := by gcongr
      linarith
    have hc1 : Mtop ≤ c₁ * E * D := by
      have : X ^ ((d : ℝ) * η) ≤ E := hE ▸ rpow_mono_exp hX1 (by
        have := mul_le_mul_of_nonneg_left (show (d : ℝ) ≤ d + α by linarith) hη0.le
        linarith)
      calc Mtop ≤ c₁ * D * X ^ ((d : ℝ) * η) := hMtop
        _ ≤ c₁ * D * E := by gcongr
        _ = c₁ * E * D := by ring
    have hc2 : C ^ (2 * α - 1) * Mt ^ (1 - α) ≤
        2 ^ (α - 1) * E * (C ^ (2 * α - 1) * D ^ (1 - α)) := by
      have hCp : 0 ≤ C ^ (2 * α - 1) := by positivity
      calc C ^ (2 * α - 1) * Mt ^ (1 - α)
          ≤ C ^ (2 * α - 1) * (2 ^ (α - 1) * E * D ^ (1 - α)) :=
            mul_le_mul_of_nonneg_left hMtα hCp
        _ = 2 ^ (α - 1) * E * (C ^ (2 * α - 1) * D ^ (1 - α)) := by ring
    have hc3 : C ≤ E * C := le_mul_of_one_le_left (by linarith) hE1
    have h2p : 0 ≤ (2 : ℝ) ^ (α - 1) := by positivity
    have hE0 : 0 ≤ E := by linarith
    have expand : (c₁ + 1 + 2 ^ (α - 1)) * E * T = c₁ * E * D + c₁ * E * C +
        c₁ * E * (C ^ (2 * α - 1) * D ^ (1 - α)) + E * D + E * C +
        E * (C ^ (2 * α - 1) * D ^ (1 - α)) + 2 ^ (α - 1) * E * D + 2 ^ (α - 1) * E * C +
        2 ^ (α - 1) * E * (C ^ (2 * α - 1) * D ^ (1 - α)) := by rw [hT]; ring
    rw [expand]
    have p1 : 0 ≤ c₁ * E * C := by positivity
    have p2 : 0 ≤ c₁ * E * (C ^ (2 * α - 1) * D ^ (1 - α)) := by positivity
    have p3 : 0 ≤ E * D := by positivity
    have p4 : 0 ≤ E * (C ^ (2 * α - 1) * D ^ (1 - α)) := by positivity
    have p5 : 0 ≤ 2 ^ (α - 1) * E * D := by positivity
    have p6 : 0 ≤ 2 ^ (α - 1) * E * C := by positivity
    linarith
  have hCM : (C * Mtop) ^ ε₁ ≤ c₁ ^ ε₁ * X ^ (ε₁ * (1 + d)) := by
    have h1 : C * Mtop ≤ c₁ * X ^ (1 + (d : ℝ)) := by
      have hdη : X ^ ((d : ℝ) * η) ≤ X ^ (d : ℝ) :=
        rpow_mono_exp hX1 (mul_le_of_le_one_right (by positivity) hη1)
      calc C * Mtop ≤ C * (c₁ * D * X ^ ((d : ℝ) * η)) := by gcongr
        _ = c₁ * X * X ^ ((d : ℝ) * η) := by rw [hXd]; ring
        _ ≤ c₁ * X * X ^ (d : ℝ) := by gcongr
        _ = c₁ * X ^ (1 + (d : ℝ)) := by rw [Real.rpow_add hX0, Real.rpow_one]; ring
    calc (C * Mtop) ^ ε₁ ≤ (c₁ * X ^ (1 + (d : ℝ))) ^ ε₁ :=
          Real.rpow_le_rpow (by positivity) h1 hε₁0.le
      _ = c₁ ^ ε₁ * X ^ (ε₁ * (1 + d)) := by
          rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hX0.le, mul_comm ε₁]
  have hΦb : Φ ≤ K₁' * (c₁ + 1 + 2 ^ (α - 1)) * c₁ ^ ε₁ * (E * X ^ (ε₁ * (1 + d))) * T := by
    rw [hΦd]
    have hA0 : 0 ≤ Mtop + C + C ^ (2 * α - 1) * Mt ^ (1 - α) := by positivity
    calc K₁' * (Mtop + C + C ^ (2 * α - 1) * Mt ^ (1 - α)) * (C * Mtop) ^ ε₁
        ≤ K₁' * ((c₁ + 1 + 2 ^ (α - 1)) * E * T) * (c₁ ^ ε₁ * X ^ (ε₁ * (1 + d))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTm hK₁'0) hCM
            (Real.rpow_nonneg (mul_nonneg (by linarith only [hC]) hMtop0) _)
            (mul_nonneg hK₁'0 (mul_nonneg (mul_nonneg (by
              have h2 := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (α - 1)
              linarith only [hc₁1, h2]) (by linarith only [hE1])) (by linarith only [hT1])))
      _ = K₁' * (c₁ + 1 + 2 ^ (α - 1)) * c₁ ^ ε₁ * (E * X ^ (ε₁ * (1 + d))) * T := by ring
  have hε0 : 0 ≤ ε := by
    have : 0 ≤ η * (d + α) := mul_nonneg hη0.le (by linarith only [hα])
    linarith only [hηda, this]
  have hexp : δ + δ * k₀ + (η * (d + α) + ε₁ * (1 + d)) ≤ ε := by
    linarith only [hηda, hε₁d, hδk, hε0]
  have hXe : X ^ δ * X ^ (δ * k₀) * (E * X ^ (ε₁ * (1 + d))) ≤ X ^ ε := by
    rw [hE, ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact rpow_mono_exp hX1 (by linarith)
  rw [← hK₁'d]
  have hcI0 : 0 ≤ 1 / (δ * Real.log 2) + 2 := by positivity
  have hJ0 : (0 : ℝ) ≤ (8 * (J : ℝ)) ^ k₀ := by positivity
  have hI0 : (0 : ℝ) ≤ ((Nat.log 2 ⌊D⌋₊ + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = K₁' * (c₁ + 1 + 2 ^ (α - 1)) * c₁ ^ ε₁ := ⟨_, rfl⟩
  rw [← hG] at hΦb ⊢
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hXp : 0 ≤ E * X ^ (ε₁ * (1 + d)) := by positivity
  calc ((Nat.log 2 ⌊D⌋₊ + 2 : ℕ) : ℝ) * ((8 * (J : ℝ)) ^ k₀ * Φ)
      ≤ ((1 / (δ * Real.log 2) + 2) * X ^ δ) * (((8 * cJ) ^ k₀ * X ^ (δ * k₀)) *
          (G * (E * X ^ (ε₁ * (1 + d))) * T)) := by
        gcongr
    _ = (1 / (δ * Real.log 2) + 2) * (8 * cJ) ^ k₀ * G * T *
          (X ^ δ * X ^ (δ * k₀) * (E * X ^ (ε₁ * (1 + d)))) := by ring
    _ ≤ (1 / (δ * Real.log 2) + 2) * (8 * cJ) ^ k₀ * G * T * X ^ ε := by
        gcongr

end L3H

end
end

section
section
/-! # L3H_Stage1: the `≤`-form of GL Theorem 4.3 from the dyadic form, for one `(𝔪, g, α)`

`up`: for every `ε > 0` the bound with rows `N 𝔡 ≤ D`, from the dyadic bounds for every `ε₁ > 0`.
The constants: `η = ε / (8 (d + α + 1))`, `ε₁ = ε / (8 (d + 1))`, `k₀ = ⌈2/η⌉`,
`δ = ε / (8 (k₀ + 1))`, `w = ⌈(2 + d)/η⌉`; small `C D` use the trivial bound. -/

open NumberField ArtinPrimitiveRoots Real

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

theorem up_main (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6)
    (hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p)
    (α : ℝ) (hα : 1 ≤ α)
    (hdy : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C M : ℝ, 1 ≤ C → 1 ≤ M →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
        (K * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C)
        (K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε) := by
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank ℤ (𝓞 F) = d := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := hd ▸ Module.finrank_pos
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (8 * (d + α + 1)) := ⟨_, rfl⟩
  have hden : 0 < 8 * ((d : ℝ) + α + 1) := by positivity
  have hη0 : 0 < η := hη ▸ div_pos hε hden
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one hden]; linarith
  have hηda : η * (d + α) ≤ ε / 8 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]; nlinarith
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = ε / (8 * (d + 1)) := ⟨_, rfl⟩
  have hden1 : 0 < 8 * ((d : ℝ) + 1) := by positivity
  have hε₁0 : 0 < ε₁ := hε₁ ▸ div_pos hε hden1
  have hε₁d : ε₁ * (1 + d) ≤ ε / 8 := by
    rw [hε₁, div_mul_eq_mul_div, div_le_div_iff₀ hden1 (by norm_num)]; nlinarith
  obtain ⟨k₀, hk₀d⟩ : ∃ k₀ : ℕ, k₀ = ⌈2 / η⌉₊ := ⟨_, rfl⟩
  have hk₀ : 2 ≤ η * k₀ := by
    have := Nat.le_ceil (2 / η)
    rw [← hk₀d, div_le_iff₀ hη0] at this; linarith
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε / (8 * (k₀ + 1)) := ⟨_, rfl⟩
  have hdenδ : 0 < 8 * ((k₀ : ℝ) + 1) := by positivity
  have hδ0 : 0 < δ := hδd ▸ div_pos hε hdenδ
  have hδ1 : δ ≤ 1 := by
    rw [hδd, div_le_one hdenδ]; have : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _; linarith
  have hδk : δ * (k₀ + 1) ≤ ε / 8 := by
    rw [hδd, div_mul_eq_mul_div, div_le_div_iff₀ hdenδ (by norm_num)]; nlinarith
  obtain ⟨w, hwd⟩ : ∃ w : ℕ, w = ⌈(2 + (d : ℝ)) / η⌉₊ := ⟨_, rfl⟩
  have hw : 2 + (d : ℝ) ≤ η * w := by
    have := Nat.le_ceil ((2 + (d : ℝ)) / η)
    rw [← hwd, div_le_iff₀ hη0] at this; linarith
  obtain ⟨K', hK'⟩ : ∃ K' : ℕ, K' = 8 * w + 8 + Ideal.absNorm 𝔪 := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (2 : ℝ) ^ (1 + K' * d + (d - 1)) * 2 ^ d := ⟨_, rfl⟩
  have hc₁1 : 1 ≤ c₁ := by
    rw [hc₁]; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by norm_num))
  obtain ⟨K₁, hK₁⟩ := hdy ε₁ hε₁0
  obtain ⟨Ncnt, hNcnt⟩ : ∃ Ncnt : ℝ, Ncnt = ((rowsF 𝔪 0 (2 * c₁ + 2)).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, Kb = (1 / (δ * Real.log 2) + 2) *
      (8 * (((1 + K' * d + (d - 1) : ℕ) : ℝ) + ((d - 1 : ℕ) : ℝ) * 2 / (δ * Real.log 2))) ^ k₀ *
      (max K₁ 0 * (c₁ + 1 + 2 ^ (α - 1)) * c₁ ^ ε₁) := ⟨_, rfl⟩
  refine ⟨max (Ncnt ^ 2) Kb, fun C D hC hD => ?_⟩
  have hX1 : 1 ≤ C * D := one_le_mul_of_one_le_of_one_le hC hD
  have hDX : D ≤ C * D := le_mul_of_one_le_left (by linarith) hC
  have hCX : C ≤ C * D := le_mul_of_one_le_right (by linarith) hD
  have hT0 : 0 ≤ C ^ (2 * α - 1) * D ^ (1 - α) := by positivity
  have hT1 : 1 ≤ D + C + C ^ (2 * α - 1) * D ^ (1 - α) := by linarith
  have hXε : 1 ≤ (C * D) ^ ε := Real.one_le_rpow hX1 hε.le
  by_cases hsmall : C * D < 2 * c₁ + 2
  · have hR : (rowsF 𝔪 0 D).card ≤ (rowsF 𝔪 0 (2 * c₁ + 2)).card := by
      refine Finset.card_le_card fun a ha => ?_
      obtain ⟨h1, h2, h3, h4⟩ := mem_rowsF.1 ha
      exact mem_rowsF.2 ⟨h1, h2, h3, by linarith⟩
    have hCs : (rowsF 𝔪 0 C).card ≤ (rowsF 𝔪 0 (2 * c₁ + 2)).card := by
      refine Finset.card_le_card fun a ha => ?_
      obtain ⟨h1, h2, h3, h4⟩ := mem_rowsF.1 ha
      exact mem_rowsF.2 ⟨h1, h2, h3, by linarith⟩
    refine (SBf_card ι 𝔪 g _ _).mono_v ?_
    have hR' : ((rowsF 𝔪 0 D).card : ℝ) ≤ Ncnt := by rw [hNcnt]; exact_mod_cast hR
    have hC' : ((rowsF 𝔪 0 C).card : ℝ) ≤ Ncnt := by rw [hNcnt]; exact_mod_cast hCs
    have hN0 : 0 ≤ Ncnt := by rw [hNcnt]; exact Nat.cast_nonneg _
    have hmax : Ncnt ^ 2 ≤ max (Ncnt ^ 2) Kb := le_max_left _ _
    have hm0 : 0 ≤ max (Ncnt ^ 2) Kb := le_trans (sq_nonneg _) hmax
    calc ((rowsF 𝔪 0 D).card : ℝ) * (rowsF 𝔪 0 C).card ≤ Ncnt ^ 2 := by
          rw [sq]; exact mul_le_mul hR' hC' (Nat.cast_nonneg _) hN0
      _ ≤ max (Ncnt ^ 2) Kb * 1 * 1 := by rw [mul_one, mul_one]; exact hmax
      _ ≤ max (Ncnt ^ 2) Kb * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε := by
          gcongr
  push Not at hsmall
  have hB := big ι 𝔪 h𝔪 g hω hgood α hα d hd hd1 ε η ε₁ δ k₀ w hη0 hη1 hε₁0 hδ0 hδ1 hηda hε₁d
    hδk hk₀ hw K₁ hK₁ K' hK' c₁ hc₁ C D hC hD hsmall
  rw [← hKb] at hB
  refine hB.mono_v ?_
  gcongr
  exact le_max_right _ _

/-- `up` for every `ε > 0`. -/
theorem up (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6)
    (hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p)
    (α : ℝ) (hα : 1 ≤ α)
    (hdy : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C M : ℝ, 1 ≤ C → 1 ≤ M →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
        (K * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C)
        (K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε) := by
  obtain ⟨K, hK⟩ := up_main ι 𝔪 h𝔪 g hω hgood α hα hdy (min ε 1) (lt_min hε one_pos)
    (min_le_right _ _)
  refine ⟨max K 0, fun C D hC hD => ?_⟩
  refine (hK C D hC hD).mono_v ?_
  have hX1 : 1 ≤ C * D := one_le_mul_of_one_le_of_one_le hC hD
  have hT : 0 ≤ D + C + C ^ (2 * α - 1) * D ^ (1 - α) := by positivity
  have h1 : (C * D) ^ min ε 1 ≤ (C * D) ^ ε := rpow_mono_exp hX1 (min_le_left _ _)
  calc K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ min ε 1
      ≤ max K 0 * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ min ε 1 := by
        gcongr; exact le_max_left _ _
    _ ≤ max K 0 * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε := by
        gcongr

end L3H

end
end

section
section
/-! # L3H_Mob: Möbius function and divisor counts for squarefree ideals of `𝓞 F`

* `pf n`: the set of prime factors; for squarefree `n ≠ ⊥`, `∏_{p ∈ pf n} p = n`.
* `mobI`: `μ(d) = (-1)^ω(d)` on squarefree `d`, `0` otherwise.
* `sum_mobI`: `∑_{d ∈ S, d ∣ n} μ(d) = [n = ⊤]` for squarefree `n ≠ ⊥`, if `S` holds every divisor.
* `card_dvd_le`: `#{d ∈ S, d ∣ n} ≤ 2^ω(n)` for squarefree `n ≠ ⊥`.
* `two_pow_card_pf_le`: `2^ω(n) ≤ C_ε (N n)^ε` for squarefree `n ≠ ⊥`.
-/

open NumberField UniqueFactorizationMonoid

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The prime factors. -/
noncomputable def pf (n : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := (normalizedFactors n).toFinset

open Classical in
/-- The Möbius function on ideals. -/
noncomputable def mobI (d : Ideal (𝓞 F)) : ℤ :=
  if Squarefree d then (-1) ^ (normalizedFactors d).card else 0

lemma nodup_of_sq {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (normalizedFactors n).Nodup :=
  (squarefree_iff_nodup_normalizedFactors hn0).1 hn

open Classical in
lemma pf_val {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (pf n).val = normalizedFactors n := by
  unfold pf; rw [Multiset.toFinset_val, Multiset.dedup_eq_self.2 (nodup_of_sq hn0 hn)]

lemma prod_pf {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) : ∏ p ∈ pf n, p = n := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', pf_val hn0 hn]
  exact Ideal.prod_normalizedFactors_eq_self hn0

lemma prime_of_mem_pf {n p : Ideal (𝓞 F)} (hp : p ∈ pf n) : Prime p := by
  unfold pf at hp; rw [Multiset.mem_toFinset] at hp
  exact prime_of_normalized_factor p hp

lemma nf_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) :
    normalizedFactors (∏ p ∈ T, p) = T.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact normalizedFactors_prod_of_prime fun p hp => hT p hp

lemma sq_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) : Squarefree (∏ p ∈ T, p) := by
  have h0 : ∏ p ∈ T, p ≠ ⊥ := by
    have : ∏ p ∈ T, p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hT p hp).ne_zero
    rwa [Ideal.zero_eq_bot] at this
  rw [squarefree_iff_nodup_normalizedFactors h0, nf_prod T hT]
  exact T.nodup

open Classical in
lemma pf_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) : pf (∏ p ∈ T, p) = T := by
  unfold pf; rw [nf_prod T hT]; simp

open Classical in
lemma mobI_prod (T : Finset (Ideal (𝓞 F))) (hT : ∀ p ∈ T, Prime p) :
    mobI (∏ p ∈ T, p) = (-1) ^ T.card := by
  unfold mobI; rw [if_pos (sq_prod T hT), nf_prod T hT]; rfl

lemma pf_subset_of_dvd {d n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hd : d ∣ n) : pf d ⊆ pf n := by
  classical
  have hd0 : d ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd)
  intro p hp
  unfold pf at hp ⊢
  rw [Multiset.mem_toFinset] at hp ⊢
  exact Multiset.subset_of_le ((dvd_iff_normalizedFactors_le_normalizedFactors hd0 hn0).1 hd) hp

lemma sq_of_dvd {d n : Ideal (𝓞 F)} (hn : Squarefree n) (hd : d ∣ n) : Squarefree d :=
  hn.squarefree_of_dvd hd

open Classical in
/-- Divisors of a squarefree `n` and subsets of its prime factors. -/
lemma sum_dvd_eq_sum_powerset {M : Type*} [AddCommMonoid M] (S : Finset (Ideal (𝓞 F)))
    {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) (hS : ∀ d, d ∣ n → d ∈ S)
    (f : Ideal (𝓞 F) → M) :
    ∑ d ∈ S.filter (· ∣ n), f d = ∑ T ∈ (pf n).powerset, f (∏ p ∈ T, p) := by
  refine Finset.sum_nbij' (fun d => pf d) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_powerset]
    exact pf_subset_of_dvd hn0 hd.2
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.mem_filter]
    have hdvd : ∏ p ∈ T, p ∣ n := by
      rw [← prod_pf hn0 hn]; exact Finset.prod_dvd_prod_of_subset _ _ _ hT
    exact ⟨hS _ hdvd, hdvd⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd0 : d ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd.2)
    exact prod_pf hd0 (sq_of_dvd hn hd.2)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact pf_prod T fun p hp => prime_of_mem_pf (hT hp)
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd0 : d ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd.2)
    rw [prod_pf hd0 (sq_of_dvd hn hd.2)]

lemma pf_eq_empty {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    pf n = ∅ ↔ n = ⊤ := by
  constructor
  · intro h; rw [← prod_pf hn0 hn, h, Finset.prod_empty, Ideal.one_eq_top]
  · rintro rfl
    classical
    unfold pf; rw [← Ideal.one_eq_top, normalizedFactors_one]; rfl

open Classical in
theorem sum_mobI (S : Finset (Ideal (𝓞 F))) {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n)
    (hS : ∀ d, d ∣ n → d ∈ S) :
    ∑ d ∈ S.filter (· ∣ n), mobI d = if n = ⊤ then 1 else 0 := by
  rw [sum_dvd_eq_sum_powerset S hn0 hn hS]
  rw [Finset.sum_congr rfl fun T hT => mobI_prod T fun p hp =>
    prime_of_mem_pf (Finset.mem_powerset.1 hT hp)]
  rw [Finset.sum_powerset_neg_one_pow_card]
  simp only [pf_eq_empty hn0 hn]

open Classical in
theorem card_dvd_le (S : Finset (Ideal (𝓞 F))) {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥)
    (hn : Squarefree n) : (S.filter (· ∣ n)).card ≤ 2 ^ (pf n).card := by
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun d => pf d) ?_ ?_
  · intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact pf_subset_of_dvd hn0 hd.2
  · intro d₁ hd₁ d₂ hd₂ h
    rw [Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
    have h1 : d₁ ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd₁.2)
    have h2 : d₂ ≠ ⊥ := by rintro rfl; exact hn0 (zero_dvd_iff.1 hd₂.2)
    rw [← prod_pf h1 (sq_of_dvd hn hd₁.2), ← prod_pf h2 (sq_of_dvd hn hd₂.2)]
    exact congrArg (fun T => ∏ p ∈ T, p) h

lemma absNorm_eq_prod_pf {n : Ideal (𝓞 F)} (hn0 : n ≠ ⊥) (hn : Squarefree n) :
    (Ideal.absNorm n : ℝ) = ∏ p ∈ pf n, (Ideal.absNorm p : ℝ) := by
  conv_lhs => rw [← prod_pf hn0 hn]
  rw [map_prod, Nat.cast_prod]

/-- The divisor bound `2^ω(n) ≤ C_ε (N n)^ε` on squarefree ideals. -/
theorem two_pow_card_pf_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Ideal (𝓞 F), n ≠ ⊥ → Squarefree n →
      (2 : ℝ) ^ (pf n).card ≤ C * (Ideal.absNorm n : ℝ) ^ ε := by
  classical
  set B : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  set small : Finset (Ideal (𝓞 F)) :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) B).toFinset
  refine ⟨2 ^ small.card, by positivity, fun n hn0 hn => ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := pf n) (fun p => p ∈ small)
  have hs : ((pf n).filter (fun p => p ∈ small)).card ≤ small.card :=
    Finset.card_le_card fun p hp => (Finset.mem_filter.1 hp).2
  have hlarge : (2 : ℝ) ^ ((pf n).filter (fun p => p ∉ small)).card ≤
      (Ideal.absNorm n : ℝ) ^ ε := by
    rw [absNorm_eq_prod_pf hn0 hn, ← Real.finset_prod_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
    rw [← Finset.prod_const]
    calc ∏ _p ∈ (pf n).filter (fun p => p ∉ small), (2 : ℝ)
        ≤ ∏ p ∈ (pf n).filter (fun p => p ∉ small), (Ideal.absNorm p : ℝ) ^ ε := by
          refine Finset.prod_le_prod (fun _ _ => by norm_num) fun p hp => ?_
          have hp' := (Finset.mem_filter.1 hp).2
          have hB : (B : ℝ) < Ideal.absNorm p := by
            by_contra h
            push Not at h
            apply hp'
            rw [Set.Finite.mem_toFinset]
            exact_mod_cast h
          have h2 : (2 : ℝ) ^ (1 / ε) ≤ B := Nat.le_ceil _
          have h3 : (2 : ℝ) ^ (1 / ε) ≤ Ideal.absNorm p := le_trans h2 hB.le
          calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
                rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
            _ ≤ (Ideal.absNorm p : ℝ) ^ ε :=
                Real.rpow_le_rpow (by positivity) h3 hε.le
      _ ≤ ∏ p ∈ pf n, (Ideal.absNorm p : ℝ) ^ ε := by
          rw [← Finset.prod_filter_mul_prod_filter_not (pf n) (fun p => p ∉ small)]
          have h1 : (1 : ℝ) ≤ ∏ p ∈ (pf n).filter (fun p => ¬ p ∉ small),
              (Ideal.absNorm p : ℝ) ^ ε := by
            rw [← Finset.prod_const_one (s := (pf n).filter (fun p => ¬ p ∉ small))]
            refine Finset.prod_le_prod (fun _ _ => zero_le_one) ?_
            intro p hp
            have hp0 : p ≠ ⊥ := (prime_of_mem_pf (Finset.mem_filter.1 hp).1).ne_zero
            have : Ideal.absNorm p ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp0
            have : (1 : ℝ) ≤ Ideal.absNorm p := by exact_mod_cast Nat.one_le_iff_ne_zero.2 this
            exact Real.one_le_rpow this hε.le
          have h0 : 0 ≤ ∏ p ∈ (pf n).filter (fun p => p ∉ small), (Ideal.absNorm p : ℝ) ^ ε :=
            Finset.prod_nonneg fun _ _ => by positivity
          nlinarith
  calc (2 : ℝ) ^ (pf n).card
      = 2 ^ ((pf n).filter (fun p => p ∈ small)).card *
          2 ^ ((pf n).filter (fun p => p ∉ small)).card := by rw [← pow_add, hsplit]
    _ ≤ 2 ^ small.card * (Ideal.absNorm n : ℝ) ^ ε := by
        gcongr
        · norm_num

end L3H

end
end

section
section
/-! # L3H_S3: the weighted forms `Q` (GL's `Σ₂`, `B₂`) and `S3` (GL's `Σ₃`)

Rows `a ∈ Rw` with weights `w a ≥ 0`, kernel `χ a c`, columns a `Finset`.
* `Qf Cs μ = ∑_a w a ‖∑_{c ∈ Cs} μ c χ a c‖²`; `B2f Cs v`: `Qf Cs μ ≤ v ∑ ‖μ c‖²` for all `μ`.
* `S3 Cs 𝔤 λ = ∑_{b₁, b₂ ∈ Cs, b₁ ⊔ b₂ = 𝔤} λ b₁ conj(λ b₂) ∑_a w a χ a b₁ conj(χ a b₂)`.
* `Qf_eq_sum_S3`: `Qf = ∑_𝔤 S3` (sorting the pairs by their gcd).
* `Qf_le_classes`: Cauchy–Schwarz over `k` classes.
* `norm_S3_le_tail`: GL Lemma 5.1's Möbius step: for `𝔤 ≠ ⊥`, `‖S3 Cs 𝔤 λ‖` is at most
  `v' ∑_{d} ∑_{c, d ∣ c} ‖λ(𝔤 c)‖²` from the bound `v'` on columns `c` with `𝔤 c ∈ Cs`.
-/

open NumberField

namespace L3H

section abstract

variable {I : Type*} (χ : I → I → ℂ) (Rw : Finset I) (w : I → ℝ)

/-- GL's `Σ₂` with the smooth weight. -/
noncomputable def Qf (Cs : Finset I) (μ : I → ℂ) : ℝ :=
  ∑ a ∈ Rw, w a * ‖∑ c ∈ Cs, μ c * χ a c‖ ^ 2

/-- GL's `B₂ ≤ v`. -/
def B2f (Cs : Finset I) (v : ℝ) : Prop :=
  ∀ μ : I → ℂ, Qf χ Rw w Cs μ ≤ v * ∑ c ∈ Cs, ‖μ c‖ ^ 2

/-- GL's `Σ₃`. -/
noncomputable def S3 [DecidableEq I] (gcd : I → I → I) (Cs : Finset I) (𝔤 : I) (μ : I → ℂ) : ℂ :=
  ∑ b₁ ∈ Cs, ∑ b₂ ∈ Cs, if gcd b₁ b₂ = 𝔤 then
    μ b₁ * starRingEnd ℂ (μ b₂) * ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂) else 0

variable {χ Rw w}

lemma Qf_nonneg (hw : ∀ a, 0 ≤ w a) (Cs : Finset I) (μ : I → ℂ) : 0 ≤ Qf χ Rw w Cs μ :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (by positivity)

lemma Qf_eq_double [DecidableEq I] (Cs : Finset I) (μ : I → ℂ) :
    (Qf χ Rw w Cs μ : ℂ) = ∑ b₁ ∈ Cs, ∑ b₂ ∈ Cs,
      μ b₁ * starRingEnd ℂ (μ b₂) * ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂) := by
  unfold Qf
  push_cast
  have : ∀ a, ((‖∑ c ∈ Cs, μ c * χ a c‖ : ℝ) : ℂ) ^ 2 =
      ∑ b₁ ∈ Cs, ∑ b₂ ∈ Cs, μ b₁ * χ a b₁ * starRingEnd ℂ (μ b₂ * χ a b₂) := by
    intro a
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]; ring

theorem Qf_eq_sum_S3 [DecidableEq I] (gcd : I → I → I) (Cs Gs : Finset I)
    (hGs : ∀ b₁ ∈ Cs, ∀ b₂ ∈ Cs, gcd b₁ b₂ ∈ Gs) (μ : I → ℂ) :
    (Qf χ Rw w Cs μ : ℂ) = ∑ 𝔤 ∈ Gs, S3 χ Rw w gcd Cs 𝔤 μ := by
  rw [Qf_eq_double]
  unfold S3
  symm
  calc ∑ 𝔤 ∈ Gs, ∑ b₁ ∈ Cs, ∑ b₂ ∈ Cs, (if gcd b₁ b₂ = 𝔤 then
        μ b₁ * starRingEnd ℂ (μ b₂) * ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂)
          else 0)
      = ∑ b₁ ∈ Cs, ∑ 𝔤 ∈ Gs, ∑ b₂ ∈ Cs, (if gcd b₁ b₂ = 𝔤 then
        μ b₁ * starRingEnd ℂ (μ b₂) * ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂)
          else 0) := Finset.sum_comm
    _ = ∑ b₁ ∈ Cs, ∑ b₂ ∈ Cs, ∑ 𝔤 ∈ Gs, (if gcd b₁ b₂ = 𝔤 then
        μ b₁ * starRingEnd ℂ (μ b₂) * ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂)
          else 0) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun b₁ hb₁ => Finset.sum_congr rfl fun b₂ hb₂ => ?_
        rw [Finset.sum_ite_eq Gs (gcd b₁ b₂), if_pos (hGs b₁ hb₁ b₂ hb₂)]

theorem B2f.mono_cols {Cs Cs' : Finset I} {v : ℝ} (h : B2f χ Rw w Cs v) (hC : Cs' ⊆ Cs) :
    B2f χ Rw w Cs' v := by
  classical
  intro μ
  have := h (fun c => if c ∈ Cs' then μ c else 0)
  have e1 : ∀ a, ∑ c ∈ Cs, (if c ∈ Cs' then μ c else 0) * χ a c = ∑ c ∈ Cs', μ c * χ a c := by
    intro a
    rw [← Finset.sum_subset hC (f := fun c => (if c ∈ Cs' then μ c else 0) * χ a c)]
    · exact Finset.sum_congr rfl fun c hc => by rw [if_pos hc]
    · intro c _ hc; rw [if_neg hc, zero_mul]
  have e2 : ∑ c ∈ Cs, ‖(if c ∈ Cs' then μ c else 0)‖ ^ 2 = ∑ c ∈ Cs', ‖μ c‖ ^ 2 := by
    rw [← Finset.sum_subset hC (f := fun c => ‖(if c ∈ Cs' then μ c else 0)‖ ^ 2)]
    · exact Finset.sum_congr rfl fun c hc => by rw [if_pos hc]
    · intro c _ hc; simp [hc]
  unfold Qf at this ⊢
  simp only [e1, e2] at this
  exact this

theorem B2f.mono_v {Cs : Finset I} {v v' : ℝ} (h : B2f χ Rw w Cs v) (hv : v ≤ v') :
    B2f χ Rw w Cs v' := fun μ =>
  (h μ).trans (mul_le_mul_of_nonneg_right hv (Finset.sum_nonneg fun _ _ => by positivity))

/-- Cauchy–Schwarz over `k` classes. -/
theorem Qf_le_classes [DecidableEq I] (hw : ∀ a, 0 ≤ w a) (k : ℕ) (cls : I → Fin k)
    (Cs : Finset I) (μ : I → ℂ) :
    Qf χ Rw w Cs μ ≤ k * ∑ j : Fin k, Qf χ Rw w (Cs.filter (fun c => cls c = j)) μ := by
  unfold Qf
  have hR : (k : ℝ) * ∑ j : Fin k, ∑ a ∈ Rw,
      w a * ‖∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c‖ ^ 2 =
      ∑ a ∈ Rw, w a * (k * ∑ j : Fin k,
        ‖∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c‖ ^ 2) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum]; ring
  rw [hR]
  refine Finset.sum_le_sum fun a _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hw a)
  have hsplit : ∑ c ∈ Cs, μ c * χ a c =
      ∑ j : Fin k, ∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c :=
    (Finset.sum_fiberwise Cs cls _).symm
  rw [hsplit]
  calc ‖∑ j : Fin k, ∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c‖ ^ 2
      ≤ (∑ j : Fin k, ‖∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (Finset.univ : Finset (Fin k)).card *
          ∑ j : Fin k, ‖∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = k * ∑ j : Fin k, ‖∑ c ∈ Cs.filter (fun c => cls c = j), μ c * χ a c‖ ^ 2 := by
        rw [Finset.card_univ, Fintype.card_fin]

end abstract

end L3H

end
end

section
section
/-! # L3H_Tail: the Möbius step of GL Lemma 5.1

For `𝔤 ≠ ⊥`: pairs `b₁, b₂` with `b₁ ⊔ b₂ = 𝔤` are `b_i = 𝔤 c_i` with `c₁ ⊔ c₂ = ⊤`; detecting
`c₁ ⊔ c₂ = ⊤` by `∑_{d ∣ c₁, d ∣ c₂} μ(d)` turns `S3` into `∑_d μ(d) Q(c ≡ 0 mod d)`. -/

open NumberField UniqueFactorizationMonoid

namespace L3H

variable {F : Type*} [Field F] [NumberField F]


open Classical in
lemma reindex {M : Type*} [AddCommMonoid M] {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (Cs C'' : Finset (Ideal (𝓞 F)))
    (hC'' : ∀ b ∈ Cs, ∀ c, b = 𝔤 * c → c ∈ C'') (f : Ideal (𝓞 F) → M)
    (hf : ∀ b ∈ Cs, ¬ 𝔤 ∣ b → f b = 0) :
    ∑ b ∈ Cs, f b = ∑ c ∈ C'', if 𝔤 * c ∈ Cs then f (𝔤 * c) else 0 := by
  have h𝔤0 : 𝔤 ≠ 0 := h𝔤
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun c => 𝔤 * c) (C''.filter (fun c => 𝔤 * c ∈ Cs) : Set (Ideal (𝓞 F))) :=
    fun x _ y _ hxy => mul_left_cancel₀ h𝔤0 hxy
  rw [← Finset.sum_image (f := f) hinj]
  have himg : (C''.filter (fun c => 𝔤 * c ∈ Cs)).image (fun c => 𝔤 * c) =
      Cs.filter (fun b => 𝔤 ∣ b) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨c, ⟨_, hc⟩, rfl⟩; exact ⟨hc, dvd_mul_right _ _⟩
    · rintro ⟨hb, c, rfl⟩; exact ⟨c, ⟨hC'' _ hb c rfl, hb⟩, rfl⟩
  rw [himg, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b hb => ?_
  split_ifs with h
  · rfl
  · exact hf b hb h

lemma mul_sup_eq_iff {𝔤 c₁ c₂ : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) : 𝔤 * c₁ ⊔ 𝔤 * c₂ = 𝔤 ↔ c₁ ⊔ c₂ = ⊤ := by
  rw [← Ideal.mul_sup]
  constructor
  · intro h
    have h' : 𝔤 * (c₁ ⊔ c₂) = 𝔤 * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ (show 𝔤 ≠ 0 from h𝔤) h'
  · intro h; rw [h, Ideal.mul_top]

lemma mobI_abs_le (d : Ideal (𝓞 F)) : |(mobI d : ℝ)| ≤ 1 := by
  classical
  unfold mobI
  split_ifs
  · push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
  · simp

variable {χ : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ} {Rw : Finset (Ideal (𝓞 F))} {w : Ideal (𝓞 F) → ℝ}

open Classical in
/-- The Möbius identity for `S3` at `𝔤 ≠ ⊥`. -/
theorem S3_eq_mob {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (Cs C'' Ds : Finset (Ideal (𝓞 F)))
    (hCs : ∀ b ∈ Cs, b ≠ ⊥ ∧ Squarefree b) (hC'' : ∀ b ∈ Cs, ∀ c, b = 𝔤 * c → c ∈ C'')
    (hDs : ∀ c ∈ C'', ∀ d, d ∣ c → d ∈ Ds)
    (hmul : ∀ a ∈ Rw, ∀ c ∈ C'', χ a (𝔤 * c) = χ a 𝔤 * χ a c) (lam : Ideal (𝓞 F) → ℂ) :
    S3 χ Rw w (· ⊔ ·) Cs 𝔤 lam = ∑ d ∈ Ds, (mobI d : ℂ) *
      (Qf χ Rw (fun a => w a * ‖χ a 𝔤‖ ^ 2) (C''.filter (fun c => d ∣ c))
        (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0) : ℂ) := by
  set μ : Ideal (𝓞 F) → ℂ := fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0 with hμ
  set G : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun b₁ b₂ =>
    ∑ a ∈ Rw, (w a : ℂ) * χ a b₁ * starRingEnd ℂ (χ a b₂) with hG
  -- step 1: reindex both variables
  have step1 : S3 χ Rw w (· ⊔ ·) Cs 𝔤 lam = ∑ c₁ ∈ C'', ∑ c₂ ∈ C'',
      if c₁ ⊔ c₂ = ⊤ then μ c₁ * starRingEnd ℂ (μ c₂) * G (𝔤 * c₁) (𝔤 * c₂) else 0 := by
    unfold S3
    have hin : ∀ b₁ ∈ Cs, ∑ b₂ ∈ Cs, (if b₁ ⊔ b₂ = 𝔤 then
        lam b₁ * starRingEnd ℂ (lam b₂) * G b₁ b₂ else 0) =
        ∑ c₂ ∈ C'', if 𝔤 * c₂ ∈ Cs then (if b₁ ⊔ 𝔤 * c₂ = 𝔤 then
          lam b₁ * starRingEnd ℂ (lam (𝔤 * c₂)) * G b₁ (𝔤 * c₂) else 0) else 0 := by
      intro b₁ _
      refine reindex h𝔤 Cs C'' hC'' _ fun b₂ _ hb₂ => ?_
      rw [if_neg]
      intro h
      exact hb₂ (Ideal.dvd_iff_le.2 (h ▸ le_sup_right))
    rw [Finset.sum_congr rfl hin]
    rw [reindex h𝔤 Cs C'' hC'' _ ?_]
    · refine Finset.sum_congr rfl fun c₁ _ => ?_
      by_cases h1 : 𝔤 * c₁ ∈ Cs
      · rw [if_pos h1]
        refine Finset.sum_congr rfl fun c₂ _ => ?_
        by_cases h2 : 𝔤 * c₂ ∈ Cs
        · rw [if_pos h2]
          by_cases h3 : c₁ ⊔ c₂ = ⊤
          · rw [if_pos ((mul_sup_eq_iff h𝔤).2 h3), if_pos h3]
            simp only [hμ, if_pos h1, if_pos h2]
          · rw [if_neg (fun h => h3 ((mul_sup_eq_iff h𝔤).1 h)), if_neg h3]
        · rw [if_neg h2]
          split_ifs <;> simp [hμ, h2]
      · rw [if_neg h1]
        symm
        refine Finset.sum_eq_zero fun c₂ _ => ?_
        split_ifs <;> simp [hμ, h1]
    · intro b₁ _ hb₁
      refine Finset.sum_eq_zero fun c₂ _ => ?_
      split_ifs with h2 h3
      · exact absurd (Ideal.dvd_iff_le.2 (h3 ▸ le_sup_left)) hb₁
      · rfl
      · rfl
  -- step 2: Möbius
  have step2 : ∀ c₁ ∈ C'', ∀ c₂ ∈ C'', μ c₁ ≠ 0 →
      (if c₁ ⊔ c₂ = ⊤ then (1 : ℂ) else 0) =
        ∑ d ∈ Ds, if d ∣ c₁ ∧ d ∣ c₂ then (mobI d : ℂ) else 0 := by
    intro c₁ hc₁ c₂ hc₂ hμ1
    have hin : 𝔤 * c₁ ∈ Cs := by
      by_contra h; exact hμ1 (by simp only [hμ, if_neg h])
    obtain ⟨hb0, hbsq⟩ := hCs _ hin
    have hc0 : c₁ ≠ ⊥ := by rintro rfl; rw [Ideal.mul_bot] at hb0; exact hb0 rfl
    have hcsq : Squarefree c₁ := hbsq.squarefree_of_dvd (dvd_mul_left _ _)
    have hn0 : c₁ ⊔ c₂ ≠ ⊥ := fun h => hc0 (eq_bot_iff.2 (h ▸ le_sup_left))
    have hnd : c₁ ⊔ c₂ ∣ c₁ := Ideal.dvd_iff_le.2 le_sup_left
    have hnsq : Squarefree (c₁ ⊔ c₂) := hcsq.squarefree_of_dvd hnd
    have hS : ∀ d, d ∣ c₁ ⊔ c₂ → d ∈ Ds := fun d hd => hDs c₁ hc₁ d (dvd_trans hd hnd)
    have := sum_mobI Ds hn0 hnsq hS
    have hcast : ((if c₁ ⊔ c₂ = ⊤ then (1 : ℤ) else 0 : ℤ) : ℂ) =
        if c₁ ⊔ c₂ = ⊤ then (1 : ℂ) else 0 := by split_ifs <;> simp
    rw [← hcast, ← this, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    have hiff : d ∣ c₁ ⊔ c₂ ↔ d ∣ c₁ ∧ d ∣ c₂ := by
      simp only [Ideal.dvd_iff_le, sup_le_iff]
    by_cases h : d ∣ c₁ ∧ d ∣ c₂
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  -- step 3: assemble
  rw [step1]
  have step3 : ∀ c₁ ∈ C'', ∀ c₂ ∈ C'',
      (if c₁ ⊔ c₂ = ⊤ then μ c₁ * starRingEnd ℂ (μ c₂) * G (𝔤 * c₁) (𝔤 * c₂) else 0) =
        ∑ d ∈ Ds, (mobI d : ℂ) * (if d ∣ c₁ ∧ d ∣ c₂ then
          μ c₁ * starRingEnd ℂ (μ c₂) * G (𝔤 * c₁) (𝔤 * c₂) else 0) := by
    intro c₁ hc₁ c₂ hc₂
    by_cases hμ1 : μ c₁ = 0
    · simp only [hμ1, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]
    have h2 := step2 c₁ hc₁ c₂ hc₂ hμ1
    calc (if c₁ ⊔ c₂ = ⊤ then μ c₁ * starRingEnd ℂ (μ c₂) * G (𝔤 * c₁) (𝔤 * c₂) else 0)
        = (if c₁ ⊔ c₂ = ⊤ then (1 : ℂ) else 0) *
            (μ c₁ * starRingEnd ℂ (μ c₂) * G (𝔤 * c₁) (𝔤 * c₂)) := by split_ifs <;> simp
      _ = _ := by
          rw [h2, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> simp
  rw [Finset.sum_congr rfl fun c₁ hc₁ => Finset.sum_congr rfl fun c₂ hc₂ => step3 c₁ hc₁ c₂ hc₂]
  rw [Finset.sum_congr rfl fun c₁ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Qf_eq_double, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c₁ hc₁ => ?_
  rw [Finset.sum_filter]
  by_cases hd1 : d ∣ c₁
  · rw [if_pos hd1]
    refine Finset.sum_congr rfl fun c₂ hc₂ => ?_
    by_cases hd2 : d ∣ c₂
    · rw [if_pos ⟨hd1, hd2⟩, if_pos hd2]
      congr 1
      rw [hG]
      refine Finset.sum_congr rfl fun a ha => ?_
      have e1 := hmul a ha c₁ hc₁
      have e2 := hmul a ha c₂ hc₂
      rw [e1, e2, map_mul]
      push_cast
      rw [← Complex.mul_conj']
      ring
    · rw [if_neg (fun h => hd2 h.2), if_neg hd2]
  · rw [if_neg hd1]
    refine Finset.sum_eq_zero fun c₂ _ => ?_
    rw [if_neg (fun h => hd1 h.1)]

open Classical in
theorem norm_S3_le {𝔤 : Ideal (𝓞 F)} (h𝔤 : 𝔤 ≠ ⊥) (Cs C'' Ds : Finset (Ideal (𝓞 F)))
    (hCs : ∀ b ∈ Cs, b ≠ ⊥ ∧ Squarefree b) (hC'' : ∀ b ∈ Cs, ∀ c, b = 𝔤 * c → c ∈ C'')
    (hDs : ∀ c ∈ C'', ∀ d, d ∣ c → d ∈ Ds)
    (hmul : ∀ a ∈ Rw, ∀ c ∈ C'', χ a (𝔤 * c) = χ a 𝔤 * χ a c)
    (hw : ∀ a, 0 ≤ w a) (hχ1 : ∀ a, ‖χ a 𝔤‖ ≤ 1) {v' : ℝ} (hv' : 0 ≤ v')
    (hB : B2f χ Rw w C'' v') (lam : Ideal (𝓞 F) → ℂ) :
    ‖S3 χ Rw w (· ⊔ ·) Cs 𝔤 lam‖ ≤ v' * ∑ d ∈ Ds, ∑ c ∈ C''.filter (fun c => d ∣ c),
      ‖(if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0)‖ ^ 2 := by
  classical
  rw [S3_eq_mob h𝔤 Cs C'' Ds hCs hC'' hDs hmul lam, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hQ0 : 0 ≤ Qf χ Rw (fun a => w a * ‖χ a 𝔤‖ ^ 2) (C''.filter (fun c => d ∣ c))
      (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0) :=
    Qf_nonneg (fun a => mul_nonneg (hw a) (by positivity)) _ _
  rw [abs_of_nonneg hQ0, Complex.norm_intCast]
  have hle : Qf χ Rw (fun a => w a * ‖χ a 𝔤‖ ^ 2) (C''.filter (fun c => d ∣ c))
      (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0) ≤
      Qf χ Rw w (C''.filter (fun c => d ∣ c))
      (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0) := by
    unfold Qf
    refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : ‖χ a 𝔤‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hχ1 a)
    nlinarith [hw a]
  have hB' := (hB.mono_cols (Finset.filter_subset (fun c => d ∣ c) C''))
    (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0)
  have hm := mobI_abs_le d
  calc |(mobI d : ℝ)| * Qf χ Rw (fun a => w a * ‖χ a 𝔤‖ ^ 2) (C''.filter (fun c => d ∣ c))
        (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0)
      ≤ 1 * Qf χ Rw (fun a => w a * ‖χ a 𝔤‖ ^ 2) (C''.filter (fun c => d ∣ c))
        (fun c => if 𝔤 * c ∈ Cs then lam (𝔤 * c) else 0) :=
        mul_le_mul_of_nonneg_right hm hQ0
    _ ≤ _ := by rw [one_mul]; exact hle.trans hB'

end L3H

end
end

section
section
/-! # L3H_L51: GL Lemma 5.1 for the family `chiK`

Columns `N < N b ≤ 2N` (`rowsF 𝔪 N (2N)`), `k` classes. From GL Prop 5.2 at the gcds `𝔤` with
`N 𝔤 ≤ G₀` (bound `A N𝔤⁴`) and the bound `v'` for every column scale `N' ≤ N / G₀`:
`B₂ ≤ k (A G₀⁴ #{N 𝔤 ≤ G₀} + v' T²)`, with `T` a bound for the number of divisors. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma exterior_of_le {𝔪 b c : Ideal (𝓞 F)} (hb : IsExterior 𝔪 b) (hc : c ≠ ⊥) (hbc : b ≤ c) :
    IsExterior 𝔪 c :=
  ⟨hc, eq_top_iff.2 (hb.2 ▸ sup_le_sup_right hbc _)⟩

lemma absNorm_le_of_le {b c : Ideal (𝓞 F)} (hb : b ≠ ⊥) (hbc : b ≤ c) :
    Ideal.absNorm c ≤ Ideal.absNorm b := by
  have h0 : Ideal.absNorm b ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hb
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Ideal.absNorm_dvd_absNorm_of_le hbc)

open Classical in
theorem lemma51 (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (Rw : Finset (Ideal (𝓞 F))) (w : Ideal (𝓞 F) → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hmulC : ∀ a ∈ Rw, ∀ 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c)
    (k : ℕ) (cls : Ideal (𝓞 F) → Fin k) {N G₀ A v' T Cnt : ℝ} (hN : 0 < N) (hG₀ : 1 ≤ G₀)
    (hA : 0 ≤ A) (hv' : 0 ≤ v') (hT0 : 0 ≤ T)
    (hcut : ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k) (lam : Ideal (𝓞 F) → ℂ),
      ‖S3 (chiK ι 𝔪 g) Rw w (· ⊔ ·) ((rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        A * (Ideal.absNorm 𝔤 : ℝ) ^ 4 *
          ∑ b ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j), ‖lam b‖ ^ 2)
    (hrec : ∀ N' : ℝ, 0 < N' → N' ≤ N / G₀ → B2f (chiK ι 𝔪 g) Rw w (rowsF 𝔪 N' (2 * N')) v')
    (hT : ∀ x : Ideal (𝓞 F), x ≠ ⊥ → Squarefree x → (Ideal.absNorm x : ℝ) ≤ 2 * N →
      (((rowsF 𝔪 0 (2 * N)).filter (· ∣ x)).card : ℝ) ≤ T)
    (hCnt : ((rowsF 𝔪 0 G₀).card : ℝ) ≤ Cnt) :
    B2f (chiK ι 𝔪 g) Rw w (rowsF 𝔪 N (2 * N)) (k * (A * G₀ ^ 4 * Cnt + v' * T ^ 2)) := by
  set χ := chiK ι 𝔪 g
  set Cs := rowsF 𝔪 N (2 * N) with hCsd
  set Gs := rowsF 𝔪 0 (2 * N) with hGsd
  have hCnt0 : 0 ≤ Cnt := le_trans (Nat.cast_nonneg _) hCnt
  -- the bound for one class
  have hclass : ∀ (j : Fin k) (lam : Ideal (𝓞 F) → ℂ),
      Qf χ Rw w (Cs.filter (fun b => cls b = j)) lam ≤
        (A * G₀ ^ 4 * Cnt + v' * T ^ 2) *
          ∑ b ∈ Cs.filter (fun b => cls b = j), ‖lam b‖ ^ 2 := by
    intro j lam
    set Cj := Cs.filter (fun b => cls b = j) with hCj
    have hCjm : ∀ b ∈ Cj, IsExterior 𝔪 b ∧ Squarefree b ∧ N < (Ideal.absNorm b : ℝ) ∧
        (Ideal.absNorm b : ℝ) ≤ 2 * N := fun b hb => mem_rowsF.1 (Finset.mem_filter.1 hb).1
    set Z := ∑ b ∈ Cj, ‖lam b‖ ^ 2 with hZ
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => by positivity
    have hGs : ∀ b₁ ∈ Cj, ∀ b₂ ∈ Cj, b₁ ⊔ b₂ ∈ Gs := by
      intro b₁ hb₁ b₂ _
      obtain ⟨e1, s1, -, n1⟩ := hCjm b₁ hb₁
      have hne : b₁ ⊔ b₂ ≠ ⊥ := fun h => e1.1 (eq_bot_iff.2 (h ▸ le_sup_left))
      refine mem_rowsF.2 ⟨exterior_of_le e1 hne le_sup_left,
        s1.squarefree_of_dvd (Ideal.dvd_iff_le.2 le_sup_left),
        lt_of_lt_of_le zero_lt_one (one_le_absNorm hne), ?_⟩
      exact le_trans (by exact_mod_cast absNorm_le_of_le e1.1 le_sup_left) n1
    have hQ := Qf_eq_sum_S3 (χ := χ) (Rw := Rw) (w := w) (· ⊔ ·) Cj Gs hGs lam
    have hQn : Qf χ Rw w Cj lam ≤ ∑ 𝔤 ∈ Gs, ‖S3 χ Rw w (· ⊔ ·) Cj 𝔤 lam‖ := by
      have h0 := Qf_nonneg (χ := χ) (Rw := Rw) hw Cj lam
      calc Qf χ Rw w Cj lam = ‖(Qf χ Rw w Cj lam : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        _ = ‖∑ 𝔤 ∈ Gs, S3 χ Rw w (· ⊔ ·) Cj 𝔤 lam‖ := by rw [hQ]
        _ ≤ _ := norm_sum_le _ _
    refine hQn.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not Gs (fun 𝔤 => (Ideal.absNorm 𝔤 : ℝ) ≤ G₀)]
    rw [add_mul]
    refine add_le_add ?_ ?_
    · -- small gcds: Prop 5.2
      calc ∑ 𝔤 ∈ Gs.filter (fun 𝔤 => (Ideal.absNorm 𝔤 : ℝ) ≤ G₀),
            ‖S3 χ Rw w (· ⊔ ·) Cj 𝔤 lam‖
          ≤ ∑ 𝔤 ∈ Gs.filter (fun 𝔤 => (Ideal.absNorm 𝔤 : ℝ) ≤ G₀), A * G₀ ^ 4 * Z := by
            refine Finset.sum_le_sum fun 𝔤 h𝔤 => (hcut 𝔤 j lam).trans ?_
            have h1 := (Finset.mem_filter.1 h𝔤).2
            have : (Ideal.absNorm 𝔤 : ℝ) ^ 4 ≤ G₀ ^ 4 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) h1 4
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hA) hZ0
        _ = (Gs.filter (fun 𝔤 => (Ideal.absNorm 𝔤 : ℝ) ≤ G₀)).card * (A * G₀ ^ 4 * Z) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Cnt * (A * G₀ ^ 4 * Z) := by
            refine mul_le_mul_of_nonneg_right (le_trans ?_ hCnt) (by positivity)
            exact_mod_cast Finset.card_le_card fun 𝔤 h𝔤 => by
              obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h𝔤
              obtain ⟨a1, a2, a3, -⟩ := mem_rowsF.1 h1
              exact mem_rowsF.2 ⟨a1, a2, a3, h2⟩
        _ = A * G₀ ^ 4 * Cnt * Z := by ring
    · -- large gcds: the Möbius step and the recursion
      have htail : ∀ 𝔤 ∈ Gs.filter (fun 𝔤 => ¬ (Ideal.absNorm 𝔤 : ℝ) ≤ G₀),
          ‖S3 χ Rw w (· ⊔ ·) Cj 𝔤 lam‖ ≤
            v' * T * ∑ b ∈ Cj, if 𝔤 ∣ b then ‖lam b‖ ^ 2 else 0 := by
        intro 𝔤 h𝔤
        obtain ⟨h𝔤G, h𝔤big⟩ := Finset.mem_filter.1 h𝔤
        obtain ⟨e𝔤, -, -, -⟩ := mem_rowsF.1 h𝔤G
        push Not at h𝔤big
        have hN𝔤 : (0 : ℝ) < Ideal.absNorm 𝔤 := by linarith
        set N' := N / Ideal.absNorm 𝔤 with hN'
        have hN'0 : 0 < N' := div_pos hN hN𝔤
        have hN'le : N' ≤ N / G₀ := div_le_div_of_nonneg_left hN.le (by linarith) h𝔤big.le
        set C'' := rowsF 𝔪 N' (2 * N') with hC''d
        have hC'' : ∀ b ∈ Cj, ∀ c, b = 𝔤 * c → c ∈ C'' := by
          intro b hb c hbc
          obtain ⟨eb, sb, nb1, nb2⟩ := hCjm b hb
          have hc0 : c ≠ ⊥ := by rintro rfl; rw [Ideal.mul_bot] at hbc; exact eb.1 hbc
          have hle : b ≤ c := hbc ▸ Ideal.mul_le_right
          have hNb : (Ideal.absNorm b : ℝ) = Ideal.absNorm 𝔤 * Ideal.absNorm c := by
            rw [hbc, map_mul, Nat.cast_mul]
          refine mem_rowsF.2 ⟨exterior_of_le eb hc0 hle,
            sb.squarefree_of_dvd (Ideal.dvd_iff_le.2 hle), ?_, ?_⟩
          · rw [hN', div_lt_iff₀ hN𝔤]; linarith
          · rw [hN', mul_div_assoc', le_div_iff₀ hN𝔤]; linarith
        have hDs : ∀ c ∈ C'', ∀ d, d ∣ c → d ∈ Gs := by
          intro c hc d hd
          obtain ⟨ec, sc, -, nc⟩ := mem_rowsF.1 hc
          have hle : c ≤ d := Ideal.dvd_iff_le.1 hd
          have hd0 : d ≠ ⊥ := fun h => ec.1 (eq_bot_iff.2 (h ▸ hle))
          refine mem_rowsF.2 ⟨exterior_of_le ec hd0 hle, sc.squarefree_of_dvd hd,
            lt_of_lt_of_le zero_lt_one (one_le_absNorm hd0), ?_⟩
          have h1 : (Ideal.absNorm d : ℝ) ≤ Ideal.absNorm c := by
            exact_mod_cast absNorm_le_of_le ec.1 hle
          have h2 : 2 * N' ≤ 2 * N := by
            rw [hN']
            have : N / Ideal.absNorm 𝔤 ≤ N := div_le_self hN.le (by linarith)
            linarith
          linarith
        have hmul : ∀ a ∈ Rw, ∀ c ∈ C'', χ a (𝔤 * c) = χ a 𝔤 * χ a c :=
          fun a ha c hc => hmulC a ha 𝔤 c e𝔤 (mem_rowsF.1 hc).1
        have h1 := norm_S3_le (χ := χ) (Rw := Rw) (w := w) e𝔤.1 Cj C'' Gs
          (fun b hb => ⟨(hCjm b hb).1.1, (hCjm b hb).2.1⟩) hC'' hDs hmul hw
          (fun a => norm_chiK_le ι 𝔪 g a 𝔤) hv' (hrec N' hN'0 hN'le) lam
        refine h1.trans ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hv'
        -- swap d and c, count divisors
        have hswap : ∑ d ∈ Gs, ∑ c ∈ C''.filter (fun c => d ∣ c),
            ‖(if 𝔤 * c ∈ Cj then lam (𝔤 * c) else 0)‖ ^ 2 =
            ∑ c ∈ C'', ((Gs.filter (· ∣ c)).card : ℝ) *
              ‖(if 𝔤 * c ∈ Cj then lam (𝔤 * c) else 0)‖ ^ 2 := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
        rw [hswap]
        have hreidx := reindex e𝔤.1 Cj C'' hC'' (fun b => if 𝔤 ∣ b then ‖lam b‖ ^ 2 else 0)
          (fun b _ hb => by simp only [if_neg hb])
        rw [hreidx, Finset.mul_sum]
        refine Finset.sum_le_sum fun c hc => ?_
        obtain ⟨ec, sc, -, nc⟩ := mem_rowsF.1 hc
        have hcard := hT c ec.1 sc (by
          have : 2 * N' ≤ 2 * N := by
            rw [hN']
            have : N / Ideal.absNorm 𝔤 ≤ N := div_le_self hN.le (by linarith)
            linarith
          linarith)
        by_cases h : 𝔤 * c ∈ Cj
        · simp only [if_pos h, if_pos (dvd_mul_right 𝔤 c)]
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
        · simp only [if_neg h, norm_zero]
          norm_num
      calc ∑ 𝔤 ∈ Gs.filter (fun 𝔤 => ¬ (Ideal.absNorm 𝔤 : ℝ) ≤ G₀),
            ‖S3 χ Rw w (· ⊔ ·) Cj 𝔤 lam‖
          ≤ ∑ 𝔤 ∈ Gs.filter (fun 𝔤 => ¬ (Ideal.absNorm 𝔤 : ℝ) ≤ G₀),
            v' * T * ∑ b ∈ Cj, (if 𝔤 ∣ b then ‖lam b‖ ^ 2 else 0) := Finset.sum_le_sum htail
        _ ≤ ∑ 𝔤 ∈ Gs, v' * T * ∑ b ∈ Cj, (if 𝔤 ∣ b then ‖lam b‖ ^ 2 else 0) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro 𝔤 _ _
            refine mul_nonneg (mul_nonneg hv' hT0) (Finset.sum_nonneg fun b _ => ?_)
            split_ifs <;> positivity
        _ = v' * T * ∑ b ∈ Cj, ((Gs.filter (· ∣ b)).card : ℝ) * ‖lam b‖ ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
        _ ≤ v' * T * ∑ b ∈ Cj, T * ‖lam b‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b hb => ?_)
              (mul_nonneg hv' hT0)
            exact mul_le_mul_of_nonneg_right (hT b (hCjm b hb).1.1 (hCjm b hb).2.1
              (hCjm b hb).2.2.2) (by positivity)
        _ = v' * T ^ 2 * Z := by rw [hZ, ← Finset.mul_sum]; ring
  -- all classes
  intro lam
  refine (Qf_le_classes hw k cls Cs lam).trans ?_
  have hsplit : ∑ b ∈ Cs, ‖lam b‖ ^ 2 =
      ∑ j : Fin k, ∑ b ∈ Cs.filter (fun b => cls b = j), ‖lam b‖ ^ 2 :=
    (Finset.sum_fiberwise Cs cls _).symm
  rw [hsplit, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hclass j lam) (Nat.cast_nonneg _)

end L3H

end
end

section
section
/-! # L3H_Iter: the iteration (5.3)–(5.4) in the proof of GL Theorem 4.3

`V 0 = v₀`, `V (i+1) = k (A G₀⁴ Cnt + V i T²) + v₀`; column scales `N' < G₀^i` are bounded by
`V i`, by GL Lemma 5.1 (`lemma51`) at each step, and `V i ≤ (k T² + 1)^i (i+1) (k A G₀⁴ Cnt + v₀)`. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

/-- The recursion values. -/
noncomputable def Vseq (k A G₀ Cnt T v₀ : ℝ) : ℕ → ℝ
  | 0 => v₀
  | i + 1 => k * (A * G₀ ^ 4 * Cnt + Vseq k A G₀ Cnt T v₀ i * T ^ 2) + v₀

lemma Vseq_nonneg {k A G₀ Cnt T v₀ : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A) (hG₀ : 0 ≤ G₀)
    (hC : 0 ≤ Cnt) (hv₀ : 0 ≤ v₀) : ∀ i, 0 ≤ Vseq k A G₀ Cnt T v₀ i
  | 0 => hv₀
  | i + 1 => by
    have := Vseq_nonneg (T := T) hk hA hG₀ hC hv₀ i
    simp only [Vseq]; positivity

lemma Vseq_le {k A G₀ Cnt T v₀ : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A) (hG₀ : 0 ≤ G₀)
    (hC : 0 ≤ Cnt) (hv₀ : 0 ≤ v₀) : ∀ i,
    Vseq k A G₀ Cnt T v₀ i ≤ (k * T ^ 2 + 1) ^ i * (i + 1) * (k * A * G₀ ^ 4 * Cnt + v₀)
  | 0 => by simp only [Vseq, pow_zero, Nat.cast_zero, zero_add, one_mul]; nlinarith [
      mul_nonneg (mul_nonneg (mul_nonneg hk hA) (pow_nonneg hG₀ 4)) hC]
  | i + 1 => by
    have ih := Vseq_le (T := T) hk hA hG₀ hC hv₀ i
    set q := k * T ^ 2 + 1
    set B := k * A * G₀ ^ 4 * Cnt + v₀
    have hB : 0 ≤ B := by positivity
    have hq : 1 ≤ q := by
      have : 0 ≤ k * T ^ 2 := by positivity
      show 1 ≤ k * T ^ 2 + 1; linarith
    have hqi : 1 ≤ q ^ i := one_le_pow₀ hq
    simp only [Vseq]
    push_cast
    have h1 : k * T ^ 2 * Vseq k A G₀ Cnt T v₀ i ≤ k * T ^ 2 * (q ^ i * (i + 1) * B) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have h2 : k * T ^ 2 * (q ^ i * (i + 1) * B) ≤ q ^ (i + 1) * (i + 1) * B := by
      have : k * T ^ 2 ≤ q := by show k * T ^ 2 ≤ k * T ^ 2 + 1; linarith
      have h0 : 0 ≤ q ^ i * (i + 1) * B := by positivity
      calc k * T ^ 2 * (q ^ i * (i + 1) * B) ≤ q * (q ^ i * (i + 1) * B) :=
            mul_le_mul_of_nonneg_right this h0
        _ = q ^ (i + 1) * (i + 1) * B := by ring
    have h3 : B ≤ q ^ (i + 1) * B := le_mul_of_one_le_left hB (one_le_pow₀ hq)
    calc k * (A * G₀ ^ 4 * Cnt + Vseq k A G₀ Cnt T v₀ i * T ^ 2) + v₀
        = B + k * T ^ 2 * Vseq k A G₀ Cnt T v₀ i := by ring
      _ ≤ q ^ (i + 1) * B + q ^ (i + 1) * (i + 1) * B := by linarith
      _ = q ^ (i + 1) * ((i : ℝ) + 1 + 1) * B := by ring

open Classical in
theorem iterate_B2 (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (Rw : Finset (Ideal (𝓞 F))) (w : Ideal (𝓞 F) → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hmulC : ∀ a ∈ Rw, ∀ 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c)
    (k : ℕ) (cls : Ideal (𝓞 F) → Fin k) {N G₀ A T Cnt v₀ : ℝ} (hG₀ : 1 ≤ G₀)
    (hA : 0 ≤ A) (hT0 : 0 ≤ T) (hv₀ : 0 ≤ v₀)
    (hcut : ∀ N' : ℝ, 1 ≤ N' → N' ≤ N → ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
      (lam : Ideal (𝓞 F) → ℂ),
      ‖S3 (chiK ι 𝔪 g) Rw w (· ⊔ ·) ((rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        A * (Ideal.absNorm 𝔤 : ℝ) ^ 4 *
          ∑ b ∈ (rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j), ‖lam b‖ ^ 2)
    (hT : ∀ N' : ℝ, N' ≤ N → ∀ x : Ideal (𝓞 F), x ≠ ⊥ → Squarefree x →
      (Ideal.absNorm x : ℝ) ≤ 2 * N' → (((rowsF 𝔪 0 (2 * N')).filter (· ∣ x)).card : ℝ) ≤ T)
    (hCnt : ((rowsF 𝔪 0 G₀).card : ℝ) ≤ Cnt)
    (hbase : ∀ N' : ℝ, 0 < N' → N' < 1 → B2f (chiK ι 𝔪 g) Rw w (rowsF 𝔪 N' (2 * N')) v₀) :
    ∀ i : ℕ, ∀ N' : ℝ, 0 < N' → N' ≤ N → N' < G₀ ^ i →
      B2f (chiK ι 𝔪 g) Rw w (rowsF 𝔪 N' (2 * N')) (Vseq k A G₀ Cnt T v₀ i) := by
  have hCnt0 : 0 ≤ Cnt := le_trans (Nat.cast_nonneg _) hCnt
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  intro i
  induction i with
  | zero =>
    intro N' hN' _ hlt
    rw [pow_zero] at hlt
    exact hbase N' hN' hlt
  | succ i ih =>
    intro N' hN' hNN hlt
    have hVi := Vseq_nonneg (k := k) (A := A) (G₀ := G₀) (Cnt := Cnt) (T := T) (v₀ := v₀)
      hk0 hA (by linarith) hCnt0 hv₀ i
    by_cases h1 : N' < 1
    · refine (hbase N' hN' h1).mono_v ?_
      simp only [Vseq]
      have : 0 ≤ (k : ℝ) * (A * G₀ ^ 4 * Cnt + Vseq k A G₀ Cnt T v₀ i * T ^ 2) := by positivity
      linarith
    push Not at h1
    have hrec : ∀ N'' : ℝ, 0 < N'' → N'' ≤ N' / G₀ →
        B2f (chiK ι 𝔪 g) Rw w (rowsF 𝔪 N'' (2 * N'')) (Vseq k A G₀ Cnt T v₀ i) := by
      intro N'' hN'' hle
      refine ih N'' hN'' ?_ ?_
      · have : N' / G₀ ≤ N' := div_le_self (by linarith) hG₀
        linarith
      · have hG0 : 0 < G₀ := by linarith
        calc N'' ≤ N' / G₀ := hle
          _ < G₀ ^ (i + 1) / G₀ := div_lt_div_of_pos_right hlt hG0
          _ = G₀ ^ i := by rw [pow_succ]; field_simp
    have h51 := lemma51 ι 𝔪 g Rw w hw hmulC k cls (by linarith : (0 : ℝ) < N') hG₀ hA hVi hT0
      (hcut N' h1 hNN) hrec (hT N' hNN) hCnt
    refine h51.mono_v ?_
    simp only [Vseq]
    linarith

end L3H

end
end

section
section
/-! # L3H_Rows: the rows of `Σ₂, Σ₃`, ideal counting, and the passage `B₁ ≤ B₂`

* `RwF 𝔪 L M`: exterior `𝔞` with squarefree part of norm `> L` and `N 𝔞 < 3M`.
* `card_le_mul`: `#{N I ≤ X} ≤ c X` (Mathlib's ideal-count asymptotic).
* `SBf_of_B2f`: rows `M < N 𝔡 ≤ 2M` (squarefree) inside `RwF` with weight `1`, for `L ≤ M`.
* `SBf_cols_blocks`: columns `N 𝔠 ≤ C` from the dyadic column blocks (Cauchy–Schwarz).
-/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma fin_rows (𝔪 : Ideal (𝓞 F)) (L M : ℝ) :
    {𝔞 : Ideal (𝓞 F) | IsExterior 𝔪 𝔞 ∧ (∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
      L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞) ∧ (Ideal.absNorm 𝔞 : ℝ) < 3 * M}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊3 * M⌋₊).subset
    (fun 𝔞 h => Nat.le_floor h.2.2.le)

/-- The rows of `Σ₂`, `Σ₃` meeting the weight. -/
noncomputable def RwF (𝔪 : Ideal (𝓞 F)) (L M : ℝ) : Finset (Ideal (𝓞 F)) :=
  (fin_rows 𝔪 L M).toFinset

lemma mem_RwF {𝔪 : Ideal (𝓞 F)} {L M : ℝ} {𝔞 : Ideal (𝓞 F)} :
    𝔞 ∈ RwF 𝔪 L M ↔ IsExterior 𝔪 𝔞 ∧ (∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
      L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞) ∧ (Ideal.absNorm 𝔞 : ℝ) < 3 * M := by
  unfold RwF; rw [Set.Finite.mem_toFinset]; rfl

/-- Linear ideal counting. -/
theorem card_le_mul (F : Type*) [Field F] [NumberField F] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset (Ideal (𝓞 F)),
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) → (S.card : ℝ) ≤ c * X := by
  have ht := NumberField.Ideal.tendsto_norm_le_div_atTop F
  set l := (2 ^ NumberField.InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^
    NumberField.InfinitePlace.nrComplexPlaces F * NumberField.Units.regulator F *
    (NumberField.classNumber F : ℝ)) /
    (NumberField.Units.torsionOrder F * Real.sqrt |(NumberField.discr F : ℝ)|) with hl
  have hev := ht.eventually (Iic_mem_nhds (lt_add_one l))
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1 hev
  set s₁ := max s₀ 1
  have hfin : ∀ X : ℝ, {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X}.Finite := fun X =>
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).subset
      (fun I h => Nat.le_floor h)
  have hcardS : ∀ X : ℝ, ∀ S : Finset (Ideal (𝓞 F)), (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (S.card : ℝ) ≤ Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} := by
    intro X S hS
    change (S.card : ℝ) ≤
      (Nat.card ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X} : Set (Ideal (𝓞 F))) : ℝ)
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact_mod_cast Set.ncard_le_ncard (fun I hI => hS I hI) (hfin X)
  set c₀ : ℝ := ((Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s₁} : ℕ) : ℝ)
  have hl0 : 0 ≤ l + 1 := by
    have : 0 ≤ l := by
      rw [hl]
      have := NumberField.Units.regulator_pos F
      positivity
    linarith
  refine ⟨max (l + 1) c₀, le_trans hl0 (le_max_left _ _), fun X hX S hS => ?_⟩
  refine (hcardS X S hS).trans ?_
  by_cases hXs : s₁ ≤ X
  · have h1 := hs₀ X (le_trans (le_max_left _ _) hXs)
    have hX0 : 0 < X := by linarith
    rw [div_le_iff₀ hX0] at h1
    calc (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ (l + 1) * X := h1
      _ ≤ max (l + 1) c₀ * X := by gcongr; exact le_max_left _ _
  · push Not at hXs
    have hmono : (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ c₀ := by
      change (Nat.card ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X} : Set (Ideal (𝓞 F))) : ℝ) ≤
        (Nat.card ({I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ s₁} : Set (Ideal (𝓞 F))) : ℝ)
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact_mod_cast Set.ncard_le_ncard (fun I (hI : (Ideal.absNorm I : ℝ) ≤ X) =>
        (show (Ideal.absNorm I : ℝ) ≤ s₁ by linarith)) (hfin s₁)
    have hc0 : 0 ≤ c₀ := Nat.cast_nonneg _
    calc (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ X} : ℝ) ≤ c₀ := hmono
      _ ≤ max (l + 1) c₀ := le_max_right _ _
      _ = max (l + 1) c₀ * 1 := (mul_one _).symm
      _ ≤ max (l + 1) c₀ * X := by gcongr

/-- `B₁ ≤ B₂`: squarefree rows `M < N 𝔡 ≤ 2M` lie in `RwF` with weight `1`. -/
theorem SBf_of_B2f (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (W : ℝ → ℝ)
    (hW1 : ∀ t, 1 < t → t ≤ 2 → W t = 1) (hW0 : ∀ t, 0 ≤ W t) {L M : ℝ} (hM : 0 < M)
    (hLM : L ≤ M) (Cs : Finset (Ideal (𝓞 F))) {v : ℝ}
    (h : B2f (chiK ι 𝔪 g) (RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M)) Cs v) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) Cs v := by
  intro z
  refine le_trans ?_ (h z)
  unfold Qf
  have hsub : rowsF 𝔪 M (2 * M) ⊆ RwF 𝔪 L M := by
    intro 𝔞 h𝔞
    obtain ⟨e, s, n1, n2⟩ := mem_rowsF.1 h𝔞
    refine mem_RwF.2 ⟨e, fun 𝔟 h𝔟 => ?_, by linarith⟩
    have hu : IsUnit 𝔟 := s 𝔟 (by rw [← sq]; exact h𝔟)
    rw [Ideal.isUnit_iff] at hu
    rw [hu, Ideal.absNorm_top]
    simp only [Nat.cast_one, one_pow, mul_one]
    linarith
  calc ∑ a ∈ rowsF 𝔪 M (2 * M), ‖∑ c ∈ Cs, z c * chiK ι 𝔪 g a c‖ ^ 2
      = ∑ a ∈ rowsF 𝔪 M (2 * M), W ((Ideal.absNorm a : ℝ) / M) *
          ‖∑ c ∈ Cs, z c * chiK ι 𝔪 g a c‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨-, -, n1, n2⟩ := mem_rowsF.1 ha
        rw [hW1 _ (by rw [lt_div_iff₀ hM]; linarith) (by rw [div_le_iff₀ hM]; linarith), one_mul]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
        mul_nonneg (hW0 _) (by positivity)

/-- Columns from disjoint column blocks, by Cauchy–Schwarz. -/
theorem SBf_cols_blocks {I : Type*} [DecidableEq I] {χ : I → I → ℂ} (R Cs : Finset I) (J : ℕ)
    (B : ℕ → Finset I) (hdisj : ∀ i < J, ∀ j < J, i ≠ j → Disjoint (B i) (B j))
    (hcov : Cs ⊆ (Finset.range J).biUnion B) {V : ℝ} (hV : 0 ≤ V)
    (hB : ∀ i < J, SBf χ R (B i) V) : SBf χ R Cs (J * V) := by
  classical
  intro z
  set z' : I → ℂ := fun c => if c ∈ Cs then z c else 0
  have hsplit : ∀ a, ∑ c ∈ Cs, z c * χ a c = ∑ i ∈ Finset.range J, ∑ c ∈ B i, z' c * χ a c := by
    intro a
    rw [← Finset.sum_biUnion (fun i hi j hj hij => hdisj i (Finset.mem_range.1 hi) j
      (Finset.mem_range.1 hj) hij)]
    rw [← Finset.sum_subset hcov (f := fun c => z' c * χ a c)]
    · exact Finset.sum_congr rfl fun c hc => by simp [z', hc]
    · intro c _ hc; simp [z', hc]
  have hnorm : ∑ i ∈ Finset.range J, ∑ c ∈ B i, ‖z' c‖ ^ 2 ≤ ∑ c ∈ Cs, ‖z c‖ ^ 2 := by
    rw [← Finset.sum_biUnion (fun i hi j hj hij => hdisj i (Finset.mem_range.1 hi) j
      (Finset.mem_range.1 hj) hij)]
    calc ∑ c ∈ (Finset.range J).biUnion B, ‖z' c‖ ^ 2
        = ∑ c ∈ ((Finset.range J).biUnion B).filter (· ∈ Cs), ‖z c‖ ^ 2 := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun c _ => by simp only [z']; split_ifs <;> simp
      _ ≤ ∑ c ∈ Cs, ‖z c‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => (Finset.mem_filter.1 hc).2)
            fun _ _ _ => by positivity
  calc ∑ a ∈ R, ‖∑ c ∈ Cs, z c * χ a c‖ ^ 2
      = ∑ a ∈ R, ‖∑ i ∈ Finset.range J, ∑ c ∈ B i, z' c * χ a c‖ ^ 2 := by
        simp_rw [hsplit]
    _ ≤ ∑ a ∈ R, J * ∑ i ∈ Finset.range J, ‖∑ c ∈ B i, z' c * χ a c‖ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        calc ‖∑ i ∈ Finset.range J, ∑ c ∈ B i, z' c * χ a c‖ ^ 2
            ≤ (∑ i ∈ Finset.range J, ‖∑ c ∈ B i, z' c * χ a c‖) ^ 2 := by
              gcongr; exact norm_sum_le _ _
          _ ≤ (Finset.range J).card * ∑ i ∈ Finset.range J, ‖∑ c ∈ B i, z' c * χ a c‖ ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = J * ∑ i ∈ Finset.range J, ‖∑ c ∈ B i, z' c * χ a c‖ ^ 2 := by
              rw [Finset.card_range]
    _ = J * ∑ i ∈ Finset.range J, ∑ a ∈ R, ‖∑ c ∈ B i, z' c * χ a c‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ J * ∑ i ∈ Finset.range J, V * ∑ c ∈ B i, ‖z' c‖ ^ 2 := by
        gcongr with i hi
        exact hB i (Finset.mem_range.1 hi) z'
    _ = J * V * ∑ i ∈ Finset.range J, ∑ c ∈ B i, ‖z' c‖ ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ J * V * ∑ c ∈ Cs, ‖z c‖ ^ 2 := by gcongr

/-- The `tsum` hypothesis `(E_α)` as an `SBf` bound. -/
lemma SBf_of_sb (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) {C D v : ℝ}
    (h : ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
        (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
      ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
          (Ideal.absNorm 𝔡 : ℝ) ≤ D},
          ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
        v * ∑' 𝔠, ‖z 𝔠‖ ^ 2) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C) v := by
  intro z'
  have h1 := h (fun c => z' c.1)
  rw [tsum_subtype_eq _ _ (fun x => mem_rowsF_zero) (fun c => ‖z' c‖ ^ 2)] at h1
  have hin : ∀ 𝔡 : Ideal (𝓞 F), ∑' 𝔠 : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
      (Ideal.absNorm 𝔠 : ℝ) ≤ C}, z' 𝔠.1 * residueSymbol ι 𝔪 𝔡 (g.gen 𝔠.1) ^ 3 =
      ∑ c ∈ rowsF 𝔪 0 C, z' c * chiK ι 𝔪 g 𝔡 c := fun 𝔡 =>
    tsum_subtype_eq _ _ (fun x => mem_rowsF_zero) (fun c => z' c * chiK ι 𝔪 g 𝔡 c)
  simp_rw [hin] at h1
  rw [tsum_subtype_eq _ _ (fun x => mem_rowsF_zero)
    (fun 𝔡 => ‖∑ c ∈ rowsF 𝔪 0 C, z' c * chiK ι 𝔪 g 𝔡 c‖ ^ 2)] at h1
  exact h1

end L3H

end
end

section
section
/-! # L3H_Big2: GL Theorem 4.3 (dyadic rows) in the range `C (CM)^ε₂ ≤ M`, from GL Prop 5.2

`L = C²/M (CM)^ε₂`; GL Lemma 5.1 iterated `r` times with `G₀ = 2 C^(1/r)` (`iterate_B2`), then the
column blocks. All constants are parameters. -/

open NumberField ArtinPrimitiveRoots Real

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma B2f_trivial (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (Rw : Finset (Ideal (𝓞 F))) (w : Ideal (𝓞 F) → ℝ) (hw : ∀ a, 0 ≤ w a ∧ w a ≤ 1)
    (Cs : Finset (Ideal (𝓞 F))) :
    B2f (chiK ι 𝔪 g) Rw w Cs (Rw.card * Cs.card) := by
  intro μ
  have h := SBf_card ι 𝔪 g Rw Cs μ
  refine le_trans ?_ h
  unfold Qf
  exact Finset.sum_le_sum fun a _ => by
    have := hw a
    have h0 : 0 ≤ ‖∑ c ∈ Cs, μ c * chiK ι 𝔪 g a c‖ ^ 2 := by positivity
    nlinarith

lemma sqrt_mul_rpow_eq {C M L α ε₂ X : ℝ} (hC : 0 < C) (hM : 0 < M) (hX : 0 < X)
    (hL : L = C ^ 2 / M * X ^ ε₂) :
    Real.sqrt M * L ^ (α - 1 / 2) = C ^ (2 * α - 1) * M ^ (1 - α) * X ^ (ε₂ * (α - 1 / 2)) := by
  rw [hL, Real.mul_rpow (by positivity) (by positivity), Real.div_rpow (by positivity) hM.le,
    ← Real.rpow_natCast C 2, ← Real.rpow_mul hC.le, ← Real.rpow_mul hX.le, Real.sqrt_eq_rpow]
  have e1 : M ^ (1 / 2 : ℝ) / M ^ (α - 1 / 2) = M ^ (1 - α) := by
    rw [← Real.rpow_sub hM]; ring_nf
  push_cast
  rw [show (2 : ℝ) * (α - 1 / 2) = 2 * α - 1 by ring]
  calc M ^ (1 / 2 : ℝ) * (C ^ (2 * α - 1) / M ^ (α - 1 / 2) * X ^ (ε₂ * (α - 1 / 2)))
      = C ^ (2 * α - 1) * (M ^ (1 / 2 : ℝ) / M ^ (α - 1 / 2)) * X ^ (ε₂ * (α - 1 / 2)) := by
        ring
    _ = _ := by rw [e1]

set_option maxHeartbeats 4000000 in
open Classical in
theorem case_big (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (hmulX : ∀ a 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 a → IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c)
    (α : ℝ) (hα : 1 ≤ α) (W : ℝ → ℝ)
    (hW01 : ∀ t, 0 ≤ W t ∧ W t ≤ 1) (hW1 : ∀ t, 1 < t → t ≤ 2 → W t = 1)
    (k : ℕ) (cls : Ideal (𝓞 F) → Fin k) (ε ε₂ δ : ℝ) (r : ℕ) (hr : 1 ≤ r) (hε₂ : 0 < ε₂)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hrε : 5 / (r : ℝ) ≤ ε / 4) (hδε : δ * (1 + 2 * r) ≤ ε / 4)
    (hε₂ε : ε₂ * (α + 1 / 2) ≤ ε / 4) (K₂ : ℝ)
    (hK₂ : ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N → N ^ 2 / M * (M * N) ^ ε₂ ≤ L → L ≤ M / (M * N) ^ ε₂ →
      ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k) (lam : Ideal (𝓞 F) → ℂ),
        ‖S3 (chiK ι 𝔪 g) (RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M)) (· ⊔ ·)
          ((rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        K₂ * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε₂ *
          (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
          ∑ b ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j), ‖lam b‖ ^ 2)
    (Cδ : ℝ) (hCδ : 0 < Cδ) (hdiv : ∀ n : Ideal (𝓞 F), n ≠ ⊥ → Squarefree n →
      (2 : ℝ) ^ (pf n).card ≤ Cδ * (Ideal.absNorm n : ℝ) ^ δ)
    (cI : ℝ) (hcI : 0 ≤ cI) (hcount : ∀ X : ℝ, 1 ≤ X → ∀ S : Finset (Ideal (𝓞 F)),
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) → (S.card : ℝ) ≤ cI * X)
    (C M : ℝ) (hC : 1 ≤ C) (hM : 1 ≤ M) (hCM : C * (C * M) ^ ε₂ ≤ M) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
      ((1 / (δ * Real.log 2) + 2) * (4 * k * Cδ ^ 2 + 1) ^ r * (r + 1) *
        (64 * k * max K₂ 0 * cI + 6 * cI ^ 2) *
        (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε) := by
  obtain ⟨X, hXd⟩ : ∃ X, X = C * M := ⟨_, rfl⟩
  rw [← hXd] at hCM ⊢
  have hX1 : 1 ≤ X := hXd ▸ one_le_mul_of_one_le_of_one_le hC hM
  have hX0 : 0 < X := by linarith
  have hC0 : 0 < C := by linarith
  have hM0 : 0 < M := by linarith
  have hCX : C ≤ X := hXd ▸ le_mul_of_one_le_right hC0.le hM
  have hMX : M ≤ X := hXd ▸ le_mul_of_one_le_left hM0.le hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = M + C + C ^ (2 * α - 1) * M ^ (1 - α) := ⟨_, rfl⟩
  rw [← hΦ]
  have hΦ3 : 0 ≤ C ^ (2 * α - 1) * M ^ (1 - α) := by positivity
  have hΦM : M ≤ Φ := by rw [hΦ]; linarith
  have hΦ1 : 1 ≤ Φ := le_trans hM hΦM
  have hXe2 : 1 ≤ X ^ ε₂ := Real.one_le_rpow hX1 hε₂.le
  -- the threshold L
  obtain ⟨L, hLd⟩ : ∃ L, L = C ^ 2 / M * X ^ ε₂ := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLd]; positivity
  have hLup : L ≤ M / X ^ ε₂ := by
    rw [hLd, le_div_iff₀ (by positivity)]
    have h1 : (C * X ^ ε₂) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hCM 2
    calc C ^ 2 / M * X ^ ε₂ * X ^ ε₂ = (C * X ^ ε₂) ^ 2 / M := by ring
      _ ≤ M ^ 2 / M := div_le_div_of_nonneg_right h1 hM0.le
      _ = M := by rw [sq, mul_div_assoc, div_self hM0.ne', mul_one]
  have hLM : L ≤ M := le_trans hLup (div_le_self hM0.le hXe2)
  set Rw := RwF 𝔪 L M with hRw
  set w : Ideal (𝓞 F) → ℝ := fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M) with hw
  have hw0 : ∀ a, 0 ≤ w a := fun a => (hW01 _).1
  -- A
  obtain ⟨K₂', hK₂'⟩ : ∃ K₂', K₂' = max K₂ 0 := ⟨_, rfl⟩
  have hK₂'0 : 0 ≤ K₂' := hK₂' ▸ le_max_right _ _
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * K₂' * X ^ (ε₂ * (α + 1 / 2)) * Φ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hcut : ∀ N' : ℝ, 1 ≤ N' → N' ≤ C → ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
      (lam : Ideal (𝓞 F) → ℂ),
      ‖S3 (chiK ι 𝔪 g) Rw w (· ⊔ ·) ((rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        A * (Ideal.absNorm 𝔤 : ℝ) ^ 4 *
          ∑ b ∈ (rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j), ‖lam b‖ ^ 2 := by
    intro N' hN1 hNC 𝔤 j lam
    have hMN : M * N' ≤ X := by rw [hXd, mul_comm C]; exact mul_le_mul_of_nonneg_left hNC hM0.le
    have hMN1 : 1 ≤ M * N' := one_le_mul_of_one_le_of_one_le hM hN1
    have hpow : (M * N') ^ ε₂ ≤ X ^ ε₂ := Real.rpow_le_rpow (by positivity) hMN hε₂.le
    have hlow : N' ^ 2 / M * (M * N') ^ ε₂ ≤ L := by
      rw [hLd]
      have : N' ^ 2 / M ≤ C ^ 2 / M := div_le_div_of_nonneg_right (by gcongr) hM0.le
      exact mul_le_mul this hpow (by positivity) (by positivity)
    have hup : L ≤ M / (M * N') ^ ε₂ :=
      le_trans hLup (div_le_div_of_nonneg_left hM0.le (by positivity) hpow)
    refine (hK₂ M N' L hM hN1 hlow hup 𝔤 j lam).trans ?_
    have hsum : 0 ≤ ∑ b ∈ (rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j), ‖lam b‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hs1 : Real.sqrt M * L ^ (α - 1 / 2) =
        C ^ (2 * α - 1) * M ^ (1 - α) * X ^ (ε₂ * (α - 1 / 2)) :=
      sqrt_mul_rpow_eq hC0 hM0 hX0 hLd
    have hs2 : Real.sqrt (M / L) * N' ≤ M := by
      have h1 : M / L ≤ (M / C) ^ 2 := by
        have hL' : C ^ 2 / M ≤ L := by rw [hLd]; exact le_mul_of_one_le_right (by positivity) hXe2
        calc M / L ≤ M / (C ^ 2 / M) := div_le_div_of_nonneg_left hM0.le (by positivity) hL'
          _ = (M / C) ^ 2 := by field_simp
      have h2 : Real.sqrt (M / L) ≤ M / C := by
        rw [← Real.sqrt_sq (show 0 ≤ M / C by positivity)]
        exact Real.sqrt_le_sqrt h1
      calc Real.sqrt (M / L) * N' ≤ M / C * C :=
            mul_le_mul h2 hNC (by linarith) (by positivity)
        _ = M := by field_simp
    have hXa : 1 ≤ X ^ (ε₂ * (α - 1 / 2)) := Real.one_le_rpow hX1 (by
      have : 0 ≤ α - 1 / 2 := by linarith
      positivity)
    have hbr : M + N' + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N' ≤
        2 * X ^ (ε₂ * (α - 1 / 2)) * Φ := by
      rw [hs1, hΦ]
      have e1 : M ≤ M * X ^ (ε₂ * (α - 1 / 2)) := le_mul_of_one_le_right hM0.le hXa
      have e2 : N' ≤ C * X ^ (ε₂ * (α - 1 / 2)) := le_trans hNC (le_mul_of_one_le_right hC0.le hXa)
      have e3 : 0 ≤ C ^ (2 * α - 1) * M ^ (1 - α) * X ^ (ε₂ * (α - 1 / 2)) := by positivity
      linarith
    have hbr0 : 0 ≤ M + N' + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N' := by
      positivity
    have hK : K₂ ≤ K₂' := hK₂' ▸ le_max_left _ _
    have hN𝔤 : (0 : ℝ) ≤ (Ideal.absNorm 𝔤 : ℝ) ^ 4 := by positivity
    calc K₂ * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N') ^ ε₂ *
          (M + N' + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N') *
          ∑ b ∈ (rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j), ‖lam b‖ ^ 2
        ≤ K₂' * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * X ^ ε₂ * (2 * X ^ (ε₂ * (α - 1 / 2)) * Φ) *
          ∑ b ∈ (rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j), ‖lam b‖ ^ 2 := by
          gcongr
      _ = A * (Ideal.absNorm 𝔤 : ℝ) ^ 4 *
          ∑ b ∈ (rowsF 𝔪 N' (2 * N')).filter (fun b => cls b = j), ‖lam b‖ ^ 2 := by
          rw [hA, show ε₂ * (α + 1 / 2) = ε₂ + ε₂ * (α - 1 / 2) by ring, Real.rpow_add hX0]
          ring
  -- G₀, Cnt, T, v₀
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : ℝ, G₀ = 2 * C ^ (1 / (r : ℝ)) := ⟨_, rfl⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hCr : 1 ≤ C ^ (1 / (r : ℝ)) := Real.one_le_rpow hC (by positivity)
  have hG₀1 : 1 ≤ G₀ := by rw [hG₀]; linarith
  have hG₀r : C < G₀ ^ r := by
    rw [hG₀, mul_pow, ← Real.rpow_natCast (C ^ (1 / (r : ℝ))), ← Real.rpow_mul hC0.le,
      one_div_mul_cancel hr0.ne', Real.rpow_one]
    have : (2 : ℝ) ≤ 2 ^ r := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
    calc C < 2 * C := by linarith
      _ ≤ 2 ^ r * C := mul_le_mul_of_nonneg_right this hC0.le
  have hCnt : ((rowsF 𝔪 0 G₀).card : ℝ) ≤ cI * G₀ :=
    hcount G₀ hG₀1 _ fun I hI => (mem_rowsF.1 hI).2.2.2
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = Cδ * (2 * C) ^ δ := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hTd]; positivity
  have hT : ∀ N' : ℝ, N' ≤ C → ∀ x : Ideal (𝓞 F), x ≠ ⊥ → Squarefree x →
      (Ideal.absNorm x : ℝ) ≤ 2 * N' → (((rowsF 𝔪 0 (2 * N')).filter (· ∣ x)).card : ℝ) ≤ T := by
    intro N' hN' x hx hsq hxN
    have h1 : (((rowsF 𝔪 0 (2 * N')).filter (· ∣ x)).card : ℝ) ≤ 2 ^ (pf x).card := by
      exact_mod_cast card_dvd_le _ hx hsq
    refine h1.trans ((hdiv x hx hsq).trans ?_)
    rw [hTd]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith)
      hδ0.le) hCδ.le
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ℝ, v₀ = (Rw.card : ℝ) * (rowsF 𝔪 0 2).card := ⟨_, rfl⟩
  have hv₀0 : 0 ≤ v₀ := by rw [hv₀]; positivity
  have hbase : ∀ N' : ℝ, 0 < N' → N' < 1 →
      B2f (chiK ι 𝔪 g) Rw w (rowsF 𝔪 N' (2 * N')) v₀ := by
    intro N' hN0 hN1
    have hsub : rowsF 𝔪 N' (2 * N') ⊆ rowsF 𝔪 0 2 := fun b hb => by
      obtain ⟨e, s, -, n2⟩ := mem_rowsF.1 hb
      exact mem_rowsF.2 ⟨e, s, lt_of_lt_of_le zero_lt_one (one_le_absNorm e.1), by linarith⟩
    refine (B2f_trivial ι 𝔪 g Rw w (fun a => hW01 _) _).mono_v ?_
    rw [hv₀]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg _)
  have hmulC : ∀ a ∈ Rw, ∀ 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c :=
    fun a ha 𝔤 c h𝔤 hc => hmulX a 𝔤 c (mem_RwF.1 ha).1 h𝔤 hc
  have hit := iterate_B2 ι 𝔪 g Rw w hw0 hmulC k cls hG₀1 hA0 hT0 hv₀0 hcut hT hCnt hbase r
  -- column blocks
  set I := Nat.log 2 ⌊C⌋₊ + 2 with hId
  set B : ℕ → Finset (Ideal (𝓞 F)) := fun i => rowsF 𝔪 ((2 : ℝ) ^ i / 2) (2 * ((2 : ℝ) ^ i / 2))
    with hB
  have hblock : ∀ i < I, SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (B i)
      (Vseq k A G₀ (cI * G₀) T v₀ r) := by
    intro i hi
    have hle : (2 : ℝ) ^ i / 2 ≤ C := by
      have h1 : 2 ^ i ≤ 2 ^ (Nat.log 2 ⌊C⌋₊ + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ Nat.log 2 ⌊C⌋₊ ≤ ⌊C⌋₊ :=
        Nat.pow_log_le_self 2 (by
          have : 1 ≤ ⌊C⌋₊ := Nat.le_floor (by exact_mod_cast hC)
          omega)
      have h3 : 2 ^ i ≤ 2 * ⌊C⌋₊ := by rw [pow_succ] at h1; omega
      have h3' : (2 : ℝ) ^ i ≤ 2 * ⌊C⌋₊ := by exact_mod_cast h3
      have h4 : (⌊C⌋₊ : ℝ) ≤ C := Nat.floor_le (by linarith)
      linarith
    refine SBf_of_B2f ι 𝔪 g W hW1 (fun t => (hW01 t).1) hM0 hLM _ ?_
    exact hit _ (by positivity) hle (lt_of_le_of_lt hle hG₀r)
  have hdisj : ∀ i < I, ∀ j < I, i ≠ j → Disjoint (B i) (B j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro b hbi hbj
    obtain ⟨-, -, a1, a2⟩ := mem_rowsF.1 hbi
    obtain ⟨-, -, b1, b2⟩ := mem_rowsF.1 hbj
    rcases lt_or_gt_of_ne hij with h | h
    · have : (2 : ℝ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h
      rw [pow_succ] at this; linarith
    · have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) h
      rw [pow_succ] at this; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hVn := Vseq_nonneg (k := (k : ℝ)) (A := A) (G₀ := G₀) (Cnt := cI * G₀) (T := T) (v₀ := v₀)
    hk0 hA0 (by linarith) (by positivity) hv₀0 r
  have hU := SBf_cols_blocks (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C) I B hdisj
    (rows_le_subset 𝔪 hC) hVn hblock
  refine hU.mono_v ?_
  -- the numbers
  have hVle := Vseq_le (k := (k : ℝ)) (A := A) (G₀ := G₀) (Cnt := cI * G₀) (T := T) (v₀ := v₀)
    hk0 hA0 (by linarith) (by positivity) hv₀0 r
  have hI : (I : ℝ) ≤ (1 / (δ * Real.log 2) + 2) * X ^ δ := by
    have h1 := natlog_le hδ0 ⌊C⌋₊
    have h2 : ((⌊C⌋₊ : ℕ) : ℝ) ^ δ ≤ X ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.floor_le (by linarith)).trans hCX) hδ0.le
    have h3 : 1 ≤ X ^ δ := Real.one_le_rpow hX1 hδ0.le
    have h4 : (⌊C⌋₊ : ℝ) ^ δ / (δ * Real.log 2) ≤ X ^ δ / (δ * Real.log 2) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    rw [hId]; push_cast
    rw [add_mul, div_mul_eq_mul_div, one_mul]
    linarith
  have hT2 : (k : ℝ) * T ^ 2 + 1 ≤ (4 * k * Cδ ^ 2 + 1) * X ^ (2 * δ) := by
    have h1 : T ^ 2 ≤ 4 * Cδ ^ 2 * X ^ (2 * δ) := by
      rw [hTd, mul_pow, ← Real.rpow_natCast ((2 * C) ^ δ) 2, ← Real.rpow_mul (by positivity)]
      have : (2 * C) ^ (δ * ((2 : ℕ) : ℝ)) ≤ 4 * X ^ (2 * δ) := by
        rw [Real.mul_rpow (by norm_num) hC0.le]
        have e1 : (2 : ℝ) ^ (δ * ((2 : ℕ) : ℝ)) ≤ 4 := by
          calc (2 : ℝ) ^ (δ * ((2 : ℕ) : ℝ)) ≤ 2 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
            _ = 4 := by norm_num
        have e2 : C ^ (δ * ((2 : ℕ) : ℝ)) ≤ X ^ (2 * δ) := by
          rw [show δ * ((2 : ℕ) : ℝ) = 2 * δ by push_cast; ring]
          exact Real.rpow_le_rpow hC0.le hCX (by positivity)
        exact mul_le_mul e1 e2 (by positivity) (by norm_num)
      calc Cδ ^ 2 * (2 * C) ^ (δ * ((2 : ℕ) : ℝ)) ≤ Cδ ^ 2 * (4 * X ^ (2 * δ)) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = 4 * Cδ ^ 2 * X ^ (2 * δ) := by ring
    have h2 : 1 ≤ X ^ (2 * δ) := Real.one_le_rpow hX1 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1 hk0
    linarith
  have hpowr : ((k : ℝ) * T ^ 2 + 1) ^ r ≤ (4 * k * Cδ ^ 2 + 1) ^ r * X ^ (2 * δ * r) := by
    calc ((k : ℝ) * T ^ 2 + 1) ^ r ≤ ((4 * k * Cδ ^ 2 + 1) * X ^ (2 * δ)) ^ r := by
          gcongr
      _ = (4 * k * Cδ ^ 2 + 1) ^ r * X ^ (2 * δ * r) := by
          rw [mul_pow, pow_rpow_eq hX0.le]
  have hG5 : G₀ ^ 4 * (cI * G₀) ≤ 32 * cI * X ^ (5 / (r : ℝ)) := by
    have : G₀ ^ 5 = 32 * C ^ (5 / (r : ℝ)) := by
      rw [hG₀, mul_pow, ← Real.rpow_natCast (C ^ (1 / (r : ℝ))), ← Real.rpow_mul hC0.le]
      norm_num
      ring_nf
    have h2 : C ^ (5 / (r : ℝ)) ≤ X ^ (5 / (r : ℝ)) :=
      Real.rpow_le_rpow hC0.le hCX (by positivity)
    calc G₀ ^ 4 * (cI * G₀) = cI * G₀ ^ 5 := by ring
      _ = cI * (32 * C ^ (5 / (r : ℝ))) := by rw [this]
      _ ≤ cI * (32 * X ^ (5 / (r : ℝ))) := by gcongr
      _ = 32 * cI * X ^ (5 / (r : ℝ)) := by ring
  have hv₀b : v₀ ≤ 6 * cI ^ 2 * Φ := by
    have h1 : (Rw.card : ℝ) ≤ cI * (3 * M) :=
      hcount (3 * M) (by linarith) _ fun I hI => (mem_RwF.1 hI).2.2.le
    have h2 : ((rowsF 𝔪 0 2).card : ℝ) ≤ cI * 2 :=
      hcount 2 (by norm_num) _ fun I hI => (mem_rowsF.1 hI).2.2.2
    rw [hv₀]
    calc (Rw.card : ℝ) * (rowsF 𝔪 0 2).card ≤ (cI * (3 * M)) * (cI * 2) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = 6 * cI ^ 2 * M := by ring
      _ ≤ 6 * cI ^ 2 * Φ := by gcongr
  have hXr : 1 ≤ X ^ (5 / (r : ℝ)) := Real.one_le_rpow hX1 (by positivity)
  have hXa : 1 ≤ X ^ (ε₂ * (α + 1 / 2)) := Real.one_le_rpow hX1 (by
    have : 0 ≤ α + 1 / 2 := by linarith
    positivity)
  have hinner : (k : ℝ) * A * G₀ ^ 4 * (cI * G₀) + v₀ ≤
      (64 * k * K₂' * cI + 6 * cI ^ 2) * (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ))) * Φ := by
    have e1 : (k : ℝ) * A * G₀ ^ 4 * (cI * G₀) ≤
        k * A * (32 * cI * X ^ (5 / (r : ℝ))) := by
      rw [mul_assoc ((k : ℝ) * A)]
      exact mul_le_mul_of_nonneg_left hG5 (by positivity)
    have e2 : (k : ℝ) * A * (32 * cI * X ^ (5 / (r : ℝ))) =
        64 * k * K₂' * cI * (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ))) * Φ := by
      rw [hA]; ring
    have e3 : 6 * cI ^ 2 * Φ ≤ 6 * cI ^ 2 * (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ))) * Φ := by
      have : 1 ≤ X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ)) := one_le_mul_of_one_le_of_one_le hXa hXr
      calc 6 * cI ^ 2 * Φ = 6 * cI ^ 2 * 1 * Φ := by ring
        _ ≤ 6 * cI ^ 2 * (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ))) * Φ := by gcongr
    linarith
  have hexp : δ + 2 * δ * r + (ε₂ * (α + 1 / 2) + 5 / (r : ℝ)) ≤ ε := by
    have : 0 ≤ 5 / (r : ℝ) := by positivity
    linarith
  have hXall : X ^ δ * X ^ (2 * δ * r) * (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ))) ≤ X ^ ε := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hP0 : 0 ≤ (4 * (k : ℝ) * Cδ ^ 2 + 1) ^ r := by positivity
  have hQ0 : 0 ≤ 64 * (k : ℝ) * K₂' * cI + 6 * cI ^ 2 := by positivity
  rw [← hK₂']
  calc (I : ℝ) * Vseq k A G₀ (cI * G₀) T v₀ r
      ≤ (I : ℝ) * ((k * T ^ 2 + 1) ^ r * (r + 1) * (k * A * G₀ ^ 4 * (cI * G₀) + v₀)) :=
        mul_le_mul_of_nonneg_left hVle (Nat.cast_nonneg _)
    _ ≤ ((1 / (δ * Real.log 2) + 2) * X ^ δ) *
          (((4 * k * Cδ ^ 2 + 1) ^ r * X ^ (2 * δ * r)) * (r + 1) *
            ((64 * k * K₂' * cI + 6 * cI ^ 2) *
              (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ))) * Φ)) := by
        gcongr
    _ = (1 / (δ * Real.log 2) + 2) * (4 * k * Cδ ^ 2 + 1) ^ r * (r + 1) *
          (64 * k * K₂' * cI + 6 * cI ^ 2) * Φ *
          (X ^ δ * X ^ (2 * δ * r) * (X ^ (ε₂ * (α + 1 / 2)) * X ^ (5 / (r : ℝ)))) := by ring
    _ ≤ (1 / (δ * Real.log 2) + 2) * (4 * k * Cδ ^ 2 + 1) ^ r * (r + 1) *
          (64 * k * K₂' * cI + 6 * cI ^ 2) * Φ * X ^ ε := by
        gcongr
    _ = _ := by ring

end L3H

end
end

section
section
/-! # L3H_Stage2: GL Theorem 4.3 with dyadic rows, from GL Proposition 5.2 and `(E_α)`

`stage2`: for every `ε > 0`, `K (M + C + C^(2α−1) M^(1−α)) (C M)^ε` on rows `M < N 𝔡 ≤ 2M`,
columns `N 𝔠 ≤ C`. When `C (CM)^ε₂ ≤ M`: `case_big` (GL §5); otherwise `(E_α)` directly. -/

open NumberField ArtinPrimitiveRoots Real

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

theorem case_small (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (α : ℝ) (hα : 1 ≤ α)
    (ε ε₂ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hε₂ : 0 < ε₂) (hε₂ε : ε₂ * (α + 1 / 2) ≤ ε / 4) (KE : ℝ)
    (hKE : ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C) (KE * (D + C ^ α) * (C * D) ^ (ε / 2)))
    (C M : ℝ) (hC : 1 ≤ C) (hM : 1 ≤ M) (hCM : ¬ C * (C * M) ^ ε₂ ≤ M) :
    SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
      (4 * max KE 0 * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε) := by
  push Not at hCM
  obtain ⟨X, hXd⟩ : ∃ X, X = C * M := ⟨_, rfl⟩
  rw [← hXd] at hCM ⊢
  have hX1 : 1 ≤ X := hXd ▸ one_le_mul_of_one_le_of_one_le hC hM
  have hX0 : 0 < X := by linarith
  have hC0 : 0 < C := by linarith
  have hM0 : 0 < M := by linarith
  have hXe : 0 < X ^ ε₂ := by positivity
  have h1 := (hKE C (2 * M) hC (by linarith)).mono_rows (R := rowsF 𝔪 M (2 * M)) (fun 𝔡 h𝔡 => by
    obtain ⟨e, s, -, n⟩ := mem_rowsF.1 h𝔡
    exact mem_rowsF.2 ⟨e, s, lt_of_lt_of_le zero_lt_one (one_le_absNorm e.1), n⟩)
  have hK := le_max_left KE 0
  have hK0 := le_max_right KE 0
  refine (h1.mono_v ?_)
  -- C^α ≤ C^(2α−1) M^(1−α) X^(ε₂(α−1))
  have hMC : M / X ^ ε₂ < C := by rw [div_lt_iff₀ hXe]; linarith
  have hpow : C ^ (1 - α) ≤ M ^ (1 - α) * X ^ (ε₂ * (α - 1)) := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) hMC.le (show 1 - α ≤ 0 by linarith)
    rw [Real.div_rpow hM0.le hXe.le, div_eq_mul_inv, ← Real.rpow_neg hXe.le,
      ← Real.rpow_mul hX0.le] at h
    rw [show ε₂ * (α - 1) = ε₂ * -(1 - α) by ring]
    exact h
  have hCa : C ^ α ≤ C ^ (2 * α - 1) * M ^ (1 - α) * X ^ (ε₂ * (α - 1)) := by
    have e : C ^ α = C ^ (2 * α - 1) * C ^ (1 - α) := by
      rw [← Real.rpow_add hC0]; ring_nf
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hXa : 1 ≤ X ^ (ε₂ * (α - 1)) := Real.one_le_rpow hX1 (by
    have : 0 ≤ α - 1 := by linarith
    positivity)
  have hT0 : 0 ≤ C ^ (2 * α - 1) * M ^ (1 - α) := by positivity
  have hsum : 2 * M + C ^ α ≤ 2 * X ^ (ε₂ * (α - 1)) * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) := by
    have e1 : M ≤ M * X ^ (ε₂ * (α - 1)) := le_mul_of_one_le_right hM0.le hXa
    have e2 : 0 ≤ C * X ^ (ε₂ * (α - 1)) := by positivity
    have e3 : 0 ≤ C ^ (2 * α - 1) * M ^ (1 - α) * X ^ (ε₂ * (α - 1)) := by positivity
    linarith
  have hX2 : (C * (2 * M)) ^ (ε / 2) ≤ 2 * X ^ (ε / 2) := by
    rw [show C * (2 * M) = 2 * X by rw [hXd]; ring, Real.mul_rpow (by norm_num) hX0.le]
    have : (2 : ℝ) ^ (ε / 2) ≤ 2 := by
      calc (2 : ℝ) ^ (ε / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hexp : X ^ (ε₂ * (α - 1)) * X ^ (ε / 2) ≤ X ^ ε := by
    rw [← Real.rpow_add hX0]
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have : ε₂ * (α - 1) ≤ ε₂ * (α + 1 / 2) := mul_le_mul_of_nonneg_left (by linarith) hε₂.le
    linarith
  have hsum0 : 0 ≤ 2 * M + C ^ α := by positivity
  calc KE * (2 * M + C ^ α) * (C * (2 * M)) ^ (ε / 2)
      ≤ max KE 0 * (2 * X ^ (ε₂ * (α - 1)) * (M + C + C ^ (2 * α - 1) * M ^ (1 - α))) *
          (2 * X ^ (ε / 2)) := by
        gcongr
    _ = 4 * max KE 0 * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) *
          (X ^ (ε₂ * (α - 1)) * X ^ (ε / 2)) := by ring
    _ ≤ 4 * max KE 0 * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * X ^ ε := by gcongr

theorem stage2_main (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (hmulX : ∀ a 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 a → IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c)
    (α : ℝ) (hα : 1 ≤ α)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C) (K * (D + C ^ α) * (C * D) ^ ε))
    (W : ℝ → ℝ) (hW01 : ∀ t, 0 ≤ W t ∧ W t ≤ 1) (hW1 : ∀ t, 1 < t → t ≤ 2 → W t = 1)
    (k : ℕ) (cls : Ideal (𝓞 F) → Fin k)
    (hcut : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
      N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
      ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k) (lam : Ideal (𝓞 F) → ℂ),
        ‖S3 (chiK ι 𝔪 g) (RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M)) (· ⊔ ·)
          ((rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
          (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
          ∑ b ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j), ‖lam b‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, ∀ C M : ℝ, 1 ≤ C → 1 ≤ M →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
        (K * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε) := by
  obtain ⟨r, hrd⟩ : ∃ r : ℕ, r = ⌈20 / ε⌉₊ := ⟨_, rfl⟩
  have hr20 : 20 / ε ≤ r := hrd ▸ Nat.le_ceil _
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr20
  have hr : 1 ≤ r := by exact_mod_cast (show (1 : ℝ) ≤ r by
    have : (20 : ℝ) ≤ 20 / ε := by rw [le_div_iff₀ hε]; linarith
    linarith)
  have hrε : 5 / (r : ℝ) ≤ ε / 4 := by
    rw [div_le_iff₀ hr0]
    rw [div_le_iff₀ hε] at hr20
    linarith
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε / (4 * (1 + 2 * r)) := ⟨_, rfl⟩
  have hden : 0 < 4 * (1 + 2 * (r : ℝ)) := by positivity
  have hδ0 : 0 < δ := hδd ▸ div_pos hε hden
  have hδε : δ * (1 + 2 * r) ≤ ε / 4 := by
    rw [hδd, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]; nlinarith
  have hδ1 : δ ≤ 1 := by
    rw [hδd, div_le_one hden]; linarith
  obtain ⟨ε₂, hε₂d⟩ : ∃ ε₂ : ℝ, ε₂ = ε / (4 * (α + 1 / 2)) := ⟨_, rfl⟩
  have hden2 : 0 < 4 * (α + 1 / 2) := by nlinarith
  have hε₂ : 0 < ε₂ := hε₂d ▸ div_pos hε hden2
  have hε₂ε : ε₂ * (α + 1 / 2) ≤ ε / 4 := by
    rw [hε₂d, div_mul_eq_mul_div, div_le_div_iff₀ hden2 (by norm_num)]; nlinarith
  obtain ⟨K₂, hK₂⟩ := hcut ε₂ hε₂
  obtain ⟨Cδ, hCδ, hdiv⟩ := two_pow_card_pf_le (F := F) hδ0
  obtain ⟨cI, hcI, hcount⟩ := card_le_mul F
  obtain ⟨KE, hKE⟩ := hE (ε / 2) (by positivity)
  refine ⟨max ((1 / (δ * Real.log 2) + 2) * (4 * k * Cδ ^ 2 + 1) ^ r * (r + 1) *
    (64 * k * max K₂ 0 * cI + 6 * cI ^ 2)) (4 * max KE 0), fun C M hC hM => ?_⟩
  have hΦ : 0 ≤ (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε := by positivity
  by_cases hCM : C * (C * M) ^ ε₂ ≤ M
  · refine (case_big ι 𝔪 g hmulX α hα W hW01 hW1 k cls ε ε₂ δ r hr hε₂ hδ0 hδ1 hrε hδε hε₂ε K₂
      hK₂ Cδ hCδ hdiv cI hcI hcount C M hC hM hCM).mono_v ?_
    rw [mul_assoc _ (M + C + _), mul_assoc (max _ _)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hΦ
  · refine (case_small ι 𝔪 g α hα ε ε₂ hε hε1 hε₂ hε₂ε KE hKE C M hC hM hCM).mono_v ?_
    rw [mul_assoc _ (M + C + _), mul_assoc (max _ _)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hΦ

theorem stage2 (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪)
    (hmulX : ∀ a 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 a → IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      chiK ι 𝔪 g a (𝔤 * c) = chiK ι 𝔪 g a 𝔤 * chiK ι 𝔪 g a c)
    (α : ℝ) (hα : 1 ≤ α)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 0 D) (rowsF 𝔪 0 C) (K * (D + C ^ α) * (C * D) ^ ε))
    (W : ℝ → ℝ) (hW01 : ∀ t, 0 ≤ W t ∧ W t ≤ 1) (hW1 : ∀ t, 1 < t → t ≤ 2 → W t = 1)
    (k : ℕ) (cls : Ideal (𝓞 F) → Fin k)
    (hcut : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
      N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
      ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k) (lam : Ideal (𝓞 F) → ℂ),
        ‖S3 (chiK ι 𝔪 g) (RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M)) (· ⊔ ·)
          ((rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
          (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
          ∑ b ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j), ‖lam b‖ ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ C M : ℝ, 1 ≤ C → 1 ≤ M →
      SBf (chiK ι 𝔪 g) (rowsF 𝔪 M (2 * M)) (rowsF 𝔪 0 C)
        (K * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε) := by
  obtain ⟨K, hK⟩ := stage2_main ι 𝔪 g hmulX α hα hE W hW01 hW1 k cls hcut (min ε 1)
    (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨max K 0, fun C M hC hM => (hK C M hC hM).mono_v ?_⟩
  have hX1 : 1 ≤ C * M := one_le_mul_of_one_le_of_one_le hC hM
  have hT : 0 ≤ M + C + C ^ (2 * α - 1) * M ^ (1 - α) := by positivity
  have h1 : (C * M) ^ min ε 1 ≤ (C * M) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hX1 (min_le_left _ _)
  calc K * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ min ε 1
      ≤ max K 0 * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ min ε 1 := by
        gcongr
        exact le_max_left _ _
    _ ≤ max K 0 * (M + C + C ^ (2 * α - 1) * M ^ (1 - α)) * (C * M) ^ ε := by
        gcongr

end L3H

end
end

section
section
/-! # L3H_CutBr: GL Prop 5.2 in the cut's `tsum` form as a bound on `S3`

The cut sums over subtypes; its row sum is over all exterior `𝔞` with squarefree part `> L`, of
which only `N 𝔞 < 3M` (the support of `W(·/M)`) contribute. -/

open NumberField ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

namespace L3H

variable {F : Type*} [Field F] [NumberField F]

lemma tsum_subtype_of_zero {β E : Type*} [AddCommMonoid E] [TopologicalSpace E] (p : β → Prop)
    (S : Finset β) (hS : ∀ x ∈ S, p x) (f : β → E) (hf : ∀ x, p x → x ∉ S → f x = 0) :
    ∑' x : {x // p x}, f x.1 = ∑ x ∈ S, f x := by
  classical
  change ∑' x : ({x | p x} : Set β), f x = _
  rw [tsum_subtype, tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hS x hx)]
  · intro x hx
    by_cases h : p x
    · rw [Set.indicator_of_mem (show x ∈ {x | p x} from h)]; exact hf x h hx
    · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from h)]

theorem cut_bridge (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (α : ℝ) (W : ℝ → ℝ)
    (hW3 : ∀ t, 3 ≤ t → W t = 0) (k : ℕ) (cls : Ideal (𝓞 F) → Fin k) (ε K : ℝ)
    (h : ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N →
      N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
      ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k)
        (z : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
          N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j} → ℂ),
        ‖∑' 𝔟₁, ∑' 𝔟₂, if 𝔟₁.1 ⊔ 𝔟₂.1 = 𝔤 then
            z 𝔟₁ * starRingEnd ℂ (z 𝔟₂) *
              ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧
                  ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
                    L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
                (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) *
                  residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₁.1) ^ 3 *
                  starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen 𝔟₂.1) ^ 3)
          else 0‖ ≤
          K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
            (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
            ∑' 𝔟, ‖z 𝔟‖ ^ 2) :
    ∀ M N L : ℝ, 1 ≤ M → 1 ≤ N → N ^ 2 / M * (M * N) ^ ε ≤ L → L ≤ M / (M * N) ^ ε →
      ∀ (𝔤 : Ideal (𝓞 F)) (j : Fin k) (lam : Ideal (𝓞 F) → ℂ),
        ‖S3 (chiK ι 𝔪 g) (RwF 𝔪 L M) (fun 𝔞 => W ((Ideal.absNorm 𝔞 : ℝ) / M)) (· ⊔ ·)
          ((rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j)) 𝔤 lam‖ ≤
        K * (Ideal.absNorm 𝔤 : ℝ) ^ 4 * (M * N) ^ ε *
          (M + N + Real.sqrt M * L ^ (α - 1 / 2) + Real.sqrt (M / L) * N) *
          ∑ b ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j), ‖lam b‖ ^ 2 := by
  classical
  intro M N L hM hN hL1 hL2 𝔤 j lam
  have h1 := h M N L hM hN hL1 hL2 𝔤 j (fun b => lam b.1)
  have hM0 : 0 < M := by linarith
  have hcol : ∀ x, x ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j) ↔
      (IsExterior 𝔪 x ∧ Squarefree x ∧ N < (Ideal.absNorm x : ℝ) ∧
        (Ideal.absNorm x : ℝ) ≤ 2 * N ∧ cls x = j) := by
    intro x
    rw [Finset.mem_filter, mem_rowsF]
    tauto
  have hrow : ∀ b₁ b₂ : Ideal (𝓞 F),
      ∑' 𝔞 : {𝔞 : Ideal (𝓞 F) // IsExterior 𝔪 𝔞 ∧ ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ^ 2 ∣ 𝔞 →
          L * (Ideal.absNorm 𝔟 : ℝ) ^ 2 < Ideal.absNorm 𝔞},
        (W ((Ideal.absNorm 𝔞.1 : ℝ) / M) : ℂ) * residueSymbol ι 𝔪 𝔞.1 (g.gen b₁) ^ 3 *
          starRingEnd ℂ (residueSymbol ι 𝔪 𝔞.1 (g.gen b₂) ^ 3) =
      ∑ a ∈ RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * chiK ι 𝔪 g a b₁ *
        starRingEnd ℂ (chiK ι 𝔪 g a b₂) := by
    intro b₁ b₂
    refine tsum_subtype_of_zero _ (RwF 𝔪 L M) (fun x hx => ⟨(mem_RwF.1 hx).1,
      (mem_RwF.1 hx).2.1⟩) (fun a => (W ((Ideal.absNorm a : ℝ) / M) : ℂ) *
        residueSymbol ι 𝔪 a (g.gen b₁) ^ 3 *
        starRingEnd ℂ (residueSymbol ι 𝔪 a (g.gen b₂) ^ 3)) ?_
    intro a ha hna
    have h3 : 3 * M ≤ (Ideal.absNorm a : ℝ) := by
      by_contra hc; push Not at hc
      exact hna (mem_RwF.2 ⟨ha.1, ha.2, hc⟩)
    have hW : W ((Ideal.absNorm a : ℝ) / M) = 0 := hW3 _ (by rw [le_div_iff₀ hM0]; linarith)
    simp only [hW, Complex.ofReal_zero, zero_mul]
  simp_rw [hrow] at h1
  rw [tsum_subtype_eq _ _ hcol (fun b => ‖lam b‖ ^ 2)] at h1
  have hin : ∀ b₁ : Ideal (𝓞 F), ∑' 𝔟₂ : {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟 ∧ Squarefree 𝔟 ∧
      N < (Ideal.absNorm 𝔟 : ℝ) ∧ (Ideal.absNorm 𝔟 : ℝ) ≤ 2 * N ∧ cls 𝔟 = j},
      (if b₁ ⊔ 𝔟₂.1 = 𝔤 then lam b₁ * starRingEnd ℂ (lam 𝔟₂.1) *
        ∑ a ∈ RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * chiK ι 𝔪 g a b₁ *
          starRingEnd ℂ (chiK ι 𝔪 g a 𝔟₂.1) else 0) =
      ∑ b₂ ∈ (rowsF 𝔪 N (2 * N)).filter (fun b => cls b = j),
        (if b₁ ⊔ b₂ = 𝔤 then lam b₁ * starRingEnd ℂ (lam b₂) *
          ∑ a ∈ RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * chiK ι 𝔪 g a b₁ *
            starRingEnd ℂ (chiK ι 𝔪 g a b₂) else 0) := fun b₁ =>
    tsum_subtype_eq _ _ hcol (fun b₂ => if b₁ ⊔ b₂ = 𝔤 then lam b₁ * starRingEnd ℂ (lam b₂) *
          ∑ a ∈ RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * chiK ι 𝔪 g a b₁ *
            starRingEnd ℂ (chiK ι 𝔪 g a b₂) else 0)
  simp_rw [hin] at h1
  rw [tsum_subtype_eq _ _ hcol (fun b₁ => ∑ b₂ ∈ (rowsF 𝔪 N (2 * N)).filter
    (fun b => cls b = j), (if b₁ ⊔ b₂ = 𝔤 then lam b₁ * starRingEnd ℂ (lam b₂) *
          ∑ a ∈ RwF 𝔪 L M, ((W ((Ideal.absNorm a : ℝ) / M) : ℝ) : ℂ) * chiK ι 𝔪 g a b₁ *
            starRingEnd ℂ (chiK ι 𝔪 g a b₂) else 0))] at h1
  exact h1

end L3H

end
end

section
section
/-! # L3H_Dev: GL Theorem 4.3 (10138558), the `≤`-form, statement verbatim

From GL Proposition 5.2 for this family (draft cut stub
`exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le`): GL Lemma 5.1
and the iteration (5.3)–(5.4) give the dyadic Theorem 4.3 (`L3H.stage2`), and GL Lemma 4.4 gives
the `≤`-form (`L3H.up`). Does not import the target's stub. -/

open NumberField

namespace ArtinPrimitiveRoots

theorem exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (α : ℝ), 1 ≤ α →
        (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2) →
        ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε *
                ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  obtain ⟨N₁, h₁⟩ :=
    exists_cutoff_norm_tsum_tsum_mul_conj_tsum_weight_mul_residueSymbol_pow_three_le
      n hn0 hn F ι
  refine ⟨max N₁ (3 ^ Module.finrank ℤ (𝓞 F)), fun 𝔪 h𝔪 hs g α hα hE ε hε => ?_⟩
  have hs₁ : SmallPrimesDvd N₁ 𝔪 := fun P hP hb hle =>
    hs P hP hb (hle.trans (le_max_left _ _))
  have hn6 : 6 ∣ n := dvd_trans (by norm_num) hn
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn6).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have hgood : ∀ p : Ideal (𝓞 F), p.IsMaximal → p ≠ ⊥ → ¬ 𝔪 ≤ p → C3B.GoodP 𝔪 p :=
    fun p hpM hp0 hpm => C3B.goodP_of_exterior n hn0 hn6 (le_max_right _ _) hs hpM.isPrime
      (L3H.exterior_of_maximal hpM hp0 hpm)
  have hE' : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
      L3H.SBf (L3H.chiK ι 𝔪 g) (L3H.rowsF 𝔪 0 D) (L3H.rowsF 𝔪 0 C)
        (K * (D + C ^ α) * (C * D) ^ ε) := by
    intro ε hε
    obtain ⟨K, hK⟩ := hE ε hε
    exact ⟨K, fun C D hC hD => L3H.SBf_of_sb ι 𝔪 g (hK C D hC hD)⟩
  obtain ⟨W, hW01, hW1, hW3, k, cls, hcut⟩ := h₁ 𝔪 h𝔪 hs₁ g α hα hE
  have hmulX : ∀ a 𝔤 c : Ideal (𝓞 F), IsExterior 𝔪 a → IsExterior 𝔪 𝔤 → IsExterior 𝔪 c →
      L3H.chiK ι 𝔪 g a (𝔤 * c) = L3H.chiK ι 𝔪 g a 𝔤 * L3H.chiK ι 𝔪 g a c :=
    fun a 𝔤 c ha h𝔤 hc => L3H.chiK_mul_col ι g hω
      (C3B.goodP_of_mem n hn0 hn6 (le_max_right _ _) hs ha) h𝔤 hc
  have hdy := L3H.stage2 ι 𝔪 g hmulX α hα hE' W hW01 hW1 k cls
    (fun ε₁ hε₁ => (hcut ε₁ hε₁).imp fun K hK => L3H.cut_bridge ι 𝔪 g α W hW3 k cls ε₁ K hK)
  obtain ⟨K, hK⟩ := L3H.up ι 𝔪 h𝔪 g hω hgood α hα hdy ε hε
  exact ⟨K, fun C D hC hD => L3H.sb_of_SBf ι 𝔪 g (hK C D hC hD)⟩

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ)
    (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (g : AllowedGen ι 𝔪) (α : ℝ), 1 ≤ α →
        (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C ^ α) * (C * D) ^ ε * ∑' 𝔠, ‖z 𝔠‖ ^ 2) →
        ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ C D : ℝ, 1 ≤ C → 1 ≤ D →
          ∀ z : {𝔠 : Ideal (𝓞 F) // IsExterior 𝔪 𝔠 ∧ Squarefree 𝔠 ∧
              (Ideal.absNorm 𝔠 : ℝ) ≤ C} → ℂ,
            ∑' 𝔡 : {𝔡 : Ideal (𝓞 F) // IsExterior 𝔪 𝔡 ∧ Squarefree 𝔡 ∧
                (Ideal.absNorm 𝔡 : ℝ) ≤ D},
                ‖∑' 𝔠, z 𝔠 * residueSymbol ι 𝔪 𝔡.1 (g.gen 𝔠.1) ^ 3‖ ^ 2 ≤
              K * (D + C + C ^ (2 * α - 1) * D ^ (1 - α)) * (C * D) ^ ε *
                ∑' 𝔠, ‖z 𝔠‖ ^ 2 := by
  exact ArtinPrimitiveRoots.exists_cutoff_tsum_norm_sq_tsum_mul_residueSymbol_pow_three_le_of_sieveExponent n hn0 hn F ι

end
