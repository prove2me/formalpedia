-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_principalCoeff_prime_pow_mul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T18:58:26.259979+00:00
-- url     : https://prove2.me/submissions/b1ae3611-2d1f-407e-a7a0-b75be4cb6aa0

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff
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

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

lemma residueSymbol_top (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 ⊤ x = 1 := by
  simp [residueSymbol, normalizedFactors_top]

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

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

lemma sexticResidueSymbol_eq_of_mk_eq (ι : F →+* ℂ) (P : Ideal (𝓞 F)) (x y : SInt 𝔪)
    (h : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x =
      Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :
    sexticResidueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P y := by
  unfold sexticResidueSymbol
  rw [h]

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

end gen

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

/-! ### Elementary lemmas -/

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

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots
end

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

/-- `x I ⊆ R` for an ideal `I` coprime to `𝔪`. -/
def ExtWit (𝔪 : Ideal (𝓞 F)) (x : F) : Prop :=
  ∃ I : Ideal (𝓞 F), I ⊔ 𝔪 = ⊤ ∧
    ∀ i ∈ I, x * algebraMap (𝓞 F) F i ∈ (placesOf 𝔪).integer F

/-- `e` is additive on elements with `ExtWit` (proved below from section A's `C3I_Add`). -/
def HypAdd (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ x y : F, ExtWit 𝔪 x → ExtWit 𝔪 y → sAddChar 𝔪 (x + y) = sAddChar 𝔪 x * sAddChar 𝔪 y

theorem hypAdd (𝔪 : Ideal (𝓞 F)) : HypAdd 𝔪 := by
  rintro x y ⟨I, hI, hx⟩ ⟨J, hJ, hy⟩
  exact C3I.sAddChar_add (C3I.hasWit_of_mul_mem x I hI hx) (C3I.hasWit_of_mul_mem y J hJ hy)

lemma extWit_div_add {𝔪 I : Ideal (𝓞 F)} (hI : I ⊔ 𝔪 = ⊤) {q : SInt 𝔪}
    (hq : Ideal.span {q} = I.map (algebraMap (𝓞 F) (SInt 𝔪))) (hq0 : (q : F) ≠ 0)
    (z r : SInt 𝔪) : ExtWit 𝔪 ((z : F) / (q : F) + (r : F)) := by
  refine ⟨I, hI, fun i hi => ?_⟩
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ Ideal.span {q} := hq ▸ Ideal.mem_map_of_mem _ hi
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  have hiF : algebraMap (𝓞 F) F i = (t : F) * (q : F) := by
    have := congrArg (fun x : SInt 𝔪 => (x : F)) ht
    simp only [Subalgebra.coe_mul] at this
    rw [this]; rfl
  rw [hiF, show ((z : F) / (q : F) + (r : F)) * ((t : F) * (q : F)) =
    (z : F) * (t : F) + (r : F) * (t : F) * (q : F) by field_simp]
  exact add_mem (mul_mem z.2 t.2) (mul_mem (mul_mem r.2 t.2) q.2)

/-- Hypothesis (section A): at an exterior prime, the sextic symbol is multiplicative on `R`, with
sixth power `1` off `PR`. -/
def HypChi (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
    (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
    (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1)

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

lemma exterior_of_mem_factors {𝔞 Q : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (hQ : Q ∈ normalizedFactors 𝔞) : Q.IsPrime ∧ IsExterior 𝔪 Q := by
  have hpr : Prime Q := prime_of_normalized_factor Q hQ
  refine ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero, ?_⟩
  have hle : 𝔞 ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
  exact eq_top_iff.mpr (h𝔞.2 ▸ sup_le_sup_right hle 𝔪)

lemma isExterior_of_mul_left {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun h0 => h.1 (by rw [h0, Ideal.bot_mul]), ?_⟩
  exact eq_top_iff.mpr (h.2 ▸ sup_le_sup_right (Ideal.mul_le_inf.trans inf_le_left) 𝔪)

lemma isExterior_of_mul_right {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) :
    IsExterior 𝔪 J := by
  rw [mul_comm] at h; exact isExterior_of_mul_left h

/-- An exterior prime does not become the unit ideal in `R`. -/
lemma map_ne_top {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ := by
  intro htop
  let v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQ, hQe.1⟩
  have hvS : v ∉ placesOf 𝔪 := by
    intro hv
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := hQe.2 ▸ sup_le le_rfl hv
    exact hQ.ne_top (eq_top_iff.mpr this)
  let J : Ideal (SInt 𝔪) :=
    { carrier := {x | v.valuation F (x : F) < 1}
      add_mem' := fun {a b} ha hb => by
        show v.valuation F ((a + b : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by
        show v.valuation F ((0 : SInt 𝔪) : F) < 1
        simp
      smul_mem' := fun c x hx => by
        show v.valuation F ((c * x : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (c.2 v hvS)) hx }
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) < 1
    rw [C3B.coe_algebraMap_SInt]
    exact (v.valuation_lt_one_iff_mem a).mpr ha
  have h1 : (1 : SInt 𝔪) ∈ J := hle (htop ▸ Submodule.mem_top)
  have : v.valuation F ((1 : SInt 𝔪) : F) < 1 := h1
  simp at this

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

/-- Coprimality to `P` for an ideal not contained in the maximal ideal `P`. -/
lemma isCoprime_pow_of_not_le {P J : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hJ : ¬ J ≤ P)
    (a : ℕ) : IsCoprime (P ^ a) J := by
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have h1 : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    have : P < P ⊔ J := lt_of_le_of_ne le_sup_left (fun h => hJ (le_sup_right.trans h.symm.le))
    exact hmax.1.2 _ this
  exact h1.pow_left

lemma isCoprime_map {I J : Ideal (𝓞 F)} (h : IsCoprime I J) :
    IsCoprime (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (J.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [← Ideal.map_sup, h, Ideal.map_top]

lemma exists_inv_mod {I : Ideal (SInt 𝔪)} {x : SInt 𝔪} (h : IsCoprime (Ideal.span {x}) I) :
    ∃ x' : SInt 𝔪, x * x' - 1 ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨c, ?_⟩
  have : x * c - 1 = -b := by rw [← hab]; ring
  rw [this]; exact neg_mem hb

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

lemma residueSymbol_mul_ideal (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  have h := C3B.normalizedFactors_prime_pow hP hP0 1
  rw [pow_one, Multiset.replicate_one] at h
  simp [residueSymbol, h]

lemma residueSymbol_prime_pow {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (k : ℕ)
    (x : SInt 𝔪) : residueSymbol ι 𝔪 (P ^ k) x = sexticResidueSymbol ι 𝔪 P x ^ k := by
  simp [residueSymbol, C3B.normalizedFactors_prime_pow hP hP0 k]

lemma residueSymbol_mul (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun Q hQ => ?_
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  exact (hχ Q hQp hQe).1 x y

lemma not_mem_of_isCoprime {I : Ideal (SInt 𝔪)} (hI : I ≠ ⊤) {x : SInt 𝔪}
    (h : IsCoprime (Ideal.span {x}) I) : x ∉ I := by
  intro hx
  apply hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hx) le_rfl

lemma residueSymbol_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ^ 6 = 1 := by
  unfold residueSymbol
  rw [← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨hQp, hQe⟩ := exterior_of_mem_factors h𝔞 hQ
  apply (hχ Q hQp hQe).2
  apply not_mem_of_isCoprime (map_ne_top hQp hQe)
  have hle : 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.map_mono (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ))
  rw [Ideal.isCoprime_iff_sup_eq] at hx ⊢
  exact eq_top_iff.mpr (hx ▸ sup_le_sup_left hle _)

lemma residueSymbol_ne_zero (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x : SInt 𝔪} (hx : IsCoprime (Ideal.span {x}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)))) :
    residueSymbol ι 𝔪 𝔞 x ≠ 0 := by
  intro h0
  have := residueSymbol_pow_six hχ h𝔞 hx
  rw [h0] at this; norm_num at this

lemma isCoprime_one (I : Ideal (SInt 𝔪)) : IsCoprime (Ideal.span {(1 : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_one]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_one (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) :
    residueSymbol ι 𝔪 𝔞 1 = 1 := by
  have h := residueSymbol_mul hχ h𝔞 (1 : SInt 𝔪) 1
  rw [one_mul] at h
  have h0 := residueSymbol_ne_zero hχ h𝔞 (isCoprime_one _)
  have : residueSymbol ι 𝔪 𝔞 1 * (residueSymbol ι 𝔪 𝔞 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 h0
  · exact sub_eq_zero.mp h1

/-- `χ_𝔞(x) χ_𝔞(x') = 1` when `x x' ≡ 1 (mod 𝔞R)`. -/
lemma residueSymbol_mul_inv (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (h : x * x' - 1 ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 x' = 1 := by
  rw [← residueSymbol_mul hχ h𝔞, C3B.residueSymbol_congr ι 𝔞 _ 1 h, residueSymbol_one hχ h𝔞]

lemma isCoprime_unit (u : (SInt 𝔪)ˣ) (I : Ideal (SInt 𝔪)) :
    IsCoprime (Ideal.span {(u : SInt 𝔪)}) I := by
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]; exact Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _)

lemma residueSymbol_unit_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  have hp : ∀ n : ℕ, residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ n) = residueSymbol ι 𝔪 𝔞 u ^ n := by
    intro n
    induction n with
    | zero => simp [residueSymbol_one hχ h𝔞]
    | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]
  rw [residueSymbol_mul hχ h𝔞, hp, residueSymbol_pow_six hχ h𝔞 (isCoprime_unit u _), one_mul]

lemma residueSymbol_pow (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (x : SInt 𝔪) (n : ℕ) : residueSymbol ι 𝔪 𝔞 (x ^ n) = residueSymbol ι 𝔪 𝔞 x ^ n := by
  induction n with
  | zero => simp [residueSymbol_one hχ h𝔞]
  | succ n ih => rw [pow_succ, residueSymbol_mul hχ h𝔞, ih, pow_succ]

/-! ### Generators -/

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul' (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

lemma gen_top (g : AllowedGen ι 𝔪) : ∃ ε : (SInt 𝔪)ˣ, g.gen ⊤ = (ε : SInt 𝔪) ^ 6 := by
  obtain ⟨ε, hε⟩ := gen_mul' g ⟨top_ne_bot, top_sup_eq _⟩ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.top_mul] at hε
  obtain ⟨u, hu⟩ := C3B.isUnit_gen_top g
  refine ⟨ε⁻¹, ?_⟩
  have h1 : (u : SInt 𝔪) * 1 = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) := by
    rw [← hu] at hε
    rw [mul_one]
    calc (u : SInt 𝔪) = (ε : SInt 𝔪) ^ 6 * u * u := hε
      _ = _ := by ring
  have h2 := u.isUnit.mul_left_cancel h1
  rw [← hu]
  have h3 : ((ε : SInt 𝔪) ^ 6) * ((↑(ε⁻¹) : SInt 𝔪) ^ 6) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  calc (u : SInt 𝔪) = (u : SInt 𝔪) * ((ε : SInt 𝔪) ^ 6 * (↑(ε⁻¹) : SInt 𝔪) ^ 6) := by
        rw [h3, mul_one]
    _ = ((ε : SInt 𝔪) ^ 6 * (u : SInt 𝔪)) * (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by ring
    _ = (↑(ε⁻¹) : SInt 𝔪) ^ 6 := by rw [← h2, one_mul]

end C3M

end ArtinPrimitiveRoots
end

section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

open Classical in
/-- The summand of the Poisson factor, with free generators `s, A`, multiplier `Af` and twist
`c`. -/
noncomputable def U (𝔰 𝔄 : Ideal (𝓞 F)) (s A Af c h d v : SInt 𝔪) : ℂ :=
  if h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) then
    residueSymbol ι 𝔪 𝔰 d * (residueSymbol ι 𝔪 𝔄 v *
      sAddChar 𝔪 (((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F))))
  else 0

/-- The Poisson factor with free generators. -/
noncomputable def PS (𝔰 𝔄 : Ideal (𝓞 F)) (s A Af c h : SInt 𝔪) : ℂ :=
  ∑ᶠ d : SInt 𝔪 ⧸ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)),
    ∑ᶠ v : SInt 𝔪 ⧸ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)),
      U ι 𝔪 𝔰 𝔄 s A Af c h (quotLift d) (quotLift v)

/-- The Gauss sum summand with free generator `c` and twist `c'`. -/
noncomputable def V (𝔠 : Ideal (𝓞 F)) (c c' : SInt 𝔪) (j : ℕ) (x : SInt 𝔪) : ℂ :=
  residueSymbol ι 𝔪 𝔠 x ^ j * sAddChar 𝔪 ((x : F) * (c' : F) / (c : F))

/-- The Gauss sum with free generator. -/
noncomputable def GS (𝔠 : Ideal (𝓞 F)) (c c' : SInt 𝔪) (j : ℕ) : ℂ :=
  ∑ᶠ x : SInt 𝔪 ⧸ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪)), V ι 𝔪 𝔠 c c' j (quotLift x)

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

lemma quotLift_mul_sub (I : Ideal (SInt 𝔪)) (u : SInt 𝔪) (x : SInt 𝔪 ⧸ I) :
    quotLift (Ideal.Quotient.mk I u * x) - u * quotLift x ∈ I := by
  rw [← Ideal.Quotient.eq, map_mul]
  rw [show Ideal.Quotient.mk I (quotLift (Ideal.Quotient.mk I u * x)) =
    Ideal.Quotient.mk I u * x from Function.surjInv_eq Ideal.Quotient.mk_surjective _]
  rw [show Ideal.Quotient.mk I (quotLift x) = x from Function.surjInv_eq Ideal.Quotient.mk_surjective _]

lemma periodic_eq {I : Ideal (SInt 𝔪)} {f : SInt 𝔪 → ℂ}
    (hf : ∀ x w, w ∈ I → f (x + w) = f x) {x y : SInt 𝔪} (h : x - y ∈ I) : f x = f y := by
  have := hf y (x - y) h
  rwa [add_sub_cancel] at this

lemma mem_iff_of_sub_mem {I : Ideal (SInt 𝔪)} {x y : SInt 𝔪} (h : x - y ∈ I) :
    x ∈ I ↔ y ∈ I := by
  constructor
  · intro hx; have := sub_mem hx h; rwa [sub_sub_cancel] at this
  · intro hy; have := add_mem h hy; rwa [sub_add_cancel] at this

lemma exists_eq_mul_of_mem {s : SInt 𝔪} {x : SInt 𝔪} (hx : x ∈ Ideal.span {s}) :
    ∃ y : SInt 𝔪, x = y * s := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  exact ⟨a, ha.symm⟩

/-- Chinese remainders for a periodic function. -/
lemma finsum_crt {I J K : Ideal (SInt 𝔪)} [Finite (SInt 𝔪 ⧸ I)] [Finite (SInt 𝔪 ⧸ J)]
    {e₁ e₂ : SInt 𝔪} (he₁ : e₁ ∈ J) (he₂ : e₂ ∈ I) (h1 : e₁ + e₂ = 1) (hK : K = I * J)
    (f : SInt 𝔪 → ℂ) (hf : ∀ x w, w ∈ K → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ K, f (quotLift x) =
      ∑ᶠ x₁ : SInt 𝔪 ⧸ I, ∑ᶠ x₂ : SInt 𝔪 ⧸ J, f (quotLift x₁ * e₁ + quotLift x₂ * e₂) := by
  subst hK
  have cop : IsCoprime I J :=
    Ideal.isCoprime_iff_exists.mpr ⟨e₂, he₂, e₁, he₁, by rw [add_comm]; exact h1⟩
  let φ := Ideal.quotientMulEquivQuotientProd I J cop
  rw [← finsum_comp_equiv φ.symm.toEquiv]
  rw [finsum_curry _ (Set.toFinite _)]
  refine finsum_congr fun x₁ => finsum_congr fun x₂ => ?_
  apply periodic_eq hf
  rw [← Ideal.Quotient.eq]
  rw [show Ideal.Quotient.mk (I * J) (quotLift (φ.symm.toEquiv (x₁, x₂))) = φ.symm (x₁, x₂) from
    Function.surjInv_eq Ideal.Quotient.mk_surjective _]
  apply φ.injective
  rw [RingEquiv.apply_symm_apply]
  have hl : ∀ (L : Ideal (SInt 𝔪)) (y : SInt 𝔪 ⧸ L), Ideal.Quotient.mk L (quotLift y) = y :=
    fun L y => Function.surjInv_eq Ideal.Quotient.mk_surjective _
  ext
  · rw [Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk]
    rw [← hl I x₁, Ideal.Quotient.eq, hl I x₁]
    have : quotLift x₁ - (quotLift x₁ * e₁ + quotLift x₂ * e₂) = (quotLift x₁ - quotLift x₂) * e₂ := by
      linear_combination (-quotLift x₁) * h1
    rw [this]; exact Ideal.mul_mem_left _ _ he₂
  · rw [Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk]
    rw [← hl J x₂, Ideal.Quotient.eq, hl J x₂]
    have : quotLift x₂ - (quotLift x₁ * e₁ + quotLift x₂ * e₂) = (quotLift x₂ - quotLift x₁) * e₁ := by
      linear_combination (-quotLift x₂) * h1
    rw [this]; exact Ideal.mul_mem_left _ _ he₁

/-- Substitution by a unit of `R/I`. -/
lemma finsum_unit_subst {I : Ideal (SInt 𝔪)} {u u' : SInt 𝔪} (hu : u * u' - 1 ∈ I)
    (f : SInt 𝔪 → ℂ) (hf : ∀ x w, w ∈ I → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ I, f (quotLift x) = ∑ᶠ x : SInt 𝔪 ⧸ I, f (u * quotLift x) := by
  have h1 : Ideal.Quotient.mk I u * Ideal.Quotient.mk I u' = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
  let w : (SInt 𝔪 ⧸ I)ˣ := Units.mkOfMulEqOne _ _ h1
  rw [← finsum_comp_equiv (Units.mulLeft w)]
  refine finsum_congr fun x => ?_
  exact periodic_eq hf (quotLift_mul_sub I u x)

/-! ### Coercions -/

lemma coe_sub' (x y : SInt 𝔪) : ((x - y : SInt 𝔪) : F) = (x : F) - (y : F) := rfl
lemma coe_mul' (x y : SInt 𝔪) : ((x * y : SInt 𝔪) : F) = (x : F) * (y : F) := rfl
lemma coe_add' (x y : SInt 𝔪) : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
lemma coe_neg' (x : SInt 𝔪) : ((-x : SInt 𝔪) : F) = -(x : F) := rfl
lemma coe_one' : ((1 : SInt 𝔪) : F) = 1 := rfl

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

lemma U_add_left (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) {B : SInt 𝔪} (hAf : Af = A * B) (d v w : SInt 𝔪)
    (hw : w ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    U ι 𝔪 𝔰 𝔄 s A Af c h (d + w) v = U ι 𝔪 𝔰 𝔄 s A Af c h d v := by
  have hw' := hw
  rw [← hs] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  have hcond : (h - Af * (d + w' * s) ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    apply mem_iff_of_sub_mem
    rw [show h - Af * (d + w' * s) - (h - Af * d) = -(Af * (w' * s)) by ring]
    exact neg_mem (Ideal.mul_mem_left _ _ hw)
  unfold U
  by_cases hc : h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos (hcond.mpr hc), if_pos hc]
    rw [C3B.residueSymbol_congr ι 𝔰 (d + w' * s) d (by rw [add_sub_cancel_left]; exact hw)]
    congr 2
    have harg : ((h - Af * (d + w' * s) : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F)) =
        ((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F)) +
          ((-(B * w' * v * c) : SInt 𝔪) : F) := by
      subst hAf
      simp only [coe_sub', coe_mul', coe_add', coe_neg']
      field_simp
      ring
    rw [harg]
    exact C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)
  · rw [if_neg (fun h1 => hc (hcond.mp h1)), if_neg hc]

lemma U_add_right (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA : Ideal.span {A} = 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) (d v w : SInt 𝔪)
    (hw : w ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    U ι 𝔪 𝔰 𝔄 s A Af c h d (v + w) = U ι 𝔪 𝔰 𝔄 s A Af c h d v := by
  have hw' := hw
  rw [← hA] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  unfold U
  by_cases hc : h - Af * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos hc, if_pos hc]
    rw [C3B.residueSymbol_congr ι 𝔄 (v + w' * A) v (by rw [add_sub_cancel_left]; exact hw)]
    have hc' := hc
    rw [← hs] at hc'
    obtain ⟨y, hy⟩ := exists_eq_mul_of_mem hc'
    congr 2
    have harg : ((h - Af * d : SInt 𝔪) : F) * ((v + w' * A : SInt 𝔪) : F) * (c : F) /
          ((s : F) * (A : F)) =
        ((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) / ((s : F) * (A : F)) +
          ((y * w' * c : SInt 𝔪) : F) := by
      rw [hy]
      simp only [coe_mul', coe_add']
      field_simp
    rw [harg]
    exact C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)
  · rw [if_neg hc, if_neg hc]

end U

/-- `poissonFactor` as a `PS`. -/
lemma poissonFactor_eq_PS (g : AllowedGen ι 𝔪) (𝔰 𝔄 : Ideal (𝓞 F)) (h : SInt 𝔪) :
    poissonFactor g 𝔰 𝔄 h = PS ι 𝔪 𝔰 𝔄 (g.gen 𝔰) (g.gen 𝔄) (g.gen 𝔄) 1 h := by
  unfold poissonFactor PS
  refine finsum_congr fun d => ?_
  by_cases hc : h - g.gen 𝔄 * quotLift d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos hc]
    unfold gaussSumAt
    rw [mul_finsum]
    refine finsum_congr fun v => ?_
    unfold U
    rw [if_pos hc]
    congr 3
    rw [coe_one']
    ring
  · rw [if_neg hc]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro v
    unfold U
    rw [if_neg hc]

/-! ### Field identities -/

lemma alg_crt (h Af d₁ d₂ v₁ v₂ c α β s₁ s₂ A₁ A₂ : F) (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0) (hαβ : α * (s₁ * A₁) + β * (s₂ * A₂) = 1) :
    (h - Af * (d₁ * (β * (s₂ * A₂)) + d₂ * (α * (s₁ * A₁)))) *
        (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))) * c / ((s₁ * s₂) * (A₁ * A₂)) =
      ((h - Af * d₁) * v₁ * (c * β) / (s₁ * A₁) +
          c * β * α * ((h - Af * d₁) * (v₂ - v₁) - Af * (d₂ - d₁) *
            (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))))) +
        ((h - Af * d₂) * v₂ * (c * α) / (s₂ * A₂) +
          c * α * β * ((h - Af * d₂) * (v₁ - v₂) - Af * (d₁ - d₂) *
            (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))))) := by
  have hp : s₁ * A₁ ≠ 0 := mul_ne_zero hs₁ hA₁
  have hα : α = (1 - β * (s₂ * A₂)) / (s₁ * A₁) := by
    field_simp; linear_combination hαβ
  subst hα
  field_simp
  ring

lemma alg_twist (h A B B' l l' c C d v s y z w : F) (hs : s ≠ 0) (hA : A ≠ 0)
    (hh : h - A * d = y * s) (hB : B * B' - 1 = z * s) (hc : l * l' * c * C - 1 = w * (s * A)) :
    (l * h - A * B * (l * B' * d)) * (l' * C * v) * c / (s * A) =
      (h - A * d) * v * 1 / (s * A) + (-(d * z * v) + w * s * (y - A * d * z) * v) := by
  have e1 : (l * h - A * B * (l * B' * d)) * (l' * C * v) * c / (s * A) =
      (l * l' * c * C) * (h - A * (B * B') * d) * v / (s * A) := by ring
  have hBB : B * B' = 1 + z * s := by linear_combination hB
  have hll : l * l' * c * C = 1 + w * (s * A) := by linear_combination hc
  have hh' : h = A * d + y * s := by linear_combination hh
  rw [e1, hBB, hll, hh']
  field_simp
  ring

lemma alg_gs_crt (x₁ x₂ c' α β c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hαβ : α * c₁ + β * c₂ = 1) :
    (x₁ * (β * c₂) + x₂ * (α * c₁)) * c' / (c₁ * c₂) =
      (x₁ * (c' * β) / c₁ + c' * β * α * (x₂ - x₁)) +
        (x₂ * (c' * α) / c₂ + c' * α * β * (x₁ - x₂)) := by
  have hα : α = (1 - β * c₂) / c₁ := by
    field_simp; linear_combination hαβ
  subst hα
  field_simp
  ring

lemma alg_gs_twist (x C c'' c w : F) (hc : c ≠ 0) (h : C * c'' - 1 = w * c) :
    (C * x) * c'' / c = x * 1 / c + x * w := by
  have h' : C * c'' = 1 + w * c := by linear_combination h
  have e : (C * x) * c'' / c = x * (C * c'') / c := by ring
  rw [e, h']
  field_simp

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

lemma castF {x y : SInt 𝔪} (h : x = y) : (x : F) = (y : F) := congrArg _ h

lemma U_crt (hadd : HypAdd 𝔪) (h𝔰₁ : 𝔰₁ ≠ ⊥) (h𝔰₂ : 𝔰₂ ≠ ⊥) (h𝔄₁ : 𝔄₁ ≠ ⊥) (h𝔄₂ : 𝔄₂ ≠ ⊥)
    (hsA₁e : 𝔰₁ * 𝔄₁ ⊔ 𝔪 = ⊤) (hsA₂e : 𝔰₂ * 𝔄₂ ⊔ 𝔪 = ⊤)
    (hs₁ : Ideal.span {s₁} = 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₂ : Ideal.span {s₂} = 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₁ : Ideal.span {A₁} = 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₂ : Ideal.span {A₂} = 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₁0 : (s₁ : F) ≠ 0) (hs₂0 : (s₂ : F) ≠ 0) (hA₁0 : (A₁ : F) ≠ 0) (hA₂0 : (A₂ : F) ≠ 0)
    (hαβ : α * (s₁ * A₁) + β * (s₂ * A₂) = 1) (d₁ d₂ v₁ v₂ : SInt 𝔪) :
    U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h
        (d₁ * (β * (s₂ * A₂)) + d₂ * (α * (s₁ * A₁)))
        (v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁))) =
      U ι 𝔪 𝔰₁ 𝔄₁ s₁ A₁ Af (c * β) h d₁ v₁ * U ι 𝔪 𝔰₂ 𝔄₂ s₂ A₂ Af (c * α) h d₂ v₂ := by
  have he₁s : β * (s₂ * A₂) ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * A₂, by ring⟩
  have he₁A : β * (s₂ * A₂) ∈ 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * s₂, by ring⟩
  have he₂s : α * (s₁ * A₁) ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * A₁, by ring⟩
  have he₂A : α * (s₁ * A₁) ∈ 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * s₁, by ring⟩
  have hsub : ∀ x₁ x₂ : SInt 𝔪,
      (x₁ * (β * (s₂ * A₂)) + x₂ * (α * (s₁ * A₁))) - x₁ = (x₂ - x₁) * (α * (s₁ * A₁)) ∧
      (x₁ * (β * (s₂ * A₂)) + x₂ * (α * (s₁ * A₁))) - x₂ = (x₁ - x₂) * (β * (s₂ * A₂)) := by
    intro x₁ x₂
    constructor
    · linear_combination x₁ * hαβ
    · linear_combination x₂ * hαβ
  have hd1 := (hsub d₁ d₂).1
  have hd2 := (hsub d₁ d₂).2
  have hv1 := (hsub v₁ v₂).1
  have hv2 := (hsub v₁ v₂).2
  have cop : IsCoprime (𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))) (𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))) :=
    Ideal.isCoprime_iff_exists.mpr ⟨_, he₂s, _, he₁s, by rw [add_comm, ← hαβ]; ring⟩
  have hmap : (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) =
      𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)) ⊓ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, Ideal.mul_eq_inf_of_isCoprime cop]
  set d := d₁ * (β * (s₂ * A₂)) + d₂ * (α * (s₁ * A₁)) with hd
  set v := v₁ * (β * (s₂ * A₂)) + v₂ * (α * (s₁ * A₁)) with hv
  have hc1 : (h - Af * d ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - Af * d₁ ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    apply mem_iff_of_sub_mem
    rw [show h - Af * d - (h - Af * d₁) = -(Af * (d - d₁)) by ring, hd1]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ he₂s))
  have hc2 : (h - Af * d ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - Af * d₂ ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    apply mem_iff_of_sub_mem
    rw [show h - Af * d - (h - Af * d₂) = -(Af * (d - d₂)) by ring, hd2]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ he₁s))
  unfold U
  by_cases H1 : h - Af * d₁ ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪))
  · by_cases H2 : h - Af * d₂ ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪))
    · have H : h - Af * d ∈ (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hmap]; exact ⟨hc1.mpr H1, hc2.mpr H2⟩
      rw [if_pos H, if_pos H1, if_pos H2]
      rw [residueSymbol_mul_ideal _ _ h𝔰₁ h𝔰₂, residueSymbol_mul_ideal _ _ h𝔄₁ h𝔄₂,
        C3B.residueSymbol_congr ι 𝔰₁ d d₁ (by rw [hd1]; exact Ideal.mul_mem_left _ _ he₂s),
        C3B.residueSymbol_congr ι 𝔰₂ d d₂ (by rw [hd2]; exact Ideal.mul_mem_left _ _ he₁s),
        C3B.residueSymbol_congr ι 𝔄₁ v v₁ (by rw [hv1]; exact Ideal.mul_mem_left _ _ he₂A),
        C3B.residueSymbol_congr ι 𝔄₂ v v₂ (by rw [hv2]; exact Ideal.mul_mem_left _ _ he₁A)]
      have hαβF := castF (F := F) hαβ
      simp only [coe_add', coe_mul', coe_one'] at hαβF
      have harg : ((h - Af * d : SInt 𝔪) : F) * (v : F) * (c : F) /
            (((s₁ * s₂ : SInt 𝔪) : F) * ((A₁ * A₂ : SInt 𝔪) : F)) =
          (((h - Af * d₁ : SInt 𝔪) : F) * (v₁ : F) * ((c * β : SInt 𝔪) : F) /
              ((s₁ : F) * (A₁ : F)) +
            ((c * β * α * ((h - Af * d₁) * (v₂ - v₁) - Af * (d₂ - d₁) * v) : SInt 𝔪) : F)) +
          (((h - Af * d₂ : SInt 𝔪) : F) * (v₂ : F) * ((c * α : SInt 𝔪) : F) /
              ((s₂ : F) * (A₂ : F)) +
            ((c * α * β * ((h - Af * d₂) * (v₁ - v₂) - Af * (d₁ - d₂) * v) : SInt 𝔪) : F)) := by
        rw [hd, hv]
        simp only [coe_sub', coe_mul', coe_add']
        exact alg_crt _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁0 hs₂0 hA₁0 hA₂0 hαβF
      have hq₁ : Ideal.span {s₁ * A₁} = (𝔰₁ * 𝔄₁).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [Ideal.map_mul, ← hs₁, ← hA₁, Ideal.span_singleton_mul_span_singleton]
      have hq₂ : Ideal.span {s₂ * A₂} = (𝔰₂ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [Ideal.map_mul, ← hs₂, ← hA₂, Ideal.span_singleton_mul_span_singleton]
      rw [harg, hadd, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _),
        C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
      · ring
      · exact extWit_div_add hsA₁e hq₁ (by rw [coe_mul']; exact mul_ne_zero hs₁0 hA₁0)
          ((h - Af * d₁) * v₁ * (c * β)) _
      · exact extWit_div_add hsA₂e hq₂ (by rw [coe_mul']; exact mul_ne_zero hs₂0 hA₂0)
          ((h - Af * d₂) * v₂ * (c * α)) _
    · have H : h - Af * d ∉ (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hmap]; exact fun hh => H2 (hc2.mp hh.2)
      rw [if_neg H, if_neg H2, mul_zero]
  · have H : h - Af * d ∉ (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [hmap]; exact fun hh => H1 (hc1.mp hh.1)
    rw [if_neg H, if_neg H1, zero_mul]

lemma PS_crt (hadd : HypAdd 𝔪) (h𝔰₁ : IsExterior 𝔪 𝔰₁) (h𝔰₂ : IsExterior 𝔪 𝔰₂)
    (h𝔄₁ : IsExterior 𝔪 𝔄₁) (h𝔄₂ : IsExterior 𝔪 𝔄₂)
    (hs₁ : Ideal.span {s₁} = 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₂ : Ideal.span {s₂} = 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₁ : Ideal.span {A₁} = 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA₂ : Ideal.span {A₂} = 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs₁0 : (s₁ : F) ≠ 0) (hs₂0 : (s₂ : F) ≠ 0) (hA₁0 : (A₁ : F) ≠ 0) (hA₂0 : (A₂ : F) ≠ 0)
    (hαβ : α * (s₁ * A₁) + β * (s₂ * A₂) = 1) {B : SInt 𝔪} (hAf : Af = A₁ * A₂ * B) :
    PS ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h =
      PS ι 𝔪 𝔰₁ 𝔄₁ s₁ A₁ Af (c * β) h * PS ι 𝔪 𝔰₂ 𝔄₂ s₂ A₂ Af (c * α) h := by
  have := finite_quot h𝔰₁; have := finite_quot h𝔰₂
  have := finite_quot h𝔄₁; have := finite_quot h𝔄₂
  have hs : Ideal.span {s₁ * s₂} = (𝔰₁ * 𝔰₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hs₁, ← hs₂, Ideal.span_singleton_mul_span_singleton]
  have hA : Ideal.span {A₁ * A₂} = (𝔄₁ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hA₁, ← hA₂, Ideal.span_singleton_mul_span_singleton]
  have hs0 : ((s₁ * s₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hs₁0 hs₂0
  have hA0 : ((A₁ * A₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hA₁0 hA₂0
  have he₁s : β * (s₂ * A₂) ∈ 𝔰₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * A₂, by ring⟩
  have he₁A : β * (s₂ * A₂) ∈ 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₂]; exact Ideal.mem_span_singleton'.mpr ⟨β * s₂, by ring⟩
  have he₂s : α * (s₁ * A₁) ∈ 𝔰₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * A₁, by ring⟩
  have he₂A : α * (s₁ * A₁) ∈ 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA₁]; exact Ideal.mem_span_singleton'.mpr ⟨α * s₁, by ring⟩
  have h1 : β * (s₂ * A₂) + α * (s₁ * A₁) = 1 := by rw [add_comm]; exact hαβ
  unfold PS
  refine (finsum_crt he₁s he₂s h1 (Ideal.map_mul _ _ _)
    (fun d => ∑ᶠ v : SInt 𝔪 ⧸ (𝔄₁ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)),
      U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d (quotLift v))
    (fun x w hw => finsum_congr fun v => U_add_left hs hs0 hA0 hAf x _ w hw)).trans ?_
  have step2 : ∀ d : SInt 𝔪,
      ∑ᶠ v : SInt 𝔪 ⧸ (𝔄₁ * 𝔄₂).map (algebraMap (𝓞 F) (SInt 𝔪)),
        U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d (quotLift v) =
      ∑ᶠ v₁ : SInt 𝔪 ⧸ 𝔄₁.map (algebraMap (𝓞 F) (SInt 𝔪)),
        ∑ᶠ v₂ : SInt 𝔪 ⧸ 𝔄₂.map (algebraMap (𝓞 F) (SInt 𝔪)),
          U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d
            (quotLift v₁ * (β * (s₂ * A₂)) + quotLift v₂ * (α * (s₁ * A₁))) := fun d =>
    finsum_crt he₁A he₂A h1 (Ideal.map_mul _ _ _)
      (fun v => U ι 𝔪 (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (s₁ * s₂) (A₁ * A₂) Af c h d v)
      (fun x w hw => U_add_right hs hA hs0 hA0 d x w hw)
  simp only [step2, U_crt hadd h𝔰₁.1 h𝔰₂.1 h𝔄₁.1 h𝔄₂.1 (C3B.isExterior_mul h𝔰₁ h𝔄₁).2
    (C3B.isExterior_mul h𝔰₂ h𝔄₂).2 hs₁ hs₂ hA₁ hA₂ hs₁0 hs₂0 hA₁0 hA₂0 hαβ]
  rw [finsum_mul]
  refine finsum_congr fun d₁ => ?_
  rw [mul_finsum]
  refine finsum_congr fun d₂ => ?_
  rw [finsum_mul]
  refine finsum_congr fun v₁ => ?_
  rw [mul_finsum]

lemma U_twist_pt (hχ : HypChi ι 𝔪) {𝔰 𝔄 : Ideal (𝓞 F)} {s A c h : SInt 𝔪}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄)
    (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) {B B' l l' l'' C : SInt 𝔪}
    (hB : B * B' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hl : l * l'' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc : l * l' * c * C - 1 ∈ Ideal.span {s * A}) (d v : SInt 𝔪) :
    U ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) (l * B' * d) (l' * C * v) =
      residueSymbol ι 𝔪 𝔰 l * residueSymbol ι 𝔪 𝔰 B' * residueSymbol ι 𝔪 𝔄 l' *
        residueSymbol ι 𝔪 𝔄 C * U ι 𝔪 𝔰 𝔄 s A A 1 h d v := by
  have hcond : (l * h - A * B * (l * B' * d) ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) ↔
      (h - A * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    have e : l * h - A * B * (l * B' * d) = l * (h - A * d) - l * A * d * (B * B' - 1) := by ring
    rw [e]
    constructor
    · intro H
      have H2 : l * (h - A * d) ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        have := add_mem H (Ideal.mul_mem_left _ (l * A * d) hB)
        rwa [sub_add_cancel] at this
      have e2 : h - A * d = l'' * (l * (h - A * d)) - (l * l'' - 1) * (h - A * d) := by ring
      rw [e2]
      exact sub_mem (Ideal.mul_mem_left _ _ H2) (Ideal.mul_mem_right _ _ hl)
    · intro H
      exact sub_mem (Ideal.mul_mem_left _ _ H) (Ideal.mul_mem_left _ _ hB)
  unfold U
  by_cases H : h - A * d ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos (hcond.mpr H), if_pos H]
    rw [residueSymbol_mul hχ h𝔰, residueSymbol_mul hχ h𝔰, residueSymbol_mul hχ h𝔄,
      residueSymbol_mul hχ h𝔄]
    have H' := H
    rw [← hs] at H'
    obtain ⟨y, hy⟩ := exists_eq_mul_of_mem H'
    have hB' := hB
    rw [← hs] at hB'
    obtain ⟨z, hz⟩ := exists_eq_mul_of_mem hB'
    obtain ⟨w, hw⟩ := exists_eq_mul_of_mem hc
    have hyF := castF (F := F) hy
    have hzF := castF (F := F) hz
    have hwF := castF (F := F) hw
    simp only [coe_sub', coe_mul', coe_one'] at hyF hzF hwF
    have harg : ((l * h - A * B * (l * B' * d) : SInt 𝔪) : F) * ((l' * C * v : SInt 𝔪) : F) *
          (c : F) / ((s : F) * (A : F)) =
        ((h - A * d : SInt 𝔪) : F) * (v : F) * ((1 : SInt 𝔪) : F) / ((s : F) * (A : F)) +
          ((-(d * z * v) + w * s * (y - A * d * z) * v : SInt 𝔪) : F) := by
      simp only [coe_sub', coe_mul', coe_add', coe_neg', coe_one']
      exact alg_twist _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs0 hA0 hyF hzF hwF
    rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
    ring
  · rw [if_neg (fun hh => H (hcond.mp hh)), if_neg H, mul_zero]

lemma PS_twist (hχ : HypChi ι 𝔪) {𝔰 𝔄 : Ideal (𝓞 F)} {s A c h : SInt 𝔪}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄)
    (hs : Ideal.span {s} = 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hA : Ideal.span {A} = 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hs0 : (s : F) ≠ 0) (hA0 : (A : F) ≠ 0) {B B' l l' l'' C : SInt 𝔪}
    (hB : B * B' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hl : l * l'' - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc : l * l' * c * C - 1 ∈ Ideal.span {s * A}) :
    PS ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) =
      residueSymbol ι 𝔪 𝔰 l * residueSymbol ι 𝔪 𝔰 B' * residueSymbol ι 𝔪 𝔄 l' *
        residueSymbol ι 𝔪 𝔄 C * PS ι 𝔪 𝔰 𝔄 s A A 1 h := by
  have hu1 : (l * B') * (l'' * B) - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have e : (l * B') * (l'' * B) - 1 = (l * l'' - 1) * (B * B') + (B * B' - 1) := by ring
    rw [e]; exact add_mem (Ideal.mul_mem_right _ _ hl) hB
  have hu2 : (l' * C) * (l * c) - 1 ∈ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have e : (l' * C) * (l * c) - 1 = l * l' * c * C - 1 := by ring
    rw [e, ← hA]
    exact (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left A s)) hc
  unfold PS
  refine (finsum_unit_subst hu1
    (fun d => ∑ᶠ v : SInt 𝔪 ⧸ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)),
      U ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) d (quotLift v))
    (fun x w hw => finsum_congr fun v => U_add_left hs hs0 hA0 rfl x _ w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun d => ?_
  refine (finsum_unit_subst hu2
    (fun v => U ι 𝔪 𝔰 𝔄 s A (A * B) c (l * h) (l * B' * quotLift d) v)
    (fun x w hw => U_add_right hs hA hs0 hA0 _ x w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun v => ?_
  exact U_twist_pt hχ h𝔰 h𝔄 hs hs0 hA0 hB hl hc _ _

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

lemma V_add (hc : Ideal.span {c} = 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) (hc0 : (c : F) ≠ 0)
    (x w : SInt 𝔪) (hw : w ∈ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    V ι 𝔪 𝔠 c c' j (x + w) = V ι 𝔪 𝔠 c c' j x := by
  have hw' := hw
  rw [← hc] at hw'
  obtain ⟨w', rfl⟩ := exists_eq_mul_of_mem hw'
  unfold V
  rw [C3B.residueSymbol_congr ι 𝔠 (x + w' * c) x (by rw [add_sub_cancel_left]; exact hw)]
  have harg : ((x + w' * c : SInt 𝔪) : F) * (c' : F) / (c : F) =
      (x : F) * (c' : F) / (c : F) + ((w' * c' : SInt 𝔪) : F) := by
    simp only [coe_mul', coe_add']
    field_simp
  rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]

lemma GS_crt (hadd : HypAdd 𝔪) {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} {c₁ c₂ α β : SInt 𝔪}
    (h𝔠₁ : IsExterior 𝔪 𝔠₁) (h𝔠₂ : IsExterior 𝔪 𝔠₂)
    (hc₁ : Ideal.span {c₁} = 𝔠₁.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc₂ : Ideal.span {c₂} = 𝔠₂.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hc₁0 : (c₁ : F) ≠ 0) (hc₂0 : (c₂ : F) ≠ 0) (hαβ : α * c₁ + β * c₂ = 1) :
    GS ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j = GS ι 𝔪 𝔠₁ c₁ (c' * β) j * GS ι 𝔪 𝔠₂ c₂ (c' * α) j := by
  have := finite_quot h𝔠₁; have := finite_quot h𝔠₂
  have hc : Ideal.span {c₁ * c₂} = (𝔠₁ * 𝔠₂).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [Ideal.map_mul, ← hc₁, ← hc₂, Ideal.span_singleton_mul_span_singleton]
  have hc0 : ((c₁ * c₂ : SInt 𝔪) : F) ≠ 0 := by rw [coe_mul']; exact mul_ne_zero hc₁0 hc₂0
  have he₁ : β * c₂ ∈ 𝔠₂.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hc₂]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have he₂ : α * c₁ ∈ 𝔠₁.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hc₁]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h1 : β * c₂ + α * c₁ = 1 := by rw [add_comm]; exact hαβ
  unfold GS
  refine (finsum_crt he₁ he₂ h1 (Ideal.map_mul _ _ _) (V ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j)
    (fun x w hw => V_add hc hc0 x w hw)).trans ?_
  have hpt : ∀ x₁ x₂ : SInt 𝔪, V ι 𝔪 (𝔠₁ * 𝔠₂) (c₁ * c₂) c' j (x₁ * (β * c₂) + x₂ * (α * c₁)) =
      V ι 𝔪 𝔠₁ c₁ (c' * β) j x₁ * V ι 𝔪 𝔠₂ c₂ (c' * α) j x₂ := by
    intro x₁ x₂
    have hx1 : x₁ * (β * c₂) + x₂ * (α * c₁) - x₁ = (x₂ - x₁) * (α * c₁) := by
      linear_combination x₁ * hαβ
    have hx2 : x₁ * (β * c₂) + x₂ * (α * c₁) - x₂ = (x₁ - x₂) * (β * c₂) := by
      linear_combination x₂ * hαβ
    unfold V
    rw [residueSymbol_mul_ideal _ _ h𝔠₁.1 h𝔠₂.1,
      C3B.residueSymbol_congr ι 𝔠₁ _ x₁ (by rw [hx1]; exact Ideal.mul_mem_left _ _ he₂),
      C3B.residueSymbol_congr ι 𝔠₂ _ x₂ (by rw [hx2]; exact Ideal.mul_mem_left _ _ he₁)]
    have hαβF := castF (F := F) hαβ
    simp only [coe_add', coe_mul', coe_one'] at hαβF
    have harg : ((x₁ * (β * c₂) + x₂ * (α * c₁) : SInt 𝔪) : F) * (c' : F) /
          ((c₁ * c₂ : SInt 𝔪) : F) =
        ((x₁ : F) * ((c' * β : SInt 𝔪) : F) / (c₁ : F) + ((c' * β * α * (x₂ - x₁) : SInt 𝔪) : F)) +
          ((x₂ : F) * ((c' * α : SInt 𝔪) : F) / (c₂ : F) +
            ((c' * α * β * (x₁ - x₂) : SInt 𝔪) : F)) := by
      simp only [coe_sub', coe_mul', coe_add']
      exact alg_gs_crt _ _ _ _ _ _ _ hc₁0 hc₂0 hαβF
    rw [harg, hadd, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _),
      C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
    · ring
    · exact extWit_div_add h𝔠₁.2 hc₁ hc₁0 (x₁ * (c' * β)) _
    · exact extWit_div_add h𝔠₂.2 hc₂ hc₂0 (x₂ * (c' * α)) _
  simp only [hpt]
  rw [finsum_mul]
  refine finsum_congr fun x₁ => ?_
  rw [mul_finsum]

lemma GS_twist (hχ : HypChi ι 𝔪) (h𝔠 : IsExterior 𝔪 𝔠)
    (hc : Ideal.span {c} = 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) (hc0 : (c : F) ≠ 0)
    {c'' C : SInt 𝔪} (hC : C * c'' - 1 ∈ 𝔠.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    GS ι 𝔪 𝔠 c c'' j = residueSymbol ι 𝔪 𝔠 C ^ j * GS ι 𝔪 𝔠 c 1 j := by
  unfold GS
  refine (finsum_unit_subst hC (V ι 𝔪 𝔠 c c'' j) (fun x w hw => V_add hc hc0 x w hw)).trans ?_
  rw [mul_finsum]
  refine finsum_congr fun x => ?_
  have hC' := hC
  rw [← hc] at hC'
  obtain ⟨w, hw⟩ := exists_eq_mul_of_mem hC'
  have hwF := castF (F := F) hw
  simp only [coe_sub', coe_mul', coe_one'] at hwF
  unfold V
  rw [residueSymbol_mul hχ h𝔠, mul_pow]
  have harg : ((C * quotLift x : SInt 𝔪) : F) * (c'' : F) / (c : F) =
      ((quotLift x : SInt 𝔪) : F) * ((1 : SInt 𝔪) : F) / (c : F) +
        ((quotLift x * w : SInt 𝔪) : F) := by
    simp only [coe_mul', coe_one']
    exact alg_gs_twist _ _ _ _ _ hc0 hwF
  rw [harg, C3B.sAddChar_add_mem _ _ (SetLike.coe_mem _)]
  ring

end gs

lemma gaussPhase_eq_GS (g : AllowedGen ι 𝔪) (j : ℕ) (𝔠 : Ideal (𝓞 F)) :
    gaussPhase g j 𝔠 =
      ((Real.sqrt (Ideal.absNorm 𝔠) : ℝ) : ℂ)⁻¹ * GS ι 𝔪 𝔠 (g.gen 𝔠) 1 j := by
  unfold gaussPhase GS V
  congr 1
  refine finsum_congr fun x => ?_
  rw [coe_one', mul_one]

end C3M

end ArtinPrimitiveRoots
end

section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

lemma cop_mono {X I J : Ideal (SInt 𝔪)} (h : IsCoprime X I) (hIJ : I ≤ J) : IsCoprime X J := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact eq_top_iff.mpr (h ▸ sup_le_sup_left hIJ X)

lemma cop_mul {x y : SInt 𝔪} {I : Ideal (SInt 𝔪)} (hx : IsCoprime (Ideal.span {x}) I)
    (hy : IsCoprime (Ideal.span {y}) I) : IsCoprime (Ideal.span {x * y}) I := by
  rw [← Ideal.span_singleton_mul_span_singleton]; exact hx.mul_left hy

lemma cop_pow {x : SInt 𝔪} {I : Ideal (SInt 𝔪)} (hx : IsCoprime (Ideal.span {x}) I) (n : ℕ) :
    IsCoprime (Ideal.span {x ^ n}) I := by
  rw [← Ideal.span_singleton_pow]; exact hx.pow_left

lemma cop_of_inv {x x' : SInt 𝔪} {I : Ideal (SInt 𝔪)} (h : x * x' - 1 ∈ I) :
    IsCoprime (Ideal.span {x'}) I := by
  refine Ideal.isCoprime_iff_exists.mpr ⟨x * x', Ideal.mul_mem_left _ _
    (Ideal.mem_span_singleton_self _), -(x * x' - 1), neg_mem h, by ring⟩

lemma cop_gen (g : AllowedGen ι 𝔪) {𝔟 𝔞 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (h : IsCoprime 𝔟 𝔞) : IsCoprime (Ideal.span {g.gen 𝔟}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [g.span_gen 𝔟 h𝔟]; exact isCoprime_map h

lemma span_gen_mul (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    Ideal.span {g.gen I * g.gen J} = (I * J).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← Ideal.span_singleton_mul_span_singleton, g.span_gen I hI, g.span_gen J hJ, Ideal.map_mul]

lemma pow_sub_one_mem {x : SInt 𝔪} {I : Ideal (SInt 𝔪)} (h : x - 1 ∈ I) (n : ℕ) :
    x ^ n - 1 ∈ I := by
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow x 1 n
  rw [one_pow] at hk
  rw [hk]; exact Ideal.mul_mem_right _ _ h

lemma exists_ab {x y : SInt 𝔪} (h : IsCoprime (Ideal.span {x}) (Ideal.span {y})) :
    ∃ α β : SInt 𝔪, α * x + β * y = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  exact ⟨α, β, hij⟩

lemma unit_pow_mul_inv (ε : (SInt 𝔪)ˣ) :
    (ε : SInt 𝔪) ^ 6 * ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

/-! ### Change of generators -/

lemma unit_coe_ne_zero (u : (SInt 𝔪)ˣ) : ((u : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : ((u : SInt 𝔪) : F) * (((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← coe_mul', Units.mul_inv]; rfl
  rw [h0, zero_mul] at this; exact zero_ne_one this

lemma GS_gen_change {𝔠 : Ideal (𝓞 F)} {c₀ c c' : SInt 𝔪} {j : ℕ} (hc₀ : (c₀ : F) ≠ 0)
    (hc' : (c' : F) ≠ 0)
    (hc : (c : F) = (c' : F) * (c₀ : F)) : GS ι 𝔪 𝔠 c₀ 1 j = GS ι 𝔪 𝔠 c c' j := by
  unfold GS V
  refine finsum_congr fun x => ?_
  congr 2
  rw [hc, coe_one']
  field_simp

lemma PS_gen_change {𝔰 𝔄 : Ideal (𝓞 F)} {s₀ A₀ s A Af c h : SInt 𝔪} (hs₀ : (s₀ : F) ≠ 0)
    (hA₀ : (A₀ : F) ≠ 0) (hc0 : (c : F) ≠ 0)
    (hrel : (s : F) * (A : F) = (c : F) * ((s₀ : F) * (A₀ : F))) :
    PS ι 𝔪 𝔰 𝔄 s₀ A₀ Af 1 h = PS ι 𝔪 𝔰 𝔄 s A Af c h := by
  unfold PS U
  refine finsum_congr fun d => finsum_congr fun v => ?_
  split_ifs
  · congr 3
    rw [hrel, coe_one']
    field_simp
  · rfl

/-! ### Generators and residue symbols -/

lemma residueSymbol_gen_mul (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I J : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I * J)) =
      residueSymbol ι 𝔪 𝔞 (g.gen I) * residueSymbol ι 𝔪 𝔞 (g.gen J) := by
  obtain ⟨ε, hε⟩ := gen_mul' g hI hJ
  rw [hε, mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_mul hχ h𝔞]

lemma residueSymbol_gen_top (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 (g.gen ⊤) = 1 := by
  obtain ⟨ε, hε⟩ := gen_top g
  rw [hε, ← mul_one ((ε : SInt 𝔪) ^ 6), residueSymbol_unit_pow_six hχ h𝔞,
    residueSymbol_one hχ h𝔞]

lemma residueSymbol_gen_pow (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔞 I : Ideal (𝓞 F)}
    (h𝔞 : IsExterior 𝔪 𝔞) (hI : IsExterior 𝔪 I) (n : ℕ) :
    residueSymbol ι 𝔪 𝔞 (g.gen (I ^ n)) = residueSymbol ι 𝔪 𝔞 (g.gen I) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, residueSymbol_gen_top hχ g h𝔞]
  | succ n ih =>
    rw [pow_succ, residueSymbol_gen_mul hχ g h𝔞 (C3B.isExterior_pow hI n) hI, ih, pow_succ]

/-- Extended reciprocity: `χ_𝔟(gen P) = χ_P(gen 𝔟)` for an exterior `𝔟` prime to `P`. -/
lemma residueSymbol_gen_prime (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (𝔟 : Ideal (𝓞 F)) :
    IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 (g.gen P) = residueSymbol ι 𝔪 P (g.gen 𝔟) := by
  induction 𝔟 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h.1
  | h₂ u hu =>
    intro hue _
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    rw [C3B.residueSymbol_top, residueSymbol_gen_top hχ g hPe]
  | h₃ 𝔞 Q _ hQ ih =>
    intro hQa hle
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := isExterior_of_mul_left hQa
    have hae : IsExterior 𝔪 𝔞 := isExterior_of_mul_right hQa
    have hQP : ¬ Q ≤ P := fun h => hle (le_trans Ideal.mul_le_left h)
    have haP : ¬ 𝔞 ≤ P := fun h => hle (le_trans Ideal.mul_le_right h)
    have hne : P ≠ Q := fun h => hQP (h ▸ le_rfl)
    rw [residueSymbol_mul_ideal _ _ hQe.1 hae.1, ih hae haP,
      residueSymbol_gen_mul hχ g hPe hQe hae, residueSymbol_prime hQp hQe.1,
      residueSymbol_prime hP hPe.1, residueSymbol_prime hP hPe.1,
      ← g.reciprocity P Q hP hQp hPe hQe hne]

/-! ### `ϑ` and norms -/

lemma thetaChar_mul (g : AllowedGen ι 𝔪) (χ : HeckeChar F 𝔪) {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : χ.thetaChar g (I * J) = χ.thetaChar g I * χ.thetaChar g J := by
  simp only [HeckeChar.thetaChar, gaussLambda, gaussG, normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add, map_mul, χ.map_mul']
  ring

lemma sqrt_norm_mul_inv (I J : Ideal (𝓞 F)) :
    ((Real.sqrt (Ideal.absNorm (I * J)) : ℝ) : ℂ)⁻¹ =
      ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Ideal.absNorm J) : ℝ) : ℂ)⁻¹ := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, mul_inv]

/-! ### (3.10) -/

theorem gaussPhase_mul (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} (h₁ : IsExterior 𝔪 𝔠₁) (h₂ : IsExterior 𝔪 𝔠₂)
    (hcop : IsCoprime 𝔠₁ 𝔠₂) (j : ℕ) :
    gaussPhase g j (𝔠₁ * 𝔠₂) =
      residueSymbol ι 𝔪 𝔠₁ (g.gen 𝔠₂) ^ j * residueSymbol ι 𝔪 𝔠₂ (g.gen 𝔠₁) ^ j *
        (gaussPhase g j 𝔠₁ * gaussPhase g j 𝔠₂) := by
  obtain ⟨ε, hε⟩ := gen_mul' g h₁ h₂
  set c₁ := g.gen 𝔠₁
  set c₂ := g.gen 𝔠₂
  have hc₁ := g.span_gen 𝔠₁ h₁
  have hc₂ := g.span_gen 𝔠₂ h₂
  have hc₁0 := C3B.gen_ne_zero g 𝔠₁ h₁
  have hc₂0 := C3B.gen_ne_zero g 𝔠₂ h₂
  have h12 := C3B.gen_ne_zero g (𝔠₁ * 𝔠₂) (C3B.isExterior_mul h₁ h₂)
  obtain ⟨α, β, hαβ⟩ := exists_ab (x := c₁) (y := c₂) (by rw [hc₁, hc₂]; exact isCoprime_map hcop)
  set c' : SInt 𝔪 := ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6
  have hεc : (ε : SInt 𝔪) ^ 6 * c' = 1 := unit_pow_mul_inv ε
  rw [gaussPhase_eq_GS, gaussPhase_eq_GS, gaussPhase_eq_GS, sqrt_norm_mul_inv]
  rw [GS_gen_change (c := c₁ * c₂) (c' := c') h12
    (by rw [Subalgebra.coe_pow]; exact pow_ne_zero _ (unit_coe_ne_zero _)) (by
    rw [hε]; have := castF (F := F) hεc; simp only [coe_mul', coe_one'] at this ⊢
    simp only [Subalgebra.coe_pow] at this ⊢
    linear_combination (-((c₁ : F) * (c₂ : F))) * this)]
  rw [GS_crt hadd h₁ h₂ hc₁ hc₂ hc₁0 hc₂0 hαβ]
  rw [GS_twist (C := (ε : SInt 𝔪) ^ 6 * c₂) hχ h₁ hc₁ hc₁0 (by
      rw [show (ε : SInt 𝔪) ^ 6 * c₂ * (c' * β) - 1 = -(α * c₁) by
        linear_combination c₂ * β * hεc + hαβ, ← hc₁]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))),
    GS_twist (C := (ε : SInt 𝔪) ^ 6 * c₁) hχ h₂ hc₂ hc₂0 (by
      rw [show (ε : SInt 𝔪) ^ 6 * c₁ * (c' * α) - 1 = -(β * c₂) by
        linear_combination c₁ * α * hεc + hαβ, ← hc₂]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))]
  rw [residueSymbol_unit_pow_six hχ h₁, residueSymbol_unit_pow_six hχ h₂]
  ring

/-! ### Cross-prime multiplicativity of the Poisson factor -/

lemma residueSymbol_units_pow_six (hχ : HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞)
    (u v : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 ((u : SInt 𝔪) ^ 6 * (v : SInt 𝔪) ^ 6 * x) = residueSymbol ι 𝔪 𝔞 x := by
  rw [mul_assoc, residueSymbol_unit_pow_six hχ h𝔞, residueSymbol_unit_pow_six hχ h𝔞]

/-- One side of the Chinese-remainder splitting, after the twists. -/
lemma PS_part (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪) {𝔰 𝔄 𝔰' 𝔄' 𝔯' : Ideal (𝓞 F)}
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔄 : IsExterior 𝔪 𝔄) (h𝔄' : IsExterior 𝔪 𝔄')
    (h𝔯' : IsExterior 𝔪 𝔯') (hr' : IsCoprime 𝔯' (𝔰 * 𝔄)) (hA' : IsCoprime 𝔄' 𝔰)
    (εs εA εr : (SInt 𝔪)ˣ) {c e f : SInt 𝔪}
    (hEc : ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6) * c = 1)
    (hef : e * (g.gen 𝔰 * g.gen 𝔄) + f * (g.gen 𝔰' * g.gen 𝔄') = 1) (r : SInt 𝔪) :
    ∃ B' : SInt 𝔪, residueSymbol ι 𝔪 𝔰 (g.gen 𝔄') * residueSymbol ι 𝔪 𝔰 B' = 1 ∧
      PS ι 𝔪 𝔰 𝔄 (g.gen 𝔰) (g.gen 𝔄) (g.gen 𝔄 * ((εA : SInt 𝔪) ^ 6 * g.gen 𝔄')) (c * f)
          (((εr : SInt 𝔪) ^ 6 * g.gen 𝔯') ^ 6 * r) =
        residueSymbol ι 𝔪 𝔰 B' * residueSymbol ι 𝔪 𝔄 (g.gen 𝔰' * g.gen 𝔄') *
          PS ι 𝔪 𝔰 𝔄 (g.gen 𝔰) (g.gen 𝔄) (g.gen 𝔄) 1 r := by
  have hs := g.span_gen 𝔰 h𝔰
  have hA := g.span_gen 𝔄 h𝔄
  have hsA := span_gen_mul g h𝔰 h𝔄
  have hs0 := C3B.gen_ne_zero g 𝔰 h𝔰
  have hA0 := C3B.gen_ne_zero g 𝔄 h𝔄
  have hsAle𝔰 : Ideal.span {g.gen 𝔰 * g.gen 𝔄} ≤ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hs]; exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  have hsAle𝔄 : Ideal.span {g.gen 𝔰 * g.gen 𝔄} ≤ 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hA]; exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)
  have hμcop : IsCoprime (Ideal.span {(εr : SInt 𝔪) ^ 6 * g.gen 𝔯'})
      (Ideal.span {g.gen 𝔰 * g.gen 𝔄}) := by
    rw [hsA]
    exact cop_mul (cop_pow (isCoprime_unit εr _) 6) (cop_gen g h𝔯' hr')
  obtain ⟨μ', hμ'⟩ := exists_inv_mod hμcop
  have hBcop : IsCoprime (Ideal.span {(εA : SInt 𝔪) ^ 6 * g.gen 𝔄'})
      (𝔰.map (algebraMap (𝓞 F) (SInt 𝔪))) :=
    cop_mul (cop_pow (isCoprime_unit εA _) 6) (cop_gen g h𝔄' hA')
  obtain ⟨B', hB'⟩ := exists_inv_mod hBcop
  refine ⟨B', ?_, ?_⟩
  · have := residueSymbol_mul_inv hχ h𝔰 hB'
    rwa [residueSymbol_unit_pow_six hχ h𝔰] at this
  set μ := (εr : SInt 𝔪) ^ 6 * g.gen 𝔯'
  have hl : μ ^ 6 * μ' ^ 6 - 1 ∈ 𝔰.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← mul_pow]; exact hsAle𝔰 (pow_sub_one_mem hμ' 6)
  have hc : μ ^ 6 * μ' ^ 6 * (c * f) *
      ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6 * (g.gen 𝔰' * g.gen 𝔄')) - 1 ∈
        Ideal.span {g.gen 𝔰 * g.gen 𝔄} := by
    have e1 : μ ^ 6 * μ' ^ 6 * (c * f) *
        ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6 * (g.gen 𝔰' * g.gen 𝔄')) - 1 =
        ((μ * μ') ^ 6 - 1) - (μ * μ') ^ 6 * e * (g.gen 𝔰 * g.gen 𝔄) := by
      linear_combination (μ * μ') ^ 6 * f * (g.gen 𝔰' * g.gen 𝔄') * hEc + (μ * μ') ^ 6 * hef
    rw [e1]
    exact sub_mem (pow_sub_one_mem hμ' 6)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  rw [PS_twist hχ h𝔰 h𝔄 hs hA hs0 hA0 (B' := B') (l'' := μ' ^ 6) (l' := μ' ^ 6) hB' hl hc]
  have t1 : residueSymbol ι 𝔪 𝔰 (μ ^ 6) = 1 := by
    rw [residueSymbol_pow hχ h𝔰]
    exact residueSymbol_pow_six hχ h𝔰 (cop_mono hμcop hsAle𝔰)
  have t3 : residueSymbol ι 𝔪 𝔄 (μ' ^ 6) = 1 := by
    rw [residueSymbol_pow hχ h𝔄]
    exact residueSymbol_pow_six hχ h𝔄 (cop_mono (cop_of_inv hμ') hsAle𝔄)
  rw [t1, t3, residueSymbol_units_pow_six hχ h𝔄]
  ring

theorem poissonFactor_mul (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (g : AllowedGen ι 𝔪)
    {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ 𝔯₁ 𝔯₂ : Ideal (𝓞 F)} (h𝔰₁ : IsExterior 𝔪 𝔰₁) (h𝔰₂ : IsExterior 𝔪 𝔰₂)
    (h𝔄₁ : IsExterior 𝔪 𝔄₁) (h𝔄₂ : IsExterior 𝔪 𝔄₂) (h𝔯₁ : IsExterior 𝔪 𝔯₁)
    (h𝔯₂ : IsExterior 𝔪 𝔯₂) (hcop : IsCoprime (𝔰₁ * 𝔄₁) (𝔰₂ * 𝔄₂))
    (hr₂ : IsCoprime 𝔯₂ (𝔰₁ * 𝔄₁)) (hr₁ : IsCoprime 𝔯₁ (𝔰₂ * 𝔄₂)) :
    residueSymbol ι 𝔪 𝔰₁ (g.gen 𝔄₂) * residueSymbol ι 𝔪 𝔰₂ (g.gen 𝔄₁) *
        poissonFactor g (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (g.gen (𝔯₁ * 𝔯₂) ^ 6) =
      residueSymbol ι 𝔪 𝔄₁ (g.gen 𝔰₂ * g.gen 𝔄₂) *
        residueSymbol ι 𝔪 𝔄₂ (g.gen 𝔰₁ * g.gen 𝔄₁) *
        (poissonFactor g 𝔰₁ 𝔄₁ (g.gen 𝔯₁ ^ 6) * poissonFactor g 𝔰₂ 𝔄₂ (g.gen 𝔯₂ ^ 6)) := by
  obtain ⟨εs, hεs⟩ := gen_mul' g h𝔰₁ h𝔰₂
  obtain ⟨εA, hεA⟩ := gen_mul' g h𝔄₁ h𝔄₂
  obtain ⟨εr, hεr⟩ := gen_mul' g h𝔯₁ h𝔯₂
  have hs₁ := g.span_gen 𝔰₁ h𝔰₁
  have hs₂ := g.span_gen 𝔰₂ h𝔰₂
  have hA₁ := g.span_gen 𝔄₁ h𝔄₁
  have hA₂ := g.span_gen 𝔄₂ h𝔄₂
  have hs₁0 := C3B.gen_ne_zero g 𝔰₁ h𝔰₁
  have hs₂0 := C3B.gen_ne_zero g 𝔰₂ h𝔰₂
  have hA₁0 := C3B.gen_ne_zero g 𝔄₁ h𝔄₁
  have hA₂0 := C3B.gen_ne_zero g 𝔄₂ h𝔄₂
  have hsA₁ := span_gen_mul g h𝔰₁ h𝔄₁
  have hsA₂ := span_gen_mul g h𝔰₂ h𝔄₂
  obtain ⟨α, β, hαβ⟩ := exists_ab (x := g.gen 𝔰₁ * g.gen 𝔄₁) (y := g.gen 𝔰₂ * g.gen 𝔄₂)
    (by rw [hsA₁, hsA₂]; exact isCoprime_map hcop)
  have ha := unit_pow_mul_inv εs
  have hb := unit_pow_mul_inv εA
  set c : SInt 𝔪 := ((εs⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * ((εA⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6
    with hcdef
  have hEc : ((εs : SInt 𝔪) ^ 6 * (εA : SInt 𝔪) ^ 6) * c = 1 := by
    rw [hcdef]
    linear_combination ((εA : SInt 𝔪) ^ 6 * ((εA⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6) * ha + hb
  have hEcF := castF (F := F) hEc
  simp only [coe_mul', coe_one', Subalgebra.coe_pow] at hEcF
  have hc0 : (c : F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hEcF; exact zero_ne_one hEcF
  have step1 : poissonFactor g (𝔰₁ * 𝔰₂) (𝔄₁ * 𝔄₂) (g.gen (𝔯₁ * 𝔯₂) ^ 6) =
      PS ι 𝔪 𝔰₁ 𝔄₁ (g.gen 𝔰₁) (g.gen 𝔄₁) (g.gen 𝔄₁ * ((εA : SInt 𝔪) ^ 6 * g.gen 𝔄₂)) (c * β)
          (((εr : SInt 𝔪) ^ 6 * g.gen 𝔯₂) ^ 6 * g.gen 𝔯₁ ^ 6) *
        PS ι 𝔪 𝔰₂ 𝔄₂ (g.gen 𝔰₂) (g.gen 𝔄₂) (g.gen 𝔄₂ * ((εA : SInt 𝔪) ^ 6 * g.gen 𝔄₁))
          (c * α) (((εr : SInt 𝔪) ^ 6 * g.gen 𝔯₁) ^ 6 * g.gen 𝔯₂ ^ 6) := by
    rw [poissonFactor_eq_PS, hεs, hεA, hεr]
    have h0s : (((εs : SInt 𝔪) ^ 6 * g.gen 𝔰₁ * g.gen 𝔰₂ : SInt 𝔪) : F) ≠ 0 := by
      simp only [coe_mul', Subalgebra.coe_pow]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (unit_coe_ne_zero _)) hs₁0) hs₂0
    have h0A : (((εA : SInt 𝔪) ^ 6 * g.gen 𝔄₁ * g.gen 𝔄₂ : SInt 𝔪) : F) ≠ 0 := by
      simp only [coe_mul', Subalgebra.coe_pow]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (unit_coe_ne_zero _)) hA₁0) hA₂0
    rw [PS_gen_change (s := g.gen 𝔰₁ * g.gen 𝔰₂) (A := g.gen 𝔄₁ * g.gen 𝔄₂) (c := c) h0s h0A hc0
      (by
        simp only [coe_mul', Subalgebra.coe_pow]
        linear_combination (-((g.gen 𝔰₁ : F) * (g.gen 𝔰₂ : F) *
          ((g.gen 𝔄₁ : F) * (g.gen 𝔄₂ : F)))) * hEcF)]
    rw [PS_crt hadd h𝔰₁ h𝔰₂ h𝔄₁ h𝔄₂ hs₁ hs₂ hA₁ hA₂ hs₁0 hs₂0 hA₁0 hA₂0 hαβ
      (B := (εA : SInt 𝔪) ^ 6) (by ring)]
    congr 1
    · congr 1 <;> ring
    · congr 1 <;> ring
  obtain ⟨B₁', hinv1, hP1⟩ := PS_part hχ g h𝔰₁ h𝔄₁ h𝔄₂ h𝔯₂ hr₂
    hcop.symm.of_mul_left_right.of_mul_right_left εs εA εr hEc hαβ (g.gen 𝔯₁ ^ 6)
  obtain ⟨B₂', hinv2, hP2⟩ := PS_part hχ g h𝔰₂ h𝔄₂ h𝔄₁ h𝔯₁ hr₁
    hcop.of_mul_left_right.of_mul_right_left εs εA εr hEc (by rw [add_comm]; exact hαβ)
    (g.gen 𝔯₂ ^ 6)
  rw [step1, hP1, hP2, ← poissonFactor_eq_PS, ← poissonFactor_eq_PS]
  linear_combination (residueSymbol ι 𝔪 𝔄₁ (g.gen 𝔰₂ * g.gen 𝔄₂) *
      residueSymbol ι 𝔪 𝔄₂ (g.gen 𝔰₁ * g.gen 𝔄₁) * poissonFactor g 𝔰₁ 𝔄₁ (g.gen 𝔯₁ ^ 6) *
      poissonFactor g 𝔰₂ 𝔄₂ (g.gen 𝔯₂ ^ 6)) *
    (residueSymbol ι 𝔪 𝔰₂ (g.gen 𝔄₁) * residueSymbol ι 𝔪 𝔰₂ B₂' * hinv1 + hinv2)

end C3M

end ArtinPrimitiveRoots
end

section
/-! # C3M_Main: CutMul from `HypAdd` and `HypChi`

`b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀}, P^l, P^k, P^m) b(𝔠, 𝔫, 𝔰, 𝔯)`: `ϑ` is completely
multiplicative; `γ₂` and `F` split by (3.10) and `poissonFactor_mul`; with `a = χ_P(gen 𝔠)`,
`w = χ_P(gen 𝔠𝔫³) = a b³`, `σ = χ_P(gen 𝔰)`, `t = e₀ + 3l` the cross factors are
`a^{4e₀}` and `w^{2t}`, whose product is `1`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- `HypChi` for all moduli divisible by the small primes. -/
def HypChiAll (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → HypChi ι 𝔪

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma not_le_mul {P I J : Ideal (𝓞 F)} (hP : P.IsPrime) (hI : ¬ I ≤ P) (hJ : ¬ J ≤ P) :
    ¬ I * J ≤ P := fun h => (hP.mul_le.mp h).elim hI hJ

lemma not_le_pow {P I : Ideal (𝓞 F)} (hP : P.IsPrime) (hI : ¬ I ≤ P) (n : ℕ) :
    ¬ I ^ n ≤ P := fun h => hI (@Ideal.IsPrime.le_of_pow_le _ _ _ _ hP _ h)

/-- The core identity, for a fixed modulus. -/
theorem coeff_mul (hadd : HypAdd 𝔪) (hχ : HypChi ι 𝔪) (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) (e₀ l k m : ℕ)
    {𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F)} (h𝔠 : IsExterior 𝔪 𝔠) (h𝔫 : IsExterior 𝔪 𝔫)
    (h𝔰 : IsExterior 𝔪 𝔰) (h𝔯 : IsExterior 𝔪 𝔯) (h𝔠P : ¬ 𝔠 ≤ P) (h𝔫P : ¬ 𝔫 ≤ P)
    (h𝔰P : ¬ 𝔰 ≤ P) (h𝔯P : ¬ 𝔯 ≤ P) :
    gaussPhase g 2 (P ^ e₀ * 𝔠) * χ.thetaChar g (P ^ e₀ * 𝔠 * (P ^ l * 𝔫) ^ 3) *
        poissonFactor g (P ^ k * 𝔰) (P ^ e₀ * 𝔠 * (P ^ l * 𝔫) ^ 3) (g.gen (P ^ m * 𝔯) ^ 6) =
      gaussPhase g 2 (P ^ e₀) * χ.thetaChar g (P ^ e₀ * (P ^ l) ^ 3) *
          poissonFactor g (P ^ k) (P ^ e₀ * (P ^ l) ^ 3) (g.gen (P ^ m) ^ 6) *
        (gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
          poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (g.gen 𝔯 ^ 6)) := by
  have hP0 := hPe.1
  have hPj : ∀ j : ℕ, IsExterior 𝔪 (P ^ j) := C3B.isExterior_pow hPe
  set T := P ^ e₀ * (P ^ l) ^ 3 with hTdef
  set A' := 𝔠 * 𝔫 ^ 3 with hA'def
  have hT : IsExterior 𝔪 T := C3B.isExterior_mul (hPj e₀) (C3B.isExterior_pow (hPj l) 3)
  have hA' : IsExterior 𝔪 A' := C3B.isExterior_mul h𝔠 (C3B.isExterior_pow h𝔫 3)
  have hTpow : T = P ^ (e₀ + 3 * l) := by rw [hTdef, ← pow_mul, ← pow_add, mul_comm l 3]
  have hA'P : ¬ A' ≤ P := not_le_mul hP h𝔠P (not_le_pow hP h𝔫P 3)
  have cop : ∀ (J : Ideal (𝓞 F)) (j : ℕ), ¬ J ≤ P → IsCoprime (P ^ j) J :=
    fun J j hJ => isCoprime_pow_of_not_le hP hP0 hJ j
  have hcop : IsCoprime (P ^ k * T) (𝔰 * A') := by
    rw [hTpow, ← pow_add]; exact cop _ _ (not_le_mul hP h𝔰P hA'P)
  have hr₂ : IsCoprime 𝔯 (P ^ k * T) := by
    rw [hTpow, ← pow_add]; exact (cop _ _ h𝔯P).symm
  have hr₁ : IsCoprime (P ^ m) (𝔰 * A') := cop _ _ (not_le_mul hP h𝔰P hA'P)
  -- the three factorizations
  have hI : P ^ e₀ * 𝔠 * (P ^ l * 𝔫) ^ 3 = T * A' := by rw [hTdef, hA'def]; ring
  rw [hI, gaussPhase_mul hadd hχ g (hPj e₀) h𝔠 (cop _ _ h𝔠P) 2, thetaChar_mul g χ hT.1 hA'.1]
  have hF := poissonFactor_mul hadd hχ g (hPj k) h𝔰 hT hA' (hPj m) h𝔯 hcop hr₂ hr₁
  -- the residue symbols
  set π := g.gen P
  set a := residueSymbol ι 𝔪 P (g.gen 𝔠)
  set bb := residueSymbol ι 𝔪 P (g.gen 𝔫)
  set σ := residueSymbol ι 𝔪 P (g.gen 𝔰)
  set w := residueSymbol ι 𝔪 P (g.gen A')
  have hrec : ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 𝔟 π = residueSymbol ι 𝔪 P (g.gen 𝔟) :=
    fun 𝔟 h1 h2 => residueSymbol_gen_prime hχ g hP hPe 𝔟 h1 h2
  have hPpow : ∀ (j : ℕ) (x : SInt 𝔪),
      residueSymbol ι 𝔪 (P ^ j) x = residueSymbol ι 𝔪 P x ^ j := by
    intro j x
    rw [residueSymbol_prime_pow hP hP0, residueSymbol_prime hP hP0]
  have hTsym : ∀ x : SInt 𝔪,
      residueSymbol ι 𝔪 T x = residueSymbol ι 𝔪 P x ^ e₀ * residueSymbol ι 𝔪 P x ^ (l * 3) := by
    intro x
    rw [hTdef, residueSymbol_mul_ideal _ _ (hPj e₀).1 (C3B.isExterior_pow (hPj l) 3).1,
      ← pow_mul, hPpow, hPpow]
  have hgenT : ∀ 𝔞 : Ideal (𝓞 F), IsExterior 𝔪 𝔞 →
      residueSymbol ι 𝔪 𝔞 (g.gen T) =
        residueSymbol ι 𝔪 𝔞 π ^ e₀ * (residueSymbol ι 𝔪 𝔞 π ^ l) ^ 3 := by
    intro 𝔞 h𝔞
    rw [hTdef, residueSymbol_gen_mul hχ g h𝔞 (hPj e₀) (C3B.isExterior_pow (hPj l) 3),
      residueSymbol_gen_pow hχ g h𝔞 hPe, residueSymbol_gen_pow hχ g h𝔞 (hPj l),
      residueSymbol_gen_pow hχ g h𝔞 hPe]
  have hw : w = a * bb ^ 3 := by
    simp only [w, a, bb]
    rw [hA'def, residueSymbol_gen_mul hχ g hPe h𝔠 (C3B.isExterior_pow h𝔫 3),
      residueSymbol_gen_pow hχ g hPe h𝔫]
  have six : ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 → ¬ 𝔟 ≤ P →
      residueSymbol ι 𝔪 P (g.gen 𝔟) ^ 6 = 1 := by
    intro 𝔟 h1 h2
    have hc : IsCoprime 𝔟 P := by
      have := (cop 𝔟 1 h2).symm; rwa [pow_one] at this
    exact residueSymbol_pow_six hχ hPe (cop_gen g h1 hc)
  have ha6 : a ^ 6 = 1 := six 𝔠 h𝔠 h𝔠P
  have hb6 : bb ^ 6 = 1 := six 𝔫 h𝔫 h𝔫P
  have hσ6 : σ ^ 6 = 1 := six 𝔰 h𝔰 h𝔰P
  have hw6 : w ^ 6 = 1 := six A' hA' hA'P
  have hσ0 : σ ≠ 0 := fun h => by rw [h] at hσ6; norm_num at hσ6
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw6; norm_num at hw6
  -- evaluate the twists in `hF`
  rw [hPpow, hgenT 𝔰 h𝔰, hrec 𝔰 h𝔰 h𝔰P, hTsym,
    residueSymbol_mul hχ hPe, residueSymbol_mul hχ hA',
    hgenT A' hA', residueSymbol_gen_pow hχ g hA' hPe, hrec A' hA' hA'P] at hF
  -- evaluate the twists of `γ₂`
  rw [hPpow, residueSymbol_gen_pow hχ g h𝔠 hPe, hrec 𝔠 h𝔠 h𝔠P]
  have key : (a ^ e₀) ^ 2 * (a ^ e₀) ^ 2 * (w ^ e₀ * (w ^ l) ^ 3) ^ 2 = 1 := by
    rw [hw]
    have e : (a ^ e₀) ^ 2 * (a ^ e₀) ^ 2 * ((a * bb ^ 3) ^ e₀ * ((a * bb ^ 3) ^ l) ^ 3) ^ 2 =
        (a ^ 6) ^ (e₀ + l) * (bb ^ 6) ^ (e₀ + 3 * l) := by ring
    rw [e, ha6, hb6, one_pow, one_pow, one_mul]
  have hK : w ^ k * (σ ^ e₀ * (σ ^ l) ^ 3) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hw0) (mul_ne_zero (pow_ne_zero _ hσ0)
      (pow_ne_zero _ (pow_ne_zero _ hσ0)))
  apply mul_left_cancel₀ hK
  linear_combination ((a ^ e₀) ^ 2 * (a ^ e₀) ^ 2 * (gaussPhase g 2 (P ^ e₀) * gaussPhase g 2 𝔠) *
      (χ.thetaChar g T * χ.thetaChar g A')) * hF +
    (gaussPhase g 2 (P ^ e₀) * gaussPhase g 2 𝔠 * (χ.thetaChar g T * χ.thetaChar g A') *
      poissonFactor g (P ^ k) T (g.gen (P ^ m) ^ 6) * poissonFactor g 𝔰 A' (g.gen 𝔯 ^ 6) *
      w ^ k * (σ ^ e₀ * (σ ^ l) ^ 3)) * key

end C3M

open C3M in
/-- CutMul, from section A's two hypotheses. -/
theorem chk_exists_cutoff_principalCoeff_prime_pow_mul_eq_mul_of_hypChi (n : ℕ) (_hn0 : 0 < n)
    (_hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hX : HypChiAll F ι) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
        let b : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (g.gen 𝔯 ^ 6)
        ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            b (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              b (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * b 𝔠 𝔫 𝔰 𝔯 := by
  obtain ⟨N₂, h2⟩ := hX
  refine ⟨N₂, fun 𝔪 h𝔪 hS χ g => ?_⟩
  intro b P hP hPe e₀ l k m _ 𝔠 𝔫 𝔰 𝔯 h𝔠 _ h𝔫 h𝔰 h𝔯 h𝔠P h𝔫P h𝔰P h𝔯P
  exact coeff_mul (hypAdd 𝔪) (h2 𝔪 h𝔪 hS) χ g hP hPe e₀ l k m
    h𝔠 h𝔫 h𝔰 h𝔯 h𝔠P h𝔫P h𝔰P h𝔯P

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

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

end chi

end C3I

end ArtinPrimitiveRoots
end

section
/-! # C3M_Chk: `HypChi` from section A's `χ_P` (`C3I_Char`), and CutMul

Exterior primes are `C3I.Good` once `N₀ ≥ max(3^[F:ℚ], N 𝔇)`: `12 ∣ N P − 1` because `μ₁₂ ⊂ F`
and `P ∤ 6`, and `P ∤ 𝔇` because `N P > N 𝔇`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
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
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- `HypChi` holds for every modulus divisible by the primes of norm `≤ max(3^[F:ℚ], N 𝔇)`. -/
theorem hypChiAll (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : HypChiAll F ι := by
  refine ⟨max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))),
    fun 𝔪 _ hS P hP hPe => ?_⟩
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hP.ne_top
    rw [eq_top_iff, ← hPe.2]
    exact sup_le le_rfl h
  have hgt : max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))) <
      Ideal.absNorm P := by
    by_contra hc
    exact h𝔪 (hS P hP hPe.1 (not_lt.mp hc))
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ P := by
    intro hle
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
    have := le_max_right (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))
    omega
  have hgood : C3I.Good 𝔪 v :=
    ⟨hPe.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hPe.1 (lt_of_le_of_lt (le_max_left _ _) hgt),
      hdiff⟩
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel (Nat.dvd_trans (by norm_num) hn)).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have e : ∀ z : SInt 𝔪, C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) z) =
      sexticResidueSymbol ι 𝔪 P z := fun z => C3I.chi_mk hgood hω z
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · have h : C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) =
        C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x) *
          C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :=
      map_mul _ _ _
    rw [← map_mul, e, e, e] at h
    exact h
  · have hne : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h := C3I.chi_pow_six_apply (ι := ι) hgood hω hne
    rwa [e] at h

end C3M

end ArtinPrimitiveRoots
end

section
set_option linter.unusedSectionVars false
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open ArtinPrimitiveRoots
open C3M in
/-- **CutMul** (a049f077), statement verbatim. -/
theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ (χ : HeckeChar F 𝔪) (g : AllowedGen ι 𝔪),
        let b : Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ := fun 𝔠 𝔫 𝔰 𝔯 =>
          gaussPhase g 2 𝔠 * χ.thetaChar g (𝔠 * 𝔫 ^ 3) *
            poissonFactor g 𝔰 (𝔠 * 𝔫 ^ 3) (g.gen 𝔯 ^ 6)
        ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → ∀ e₀ l k m : ℕ, e₀ ≤ 1 →
          ∀ 𝔠 𝔫 𝔰 𝔯 : Ideal (𝓞 F), IsExterior 𝔪 𝔠 → Squarefree 𝔠 → IsExterior 𝔪 𝔫 →
            IsExterior 𝔪 𝔰 → IsExterior 𝔪 𝔯 → ¬ 𝔠 ≤ P → ¬ 𝔫 ≤ P → ¬ 𝔰 ≤ P → ¬ 𝔯 ≤ P →
            b (P ^ e₀ * 𝔠) (P ^ l * 𝔫) (P ^ k * 𝔰) (P ^ m * 𝔯) =
              b (P ^ e₀) (P ^ l) (P ^ k) (P ^ m) * b 𝔠 𝔫 𝔰 𝔯 :=
  chk_exists_cutoff_principalCoeff_prime_pow_mul_eq_mul_of_hypChi n hn0 hn F ι
    (hypChiAll n hn0 hn ι)
end
