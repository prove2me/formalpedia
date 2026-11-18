-- Prove2me | solution 1 for ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:45.425164+00:00
-- url     : https://prove2.me/submissions/ce6065d5-758d-4f6c-9e1a-bdcb5c090029

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017

section
-- module Solutions.Artin.T12.C3B_Norm
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- The generator of the unit ideal is a unit of `R`. -/
lemma isUnit_gen_top {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) :
    IsUnit (g.gen ⊤) := by
  have h := g.span_gen ⊤ ⟨top_ne_bot, top_sup_eq _⟩
  rw [Ideal.map_top] at h
  exact Ideal.span_singleton_eq_top.mp h

lemma normalizedFactors_top : normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
  rw [← Ideal.one_eq_top, normalizedFactors_one]

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3B_Unit
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end residue

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3B_Good
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.T12.C3B_Main
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma isExterior_mul {𝔪 I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3M_Base
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma isExterior_of_mul_left {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) : IsExterior 𝔪 I := by
  refine ⟨fun h0 => h.1 (by rw [h0, Ideal.bot_mul]), ?_⟩
  exact eq_top_iff.mpr (h.2 ▸ sup_le_sup_right (Ideal.mul_le_inf.trans inf_le_left) 𝔪)

lemma isExterior_of_mul_right {I J : Ideal (𝓞 F)} (h : IsExterior 𝔪 (I * J)) :
    IsExterior 𝔪 J := by
  rw [mul_comm] at h; exact isExterior_of_mul_left h

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

/-- `gen(I J) = ε⁶ gen(I) gen(J)` with `ε` a unit of `R`. -/
lemma gen_mul' (g : AllowedGen ι 𝔪) {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I)
    (hJ : IsExterior 𝔪 J) :
    ∃ ε : (SInt 𝔪)ˣ, g.gen (I * J) = (ε : SInt 𝔪) ^ 6 * g.gen I * g.gen J := by
  obtain ⟨ε, hε⟩ := g.gen_mul I J hI hJ
  refine ⟨Set.unitEquivUnitsInteger (placesOf 𝔪) F ε, ?_⟩
  apply Subtype.ext
  rw [hε]
  simp

end C3M

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.H0_Row
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

theorem coe_eq_gamOf_mul (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ((ν : SInt 𝔪) : F) =
      (((gamOf h𝔪 g ν : SUnit 𝔪) : Fˣ) : F) * (rowElt g (rowOf h𝔪 g ν) : F) := by
  have h := congrArg (fun x : {ν : SInt 𝔪 // ν ≠ 0} => ((x : SInt 𝔪) : F))
    ((rowEquiv h𝔪 g).apply_symm_apply ν)
  exact h.symm

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.T12.L2D_Fact
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

/-! L2D: factorization combinatorics for the proof of (4.5). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_prime_of_mem {I P : Ideal (𝓞 F)} (hP : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P hP

/-! ### `β_p` and the sum of `β_𝔣` -/


end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Ideal
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Ideal: prime-exponent bookkeeping for ideals of `𝓞 F`

`cnt P I = v_P(I)` (count in `normalizedFactors`), `prim I` its prime support; products, powers,
prime-power products over a finset, ideal equality from exponents, squarefreeness and coprimality
in exponent form, norms; `residueSymbol` over a squarefree ideal, and reciprocity
`χ_𝔠(gen 𝔡) = χ_𝔡(gen 𝔠)` for coprime exterior `𝔠, 𝔡`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F]

lemma cnt_mul {P I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    cnt P (I * J) = cnt P I + cnt P J := by
  unfold cnt; rw [normalizedFactors_mul hI hJ, Multiset.count_add]

lemma prime_of_mem_prim {P I : Ideal (𝓞 F)} (hP : P ∈ prim I) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp := L2D_prime_of_mem (Multiset.mem_toFinset.1 hP)
  exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩

lemma mem_prim_iff {P I : Ideal (𝓞 F)} : P ∈ prim I ↔ 0 < cnt P I := by
  unfold prim cnt; rw [Multiset.mem_toFinset, Multiset.count_pos]

lemma exterior_of_prim {𝔪 I P : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hP : P ∈ prim I) :
    IsExterior 𝔪 P :=
  (C3M.exterior_of_mem_factors hI (Multiset.mem_toFinset.1 hP)).2

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_VP
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_VP: the `P`-adic valuation `vP` and the unit-part symbol `uSym` (definitions and the
valuation algebra) -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma vP_v (x : F) : vP v.asIdeal x = -log (v.valuation F x) := by
  unfold vP
  rw [dif_pos ⟨v.isPrime, v.ne_bot⟩]

lemma val_eq_exp_vP {x : F} (hx : x ≠ 0) : v.valuation F x = exp (-(vP v.asIdeal x)) := by
  rw [vP_v, neg_neg, exp_log]
  exact (Valuation.ne_zero_iff _).2 hx

lemma vP_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    vP v.asIdeal (x * y) = vP v.asIdeal x + vP v.asIdeal y := by
  rw [vP_v, vP_v, vP_v, map_mul, log_mul ((Valuation.ne_zero_iff _).2 hx)
    ((Valuation.ne_zero_iff _).2 hy)]
  ring

lemma vP_inv (x : F) : vP v.asIdeal x⁻¹ = -vP v.asIdeal x := by
  rw [vP_v, vP_v, map_inv₀, log_inv, neg_neg]

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Char
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable {v : HeightOneSpectrum (𝓞 F)}

/-! ### The sixth roots of unity -/

section chi

variable {ι : F →+* ℂ}

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
-- module Solutions.Artin.T12.C3I_Gauss
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

/-! ### Characters on the finite field `L` -/

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Cut
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.T12.C3I_Loc
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

section prime

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma ext_pow (j : ℕ) : IsExterior 𝔪 (v.asIdeal ^ j) := isExterior_pow h.ext j

/-! ### Valuations -/

lemma val_unit (μ : (SInt 𝔪)ˣ) : v.valuation F ((μ : SInt 𝔪) : F) = 1 := by
  have h1 := val_le_one h.notS (μ : SInt 𝔪)
  have h2 := val_le_one h.notS ((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪)
  have h3 : v.valuation F ((μ : SInt 𝔪) : F) * v.valuation F (((μ⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

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

lemma val_eq_one_of_not_mem {q : SInt 𝔪} (hq : q ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (q : F) = 1 := by
  apply le_antisymm (val_le_one h.notS q)
  have := exp_le_val_of_not_mem h.notS 0 q (by rwa [zero_add, pow_one])
  simpa using this

end prime

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_F
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

section main

variable (g : AllowedGen ι 𝔪) (h : Good 𝔪 v)
include h

lemma goodP_v : C3B.GoodP 𝔪 v.asIdeal :=
  ⟨v.isPrime, v.ne_bot, h.notS, Nat.dvd_trans (by norm_num) h.twelve⟩

lemma sext_one {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : sexticResidueSymbol ι 𝔪 v.asIdeal 1 = 1 := by
  rw [← chi_mk h hω, map_one, MulChar.map_one]

lemma sext_unit_six {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (μ : (SInt 𝔪)ˣ) :
    sexticResidueSymbol ι 𝔪 v.asIdeal ((μ : SInt 𝔪) ^ 6) = 1 := by
  have := C3B.sexticResidueSymbol_unit_pow_six ι v.asIdeal (goodP_v h) μ 1
  rw [mul_one] at this; rw [this, sext_one h hω]

end main

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Res: the residue map `O_P → R / P R` on `F`, and the local symbols

For a height-one prime `v ∉ S`:
* `L3V.res 𝔪 v w ∈ R / v R` for `v(w) ≤ 1` (`0` otherwise); `res_eq`: `res w = [y]` whenever
  `v(w − y) ≤ exp(−1)`; `res` is additive and multiplicative on `O_v`, `res y = [y]` on `R`,
  `res w = 0 ↔ v(w) < 1`.
* `localSymbol_eq`: `localSymbol ι 𝔪 P t = χ(res t)` (all `t`, `Good`);
* `localAddChar_eq`: `localAddChar g P w = ψ(−res w)` for `v(w) ≤ 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma exp_neg_one_lt_one : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
  rw [← exp_zero]; exact exp_lt_exp.2 (by norm_num)

lemma mem_iff_val (hv : v ∉ placesOf 𝔪) (y : SInt 𝔪) :
    y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ v.valuation F (y : F) ≤ exp (-1 : ℤ) := by
  have := C3I.mem_map_pow_iff (𝔪 := 𝔪) hv 1 y
  rw [pow_one] at this
  rw [this]; simp

lemma val_le_exp_iff_lt_one (x : F) : v.valuation F x ≤ exp (-1 : ℤ) ↔ v.valuation F x < 1 := by
  constructor
  · intro h; exact lt_of_le_of_lt h exp_neg_one_lt_one
  · intro h
    by_contra hc
    push Not at hc
    have := C3I.exp_le_of_lt (j := 0) (by simpa using hc)
    rw [exp_zero] at this
    exact absurd h (not_lt.2 this)

lemma mk_eq_of_approx (hv : v ∉ placesOf 𝔪) {w : F} {y : SInt 𝔪} {a : 𝓞 F}
    (h : v.valuation F (w - (y : F)) ≤ exp (-1 : ℤ))
    (ha : v.valuation F (w - algebraMap (𝓞 F) F a) ≤ exp (-((1 : ℕ) : ℤ))) :
    (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
      (algebraMap (𝓞 F) (SInt 𝔪) a)) = Ideal.Quotient.mk _ y := by
  rw [Ideal.Quotient.eq, mem_iff_val hv]
  have h2 : ((algebraMap (𝓞 F) (SInt 𝔪) a - y : SInt 𝔪) : F) =
      -(w - algebraMap (𝓞 F) F a) + (w - (y : F)) := by
    rw [Subalgebra.coe_sub, C3I.coe_alg]; ring
  rw [h2]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ h)
  rw [Valuation.map_neg]
  simpa using ha

lemma res_eq (hv : v ∉ placesOf 𝔪) {w : F} {y : SInt 𝔪}
    (h : v.valuation F (w - (y : F)) ≤ exp (-1 : ℤ)) :
    res 𝔪 v w = Ideal.Quotient.mk _ y := by
  have hw : v.valuation F w ≤ 1 := by
    have h1 : w = (w - (y : F)) + (y : F) := by ring
    rw [h1]
    exact (Valuation.map_add _ _ _).trans
      (max_le (h.trans exp_neg_one_lt_one.le) (C3I.val_le_one hv y))
  rw [res, dif_pos hw]
  exact mk_eq_of_approx hv h (C3I.exists_val_sub_le (v := v) 1 w hw).choose_spec

lemma res_of_SInt (hv : v ∉ placesOf 𝔪) (y : SInt 𝔪) :
    res 𝔪 v (y : F) = Ideal.Quotient.mk _ y :=
  res_eq hv (by simp)

lemma exists_approx {w : F} (hw : v.valuation F w ≤ 1) :
    ∃ y : SInt 𝔪, v.valuation F (w - (y : F)) ≤ exp (-1 : ℤ) := by
  obtain ⟨a, ha⟩ := C3I.exists_val_sub_le (v := v) 1 w hw
  exact ⟨algebraMap (𝓞 F) (SInt 𝔪) a, by rw [C3I.coe_alg]; simpa using ha⟩

lemma res_of_not_le {w : F} (hw : ¬ v.valuation F w ≤ 1) : res 𝔪 v w = 0 := by
  rw [res, dif_neg hw]

lemma res_mul (hv : v ∉ placesOf 𝔪) {w w' : F} (hw : v.valuation F w ≤ 1)
    (hw' : v.valuation F w' ≤ 1) : res 𝔪 v (w * w') = res 𝔪 v w * res 𝔪 v w' := by
  obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
  obtain ⟨y', hy'⟩ := exists_approx (𝔪 := 𝔪) hw'
  rw [res_eq hv hy, res_eq hv hy', ← map_mul]
  apply res_eq hv
  have : w * w' - ((y * y' : SInt 𝔪) : F) = w * (w' - y') + (w - y) * (y' : F) := by
    rw [Subalgebra.coe_mul]; ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    calc v.valuation F w * v.valuation F (w' - y') ≤ 1 * exp (-1 : ℤ) := mul_le_mul' hw hy'
      _ = _ := one_mul _
  · rw [map_mul]
    calc v.valuation F (w - y) * v.valuation F (y' : F) ≤ exp (-1 : ℤ) * 1 :=
          mul_le_mul' hy (C3I.val_le_one hv y')
      _ = _ := mul_one _

lemma res_one (hv : v ∉ placesOf 𝔪) : res 𝔪 v (1 : F) = 1 := by
  have := res_of_SInt (𝔪 := 𝔪) hv 1
  simpa using this

lemma res_eq_zero_iff (hv : v ∉ placesOf 𝔪) {w : F} (hw : v.valuation F w ≤ 1) :
    res 𝔪 v w = 0 ↔ v.valuation F w < 1 := by
  obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
  rw [res_eq hv hy, Ideal.Quotient.eq_zero_iff_mem, mem_iff_val hv, val_le_exp_iff_lt_one]
  rw [val_le_exp_iff_lt_one] at hy
  constructor
  · intro h
    have h2 : w = (y : F) + (w - y) := by ring
    rw [h2]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h hy)
  · intro h
    have h1 : (y : F) = w - (w - y) := by ring
    rw [h1]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h hy)

lemma res_ne_zero_of_val_eq_one (hv : v ∉ placesOf 𝔪) {w : F} (hw : v.valuation F w = 1) :
    res 𝔪 v w ≠ 0 := by
  rw [Ne, res_eq_zero_iff hv hw.le, hw]; exact lt_irrefl _

/-! ### The local symbols -/

section good

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include h

lemma val_of_not_mem {z : SInt 𝔪} (hz : z ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) = 1 := C3I.val_eq_one_of_not_mem h hz

include hω in
lemma localSymbol_eq (t : F) :
    localSymbol ι 𝔪 v.asIdeal t = C3I.chi ι h hω (res 𝔪 v t) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [localSymbol]
  split_ifs with hex
  · set yz := hex.choose
    have hyz := hex.choose_spec
    have hz1 := val_of_not_mem h hyz.1
    have ht : v.valuation F t ≤ 1 := by
      have := congrArg (v.valuation F) hyz.2
      rw [map_mul, hz1, one_mul] at this
      rw [this]; exact C3I.val_le_one h.notS _
    have hres : res 𝔪 v (yz.1 : F) = res 𝔪 v (yz.2 : F) * res 𝔪 v t := by
      rw [← hyz.2, res_mul h.notS (C3I.val_le_one h.notS _) ht]
    rw [res_of_SInt h.notS, res_of_SInt h.notS] at hres
    rw [← C3I.chi_mk h hω, ← C3I.chi_mk h hω, hres, map_mul]
    have hz0 : Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) yz.2 ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hyz.1
    have hu : IsUnit (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) yz.2) :=
      Ne.isUnit hz0
    have hn : ‖C3I.chi ι h hω (Ideal.Quotient.mk _ yz.2)‖ = 1 := by
      have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hz0
      have := norm_pow (C3I.chi ι h hω (Ideal.Quotient.mk _ yz.2)) 6
      rw [h6, norm_one] at this
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm)
    rw [mul_comm (C3I.chi ι h hω _), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  · -- no representation: `t` is not `v`-integral, or ...
    by_cases ht : v.valuation F t ≤ 1
    · exfalso
      apply hex
      obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) t ht
      refine ⟨(algebraMap (𝓞 F) (SInt 𝔪) n, algebraMap (𝓞 F) (SInt 𝔪) d), ?_, ?_⟩
      · rw [show (algebraMap (𝓞 F) (SInt 𝔪) d) ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
            d ∈ v.asIdeal ^ 1 from by
              rw [← C3I.alg_mem_map_pow_iff h.notS 1 d, pow_one]]
        rw [pow_one]; exact hd
      · simp only [C3I.coe_alg]
        rw [mul_comm]; exact hnd
    · rw [res_of_not_le ht, MulChar.map_zero]

lemma val_sub_le_of_rep {w : F} {y z r : SInt 𝔪}
    (hz : z ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (hr : r ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (he : (z : F) * (w - y) = r) :
    v.valuation F (w - y) ≤ exp (-1 : ℤ) := by
  have := congrArg (v.valuation F) he
  rw [map_mul, val_of_not_mem h hz, one_mul] at this
  rw [this]; exact (mem_iff_val h.notS r).1 hr

lemma localAddChar_eq (g : AllowedGen ι 𝔪) {w : F} (hw : v.valuation F w ≤ 1) :
    localAddChar g v.asIdeal w = C3I.psi g h (-(res 𝔪 v w)) := by
  rw [localAddChar]
  split_ifs with hex
  · set yzr := hex.choose
    have hyzr := hex.choose_spec
    have hres := res_eq h.notS (val_sub_le_of_rep h hyzr.1 hyzr.2.1 hyzr.2.2)
    rw [hres, ← map_neg, C3I.psi_mk, Subalgebra.coe_neg, neg_div]
  · exfalso
    apply hex
    obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
    have hy1 : v.valuation F (w - y) ≤ 1 := hy.trans exp_neg_one_lt_one.le
    obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (w - y) hy1
    have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
    refine ⟨(y, algebraMap (𝓞 F) (SInt 𝔪) d, algebraMap (𝓞 F) (SInt 𝔪) n), ?_, ?_, ?_⟩
    · intro hm
      rw [mem_iff_val h.notS, C3I.coe_alg, hdv] at hm
      exact absurd hm (not_le.2 exp_neg_one_lt_one)
    · rw [mem_iff_val h.notS, C3I.coe_alg]
      have : algebraMap (𝓞 F) F n = (w - y) * algebraMap (𝓞 F) F d := hnd.symm
      rw [this, map_mul, hdv, mul_one]; exact hy
    · simp only [C3I.coe_alg]
      rw [mul_comm]; exact hnd

end good

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Loc
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Loc: characters, Gauss sums and masks on `k_P = R / P R`

At a good prime `v` (with `χ = C3I.chi`, `ψ = C3I.psi`):
* `chi_ql`, `add_ql`: the cut's `χ_P(quotLift y)` and `e(−quotLift y / p)` are `χ y`, `ψ(−y)`;
* `conj_chi_pow`: `conj(χ y)^j = (χ^{5j}) y`; `tau_eq`: `τ_j = g(χ^{5j}, ψ)`;
* `norm_gs`, `norm_gs_le`: `‖g(χ^m, ψ)‖ = √q` (`6 ∤ m`), `≤ √q` (all `m`); `norm_tau`;
* the masks: `mask_zero_of_ne`, `norm_mask_zero_le`, `norm_mask_le`, `mask_mul`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section loc

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
include h hω

lemma chi_ql (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = C3I.chi ι h hω y := by
  rw [← C3I.chi_mk h hω, C3I.mk_quotLift]

lemma norm_chi_eq_one {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ‖C3I.chi ι h hω y‖ = 1 := by
  have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
  have := norm_pow (C3I.chi ι h hω y) 6
  rw [h6, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm

lemma conj_chi {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    starRingEnd ℂ (C3I.chi ι h hω y) = C3I.chi ι h hω y ^ 5 := by
  have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
  have hn := norm_chi_eq_one (ι := ι) h hω hy
  have h0 : C3I.chi ι h hω y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  have hc : starRingEnd ℂ (C3I.chi ι h hω y) * C3I.chi ι h hω y = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  apply mul_right_cancel₀ h0
  rw [hc, ← pow_succ, h6]

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

/-! ### Masks -/

/-- `α(τ y) = conj(χ τ)^j α(y)` for `τ ≠ 0`. -/
lemma mask_mul {j : ℕ} {τ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hτ : τ ≠ 0)
    (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    mask g v.asIdeal j (τ * y) = starRingEnd ℂ (C3I.chi ι h hω τ) ^ j * mask g v.asIdeal j y := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  unfold mask
  by_cases hj : j = 0
  · subst hj
    have e : (τ * y = 0) ↔ (y = 0) := by simp [hτ]
    by_cases hy : y = 0
    · rw [if_pos rfl, if_pos rfl, if_pos (e.2 hy), if_pos hy, pow_zero, one_mul]
    · rw [if_pos rfl, if_pos rfl, if_neg (fun h' => hy (e.1 h')), if_neg hy, pow_zero, one_mul]
  · rw [if_neg hj, if_neg hj, chi_ql h hω, chi_ql h hω, map_mul, map_mul, mul_pow]
    ring

end loc

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Weyl
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Weyl: Lemma 6.2 — the digit sums of the local Weyl calculation

At a good prime `v`, for the cut's local data:
* `Wsph_eq`, `Wv` values and `norm_gaussPhase_two`;
* `Eloc_split`: for `k ≥ 1`, `E_P = α(0) W_P(a(ν)) + R_P`, `R_P = Rsum` the nonzero digits;
* `Wweyl_eq`: the per-digit value in terms of `χ(res t)`, `χ(v)`, `ψ`;
* (6.15) `Rsum_monomial`: `R(t) = R(1) χ(res t)^{b(j,e)}` for a `P`-unit `t`, with
  `b(j,0) = 8 + 5j ≡ 8 − j`, `b(j,e) = 4 + 2e` (`e > 0`);
* (6.14) `Rsum_one_vanish`: `j = 1`, `e > 0` gives `0`;
* `norm_Rsum_one_le`: `|R(1)| ≤ β_P(e)` of (6.20) (`L2D_betaP`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section weyl

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

omit hω in
lemma Wv_mod0 {e : ℕ} (he : e % 3 = 0) :
    Wv g v.asIdeal e = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  unfold Wv; rw [if_pos he]

omit hω in
lemma Wv_zero : Wv g v.asIdeal 0 = 1 := by
  rw [Wv_mod0 h g (by norm_num)]; simp

lemma Wsph_eq {e₀ : ℤ} (he : 0 ≤ e₀) (t : F) :
    Wsph g v.asIdeal e₀ t = C3I.chi ι h hω (res 𝔪 v t) ^ (2 * e₀.toNat) *
      Wv g v.asIdeal e₀.toNat := by
  unfold Wsph; rw [if_neg (not_lt.2 he), localSymbol_eq h hω]

omit hω in
lemma Wsph_neg {e₀ : ℤ} (he : e₀ < 0) (t : F) : Wsph g v.asIdeal e₀ t = 0 := by
  unfold Wsph; rw [if_pos he]

open Classical in
lemma Eloc_split {k : ℕ} (hk : k ≠ 0) (e₀ : ℤ) (t : F) :
    Eloc g v.asIdeal k e₀ t =
      mask g v.asIdeal (k % 6) 0 * Wsph g v.asIdeal e₀ t + Rsum g v.asIdeal (k % 6) e₀ t := by
  unfold Eloc Rsum
  rw [if_neg hk, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have : ∀ y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      mask g v.asIdeal (k % 6) y *
          (if y = 0 then Wsph g v.asIdeal e₀ t else Wweyl g v.asIdeal e₀ t y) =
        (if y = 0 then mask g v.asIdeal (k % 6) 0 * Wsph g v.asIdeal e₀ t else 0) +
          mask g v.asIdeal (k % 6) y *
            (if y = 0 then 0 else Wweyl g v.asIdeal e₀ t y) := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma val_ql_eq_one {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    v.valuation F (quotLift y : F) = 1 := by
  apply val_of_not_mem h
  rw [← Ideal.Quotient.eq_zero_iff_mem, C3I.mk_quotLift]; exact hy

lemma Wweyl_eq {t : F} (ht : v.valuation F t ≤ 1)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {e₀ : ℤ}
    (he : 0 ≤ e₀ + 2) {x : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))}
    (hx : x * y = res 𝔪 v t) :
    Wweyl g v.asIdeal e₀ t y = Wv g v.asIdeal (e₀ + 2).toNat *
      C3I.chi ι h hω (res 𝔪 v t) ^ (4 + 2 * (e₀ + 2).toNat) * C3I.chi ι h hω y ^ 4 *
      (if (e₀ + 2).toNat = 0 then C3I.psi g h (-x) else 1) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hvq := val_ql_eq_one h hω hy
  have hq0 : (quotLift y : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvq; exact zero_ne_one hvq
  set w := t / (quotLift y : F) with hw
  have hvw : v.valuation F w ≤ 1 := by
    rw [hw, map_div₀, hvq, div_one]; exact ht
  have hresw : res 𝔪 v w = x := by
    have h1 : res 𝔪 v (w * (quotLift y : F)) = res 𝔪 v w * y := by
      rw [res_mul h.notS hvw (C3I.val_le_one h.notS _), res_of_SInt h.notS, C3I.mk_quotLift]
    rw [hw, div_mul_cancel₀ _ hq0, ← hw, ← hx] at h1
    exact (mul_right_cancel₀ hy h1).symm
  have hvp : v.valuation F (g.gen v.asIdeal : F) ≤ 1 := C3I.val_le_one h.notS _
  have hresp : res 𝔪 v (g.gen v.asIdeal : F) = 0 := by
    rw [res_of_SInt h.notS, Ideal.Quotient.eq_zero_iff_mem]
    have := C3I.gen_mem g h 1
    rwa [pow_one] at this
  have key : ∀ n : ℕ, v.valuation F ((g.gen v.asIdeal : F) ^ n * w) ≤ 1 ∧
      res 𝔪 v ((g.gen v.asIdeal : F) ^ n * w) = if n = 0 then x else 0 := by
    intro n
    induction n with
    | zero => simp [hvw, hresw]
    | succ n ih =>
      have e1 : (g.gen v.asIdeal : F) ^ (n + 1) * w =
          (g.gen v.asIdeal : F) * ((g.gen v.asIdeal : F) ^ n * w) := by ring
      rw [e1, map_mul, res_mul h.notS hvp ih.1, hresp, zero_mul]
      refine ⟨?_, by simp⟩
      calc v.valuation F (g.gen v.asIdeal : F) * v.valuation F ((g.gen v.asIdeal : F) ^ n * w)
          ≤ 1 * 1 := mul_le_mul' hvp ih.1
        _ = 1 := one_mul 1
  have e2 : (g.gen v.asIdeal : F) ^ (e₀ + 2).toNat * t / (quotLift y : F) =
      (g.gen v.asIdeal : F) ^ (e₀ + 2).toNat * w := by rw [hw, mul_div_assoc]
  unfold Wweyl
  rw [if_neg (not_lt.2 he), localSymbol_eq h hω, chi_ql h hω, e2,
    localAddChar_eq h g (key _).1, (key _).2]
  split_ifs with hn
  · rfl
  · rw [neg_zero, AddChar.map_zero_eq_one]

lemma Rsum_neg {j : ℕ} {e₀ : ℤ} (he : e₀ + 2 < 0) (t : F) : Rsum g v.asIdeal j e₀ t = 0 := by
  unfold Rsum Wweyl
  simp [he]

open Classical in
/-- `R(t)` for `e > 0`: `W_e χ(res t)^{4+2e} ∑_{v ≠ 0} α(v) χ(v)^4`. -/
lemma Rsum_pos {j : ℕ} {e₀ : ℤ} (he : 0 < e₀ + 2) {t : F} (ht : v.valuation F t ≤ 1) :
    Rsum g v.asIdeal j e₀ t = Wv g v.asIdeal (e₀ + 2).toNat *
      C3I.chi ι h hω (res 𝔪 v t) ^ (4 + 2 * (e₀ + 2).toNat) *
      ∑ y, mask g v.asIdeal j y * (if y = 0 then 0 else C3I.chi ι h hω y ^ 4) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  unfold Rsum
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y = 0
  · simp [hy]
  · rw [if_neg hy, if_neg hy, Wweyl_eq h hω g ht hy he.le (x := res 𝔪 v t * y⁻¹)
      (by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]), if_neg (by omega)]
    ring

open Classical in
/-- `R(t)` for `e = 0`. -/
lemma Rsum_zero {j : ℕ} {e₀ : ℤ} (he : e₀ + 2 = 0) {t : F} (ht : v.valuation F t ≤ 1) :
    haveI := C3I.isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    Rsum g v.asIdeal j e₀ t = C3I.chi ι h hω (res 𝔪 v t) ^ 4 *
      ∑ y, mask g v.asIdeal j y *
        (if y = 0 then 0 else C3I.chi ι h hω y ^ 4 * C3I.psi g h (-(res 𝔪 v t * y⁻¹))) := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  unfold Rsum
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y = 0
  · simp [hy]
  · rw [if_neg hy, if_neg hy, Wweyl_eq h hω g ht hy (by omega) (x := res 𝔪 v t * y⁻¹)
      (by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one])]
    have e1 : (e₀ + 2).toNat = 0 := by omega
    rw [e1, if_pos rfl, Wv_zero h g]
    ring

lemma res_one' : res 𝔪 v (1 : F) = 1 := res_one h.notS

open Classical in
/-- (6.15): `R(t) = R(1) χ(res t)^{b(j,e)}` for a `P`-unit `t`. -/
lemma Rsum_monomial {j : ℕ} {e₀ : ℤ} (he : 0 ≤ e₀ + 2) {t : F} (ht : v.valuation F t = 1) :
    Rsum g v.asIdeal j e₀ t =
      Rsum g v.asIdeal j e₀ 1 * C3I.chi ι h hω (res 𝔪 v t) ^ bexp j (e₀ + 2).toNat := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h1 : v.valuation F (1 : F) ≤ 1 := by rw [map_one]
  have hτ : res 𝔪 v t ≠ 0 := res_ne_zero_of_val_eq_one h.notS ht
  rcases he.lt_or_eq with hpos | hz
  · rw [Rsum_pos h hω g hpos ht.le, Rsum_pos h hω g hpos h1, res_one' h hω, map_one, one_pow,
      bexp, if_neg (by omega)]
    ring
  · have hz' : e₀ + 2 = 0 := hz.symm
    rw [Rsum_zero h hω g hz' ht.le, Rsum_zero h hω g hz' h1, res_one' h hω, map_one, one_pow,
      one_mul, bexp, if_pos (by omega)]
    set τ := res 𝔪 v t
    rw [← Fintype.sum_equiv (Equiv.mulLeft₀ τ hτ) (fun z => mask g v.asIdeal j (τ * z) *
        (if τ * z = 0 then 0 else C3I.chi ι h hω (τ * z) ^ 4 *
          C3I.psi g h (-(τ * (τ * z)⁻¹)))) _ (fun z => rfl)]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [mask_mul h hω g hτ, one_mul]
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hτz : τ * z ≠ 0 := mul_ne_zero hτ hz0
      have e3 : τ * (τ * z)⁻¹ = z⁻¹ := by field_simp
      rw [if_neg hτz, if_neg hz0, e3, map_mul]
      have hc : starRingEnd ℂ (C3I.chi ι h hω τ) ^ j = C3I.chi ι h hω τ ^ (5 * j) := by
        rw [conj_chi (ι := ι) h hω hτ, ← pow_mul]
      rw [hc]
      ring

end weyl

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Eval1
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Eval1: the reflected frequency of a key, its exponents and unit parts

For a key `(𝔣, 𝔞', 𝔫', u, 𝔠')` with `𝔥 = 𝔣 𝔤` the frequency is `x = ε_u gen(𝔤² 𝔞' 𝔠' 𝔫'³)`,
`ν = x / b²` (6.21). `KeyHyp` collects the support conditions; `cnt_x`, `e0_eq` compute
`v_P(ν) = v_P(𝔞') + v_P(𝔠') + 3 v_P(𝔫') − 2 v_P(𝔣) − 2 v_P(𝔡)`; `e0_eq_vP`: it is `vP P ν`, so the
cut's local argument is the unit part of `ν`; `Rsum_tz`, `Wsph_tz` evaluate the local factors with
`U_P = uSym_P(ν)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### `ν` and its unit parts -/

section nu

variable (g : AllowedGen ι 𝔪)

lemma rep_ne_zero (u : SClass 𝔪) : ((u.rep : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : (u.rep : SInt 𝔪) = 0 := Subtype.ext h0
  have hu : IsUnit (u.rep : SInt 𝔪) := by
    unfold SClass.rep; exact Units.isUnit _
  rw [this] at hu
  exact not_isUnit_zero hu

lemma nu_ne_zero (r z : RowClass 𝔪) : nu g r z ≠ 0 := by
  unfold nu rowElt
  rw [Subalgebra.coe_mul]
  exact div_ne_zero (mul_ne_zero (rep_ne_zero z.2) (C3B.gen_ne_zero g z.1.1 z.1.2))
    (pow_ne_zero _ (C3B.gen_ne_zero g r.1.1 r.1.2))

end nu

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L2A_FSQuot
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinPrimitiveRoots.L2A
end

section
-- module Solutions.Artin.T12.L3V_Val
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Val: valuations of allowed generators and the unit-part symbol `uSym`

* `val_gen_eq`: `v(gen I) = exp(−v_P(I))` for exterior `I` at a good prime;
* `vP P x = −log v(x)` (the `P`-adic valuation), `uSym g P x = χ_P(x p^{−v_P(x)})`, the symbol of the
  unit part;
* `uSym_mul`, `uSym_inv`, `uSym_pow_six`, `uSym_ne_zero`, `uSym_of_unit`, `uSym_SInt` (for
  `y ∈ R ∖ P R`: `uSym y = χ_P(y)`), `uSym_unit_pow_six` (`= 1` on `U_S^6`), `vP_gen`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

section good

variable (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪)
include h

lemma gen_not_mem_of_ne {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q)
    (hne : Q ≠ v.asIdeal) :
    g.gen Q ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  intro hmem
  have hspan : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen Q hQe, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  have hle : Q ≤ v.asIdeal := fun a ha =>
    L2A.mem_of_map_mem v.asIdeal h.cop a (hspan (Ideal.mem_map_of_mem _ ha))
  have hmax : Q.IsMaximal := hQ.isMaximal hQe.1
  exact hne (hmax.eq_of_le v.isPrime.ne_top hle)

lemma nf_prime {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

/-- `v(gen I) = exp(−v_P(I))`. -/
lemma val_gen_eq (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    v.valuation F (g.gen I : F) = exp (-(((normalizedFactors I).count v.asIdeal : ℕ) : ℤ)) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI.1
  | h₂ u hu =>
    have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
    subst hu'
    obtain ⟨μ, hμ⟩ := C3B.isUnit_gen_top g
    rw [← hμ, C3I.val_unit h, C3B.normalizedFactors_top]
    simp
  | h₃ 𝔞 Q hane hQ ih =>
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hQe : IsExterior 𝔪 Q := C3M.isExterior_of_mul_left hI
    have hae : IsExterior 𝔪 𝔞 := C3M.isExterior_of_mul_right hI
    obtain ⟨ε, hε⟩ := C3M.gen_mul' g hQe hae
    rw [hε, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, map_mul, map_pow,
      C3I.val_unit h, one_pow, one_mul, ih hae, normalizedFactors_mul hQe.1 hae.1,
      nf_prime h hQp hQe.1, Multiset.count_add, Multiset.count_singleton]
    by_cases hQv : Q = v.asIdeal
    · subst hQv
      rw [C3I.val_pi g h, if_pos rfl, ← exp_add]
      congr 1; push_cast; ring
    · rw [C3I.val_eq_one_of_not_mem h (gen_not_mem_of_ne h g hQp hQe hQv), if_neg (Ne.symm hQv),
        one_mul, zero_add]

lemma vP_gen (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    vP v.asIdeal (g.gen I : F) = ((normalizedFactors I).count v.asIdeal : ℤ) := by
  rw [vP_v, val_gen_eq h g I hI, log_exp, neg_neg]

omit g in
lemma vP_unit (μ : (SInt 𝔪)ˣ) : vP v.asIdeal ((μ : SInt 𝔪) : F) = 0 := by
  rw [vP_v, C3I.val_unit h]; simp

lemma val_unitPart {x : F} (hx : x ≠ 0) :
    v.valuation F (x * (g.gen v.asIdeal : F) ^ (-(vP v.asIdeal x))) = 1 := by
  rw [map_mul, map_zpow₀, C3I.val_pi g h, val_eq_exp_vP hx, ← exp_zsmul, ← exp_add]
  simp

end good

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.HB_Dig
/-! # WP-HB, file 1: the per-digit coefficient at the frequency `ν` itself

MATH3 §3.4, §6.2.  HA's `H.digCoef g (⟨𝔟,h𝔟⟩,1) v (H0.rowOf h𝔪 g ν)` takes the unit parts `t_P`
from the row representative `rowElt (rowOf ν) = ν / u⁶`; the true per-digit coefficient of the
reflected expansion is not `U_S⁶`-invariant (at a nonzero digit with `e = 0` it contains the
additive phase `ladd_P(t_P / ṽ_P)`).  Here:

* `eNu`, `tNu`, `digCoefNu`: the same product with `t_P = (ν / b²) · p_P^{−e₀}` taken from `ν`;
* `Eloc_unit_six`: `Eloc_P(k, e₀, t u⁶) = Eloc_P(k, e₀, t)` for a `P`-unit `t`, `u ∈ U_S`
  (from `L3V.Rsum_monomial`, `L3V.Wsph_eq`, `C3I.sext_unit_six`);
* `sum_maskProd_digLoc`: the mask-weighted digit sum of a product of `digLoc`s is the product of
  the `Eloc`s, for arbitrary exponents and unit parts (HA's `sum_maskProd_digCoef`, generalized);
* `sum_maskProd_digCoefNu`: `∑_v maskProd(v) · digCoefNu(v, ν) = Eprod g (𝔟,1) (rowOf ν)`
  (needs good primes: `12 ∣ n`, `N₀ ≥ cutN`). -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Local: invariance of `Eloc` under sixth powers of `S`-units -/

section loc

variable {v : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (g : AllowedGen ι 𝔪)

include h hω

/-- `χ_P(res(t u⁶)) = χ_P(res t)` for a `P`-integral `t` and an `S`-unit `u`. -/
theorem chi_res_unit_six {t : F} (ht : v.valuation F t ≤ 1) (u : (SInt 𝔪)ˣ) :
    C3I.chi ι h hω (L3V.res 𝔪 v (t * ((u : SInt 𝔪) : F) ^ 6)) =
      C3I.chi ι h hω (L3V.res 𝔪 v t) := by
  have hu : v.valuation F ((((u : SInt 𝔪) ^ 6 : SInt 𝔪)) : F) ≤ 1 := C3I.val_le_one h.notS _
  have h6 := C3I.sext_unit_six (ι := ι) h hω u
  rw [← C3I.chi_mk h hω] at h6
  rw [← Subalgebra.coe_pow, L3V.res_mul h.notS ht hu, L3V.res_of_SInt h.notS, map_mul, h6,
    mul_one]

/-- **`Eloc_P(k, e₀, t u⁶) = Eloc_P(k, e₀, t)`** for a `P`-unit `t` and `u ∈ U_S`. -/
theorem Eloc_unit_six (k : ℕ) (e₀ : ℤ) {t : F} (ht : v.valuation F t = 1) (u : (SInt 𝔪)ˣ) :
    L3V.Eloc g v.asIdeal k e₀ (t * ((u : SInt 𝔪) : F) ^ 6) = L3V.Eloc g v.asIdeal k e₀ t := by
  haveI := C3I.finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have ht' : v.valuation F (t * ((u : SInt 𝔪) : F) ^ 6) = 1 := by
    rw [map_mul, map_pow, C3I.val_unit h, one_pow, mul_one, ht]
  have hχ := chi_res_unit_six (ι := ι) h hω ht.le u
  have hW : L3V.Wsph g v.asIdeal e₀ (t * ((u : SInt 𝔪) : F) ^ 6) = L3V.Wsph g v.asIdeal e₀ t := by
    rcases lt_or_ge e₀ 0 with he | he
    · rw [L3V.Wsph_neg h g he, L3V.Wsph_neg h g he]
    · rw [L3V.Wsph_eq h hω g he, L3V.Wsph_eq h hω g he, hχ]
  by_cases hk : k = 0
  · unfold L3V.Eloc; rw [if_pos hk, if_pos hk, hW]
  · rw [L3V.Eloc_split h hω g hk, L3V.Eloc_split h hω g hk, hW]
    congr 1
    rcases lt_or_ge (e₀ + 2) 0 with he | he
    · rw [L3V.Rsum_neg h hω g he, L3V.Rsum_neg h hω g he]
    · rw [L3V.Rsum_monomial h hω g he ht', L3V.Rsum_monomial h hω g he ht, hχ]

omit hω in
/-- `v_P(ν(r, z)) = e0 r z P` at a good prime. -/
theorem vP_nu_good (r z : RowClass 𝔪) :
    L3V.vP v.asIdeal (L3V.nu g r z) = L3V.e0 r z v.asIdeal := by
  have hrep : L3V.vP v.asIdeal ((z.2.rep : SInt 𝔪) : F) = 0 := by
    unfold SClass.rep; exact L3V.vP_unit h _
  have hx := C3B.gen_ne_zero g z.1.1 z.1.2
  have hb := C3B.gen_ne_zero g r.1.1 r.1.2
  have hr := L3V.rep_ne_zero z.2
  unfold L3V.nu rowElt L3V.e0
  rw [Subalgebra.coe_mul, div_eq_mul_inv,
    L3V.vP_mul (mul_ne_zero hr hx) (inv_ne_zero (pow_ne_zero _ hb)), L3V.vP_mul hr hx,
    L3V.vP_inv, pow_two, L3V.vP_mul hb hb, hrep, L3V.vP_gen h g _ z.1.2, L3V.vP_gen h g _ r.1.2]
  ring

omit hω in
/-- The unit part `ν(r,z) · p^{−e0}` of the frozen product is a `P`-unit. -/
theorem val_tz_good (r z : RowClass 𝔪) :
    v.valuation F (L3V.nu g r z * (g.gen v.asIdeal : F) ^ (-(L3V.e0 r z v.asIdeal))) = 1 := by
  rw [← vP_nu_good h g r z]
  exact L3V.val_unitPart h g (L3V.nu_ne_zero g r z)

end loc

/-! ### The coefficient at `ν` -/

theorem eNu_eq_e0 (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (ν : {ν : SInt 𝔪 // ν ≠ 0}) (P : Ideal (𝓞 F)) :
    eNu h𝔪 g 𝔟 ν P = L3V.e0 ((⟨𝔟, h𝔟⟩, 1) : RowClass 𝔪) (H0.rowOf h𝔪 g ν) P := rfl

/-- **The digit sum of a product of per-digit local values**, for arbitrary exponents `e` and
unit parts `t`, over any finite set of primes `S ⊇ supp 𝔟`: pure distributivity. -/
theorem sum_maskProd_digLoc (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (S : Finset (Ideal (𝓞 F))) (hTS : (normalizedFactors 𝔟).toFinset ⊆ S)
    (e : Ideal (𝓞 F) → ℤ) (t : Ideal (𝓞 F) → F) :
    ∑ᶠ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * ∏ P ∈ S, H.digLoc g 𝔟 v P (e P) (t P) =
      ∏ P ∈ S, L3V.Eloc g P ((normalizedFactors 𝔟).count P) (e P) (t P) := by
  haveI : ∀ P : {P : Ideal (𝓞 F) // P ∈ (normalizedFactors 𝔟).toFinset},
      Fintype (SInt 𝔪 ⧸ P.1.map (algebraMap (𝓞 F) (SInt 𝔪))) := fun P =>
    @Fintype.ofFinite _
      (C3M.finite_quot (C3M.exterior_of_mem_factors h𝔟 (Multiset.mem_toFinset.1 P.2)).2)
  rw [finsum_eq_sum_of_fintype]
  set T := (normalizedFactors 𝔟).toFinset with hT
  set A : ℂ := ∏ P ∈ S \ T, L3V.Eloc g P ((normalizedFactors 𝔟).count P) (e P) (t P) with hA
  have hdig : ∀ v : H.Dig 𝔪 𝔟, ∏ P ∈ S, H.digLoc g 𝔟 v P (e P) (t P) =
      A * ∏ P : {P : Ideal (𝓞 F) // P ∈ T},
        (if v P = 0 then L3V.Wsph g P.1 (e P.1) (t P.1)
          else L3V.Wweyl g P.1 (e P.1) (t P.1) (v P)) := by
    intro v
    rw [← Finset.prod_sdiff hTS]
    congr 1
    · refine Finset.prod_congr rfl fun P hP => ?_
      have hPT : P ∉ T := (Finset.mem_sdiff.1 hP).2
      have hc : (normalizedFactors 𝔟).count P = 0 :=
        Multiset.count_eq_zero.2 fun hm => hPT (Multiset.mem_toFinset.2 hm)
      unfold H.digLoc L3V.Eloc
      rw [dif_neg hPT, hc, if_pos rfl]
    · rw [← Finset.prod_coe_sort T]
      refine Finset.prod_congr rfl fun P _ => ?_
      unfold H.digLoc
      rw [dif_pos P.2]
  have hsum : ∀ v : H.Dig 𝔪 𝔟,
      H.maskProd g 𝔟 v * ∏ P ∈ S, H.digLoc g 𝔟 v P (e P) (t P) =
      A * ∏ P : {P : Ideal (𝓞 F) // P ∈ T},
        (L3V.mask g P.1 ((normalizedFactors 𝔟).count P.1 % 6) (v P) *
          (if v P = 0 then L3V.Wsph g P.1 (e P.1) (t P.1)
            else L3V.Wweyl g P.1 (e P.1) (t P.1) (v P))) := by
    intro v
    rw [hdig v, Finset.prod_mul_distrib]
    unfold H.maskProd
    ring
  have hps := (Fintype.prod_sum (fun (P : {P : Ideal (𝓞 F) // P ∈ T})
      (d : SInt 𝔪 ⧸ P.1.map (algebraMap (𝓞 F) (SInt 𝔪))) =>
        L3V.mask g P.1 ((normalizedFactors 𝔟).count P.1 % 6) d *
          (if d = 0 then L3V.Wsph g P.1 (e P.1) (t P.1)
            else L3V.Wweyl g P.1 (e P.1) (t P.1) d))).symm
  have hloc : ∀ P : {P : Ideal (𝓞 F) // P ∈ T},
      ∑ d : SInt 𝔪 ⧸ P.1.map (algebraMap (𝓞 F) (SInt 𝔪)),
        L3V.mask g P.1 ((normalizedFactors 𝔟).count P.1 % 6) d *
          (if d = 0 then L3V.Wsph g P.1 (e P.1) (t P.1)
            else L3V.Wweyl g P.1 (e P.1) (t P.1) d) =
        L3V.Eloc g P.1 ((normalizedFactors 𝔟).count P.1) (e P.1) (t P.1) := by
    intro P
    have hc : (normalizedFactors 𝔟).count P.1 ≠ 0 :=
      (Multiset.count_pos.2 (Multiset.mem_toFinset.1 P.2)).ne'
    unfold L3V.Eloc
    rw [if_neg hc, finsum_eq_sum_of_fintype]
  have hfin : (∏ P : {P : Ideal (𝓞 F) // P ∈ T},
      ∑ d : SInt 𝔪 ⧸ P.1.map (algebraMap (𝓞 F) (SInt 𝔪)),
        L3V.mask g P.1 ((normalizedFactors 𝔟).count P.1 % 6) d *
          (if d = 0 then L3V.Wsph g P.1 (e P.1) (t P.1)
            else L3V.Wweyl g P.1 (e P.1) (t P.1) d)) =
      ∏ P ∈ T, L3V.Eloc g P ((normalizedFactors 𝔟).count P) (e P) (t P) := by
    rw [Finset.prod_congr rfl fun P _ => hloc P,
      Finset.prod_coe_sort T
        (fun P => L3V.Eloc g P ((normalizedFactors 𝔟).count P) (e P) (t P))]
  have hE : A * ∏ P ∈ T, L3V.Eloc g P ((normalizedFactors 𝔟).count P) (e P) (t P) =
      ∏ P ∈ S, L3V.Eloc g P ((normalizedFactors 𝔟).count P) (e P) (t P) := by
    rw [hA, Finset.prod_sdiff hTS]
  rw [Finset.sum_congr rfl fun v _ => hsum v, ← Finset.mul_sum, ← hE, ← hfin]
  congr 1
  convert hps

theorem factors_subset_mul (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    (normalizedFactors 𝔟).toFinset ⊆
      (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset := by
  intro P hP
  have h1 : P ∈ L3V.prim 𝔟 := hP
  have h2 : P ∈ L3V.prim ((H0.rowOf h𝔪 g ν).1.1 * 𝔟) := by
    rw [L3V.mem_prim_iff] at h1 ⊢
    rw [L3V.cnt_mul (H0.rowOf h𝔪 g ν).1.2.1 h𝔟.1]; omega
  exact h2

/-- `ν = u⁶ · rowElt (rowOf ν)` with `u ∈ U_S`. -/
theorem exists_unit_six (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ∃ u : (SInt 𝔪)ˣ, ((ν : SInt 𝔪) : F) =
      (rowElt g (H0.rowOf h𝔪 g ν) : F) * ((u : SInt 𝔪) : F) ^ 6 := by
  obtain ⟨δ, hδ⟩ := (H0.gamOf h𝔪 g ν).2
  refine ⟨H0.uInt δ, ?_⟩
  rw [H0.coe_eq_gamOf_mul h𝔪 g ν, ← hδ, mul_comm]
  simp only [powMonoidHom_apply, H0.coe_uInt, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

section good

variable (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] {N₀ : ℕ}
  (hN₀ : C3I.cutN F ≤ N₀) (hsm : SmallPrimesDvd N₀ 𝔪)

include hn0 hn hN₀ hsm

/-- **The reflected digit sum at `ν`**: the mask-weighted sum of the per-digit coefficients
`digCoefNu` is the frozen exterior product at the row class of `ν`. -/
theorem finsum_maskProd_mul_digCoefNu_eq_eprod_oai (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ∑ᶠ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * digCoefNu h𝔪 g 𝔟 v ν =
      L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (H0.rowOf h𝔪 g ν) := by
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  obtain ⟨u, hu⟩ := exists_unit_six h𝔪 g ν
  set z := H0.rowOf h𝔪 g ν with hz
  set r : RowClass 𝔪 := (⟨𝔟, h𝔟⟩, 1) with hr
  have hzr : IsExterior 𝔪 (z.1.1 * 𝔟) := C3B.isExterior_mul z.1.2 h𝔟
  unfold digCoefNu
  rw [sum_maskProd_digLoc g h𝔟 _ (factors_subset_mul h𝔪 g h𝔟 ν)]
  unfold L3V.Eprod
  refine Finset.prod_congr rfl fun P hP => ?_
  obtain ⟨hPp, _⟩ := L3V.prime_of_mem_prim hP
  have hPe := L3V.exterior_of_prim hzr hP
  have hgood := C3I.good_of_exterior n hn0 hn hN₀ hsm hPp hPe
  have ht : tNu h𝔪 g 𝔟 ν P =
      L3V.nu g r z * (g.gen P : F) ^ (-(L3V.e0 r z P)) * ((u : SInt 𝔪) : F) ^ 6 := by
    unfold tNu L3V.nu
    rw [hu, eNu_eq_e0 h𝔪 g h𝔟 ν P]
    ring
  rw [ht, eNu_eq_e0 h𝔪 g h𝔟 ν P]
  exact Eloc_unit_six (v := ⟨P, hPp, hPe.1⟩) hgood hω g _ _ (val_tz_good hgood g r z) u

end good

end

end ArtinKP.HB
end

theorem solution.{u_1} : type_of% @ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod_oai.{u_1} := @ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod_oai.{u_1}
