-- Prove2me | solution 1 for ArtinKP.HB.kpCutNu_of_autCut2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:12.035594+00:00
-- url     : https://prove2.me/submissions/72bf2aed-27eb-45e9-bee8-4bb646e70d8d

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_H_sum_maskProd_sAddChar
import Theorems.Thm_ArtinKP_H_summable_forward_coef
import Theorems.Thm_ArtinKP_H_summable_reflected_coef
import Theorems.Thm_ArtinKP_HB_finsum_maskProd_mul_digCoefNu_eq_eprod

section
-- module Solutions.Artin.T12.L3X_Meas
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The finite norm -/

theorem SFin.mk_mul (x y : Fˣ) : SFin.mk 𝔪 k (x * y) = SFin.mk 𝔪 k x + SFin.mk 𝔪 k y := rfl

theorem SFin.mk_one : SFin.mk 𝔪 k 1 = 0 := rfl

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Emb
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sEmb_of_ne {x : F} (hx : x ≠ 0) :
    sEmb 𝔪 k x = (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)),
      SFin.mk 𝔪 k (Units.mk0 x hx)) := by
  rw [sEmb, dif_neg hx]

theorem sEmb_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    sEmb 𝔪 k (x * y) = sEmb 𝔪 k x + sEmb 𝔪 k y := by
  rw [sEmb_of_ne (mul_ne_zero hx hy), sEmb_of_ne hx, sEmb_of_ne hy]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext w
    simp only [Prod.fst_add, Pi.add_apply, map_mul]
    rw [Real.log_mul ((map_ne_zero w).2 hx) ((map_ne_zero w).2 hy)]
    ring
  · funext w
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_mul]
    exact Complex.arg_mul_coe_angle ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)
  · show SFin.mk 𝔪 k (Units.mk0 (x * y) _) = SFin.mk 𝔪 k _ + SFin.mk 𝔪 k _
    rw [← SFin.mk_mul]
    congr 1
    ext; simp

theorem sEmb_one : sEmb 𝔪 k (1 : F) = 0 := by
  rw [sEmb_of_ne one_ne_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext w; simp
  · funext w; simp
  · show SFin.mk 𝔪 k (Units.mk0 1 _) = 0
    rw [← SFin.mk_one (𝔪 := 𝔪) (k := k)]
    congr 1
    ext; simp

theorem sEmb_inv {x : F} (hx : x ≠ 0) : sEmb 𝔪 k x⁻¹ = -sEmb 𝔪 k x := by
  have h := sEmb_mul (𝔪 := 𝔪) (k := k) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, sEmb_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem sEmb_div {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    sEmb 𝔪 k (x / y) = sEmb 𝔪 k x - sEmb 𝔪 k y := by
  rw [div_eq_mul_inv, sEmb_mul hx (inv_ne_zero hy), sEmb_inv hy, sub_eq_add_neg]

/-! ### Absolute values and valuations -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.C3B_Norm
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

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
-- module Solutions.Artin.T12.C3M_Base
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L2B_Bound
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinPrimitiveRoots.L2B
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
-- module Solutions.Artin.KP.K_Bessel
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 1: the K-Bessel function

`besselK μ z = ½ ∫_0^∞ t^{μ−1} exp(−(z/2)(t + 1/t)) dt` (`μ : ℂ`, `z : ℝ`; meaningful for `z > 0`),
defined as half the Mellin transform of `besselKer z`.  Mathlib only.

* `besselK_differentiable`: entire in `μ`;
* `besselK_neg`: `K_{−μ} = K_μ`;
* `besselK_ofReal`, `besselKR_pos`: real and positive for real `μ`;
* `norm_besselK_le`: `‖K_μ(z)‖ ≤ K_{Re μ}(z)`;
* `besselKR_le_exp_mul`: `K_μ(z) ≤ e^{−(z−z₀)} K_μ(z₀)` for `z ≥ z₀ > 0`;
* `besselKR_le_gamma`: `K_μ(z) ≤ ½ Γ(|μ|) (z/2)^{−|μ|}` (`μ ≠ 0`);
* `besselKR_le_two_mul`: `K_μ(z) ≤ 2 K_M(z)` for `|μ| ≤ M`;
* `besselKR_le_min`: `K_μ(z) ≤ C min(z^{−|μ|}, z^{−N})` uniformly for `a ≤ |μ| ≤ M ≤ N`;
* `besselK_eq_schlafli`: the Schläfli form `½ (z/2)^{−μ} ∫ t^{μ−1} exp(−t − z²/(4t)) dt`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter Asymptotics Topology

noncomputable section

theorem besselK_ofReal (μ z : ℝ) : besselK (μ : ℂ) z = (besselKR μ z : ℂ) := by
  unfold besselK besselKR mellin
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  · norm_num
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [smul_eq_mul, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_cpow ht'.le]
    push_cast
    rfl

end

end ArtinKP.K
end

section
-- module Solutions.Artin.T12.L3X_V
/-! # L3X_V: the radial profile `V` of (5.21) and its Mellin transform

* `Vprof w₀ 𝔪 k κ u`: the sheet integral over `X_u` of `1_{y_f = 0} ∏_w κ(|y_w|_w)`.
* `Vprof_eq`: `V(u) = (2π)^{|W|} ∫_{x' ∈ ℝ^{W∖w₀}} κ(e^{log u − Σx'}) ∏_{w'} κ(e^{x'_{w'}})`.
* `Vprof_mellin`: measurability and `V̂(s) = (2π)^{|W|} cκ^{|W|} (Aκ^{|W|})^s (Γ(s+5/6)Γ(s+7/6))^{|W|}`
  for `Re s > −5/6`, from `κ̂(s) = cκ Aκ^s Γ(s+5/6)Γ(s+7/6)` (Fubini; `κ ≥ 0`).
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The exponential substitution in the Mellin transform -/

theorem cpow_exp_eq (a : ℝ) (s : ℂ) :
    ((Real.exp a : ℝ) : ℂ) * ((Real.exp a : ℝ) : ℂ) ^ (s - 1) = Complex.exp (s * a) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos a).ne'),
    ← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; ring

theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ a : ℝ, Complex.exp (s * a) * f (Real.exp a) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [mellin, h]
  congr 1; funext a
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

theorem mellinConvergent_iff_exp (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun a : ℝ => Complex.exp (s * a) * f (Real.exp a)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  rw [Set.image_univ, Real.range_exp, integrableOn_univ] at h
  rw [MellinConvergent, h]
  refine integrable_congr (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [abs_of_pos (Real.exp_pos a), smul_eq_mul, Complex.real_smul, ← mul_assoc, cpow_exp_eq]

/-! ### The Mellin transform of `V` -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3J_Kappa
attribute [-instance] _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinKP.X.instSigmaFiniteXVol
/-! # L3J_Kappa: the κ-clauses of the corrected KP cut are satisfiable

`κ₀(t) = ∫ g_{5/6}(log t − y) g_{7/6}(y) dy`, with `g_a(b) = exp(a b − e^b)`, is the Mellin
convolution of `t^{5/6} e^{-t}` and `t^{7/6} e^{-t}`. So `mellin κ₀ s = Γ(s+5/6) Γ(s+7/6)` for
`Re s > −5/6`, and `κ₀(t) ≤ C_N min(t^α, t^{-N})` for every `0 < α ≤ 5/6` and every `N > 0`.
It is the archimedean Whittaker profile `t K_{1/3}(2√t)` of (5.7)/(5.11), up to normalization. -/

namespace ArtinPrimitiveRoots.L3J

open MeasureTheory Set

noncomputable section

theorem gA_pos (a b : ℝ) : 0 < gA a b := Real.exp_pos _

theorem continuous_gA (a : ℝ) : Continuous (gA a) := by
  unfold gA; fun_prop

/-- `exp(s b) g_a(b) = exp((s + a) b) exp(−e^b)`. -/
theorem cexp_mul_gA (s : ℂ) (a b : ℝ) :
    Complex.exp (s * b) * (gA a b : ℂ) =
      Complex.exp ((s + a) * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ) := by
  unfold gA
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `Γ(c)` in exponential coordinates. -/
theorem gamma_exp {c : ℂ} (hc : 0 < c.re) :
    Integrable (fun b : ℝ => Complex.exp (c * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ)) ∧
    ∫ b : ℝ, Complex.exp (c * b) * ((Real.exp (-Real.exp b) : ℝ) : ℂ) = Complex.Gamma c := by
  have hm : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) c := by
    unfold MellinConvergent
    refine (Complex.GammaIntegral_convergent hc).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  refine ⟨(L3X.mellinConvergent_iff_exp _ c).1 hm, ?_⟩
  rw [Complex.Gamma_eq_integral hc, Complex.GammaIntegral_eq_mellin, L3X.mellin_eq_integral_exp]

theorem integrable_cexp_gA {s : ℂ} {a : ℝ} (h : 0 < s.re + a) :
    Integrable (fun b : ℝ => Complex.exp (s * b) * (gA a b : ℂ)) := by
  have := (gamma_exp (c := s + a) (by simpa using h)).1
  simpa only [cexp_mul_gA] using this

theorem integral_cexp_gA {s : ℂ} {a : ℝ} (h : 0 < s.re + a) :
    ∫ b : ℝ, Complex.exp (s * b) * (gA a b : ℂ) = Complex.Gamma (s + a) := by
  have := (gamma_exp (c := s + a) (by simpa using h)).2
  simpa only [cexp_mul_gA] using this

theorem integrable_gA {a : ℝ} (ha : 0 < a) : Integrable (gA a) := by
  have h := (integrable_cexp_gA (s := 0) (a := a) (by simpa using ha)).norm
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [zero_mul, Complex.exp_zero, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (gA_pos a b).le]

theorem measurable_kappa0 : Measurable kappa0 := by
  have hfm : Measurable (fun q : ℝ × ℝ => gA (5 / 6) (q.1 - q.2) * gA (7 / 6) q.2) := by
    have : Continuous (fun q : ℝ × ℝ => gA (5 / 6) (q.1 - q.2) * gA (7 / 6) q.2) :=
      ((continuous_gA _).comp (continuous_fst.sub continuous_snd)).mul
        ((continuous_gA _).comp continuous_snd)
    exact this.measurable
  have : Measurable (fun x : ℝ => ∫ y, gA (5 / 6) (x - y) * gA (7 / 6) y) :=
    (hfm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  exact this.comp Real.measurable_log

theorem kappa0_nonneg (t : ℝ) : 0 ≤ kappa0 t :=
  integral_nonneg fun y => (mul_pos (gA_pos _ _) (gA_pos _ _)).le

/-- The pointwise identity `g_{5/6}(x−y) g_{7/6}(y) = e^{5x/6} exp(y/3 − e^{x−y} − e^y)`. -/
theorem gA_mul_eq (x y : ℝ) :
    gA (5 / 6) (x - y) * gA (7 / 6) y =
      Real.exp (5 / 6 * x) * Real.exp (1 / 3 * y - Real.exp (x - y) - Real.exp y) := by
  unfold gA
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem kappa0_le_small (x : ℝ) :
    kappa0 (Real.exp x) ≤ Real.exp (5 / 6 * x) * ∫ y, gA (1 / 3) y := by
  unfold kappa0
  rw [Real.log_exp, ← integral_const_mul]
  have hi : Integrable (fun y => Real.exp (5 / 6 * x) * gA (1 / 3) y) :=
    (integrable_gA (by norm_num)).const_mul _
  have hle : ∀ y, gA (5 / 6) (x - y) * gA (7 / 6) y ≤ Real.exp (5 / 6 * x) * gA (1 / 3) y := by
    intro y
    rw [gA_mul_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have := Real.exp_pos (x - y)
    linarith
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
    (mul_pos (gA_pos _ _) (gA_pos _ _)).le) hi (Filter.Eventually.of_forall hle)

/-- `e^{x−y} + e^y ≥ e^{x/2} + e^y/2`. -/
theorem exp_sum_ge (x y : ℝ) :
    Real.exp (x / 2) + Real.exp y / 2 ≤ Real.exp (x - y) + Real.exp y := by
  set A := Real.exp (x - y)
  set B := Real.exp y
  set E := Real.exp (x / 2)
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 < B := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hAB : A * B = E * E := by
    simp only [A, B, E]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h2 : E ≤ A + B / 2 := by
    nlinarith [sq_nonneg (A - B / 2), sq_nonneg (E - (A + B / 2))]
  linarith

theorem kappa0_le_large (x : ℝ) :
    kappa0 (Real.exp x) ≤
      Real.exp (5 / 6 * x) * Real.exp (-Real.exp (x / 2)) *
        (Real.exp (Real.log 2 / 3) * ∫ y, gA (1 / 3) y) := by
  unfold kappa0
  rw [Real.log_exp]
  set K := Real.exp (5 / 6 * x) * Real.exp (-Real.exp (x / 2)) * Real.exp (Real.log 2 / 3)
  have hshift : ∀ y, Real.exp (1 / 3 * y - Real.exp y / 2) =
      Real.exp (Real.log 2 / 3) * gA (1 / 3) (y - Real.log 2) := by
    intro y
    unfold gA
    rw [← Real.exp_add, show Real.exp (y - Real.log 2) = Real.exp y / 2 by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
    congr 1; ring
  have hi : Integrable (fun y => K * gA (1 / 3) (y - Real.log 2)) :=
    ((integrable_gA (by norm_num)).comp_sub_right _).const_mul _
  have hle : ∀ y, gA (5 / 6) (x - y) * gA (7 / 6) y ≤ K * gA (1 / 3) (y - Real.log 2) := by
    intro y
    rw [gA_mul_eq]
    have h1 : Real.exp (1 / 3 * y - Real.exp (x - y) - Real.exp y) ≤
        Real.exp (-Real.exp (x / 2)) * Real.exp (1 / 3 * y - Real.exp y / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := exp_sum_ge x y
      linarith
    rw [hshift] at h1
    calc Real.exp (5 / 6 * x) * Real.exp (1 / 3 * y - Real.exp (x - y) - Real.exp y)
        ≤ Real.exp (5 / 6 * x) * (Real.exp (-Real.exp (x / 2)) *
            (Real.exp (Real.log 2 / 3) * gA (1 / 3) (y - Real.log 2))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = K * gA (1 / 3) (y - Real.log 2) := by simp only [K]; ring
  have := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
    (mul_pos (gA_pos (5 / 6) (x - y)) (gA_pos (7 / 6) y)).le) hi (Filter.Eventually.of_forall hle)
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => gA (1 / 3) y)]
  simp only [K]; ring

/-- `t^{a} e^{-√t} ≤ ⌈2a⌉₊!` for `t ≥ 1`, `a ≥ 0`. -/
theorem rpow_mul_exp_neg_sqrt_le {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 1 ≤ t) :
    t ^ a * Real.exp (-Real.sqrt t) ≤ (Nat.ceil (2 * a)).factorial := by
  set u := Real.sqrt t
  have hu1 : 1 ≤ u := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ht
  have hu0 : 0 ≤ u := by linarith
  set m := Nat.ceil (2 * a)
  have htu : t = u ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.sq_sqrt (by linarith)]
  have h1 : t ^ a = u ^ (2 * a) := by
    rw [htu, ← Real.rpow_mul hu0]
  have h2 : u ^ (2 * a) ≤ u ^ (m : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (Nat.le_ceil _)
  have h3 : u ^ (m : ℝ) = u ^ m := Real.rpow_natCast u m
  have h4 : u ^ m / m.factorial ≤ Real.exp u := Real.pow_div_factorial_le_exp (x := u) hu0 m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h4
  rw [h1]
  calc u ^ (2 * a) * Real.exp (-u) ≤ u ^ m * Real.exp (-u) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ ≤ Real.exp u * m.factorial * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = m.factorial := by rw [mul_comm (Real.exp u), mul_assoc, ← Real.exp_add]; simp

theorem kappa0_bound {α : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) {N : ℝ} (hN : 0 < N) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → kappa0 t ≤ C * min (t ^ α) (t ^ (-N)) := by
  set I := ∫ y, gA (1 / 3) y
  have hI : 0 ≤ I := integral_nonneg fun y => (gA_pos _ _).le
  set M : ℝ := ((Nat.ceil (2 * (N + 5 / 6))).factorial : ℝ)
  refine ⟨max I (Real.exp (Real.log 2 / 3) * I * M), fun t ht => ?_⟩
  have hx := Real.exp_log ht
  set x := Real.log t
  rcases le_or_gt t 1 with h1 | h1
  · -- small `t`: `κ₀(t) ≤ I t^{5/6} ≤ I t^α`, and the min is `t^α`
    have hmin : min (t ^ α) (t ^ (-N)) = t ^ α := by
      refine min_eq_left ?_
      have : t ^ α ≤ 1 := Real.rpow_le_one ht.le h1 hα.le
      have : 1 ≤ t ^ (-N) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht h1 (by linarith)
      linarith
    rw [hmin]
    have hk := kappa0_le_small x
    rw [hx] at hk
    have he : Real.exp (5 / 6 * x) = t ^ (5 / 6 : ℝ) := by
      rw [← hx, ← Real.exp_mul]; ring_nf
    rw [he] at hk
    have hpow : t ^ (5 / 6 : ℝ) ≤ t ^ α := Real.rpow_le_rpow_of_exponent_ge ht h1 hα'
    calc kappa0 t ≤ t ^ (5 / 6 : ℝ) * I := hk
      _ ≤ t ^ α * I := mul_le_mul_of_nonneg_right hpow hI
      _ = I * t ^ α := mul_comm _ _
      _ ≤ max I (Real.exp (Real.log 2 / 3) * I * M) * t ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le _)
  · -- large `t`: `κ₀(t) ≤ 2^{1/3} I t^{5/6} e^{−√t} ≤ 2^{1/3} I M t^{−N}`
    have hmin : min (t ^ α) (t ^ (-N)) = t ^ (-N) := by
      refine min_eq_right ?_
      have : t ^ (-N) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith)
      have : 1 ≤ t ^ α := Real.one_le_rpow h1.le hα.le
      linarith
    rw [hmin]
    have hk := kappa0_le_large x
    rw [hx] at hk
    have he : Real.exp (5 / 6 * x) = t ^ (5 / 6 : ℝ) := by
      rw [← hx, ← Real.exp_mul]; ring_nf
    have hs : Real.exp (x / 2) = Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, ← hx, ← Real.exp_mul]; ring_nf
    rw [he, hs] at hk
    have hb := rpow_mul_exp_neg_sqrt_le (a := N + 5 / 6) (by linarith) h1.le
    have hsplit : t ^ (5 / 6 : ℝ) = t ^ (N + 5 / 6) * t ^ (-N) := by
      rw [← Real.rpow_add ht]; ring_nf
    have hc : 0 ≤ Real.exp (Real.log 2 / 3) * I := mul_nonneg (Real.exp_pos _).le hI
    calc kappa0 t ≤ t ^ (5 / 6 : ℝ) * Real.exp (-Real.sqrt t) * (Real.exp (Real.log 2 / 3) * I) := hk
      _ = (t ^ (N + 5 / 6) * Real.exp (-Real.sqrt t)) * (Real.exp (Real.log 2 / 3) * I) *
            t ^ (-N) := by rw [hsplit]; ring
      _ ≤ M * (Real.exp (Real.log 2 / 3) * I) * t ^ (-N) := by
          gcongr
      _ = Real.exp (Real.log 2 / 3) * I * M * t ^ (-N) := by ring
      _ ≤ max I (Real.exp (Real.log 2 / 3) * I * M) * t ^ (-N) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

/-- The Mellin transform: `mellin κ₀ s = Γ(s + 5/6) Γ(s + 7/6)` for `Re s > −5/6`. -/
theorem kappa0_mellin (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (fun t => (kappa0 t : ℂ)) s ∧
      mellin (fun t => (kappa0 t : ℂ)) s =
        Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) := by
  set G₁ : ℝ → ℂ := fun b => Complex.exp (s * b) * (gA (5 / 6) b : ℂ)
  set G₂ : ℝ → ℂ := fun b => Complex.exp (s * b) * (gA (7 / 6) b : ℂ)
  have hG₁ : Integrable G₁ := integrable_cexp_gA (by linarith)
  have hG₂ : Integrable G₂ := integrable_cexp_gA (by linarith)
  have iG₁ : ∫ b, G₁ b = Complex.Gamma (s + 5 / 6) := by
    rw [integral_cexp_gA (by linarith)]; push_cast; ring_nf
  have iG₂ : ∫ b, G₂ b = Complex.Gamma (s + 7 / 6) := by
    rw [integral_cexp_gA (by linarith)]; push_cast; ring_nf
  set f₂ : ℝ × ℝ → ℂ := fun q => G₁ (q.1 - q.2) * G₂ q.2
  have hf₂m : AEStronglyMeasurable f₂ (volume.prod volume) := by
    have hc : Continuous f₂ := by
      simp only [f₂, G₁, G₂]
      have := continuous_gA (5 / 6); have := continuous_gA (7 / 6)
      fun_prop
    exact hc.aestronglyMeasurable
  have hf₂i : Integrable f₂ (volume.prod volume) := by
    rw [integrable_prod_iff' hf₂m]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · exact (hG₁.comp_sub_right y).mul_const (G₂ y)
    · have : (fun y : ℝ => ∫ x, ‖f₂ (x, y)‖) = fun y => (∫ b, ‖G₁ b‖) * ‖G₂ y‖ := by
        funext y
        simp only [f₂, norm_mul]
        rw [integral_mul_const, integral_sub_right_eq_self (fun b => ‖G₁ b‖)]
      rw [this]
      exact hG₂.norm.const_mul _
  have hpt : ∀ x : ℝ, Complex.exp (s * x) * ((kappa0 (Real.exp x) : ℝ) : ℂ) = ∫ y, f₂ (x, y) := by
    intro x
    simp only [kappa0, Real.log_exp]
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [f₂, G₁, G₂, Complex.ofReal_mul]
    rw [show Complex.exp (s * (x : ℂ)) = Complex.exp (s * ((x - y : ℝ) : ℂ)) *
        Complex.exp (s * (y : ℂ)) by rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  refine ⟨?_, ?_⟩
  · rw [L3X.mellinConvergent_iff_exp]
    simp only [hpt]
    exact hf₂i.integral_prod_left
  · rw [L3X.mellin_eq_integral_exp]
    simp only [hpt]
    rw [integral_integral_swap (f := fun x y => f₂ (x, y))
      (by have : Function.uncurry (fun x y => f₂ (x, y)) = f₂ := by funext q; rfl
          rw [this]; exact hf₂i)]
    have hin : ∀ y : ℝ, ∫ x, f₂ (x, y) = Complex.Gamma (s + 5 / 6) * G₂ y := by
      intro y
      simp only [f₂]
      rw [integral_mul_const, integral_sub_right_eq_self G₁, iG₁]
    simp only [hin]
    rw [integral_const_mul, iG₂]

end

end ArtinPrimitiveRoots.L3J
end

section
-- module Solutions.Artin.KP.K_Kappa
/-! # WP-K, file 3: the profile `κ`

* `cc a b x = ∫ g_a(x−y) g_b(y) dy` (`g_a(u) = exp(a u − e^u)`, `L3J.gA`): the Mellin convolution of
  `t^a e^{−t}` and `t^b e^{−t}` in the variable `x = log t`; `L3J.kappa0 (e^x) = cc (5/6) (7/6) x`.
  `hasDerivAt_cc`: `cc a b ' = a · cc a b − cc (a+1) b`; `contDiff_cc`: smooth;
  `cc_bound`: `cc a b x ≤ C min(e^{αx}, e^{−Nx})` for `a ≠ b`, `0 < α ≤ min a b`.
* `kappa0_eq_bessel`: `κ₀(t) = 2 t K_{1/3}(2√t)`.
* `kappaB c t = t · K_{1/3}(c √t)` (`t > 0`; `0` otherwise) `= (2/c²) κ₀(c² t/4)`;
  `kappaB_clauses`: all `κ`-clauses of the frozen goal with `cκ = 2/c²`, `Aκ = (c²/4)⁻¹ = 4/c²`
  (for `c = 4π`: `cκ = 1/(8π²)`, `Aκ = 1/(4π²)`).
* `kappaB_contDiff`, `kappaB_iteratedDeriv_bound`, `kappaB_iteratedDeriv_bound_shift`,
  `kappaB_ofReal_iteratedDeriv_bound_shift`: `s ↦ κ(e^{x+s})` is smooth and its derivatives of
  order `≤ 2` are `≤ C min(e^{αx}, e^{−Nx})`, `0 < α ≤ 5/6`, any `N > 0`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open ArtinPrimitiveRoots.L3J (gA kappa0 gA_pos continuous_gA integrable_gA)

noncomputable section

/-! ## The functions `g_a` -/

/-! ## The family `cc a b` -/

theorem kappa0_eq_cc (t : ℝ) : kappa0 t = cc (5 / 6) (7 / 6) (Real.log t) := rfl

theorem kappa0_exp (x : ℝ) : kappa0 (Real.exp x) = cc (5 / 6) (7 / 6) x := by
  rw [kappa0_eq_cc, Real.log_exp]

/-! ## Bounds for `cc a b` -/

theorem gA_mul_eq' (a b x y : ℝ) :
    gA a (x - y) * gA b y =
      Real.exp (a * x) * Real.exp ((b - a) * y - Real.exp (x - y) - Real.exp y) := by
  unfold gA
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-! ## `κ₀` is a K-Bessel function -/

/-- `K_μ(z) = ½ ∫_ℝ e^{μ a} exp(−(z/2)(e^a + e^{−a})) da`. -/
theorem besselKR_eq_integral_exp (μ z : ℝ) :
    besselKR μ z = 1 / 2 * ∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) := by
  have h := besselK_ofReal μ z
  unfold besselK at h
  rw [ArtinPrimitiveRoots.L3X.mellin_eq_integral_exp] at h
  have e : (∫ a : ℝ, Complex.exp ((μ : ℂ) * a) * (besselKer z (Real.exp a) : ℂ)) =
      ((∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    push_cast
    rfl
  rw [e] at h
  have h' : ((1 / 2 * ∫ a : ℝ, Real.exp (μ * a) * besselKer z (Real.exp a) : ℝ) : ℂ) =
      (besselKR μ z : ℂ) := by
    rw [← h]; push_cast; ring
  exact_mod_cast h'.symm

/-- `κ₀(e^x) = 2 e^x K_{1/3}(2 e^{x/2})`. -/
theorem kappa0_exp_eq_bessel (x : ℝ) :
    kappa0 (Real.exp x) = 2 * Real.exp x * besselKR (1 / 3) (2 * Real.exp (x / 2)) := by
  rw [besselKR_eq_integral_exp,
    ← integral_sub_right_eq_self
      (fun a => Real.exp (1 / 3 * a) * besselKer (2 * Real.exp (x / 2)) (Real.exp a)) (x / 2),
    kappa0_exp]
  unfold cc
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [gA_mul_eq']
  have e1 : Real.exp (x / 2) * Real.exp (y - x / 2) = Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (x / 2) * (Real.exp (y - x / 2))⁻¹ = Real.exp (x - y) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hk : besselKer (2 * Real.exp (x / 2)) (Real.exp (y - x / 2)) =
      Real.exp (-(Real.exp y + Real.exp (x - y))) := by
    unfold besselKer
    congr 1
    rw [← e1, ← e2]; ring
  rw [hk, ← Real.exp_add, ← Real.exp_add]
  have e3 : Real.exp (5 / 6 * x + ((7 / 6 - 5 / 6) * y - Real.exp (x - y) - Real.exp y)) =
      Real.exp x * Real.exp (1 / 3 * (y - x / 2) + -(Real.exp y + Real.exp (x - y))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e3]; ring

/-- `κ₀(t) = 2 t K_{1/3}(2√t)` for `t > 0`. -/
theorem kappa0_eq_bessel {t : ℝ} (ht : 0 < t) :
    kappa0 t = 2 * t * besselKR (1 / 3) (2 * Real.sqrt t) := by
  have h := kappa0_exp_eq_bessel (Real.log t)
  rwa [Real.exp_half, Real.exp_log ht] at h

/-! ## The Bessel profile `κ(t) = t K_{1/3}(c√t)` -/

theorem kappaB_of_pos (c : ℝ) {t : ℝ} (ht : 0 < t) :
    kappaB c t = t * besselKR (1 / 3) (c * Real.sqrt t) := if_pos ht

/-- `κ(t) = (2/c²) κ₀(c² t / 4)`. -/
theorem kappaB_eq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    kappaB c t = 2 / c ^ 2 * kappa0 (c ^ 2 / 4 * t) := by
  have hL : 0 < c ^ 2 / 4 * t := by positivity
  have hs : Real.sqrt (c ^ 2 / 4 * t) = c / 2 * Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity), show c ^ 2 / 4 = (c / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [kappaB_of_pos c ht, kappa0_eq_bessel hL, hs, show 2 * (c / 2 * Real.sqrt t) = c * Real.sqrt t
    by ring]
  field_simp
  ring

theorem kappaB_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ kappaB c t := by
  by_cases ht : 0 < t
  · rw [kappaB_eq hc ht]
    exact mul_nonneg (by positivity) (ArtinPrimitiveRoots.L3J.kappa0_nonneg _)
  · simp [kappaB, ht]

theorem measurable_kappaB {c : ℝ} (hc : 0 < c) : Measurable (kappaB c) := by
  have h : kappaB c = fun t => if 0 < t then 2 / c ^ 2 * kappa0 (c ^ 2 / 4 * t) else 0 := by
    funext t
    by_cases ht : 0 < t
    · rw [kappaB_eq hc ht, if_pos ht]
    · simp [kappaB, ht]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((ArtinPrimitiveRoots.L3J.measurable_kappa0.comp (measurable_const.mul measurable_id)).const_mul _)
    measurable_const

theorem kappaB_mellin {c : ℝ} (hc : 0 < c) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (fun t => (kappaB c t : ℂ)) s ∧
      mellin (fun t => (kappaB c t : ℂ)) s =
        ((2 / c ^ 2 : ℝ) : ℂ) * (((c ^ 2 / 4)⁻¹ : ℝ) : ℂ) ^ s *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  have hL : 0 < c ^ 2 / 4 := by positivity
  obtain ⟨h1, h2⟩ := ArtinPrimitiveRoots.L3J.kappa0_mellin s hs
  have hEq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (((2 / c ^ 2 : ℝ) : ℂ) •
        (fun t : ℝ => (kappa0 t : ℂ)) (c ^ 2 / 4 * t)))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (kappaB c t : ℂ)) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [smul_eq_mul]
    rw [kappaB_eq hc ht']
    push_cast
    ring
  have hc1 : MellinConvergent (fun t : ℝ => ((2 / c ^ 2 : ℝ) : ℂ) •
      (fun t : ℝ => (kappa0 t : ℂ)) (c ^ 2 / 4 * t)) s :=
    ((MellinConvergent.comp_mul_left hL).2 h1).const_smul _
  refine ⟨IntegrableOn.congr_fun hc1 hEq measurableSet_Ioi, ?_⟩
  have hm : mellin (fun t => (kappaB c t : ℂ)) s =
      mellin (fun t : ℝ => ((2 / c ^ 2 : ℝ) : ℂ) •
        (fun t : ℝ => (kappa0 t : ℂ)) (c ^ 2 / 4 * t)) s := by
    unfold mellin
    exact (setIntegral_congr_fun measurableSet_Ioi hEq).symm
  rw [hm, mellin_const_smul, mellin_comp_mul_left (fun t : ℝ => (kappa0 t : ℂ)) s hL, h2, smul_eq_mul, smul_eq_mul,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hL.le, Complex.cpow_neg]
  ring

theorem min_rpow_scale {L α N t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    min ((L * t) ^ α) ((L * t) ^ (-N)) ≤ max (L ^ α) (L ^ (-N)) * min (t ^ α) (t ^ (-N)) := by
  have hmx : 0 ≤ max (L ^ α) (L ^ (-N)) := le_max_of_le_left (Real.rpow_nonneg hL.le _)
  rw [mul_min_of_nonneg _ _ hmx, Real.mul_rpow hL.le ht.le, Real.mul_rpow hL.le ht.le]
  exact min_le_min (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _))

theorem kappaB_bound {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) {N : ℝ}
    (hN : 0 < N) : ∃ C : ℝ, ∀ t : ℝ, 0 < t → kappaB c t ≤ C * min (t ^ α) (t ^ (-N)) := by
  have hL : 0 < c ^ 2 / 4 := by positivity
  obtain ⟨C, hC⟩ := ArtinPrimitiveRoots.L3J.kappa0_bound hα hα' hN
  refine ⟨2 / c ^ 2 * (|C| * max ((c ^ 2 / 4) ^ α) ((c ^ 2 / 4) ^ (-N))), fun t ht => ?_⟩
  rw [kappaB_eq hc ht]
  have hLt : 0 < c ^ 2 / 4 * t := by positivity
  have h1 := hC _ hLt
  have hmin0 : 0 ≤ min ((c ^ 2 / 4 * t) ^ α) ((c ^ 2 / 4 * t) ^ (-N)) :=
    le_min (Real.rpow_nonneg hLt.le _) (Real.rpow_nonneg hLt.le _)
  have h2 : C * min ((c ^ 2 / 4 * t) ^ α) ((c ^ 2 / 4 * t) ^ (-N)) ≤
      |C| * min ((c ^ 2 / 4 * t) ^ α) ((c ^ 2 / 4 * t) ^ (-N)) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hmin0
  have h3 := mul_le_mul_of_nonneg_left (min_rpow_scale (α := α) (N := N) hL ht) (abs_nonneg C)
  have hpos : (0 : ℝ) ≤ 2 / c ^ 2 := by positivity
  calc 2 / c ^ 2 * kappa0 (c ^ 2 / 4 * t)
      ≤ 2 / c ^ 2 * (|C| * (max ((c ^ 2 / 4) ^ α) ((c ^ 2 / 4) ^ (-N)) * min (t ^ α) (t ^ (-N)))) :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hpos
    _ = _ := by ring

/-- **The `κ`-clauses of the frozen goal for the Bessel profile** `κ(t) = t K_{1/3}(c√t)`, with
`cκ = 2/c²`, `Aκ = (c²/4)⁻¹`, and any `0 < α ≤ 5/6`. -/
theorem kappaB_clauses {c : ℝ} (hc : 0 < c) {α : ℝ} (hα : 0 < α) (hα' : α ≤ 5 / 6) :
    Measurable (kappaB c) ∧ (0 : ℝ) < 2 / c ^ 2 ∧ (0 : ℝ) < (c ^ 2 / 4)⁻¹ ∧ 0 < α ∧
      (∀ t, 0 ≤ kappaB c t) ∧
      (∀ s : ℂ, -(5 / 6 : ℝ) < s.re →
        MellinConvergent (fun t => (kappaB c t : ℂ)) s ∧
        mellin (fun t => (kappaB c t : ℂ)) s =
          ((2 / c ^ 2 : ℝ) : ℂ) * (((c ^ 2 / 4)⁻¹ : ℝ) : ℂ) ^ s *
            (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) ∧
      (∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → kappaB c t ≤ C * min (t ^ α) (t ^ (-N))) :=
  ⟨measurable_kappaB hc, by positivity, by positivity, hα, kappaB_nonneg hc,
    fun s hs => kappaB_mellin hc s hs, fun _ hN => kappaB_bound hc hα hα' hN⟩

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

end

end ArtinKP.K
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

lemma prime_of_mem_prim {P I : Ideal (𝓞 F)} (hP : P ∈ prim I) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp := L2D_prime_of_mem (Multiset.mem_toFinset.1 hP)
  exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩

lemma exterior_of_prim {𝔪 I P : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hP : P ∈ prim I) :
    IsExterior 𝔪 P :=
  (C3M.exterior_of_mem_factors hI (Multiset.mem_toFinset.1 hP)).2

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3X_Coef
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3X_Coef: the forward Fourier coefficient and Cor 5.2

* `coefF g 𝔟 z`: the forward coefficient of `L3X_CutKP` at the frequency class `z` (row ideal `𝔟`):
  `χ_𝔟(x) ∏_{P ∣ 𝔷} W_P(a(x))`, `x = rowElt g z`, with `W_P` the spherical values (5.4).
* `gaussPhase_eq_prod_uSym` (from (3.10)): `γ₂(𝔠) = ∏_{P ∣ 𝔠} γ₂(P) χ_P(c/p)²` for squarefree `𝔠`.
* `prodW_cube` (Cor 5.2): `∏_{P ∣ 𝔠𝔫³} χ_P(A/p^e)^{2e} W_P(p^e) = γ₂(𝔠) / (q_𝔠^{1/2} q_𝔫)`,
  `A = gen(𝔠𝔫³)`, and the product vanishes when some exponent is `≡ 2 (mod 3)`.
* `tsum_coefF_eq_fwd`: the forward unfolded sum is Cut63V's left side `L3V.fwd`.
* `norm_coefF_le`: `‖coefF‖ ≤ 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots.L3X

open L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Norm bounds -/

lemma norm_sext_le (P : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖sexticResidueSymbol ι 𝔪 P x‖ ≤ 1 := by
  unfold sexticResidueSymbol
  split_ifs with h1 h2
  · simp
  · have hζ := h2.choose_spec.1
    have h6 : (ι (h2.choose : F)) ^ 6 = 1 := by
      rw [← map_pow]
      have : ((h2.choose : 𝓞 F) : F) ^ 6 = 1 := by
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) hζ
      rw [this, map_one]
    have hn : ‖ι (h2.choose : F)‖ ^ 6 = 1 := by rw [← norm_pow, h6, norm_one]
    have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num : (6 : ℕ) ≠ 0)).1 hn
    rw [this]
  · simp

lemma norm_residueSymbol_le' (𝔞 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ‖residueSymbol ι 𝔪 𝔞 x‖ ≤ 1 := by
  unfold residueSymbol
  induction (normalizedFactors 𝔞) using Multiset.induction_on with
  | empty => simp
  | cons P s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact (mul_le_mul (norm_sext_le P x) ih (norm_nonneg _) zero_le_one).trans (by norm_num)

lemma norm_localSymbol_le (P : Ideal (𝓞 F)) (t : F) : ‖localSymbol ι 𝔪 P t‖ ≤ 1 := by
  unfold localSymbol
  split_ifs with h
  · rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul (norm_sext_le P _) (norm_sext_le P _) (norm_nonneg _) zero_le_one).trans
      (by norm_num)
  · simp

lemma one_le_absNorm_of_prime {P : Ideal (𝓞 F)} (_hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (1 : ℝ) ≤ Ideal.absNorm P := by
  have : Ideal.absNorm P ≠ 0 := fun h => hP0 (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this


/-! ### Unit-part symbols of generators -/


/-! ### (3.10) in unit-part form, and Cor 5.2 -/


/-! ### The forward sum -/


/-! ### Bounds on the exterior local factors (no `HypChi`) -/

section bounds

variable (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P)
include hP hPe

theorem norm_Wv_le (e : ℕ) : ‖L3V.Wv g P e‖ ≤ 1 := by
  have hP1 := one_le_absNorm_of_prime hP hPe.1
  have hq0 : (0 : ℝ) < Ideal.absNorm P := lt_of_lt_of_le zero_lt_one hP1
  have hgp := L2B.norm_gaussPhase_le g 2 hPe
  unfold Wv
  split_ifs with h0 h1
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
    calc (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) * ‖gaussPhase g 2 P‖
        ≤ (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) * Real.sqrt (Ideal.absNorm P) :=
          mul_le_mul_of_nonneg_left hgp (Real.rpow_nonneg hq0.le _)
      _ = (Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq0]; ring_nf
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hP1 (by simp)
  · simp

theorem norm_Wsph_le (e₀ : ℤ) (t : F) : ‖L3V.Wsph g P e₀ t‖ ≤ 1 := by
  unfold Wsph
  split_ifs
  · simp
  · rw [norm_mul, norm_pow]
    exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (norm_localSymbol_le P t))
      (norm_Wv_le g hP hPe _) (norm_nonneg _) zero_le_one).trans (by norm_num)

omit hP hPe in
lemma norm_localAddChar_le (w : F) : ‖localAddChar g P w‖ ≤ 1 := by
  unfold localAddChar
  split_ifs
  · exact L2B.norm_sAddChar_le _ _
  · simp

theorem norm_Wweyl_le (e₀ : ℤ) (t : F) (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ‖L3V.Wweyl g P e₀ t v‖ ≤ 1 := by
  unfold Wweyl
  split_ifs
  · simp
  · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    have h1 := norm_Wv_le g hP hPe (e₀ + 2).toNat
    have h2 := pow_le_one₀ (n := 4 + 2 * (e₀ + 2).toNat) (norm_nonneg _) (norm_localSymbol_le (ι := ι) (𝔪 := 𝔪) P t)
    have h3 := pow_le_one₀ (n := 4) (norm_nonneg _) (norm_sext_le (ι := ι) P (quotLift v))
    have h4 := norm_localAddChar_le (P := P) g ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    calc _ ≤ (1 : ℝ) * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num

end bounds

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H_SumMain
/-! # WP-HA, file 3: pointwise summability of the two sums of `H0.KPCutNu`

For every `y : SModel 𝔪 k`:

* `summable_forward_coef`: `∑_{ν ∈ R∖0} coef(ν) · fp(sEmb ν + y)` converges absolutely for any
  bounded coefficient function (the support condition `[ν] + y_f = 0` confines `ν` to one class of
  `SFin`, a separated set in the Minkowski space; `κ(t) ≤ C min(t^α, t^{-4})`).
* `summable_reflected_coef`: `∑_{ν ∈ R∖0} coef(ν) · Fm(cl ν, sEmb ν − y)` converges absolutely for
  any bounded coefficient function and any class function `cl`, under the cut's hypotheses on
  `J`, `bf` (used at `σ = 0` and `σ = 4·#places`).
* `summable_forward`, `summable_reflected`: the two families of `KPCutNu` verbatim;
  `summable_forward_kappaB`, `summable_reflected_kappaB`: with `κ = K.kappaB c` and the cut's
  hypotheses exactly. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- `‖coefF'‖ ≤ 1`, with no hypothesis on `𝔪`. -/
theorem norm_coefF'_le (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) :
    ‖L3X.coefF' g 𝔟 z‖ ≤ 1 := by
  unfold L3X.coefF'
  rw [norm_mul, norm_prod]
  refine (mul_le_mul (L3X.norm_residueSymbol_le' _ _) (Finset.prod_le_one (fun _ _ => norm_nonneg _)
    fun P hP => ?_) (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one).trans (by norm_num)
  obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors z.1.2 (Multiset.mem_toFinset.1 hP)
  exact L3X.norm_Wsph_le g hPp hPe _ _

/-- `sEmb (ν / b²) − y = sEmb ν − (sEmb (b²) + y)`. -/
theorem sEmb_div_sq_sub {ν b : F} (hν : ν ≠ 0) (hb : b ≠ 0) (y : SModel 𝔪 k) :
    sEmb 𝔪 k (ν / b ^ 2) - y = sEmb 𝔪 k ν - (sEmb 𝔪 k (b ^ 2) + y) := by
  rw [L3X.sEmb_div hν (pow_ne_zero 2 hb), sub_sub]

end

end ArtinKP.H
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

end chi

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
-- module Solutions.Artin.KP.H_Dig
/-! # WP-HA, file 4: the digit sums

Local, at a good prime `P` (`C3I.Good`), with `χ = C3I.chi`, `ψ = C3I.psi`:

* `sum_mask_psi`: (6.4) `∑_d α_{P,k mod 6}(d) ψ(a d) = χ(a)^k` for `k ≥ 1` and every residue `a`;
* `sum_mask_sAddChar`: the same with `e(x d̃ / p)`, `x ∈ R`: the value is `χ_P(x)^k`.

Global, for an exterior ideal `𝔟`:

* `Dig 𝔪 𝔟`: digit vectors `(v_P)_{P ∣ 𝔟}`, `v_P ∈ R/PR`; `xdig g 𝔟 v = ∑_P ṽ_P / p_P ∈ F`;
  `maskProd g 𝔟 v = ∏_P α_{P, v_P(𝔟) mod 6}(v_P)`;
* `digCoef g r v z`: the exterior product of `L3V.Eprod` with each `Eloc` replaced by the value
  at the digit `v_P` (`Wsph` at the zero digit and outside `𝔟`, `Wweyl` at a nonzero digit);
* `sum_maskProd_sAddChar`: `∑_v maskProd(v) e(x · x_v) = χ_𝔟(x)` (needs good primes);
* `sum_maskProd_digCoef`: `∑_v maskProd(v) digCoef(v, z) = Eprod g r z` (no hypothesis);
* `residueSymbol_rowOf`, `residueSymbol_neg`: `χ_𝔟` is `U_S⁶`-invariant and even. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Local: (6.4) -/

section loc

variable {v : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (g : AllowedGen ι 𝔪)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

omit [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))] in
/-- `χ_P(−x) = χ_P(x)`. -/
theorem sextic_neg (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (-x) = sexticResidueSymbol ι 𝔪 v.asIdeal x := by
  rw [← C3I.chi_mk h hω, ← C3I.chi_mk h hω, show -x = -1 * x by ring, map_mul, map_mul, map_neg,
    map_one, C3I.chi_neg_one h hω, one_mul]

omit [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))] in
/-- `χ_P(μ⁶ x) = χ_P(x)` for a unit `μ` of `R`. -/
theorem sextic_unit_six_mul (μ : (SInt 𝔪)ˣ) (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal ((μ : SInt 𝔪) ^ 6 * x) =
      sexticResidueSymbol ι 𝔪 v.asIdeal x := by
  have h6 := C3I.sext_unit_six (ι := ι) h hω μ
  rw [← C3I.chi_mk h hω] at h6
  rw [← C3I.chi_mk h hω, ← C3I.chi_mk h hω, map_mul, map_mul, h6, one_mul]

end loc

/-! ### The additive character on finite sums -/

/-! ### Digit vectors -/

theorem finite_dig {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) : Finite (Dig 𝔪 𝔟) := by
  haveI : ∀ P : {P : Ideal (𝓞 F) // P ∈ (normalizedFactors 𝔟).toFinset},
      Finite (SInt 𝔪 ⧸ P.1.map (algebraMap (𝓞 F) (SInt 𝔪))) := fun P =>
    C3M.finite_quot (C3M.exterior_of_mem_factors h𝔟 (Multiset.mem_toFinset.1 P.2)).2
  infer_instance

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.H_Aut
/-! # WP-HA, file 5: the contract `AutInput` for the automorphic packages, and `AutInput → KPCutNu`

`AutInput h𝔪 g k κ m J` says: there is one function `Θ(x, y)` (`x ∈ F` a rational translation,
`y : SModel 𝔪 k`; in the adelic picture `Θ(x, y) = θ(n_S(−x) a(y))` for the level-one-outside-`S`
theta function of type `m` whose `S_f`-Kirillov function is `1_{U_k}`), with **two expansions at
each digit point `x_v = ∑_{P ∣ 𝔟} ṽ_P / p_P`**:

* `forward` (expansion at `a(y)`): the `ν`-th coefficient is
  `e(−ν x) · ∏_{P ∣ ν} Wsph_P · fp(sEmb ν + y)` — the `𝔟`-independent coefficient
  `coefF' g ⊤`, twisted by the additive character;
* `reflected` (expansion at `w · a(y)`): the coefficient at `ν / b²` is
  `∏_P (per-digit local value) · Fm([ν/b²], sEmb(ν/b²) − y)`, the local value being `Wsph` at a
  zero digit and at `P ∤ 𝔟`, and `Wweyl` at a nonzero digit (`digCoef`).

Both are stated as `tsum` identities (the summability is proved here from the cut's hypotheses).
`cut_identity`: summing over the digit vectors against the masks gives the identity of
`H0.KPCutNu` ((6.4) on the forward side, distributivity on the reflected side).
`KPCutNu_of_autInput`: the cut. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- `coefF' g 𝔟 = χ_𝔟 · coefF' g ⊤`. -/
theorem coefF'_eq (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) :
    L3X.coefF' g 𝔟 z = residueSymbol ι 𝔪 𝔟 (rowElt g z) * L3X.coefF' g ⊤ z := by
  have h1 : residueSymbol ι 𝔪 ⊤ (rowElt g z) = 1 := by
    unfold residueSymbol; rw [C3B.normalizedFactors_top]; simp
  unfold L3X.coefF'
  rw [h1, one_mul]

theorem residueSymbol_congr {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {a b : SInt 𝔪}
    (hab : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
      sexticResidueSymbol ι 𝔪 P a = sexticResidueSymbol ι 𝔪 P b) :
    residueSymbol ι 𝔪 𝔟 a = residueSymbol ι 𝔪 𝔟 b := by
  unfold residueSymbol
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  obtain ⟨h1, h2⟩ := C3M.exterior_of_mem_factors h𝔟 hP
  exact hab P h1 h2

section good

variable (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] {N₀ : ℕ}
  (hN₀ : C3I.cutN F ≤ N₀) (hsm : SmallPrimesDvd N₀ 𝔪)

include hn0 hn hN₀ hsm

/-- `χ_𝔟(−x) = χ_𝔟(x)`. -/
theorem residueSymbol_neg {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔟 (-x) = residueSymbol ι 𝔪 𝔟 x := by
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  exact residueSymbol_congr h𝔟 fun P hP hPe =>
    sextic_neg (v := ⟨P, hP, hPe.1⟩) (C3I.good_of_exterior n hn0 hn hN₀ hsm hP hPe) hω x

/-- `χ_𝔟` of the row representative of `ν` is `χ_𝔟(ν)` (`U_S⁶`-invariance). -/
theorem residueSymbol_rowOf (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    residueSymbol ι 𝔪 𝔟 (rowElt g (H0.rowOf h𝔪 g ν)) = residueSymbol ι 𝔪 𝔟 (ν : SInt 𝔪) := by
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  obtain ⟨δ, hδ⟩ := (H0.gamOf h𝔪 g ν).2
  have hF : ((ν : SInt 𝔪) : F) =
      ((((H0.uInt δ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * rowElt g (H0.rowOf h𝔪 g ν) : SInt 𝔪) : F) := by
    rw [H0.coe_eq_gamOf_mul h𝔪 g ν, ← hδ]
    simp only [powMonoidHom_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, H0.coe_uInt,
      Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hS : (ν : SInt 𝔪) =
      ((H0.uInt δ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * rowElt g (H0.rowOf h𝔪 g ν) := Subtype.ext hF
  rw [show residueSymbol ι 𝔪 𝔟 (ν : SInt 𝔪) = residueSymbol ι 𝔪 𝔟
    (((H0.uInt δ : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 * rowElt g (H0.rowOf h𝔪 g ν)) from congrArg _ hS]
  exact (residueSymbol_congr h𝔟 fun P hP hPe =>
    sextic_unit_six_mul (v := ⟨P, hP, hPe.1⟩)
      (C3I.good_of_exterior n hn0 hn hN₀ hsm hP hPe) hω (H0.uInt δ) _).symm

end good

end

end ArtinKP.H
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

/-! ### The coefficient at `ν` -/

theorem norm_digCoefNu_le (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)}
    (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ‖digCoefNu h𝔪 g 𝔟 v ν‖ ≤ 1 := by
  have hzr : IsExterior 𝔪 ((H0.rowOf h𝔪 g ν).1.1 * 𝔟) :=
    C3B.isExterior_mul (H0.rowOf h𝔪 g ν).1.2 h𝔟
  unfold digCoefNu
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun P hP => ?_
  obtain ⟨hPp, _⟩ := L3V.prime_of_mem_prim hP
  have hPe := L3V.exterior_of_prim hzr hP
  unfold H.digLoc
  split_ifs
  · exact L3X.norm_Wsph_le g hPp hPe _ _
  · exact L3X.norm_Wweyl_le g hPp hPe _ _ _
  · exact L3X.norm_Wsph_le g hPp hPe _ _

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Aut
/-! # WP-HB, file 2: the repaired contract `AutInput2`, and `AutCut2 → KPCutNu`

`H.AutInput.reflected` is false as stated (MATH3 §3.4): its coefficient
`H.digCoef g (⟨𝔟,h𝔟⟩,1) v (H0.rowOf h𝔪 g ν)` is a function of the row class of `ν`, while the true
per-digit coefficient contains `sAddChar(μ a / c)`, which is not `U_S⁶`-invariant.  `AutInput2` is
`H.AutInput` with `reflected` stated with `HB.digCoefNu h𝔪 g 𝔟 v ν` (unit parts from `ν` itself).
All other fields are unchanged; they were re-examined against MATH3 §1–§4 (see `WP-HB.md`):

* `Θ : F → SModel 𝔪 k → ℂ` and the digit points `x = eps · x_v`: MATH3 §1.1, §3.1 (`eps = −1`);
* `forward`: MATH3 §1.3 (character `sAddChar(−ν x)`, coefficient `coefF' g ⊤ (rowOf ν)`, argument
  `sEmb ν + y`);
* `reflected`: frequency `ν / b²`, class argument `[ν / b²]`, `S`-argument `sEmb(ν / b²) − y`:
  MATH3 (2.4), (4.1) with `ν = μ (b / c_v)²`.

`cut_identity2`: summing over the digit vectors against the masks gives the identity of
`H0.KPCutNu` (HA's forward digit sum; `HB.sum_maskProd_digCoefNu` on the reflected side).
`KPCutNu_of_autInput2`: the cut. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- **From the contract to the identity of the cut**, for one `𝔟` and one `y`. -/
theorem cut_identity2 (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    {N₀ : ℕ} (hN₀ : C3I.cutN F ≤ N₀) (hsm : SmallPrimesDvd N₀ 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    (g : AllowedGen ι 𝔪) {κ : ℝ → ℝ} (hκ0 : ∀ t, 0 ≤ κ t) {α : ℝ} (hα : 0 ≤ α)
    (hκb : ∀ N : ℝ, 0 < N → ∃ C : ℝ, ∀ t : ℝ, 0 < t → κ t ≤ C * min (t ^ α) (t ^ (-N)))
    (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) {bf : SFin 𝔪 k → ℝ}
    (hJ : ∀ cl y, ‖J cl y‖ ≤ bf y)
    (hbf : ∀ σ : ℝ, 0 ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ))
    (A : AutInput2 h𝔪 g k κ m J) (𝔟 : Ideal (𝓞 F)) (h𝔟 : IsExterior 𝔪 𝔟) (y : SModel 𝔪 k) :
    ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        L3X.coefF' g 𝔟 (H0.rowOf h𝔪 g ν) *
          L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y) =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (H0.rowOf h𝔪 g ν) *
          H0.FmOf κ m J
            (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y) := by
  haveI := H.finite_dig (𝔪 := 𝔪) h𝔟
  letI := Fintype.ofFinite (H.Dig 𝔪 𝔟)
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have hb : (g.gen 𝔟 : F) ≠ 0 := L3P.gen_ne_zero g ⟨𝔟, h𝔟⟩
  set fT : H.Dig 𝔪 𝔟 → {ν : SInt 𝔪 // ν ≠ 0} → ℂ := fun v ν =>
    sAddChar 𝔪 (-(((ν : SInt 𝔪) : F) * ((A.eps : F) * H.xdig g 𝔟 v))) *
      (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g ν) * L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y))
    with hfT
  set rT : H.Dig 𝔪 𝔟 → {ν : SInt 𝔪 // ν ≠ 0} → ℂ := fun v ν =>
    digCoefNu h𝔪 g 𝔟 v ν *
      H0.FmOf κ m J
        (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
        (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y) with hrT
  have hFs : ∀ v, Summable (fT v) := by
    intro v
    have := H.summable_forward_coef h𝔪 g hκ0 hα hκb m
      (fun ν : {ν : SInt 𝔪 // ν ≠ 0} =>
        sAddChar 𝔪 (-(((ν : SInt 𝔪) : F) * ((A.eps : F) * H.xdig g 𝔟 v))) *
          L3X.coefF' g ⊤ (H0.rowOf h𝔪 g ν)) (C := 1)
      (fun ν => by
        rw [norm_mul]
        exact mul_le_one₀ (L2B.norm_sAddChar_le _ _) (norm_nonneg _) (H.norm_coefF'_le g ⊤ _)) y
    exact this.congr fun ν => mul_assoc _ _ _
  have hRs : ∀ v, Summable (rT v) := by
    intro v
    have := H.summable_reflected_coef h𝔪 g hκ0 hα hκb m J hJ hbf
      (fun ν => digCoefNu h𝔪 g 𝔟 v ν) (C := 1)
      (fun ν => norm_digCoefNu_le h𝔪 g h𝔟 v ν)
      (fun ν => QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
      (sEmb 𝔪 k ((g.gen 𝔟 : F) ^ 2) + y)
    refine this.congr fun ν => ?_
    simp only [hrT]
    rw [H.sEmb_div_sq_sub (H0.coe_ne_zero ν) hb]
  have hL : ∀ ν : {ν : SInt 𝔪 // ν ≠ 0},
      L3X.coefF' g 𝔟 (H0.rowOf h𝔪 g ν) * L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y) =
        ∑ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * fT v ν := by
    intro ν
    have h1 := H.sum_maskProd_sAddChar n hn0 hn hN₀ hsm g h𝔟 (-((ν : SInt 𝔪) * A.eps))
    rw [finsum_eq_sum_of_fintype] at h1
    have h2 : residueSymbol ι 𝔪 𝔟 (-((ν : SInt 𝔪) * A.eps)) =
        residueSymbol ι 𝔪 𝔟 (rowElt g (H0.rowOf h𝔪 g ν)) := by
      rw [H.residueSymbol_rowOf n hn0 hn hN₀ hsm h𝔪 g h𝔟 ν]
      rcases A.eps_eq with he | he
      · rw [he, mul_one, H.residueSymbol_neg n hn0 hn hN₀ hsm h𝔟]
      · rw [he, mul_neg, mul_one, neg_neg]
    rw [H.coefF'_eq, ← h2, ← h1, mul_assoc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hfT]
    have : ((-((ν : SInt 𝔪) * A.eps) : SInt 𝔪) : F) * H.xdig g 𝔟 v =
        -(((ν : SInt 𝔪) : F) * ((A.eps : F) * H.xdig g 𝔟 v)) := by
      rw [Subalgebra.coe_neg, Subalgebra.coe_mul]; ring
    rw [this, mul_assoc]
  have hR : ∀ ν : {ν : SInt 𝔪 // ν ≠ 0},
      L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (H0.rowOf h𝔪 g ν) *
          H0.FmOf κ m J
            (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y) =
        ∑ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * rT v ν := by
    intro ν
    have h1 := finsum_maskProd_mul_digCoefNu_eq_eprod n hn0 hn hN₀ hsm h𝔪 g h𝔟 ν
    rw [finsum_eq_sum_of_fintype] at h1
    rw [← h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hrT]
    rw [mul_assoc]
  calc ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        L3X.coefF' g 𝔟 (H0.rowOf h𝔪 g ν) * L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y)
      = ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, ∑ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * fT v ν :=
        tsum_congr hL
    _ = ∑ v : H.Dig 𝔪 𝔟, ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, H.maskProd g 𝔟 v * fT v ν :=
        Summable.tsum_finsetSum fun v _ => (hFs v).mul_left _
    _ = ∑ v : H.Dig 𝔪 𝔟, ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, H.maskProd g 𝔟 v * rT v ν := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [tsum_mul_left, tsum_mul_left]
        congr 1
        exact (A.forward 𝔟 h𝔟 v y).symm.trans (A.reflected 𝔟 h𝔟 v y)
    _ = ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, ∑ v : H.Dig 𝔪 𝔟, H.maskProd g 𝔟 v * rT v ν :=
        (Summable.tsum_finsetSum fun v _ => (hRs v).mul_left _).symm
    _ = _ := tsum_congr fun ν => (hR ν).symm

/-- **`AutCut2 → KPCutNu`.** -/
theorem kpCutNu_of_autCut2_oai (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h : AutCut2 n F ι) :
    H0.KPCutNu n F ι := by
  obtain ⟨N₀, hN⟩ := h
  refine ⟨max N₀ (C3I.cutN F), fun 𝔪 h𝔪 hs g => ?_⟩
  have hs' : SmallPrimesDvd N₀ 𝔪 := fun Q hQ hQ0 hle =>
    hs Q hQ hQ0 (hle.trans (le_max_left _ _))
  obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs' g
  refine ⟨k₀, fun k hk' => ?_⟩
  obtain ⟨c, α, hc, hα, hα', hm⟩ := hk k hk'
  refine ⟨c, α, hc, hα, hα', fun m hm' => ?_⟩
  obtain ⟨J, bf, hJ, hbf, ⟨A⟩⟩ := hm m hm'
  obtain ⟨-, -, -, -, h0, -, hb⟩ := K.kappaB_clauses hc (α := 5 / 6) (by norm_num) le_rfl
  exact ⟨J, bf, hJ, hbf, fun 𝔟 h𝔟 y =>
    cut_identity2 n hn0 hn (le_max_right _ _) hs h𝔪 g h0 (by norm_num : (0 : ℝ) ≤ 5 / 6) hb m J hJ
      (fun σ hσ => hbf σ (by linarith)) A 𝔟 h𝔟 y⟩

end

end ArtinKP.HB
end

theorem solution.{u_2} : type_of% @ArtinKP.HB.kpCutNu_of_autCut2_oai.{u_2} := @ArtinKP.HB.kpCutNu_of_autCut2_oai.{u_2}
