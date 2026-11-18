-- Prove2me | solution 1 for ArtinKP.HB.autCut2_of_secCut
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:43.605413+00:00
-- url     : https://prove2.me/submissions/657a66f0-b868-423a-a626-57eb63615d2d

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_HB_digCoefNu_eq

section
-- module Solutions.Artin.C0.C0R_P
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# C0-P: the `S`-integers form a PID once `S` contains the small primes

Every ideal class contains a nonzero ideal of bounded norm; once `𝔪` is divisible by every prime of
norm at most that bound, every ideal of `R = 𝓞_S` is principal.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

/-- **C0-P.** Once `S` contains the primes of small norm, `R = 𝓞_S` is a PID. -/
theorem exists_cutoff_isPrincipal_map (F : Type*) [Field F] [NumberField F] :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
      ∀ I : Ideal (𝓞 F), (I.map (algebraMap (𝓞 F) (SInt 𝔪))).IsPrincipal := by
  classical
  let rep : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ :=
    fun C => Function.surjInv ClassGroup.mk0_surjective C
  have hrep : ∀ C, ClassGroup.mk0 (rep C) = C := fun C =>
    Function.surjInv_eq ClassGroup.mk0_surjective C
  refine ⟨Finset.univ.sup fun C => Ideal.absNorm (rep C : Ideal (𝓞 F)), ?_⟩
  intro 𝔪 h𝔪 hsmall I
  by_cases hI : I = ⊥
  · rw [hI, Ideal.map_bot]; exact bot_isPrincipal
  have hI' : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set J := rep (ClassGroup.mk0 ⟨I, hI'⟩)⁻¹ with hJdef
  have hJ0 : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have hIJ : (I * J).IsPrincipal := by
    have hmem : I * (J : Ideal (𝓞 F)) ∈ (Ideal (𝓞 F))⁰ := mul_mem hI' J.2
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have : (⟨I * J, hmem⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI'⟩ * J := rfl
    rw [this, map_mul, hJdef, hrep, mul_inv_cancel]
  have hJtop : (J : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤ := by
    apply C0R.map_eq_top_of_primes 𝔪 h𝔪 _
    intro Q hQ hJQ
    have hQ0 : Q ≠ ⊥ := fun h => hJ0 (le_bot_iff.1 (h ▸ hJQ))
    apply hsmall Q hQ hQ0
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hJQ
    have hJn : Ideal.absNorm (J : Ideal (𝓞 F)) ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors J
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hJn) hdvd)
      (Finset.le_sup (f := fun C => Ideal.absNorm (rep C : Ideal (𝓞 F))) (Finset.mem_univ _))
  obtain ⟨a, ha⟩ := hIJ.principal
  rw [Ideal.submodule_span_eq] at ha
  refine ⟨⟨algebraMap (𝓞 F) (SInt 𝔪) a, ?_⟩⟩
  rw [Ideal.submodule_span_eq]
  calc I.map (algebraMap (𝓞 F) (SInt 𝔪))
      = I.map (algebraMap (𝓞 F) (SInt 𝔪)) * (J : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [hJtop, Ideal.mul_top]
    _ = (I * J).map (algebraMap (𝓞 F) (SInt 𝔪)) := (Ideal.map_mul _ _ _).symm
    _ = _ := by rw [ha, Ideal.map_span, Set.image_singleton]

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.A_Residue
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: the exterior cubic residue symbol and reciprocity

* `Good 𝔪`: the standing hypotheses on the modulus (`𝔪 ≠ ⊥`, every prime over `6` divides `𝔪`,
  `R = SInt 𝔪` is a PID in the form "every extended ideal is principal");
  `exists_cutoff_good` gives it from `SmallPrimesDvd N₀ 𝔪`.
* `cubicExt ι 𝔪 d c = ∏_{P ∉ S, P ∣ c} χ_P(d)^{2 v_P(c)}` in terms of the goal's
  `sexticResidueSymbol`.
* `cubicExt_eq_prod`: `(d/c) = ι ∏_v (d, c)_v` over the exterior places dividing `c`.
* `cubicExt_reciprocity` (A3): `(d/c) = (c/d) · (c, d)_S` — with the orientation of `CubicPkg`
  the sign in MATH.md (A3) is `+1`.
* unit laws, multiplicativity, dependence on `d mod c` only.

The first section is a universe-polymorphic copy of `C0Y.val_generator`, `C0Y.sextic_spec`
(`Solutions/Artin/C0/C0YR.lean`, stated there for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- `Good 𝔪` holds as soon as `𝔪` is divisible by all primes of small norm. -/
theorem exists_cutoff_good (F : Type*) [Field F] [NumberField F] :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → Good 𝔪 := by
  obtain ⟨N₁, hN₁⟩ := exists_cutoff_isPrincipal_map F
  refine ⟨max N₁ (Ideal.absNorm (Ideal.span {(6 : 𝓞 F)})), fun 𝔪 h𝔪 hs =>
    ⟨h𝔪, fun v h6 => ?_, hN₁ 𝔪 h𝔪 fun P hP h0 hN => hs P hP h0 (hN.trans (le_max_left _ _))⟩⟩
  apply hs v.asIdeal v.isPrime v.ne_bot
  have h60 : Ideal.span {(6 : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h0
    have := congrArg (algebraMap (𝓞 F) F) h0
    simp at this
  have hle : Ideal.span {(6 : 𝓞 F)} ≤ v.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h6
  have hn0 : Ideal.absNorm (Ideal.span {(6 : 𝓞 F)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact h60
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Ideal.absNorm_dvd_absNorm_of_le hle)).trans
    (le_max_right _ _)

end ArtinKP.A
end
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

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

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

/-! ### Residue symbols -/

/-! ### Generators -/

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

/-- The ideal of `rowOf ν` generates `νR`. -/
theorem span_eq_map_rowOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    Ideal.span {(ν : SInt 𝔪)} = (rowOf h𝔪 g ν).1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have h : (ν : SInt 𝔪) = rowSInt g ((rowEquiv h𝔪 g).symm ν) :=
    (congrArg Subtype.val ((rowEquiv h𝔪 g).apply_symm_apply ν)).symm
  rw [h, rowSInt_eq_par]
  exact L3P.span_unit_mul_gen g _ _

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
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

end prime

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

lemma res_add (hv : v ∉ placesOf 𝔪) {w w' : F} (hw : v.valuation F w ≤ 1)
    (hw' : v.valuation F w' ≤ 1) : res 𝔪 v (w + w') = res 𝔪 v w + res 𝔪 v w' := by
  obtain ⟨y, hy⟩ := exists_approx (𝔪 := 𝔪) hw
  obtain ⟨y', hy'⟩ := exists_approx (𝔪 := 𝔪) hw'
  rw [res_eq hv hy, res_eq hv hy', ← map_add]
  apply res_eq hv
  have : w + w' - ((y + y' : SInt 𝔪) : F) = (w - y) + (w' - y') := by
    rw [Subalgebra.coe_add]; ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le hy hy')

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

/-! ### The local symbols -/

end L3V

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

lemma nf_prime' {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

lemma cnt_prime {P Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    cnt P Q = if P = Q then 1 else 0 := by
  unfold cnt; rw [nf_prime' hQ hQ0, Multiset.count_singleton]

lemma mem_prim_iff {P I : Ideal (𝓞 F)} : P ∈ prim I ↔ 0 < cnt P I := by
  unfold prim cnt; rw [Multiset.mem_toFinset, Multiset.count_pos]

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
-- module Solutions.Artin.T12.L3V_ValB
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_ValB: the local package `Env` (from `L3V_LocPkg`) and the unit-part symbol calculus

`Env ι 𝔪` records, at every exterior prime, the facts of the local statement `L3V_LocPkg`; from it:
valuations of generators and units, the unit part `x p^{−v_P(x)}`, and `uSym` multiplicative, of
order dividing `6`, equal to `χ_P` on `R ∖ P R`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}


section ucalc

variable (g : AllowedGen ι 𝔪)
  {P : Ideal (𝓞 F)}
  (hP : P.IsPrime)
  (he : IsExterior 𝔪 P)
include hP he

lemma notS_of_ext : (⟨P, hP, he.1⟩ : HeightOneSpectrum (𝓞 F)) ∉ placesOf 𝔪 := fun hv =>
  hP.ne_top (eq_top_iff.2 (he.2 ▸ sup_le le_rfl hv))

end ucalc

end L3V

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

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_C
/-! # WP-HB, file 4: the element `c_v` of a digit vector

MATH3 §3.1.  For a digit vector `v ∈ Dig 𝔪 𝔟`: `D = {P ∣ 𝔟 : v_P ≠ 0}`,
`c_v = ∏_{P ∈ D} gen P = cdig g 𝔟 v` (as a product over all `P ∣ 𝔟` of `cfac P ∈ {1, gen P}`),
`ccof P = c_v / cfac P`.

* `val_cdig`, `vP_cdig`: `v_P(c_v) = 1` for `P ∈ D` and `0` at the other exterior primes;
* `cubicExt_cdig`: `(d / c_v) = ∏_{P ∈ D} χ_P(d)²` (so `κ(γ) = ∏_{P ∈ D} χ_P(d)^{−2}`);
* `exists_pf`: partial fractions, `e(r / c_v) = ∏_{P ∈ D} e(r m_P / p_P)` with
  `m_P · ccof P ≡ 1 mod P`.

(`res_cdig_xdig` is in `HB_Loc`, `exists_gamma` in `HB_Refl`.) -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

theorem cfac_mul_ccof (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) :
    cfac g 𝔟 v P * ccof g 𝔟 v P = cdig g 𝔟 v :=
  (Fintype.prod_eq_mul_prod_compl P _).symm

theorem pidx_ext {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (P : PIdx 𝔟) :
    P.1.IsPrime ∧ IsExterior 𝔪 P.1 :=
  C3M.exterior_of_mem_factors h𝔟 (Multiset.mem_toFinset.1 P.2)

/-- `w(gen Q) = exp(−1)` if `w = Q`, `1` otherwise (`Q` an exterior prime, `w` exterior). -/
theorem val_gen_prime (g : AllowedGen ι 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal)
    {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    w.valuation F (g.gen Q : F) = if w.asIdeal = Q then exp (-1 : ℤ) else 1 := by
  rw [val_eq_exp_count w hw hQe.1 (g.gen Q) (g.span_gen Q hQe)]
  have := L3V.cnt_prime (P := w.asIdeal) hQ hQe.1
  unfold L3V.cnt at this
  rw [this]
  split_ifs <;> simp

theorem cfac_ne_zero (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) : (cfac g 𝔟 v P : F) ≠ 0 := by
  unfold cfac
  split_ifs
  · simp
  · exact C3B.gen_ne_zero g P.1 (pidx_ext h𝔟 P).2

theorem coe_cdig (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) :
    ((cdig g 𝔟 v : SInt 𝔪) : F) = ∏ P : PIdx 𝔟, (cfac g 𝔟 v P : F) := by
  unfold cdig
  exact map_prod ((placesOf 𝔪).integer F).subtype _ _

theorem cdig_ne_zero (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) : (cdig g 𝔟 v : F) ≠ 0 := by
  rw [coe_cdig]
  exact Finset.prod_ne_zero_iff.2 fun P _ => cfac_ne_zero g h𝔟 v P

/-- `w(c_v) = exp(−1)` at the primes with a nonzero digit, `1` at the other exterior places. -/
theorem val_cdig (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (cdig g 𝔟 v : F) = if Dnz 𝔟 v w.asIdeal then exp (-1 : ℤ) else 1 := by
  rw [coe_cdig, map_prod]
  have hfac : ∀ Q : PIdx 𝔟, w.valuation F (cfac g 𝔟 v Q : F) =
      if v Q ≠ 0 ∧ w.asIdeal = Q.1 then exp (-1 : ℤ) else 1 := by
    intro Q
    unfold cfac
    by_cases hQ : v Q = 0
    · rw [if_pos hQ, if_neg (fun h => h.1 hQ)]; simp
    · rw [if_neg hQ, val_gen_prime g w hw (pidx_ext h𝔟 Q).1 (pidx_ext h𝔟 Q).2]
      by_cases hwQ : w.asIdeal = Q.1
      · rw [if_pos hwQ, if_pos ⟨hQ, hwQ⟩]
      · rw [if_neg hwQ, if_neg (fun h => hwQ h.2)]
  by_cases hD : Dnz 𝔟 v w.asIdeal
  · obtain ⟨hP, hne⟩ := hD
    rw [if_pos ⟨hP, hne⟩, Finset.prod_eq_single ⟨w.asIdeal, hP⟩]
    · rw [hfac, if_pos ⟨hne, rfl⟩]
    · intro Q _ hQ
      rw [hfac, if_neg]
      rintro ⟨-, h2⟩
      exact hQ (Subtype.ext h2.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hD]
    refine Finset.prod_eq_one fun Q _ => ?_
    rw [hfac, if_neg]
    rintro ⟨h1, h2⟩
    apply hD
    refine ⟨h2 ▸ Q.2, ?_⟩
    have : (⟨w.asIdeal, h2 ▸ Q.2⟩ : PIdx 𝔟) = Q := Subtype.ext h2
    rw [this]; exact h1

/-- `v_P(c_v) = 1` if `P` carries a nonzero digit, `0` otherwise (`P` an exterior prime). -/
theorem vP_cdig (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    L3V.vP P (cdig g 𝔟 v : F) = if Dnz 𝔟 v P then 1 else 0 := by
  have h1 := L3V.vP_v (v := ⟨P, hP, hPe.1⟩) (cdig g 𝔟 v : F)
  have h2 := val_cdig g h𝔟 v ⟨P, hP, hPe.1⟩ (L3V.notS_of_ext hP hPe)
  change L3V.vP P _ = _ at h1
  rw [h1, h2]
  split_ifs <;> simp

/-! ### The Kubota symbol of `γ_v` -/

/-! ### Partial fractions -/

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Loc
/-! # WP-HB, file 5: identity (D) at one prime carrying a nonzero digit

Local statements at a good prime `w = P` (`C3I.Good`), residue field `k_P = R / P R`,
`χ = C3I.chi`, `ψ = C3I.psi`:

* `res_sum`, `res_neg`: `L3V.res` on finite sums and negatives;
* `res_cdig_xdig`: `c_v · x_v ≡ ccof P · v_P mod P` at a prime with `v_P ≠ 0`;
* `loc_weyl`: MATH3 §3.2, the case `P ∈ D`: the four local factors of the left side of (D)
  (`Wsph` of the level-one coefficient, the additive phase `e(μ a m_P / p)`, the Kubota factor
  `χ_P(d)^{−2}`, the tame factor of `⟨μ, c⟩`) multiply to `Wweyl_P(e − 2, t, v_P)`. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

section loc

variable {w : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 w) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (g : AllowedGen ι 𝔪)

include h

theorem res_sum {α : Type*} (s : Finset α) (f : α → F)
    (hf : ∀ a ∈ s, w.valuation F (f a) ≤ 1) :
    w.valuation F (∑ a ∈ s, f a) ≤ 1 ∧
      L3V.res 𝔪 w (∑ a ∈ s, f a) = ∑ a ∈ s, L3V.res 𝔪 w (f a) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero]
    refine ⟨zero_le, ?_⟩
    have := L3V.res_of_SInt (𝔪 := 𝔪) h.notS (0 : SInt 𝔪)
    simpa using this
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have h1 := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, L3V.res_add h.notS h1 ih1, ih2]
    exact ⟨(Valuation.map_add _ _ _).trans (max_le h1 ih1), rfl⟩

theorem res_neg {x : F} (hx : w.valuation F x ≤ 1) :
    L3V.res 𝔪 w (-x) = -L3V.res 𝔪 w x := by
  have h1 : L3V.res 𝔪 w ((-1 : F)) = -1 := by
    have := L3V.res_of_SInt (𝔪 := 𝔪) h.notS (-1 : SInt 𝔪)
    simpa using this
  have hm1 : w.valuation F (-1 : F) ≤ 1 := by simp
  rw [show -x = (-1 : F) * x by ring, L3V.res_mul h.notS hm1 hx, h1]
  ring

end loc

/-- `c_v · x_v ≡ ccof Q · v_Q mod Q` at a prime `Q ∣ 𝔟` with `v_Q ≠ 0`. -/
theorem res_cdig_xdig (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (Q : PIdx 𝔟) (hQ : v Q ≠ 0) (hp : Q.1.IsPrime) (h0 : Q.1 ≠ ⊥)
    (hg : C3I.Good 𝔪 (⟨Q.1, hp, h0⟩ : HeightOneSpectrum (𝓞 F))) :
    (⟨Q.1, hp, h0⟩ : HeightOneSpectrum (𝓞 F)).valuation F
        ((cdig g 𝔟 v : F) * H.xdig g 𝔟 v) ≤ 1 ∧
      L3V.res 𝔪 (⟨Q.1, hp, h0⟩ : HeightOneSpectrum (𝓞 F)) ((cdig g 𝔟 v : F) * H.xdig g 𝔟 v) =
        Ideal.Quotient.mk _ (ccof g 𝔟 v Q) * v Q := by
  set w : HeightOneSpectrum (𝓞 F) := ⟨Q.1, hp, h0⟩ with hw
  have hc : w.valuation F (cdig g 𝔟 v : F) = exp (-1 : ℤ) := by
    rw [val_cdig g h𝔟 v w hg.notS, if_pos ⟨Q.2, hQ⟩]
  have hsum : (cdig g 𝔟 v : F) * H.xdig g 𝔟 v =
      ∑ Q' : PIdx 𝔟, (cdig g 𝔟 v : F) * ((quotLift (v Q') : F) / (g.gen Q'.1 : F)) := by
    unfold H.xdig; rw [Finset.mul_sum]
  have hterm : ∀ Q' : PIdx 𝔟, Q' ≠ Q →
      w.valuation F ((cdig g 𝔟 v : F) * ((quotLift (v Q') : F) / (g.gen Q'.1 : F))) < 1 := by
    intro Q' hne
    rw [map_mul, map_div₀, hc,
      val_gen_prime g w hg.notS (pidx_ext h𝔟 Q').1 (pidx_ext h𝔟 Q').2,
      if_neg (fun h => hne (Subtype.ext h.symm)), div_one]
    calc exp (-1 : ℤ) * w.valuation F (quotLift (v Q') : F)
        ≤ exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl (C3I.val_le_one hg.notS _)
      _ < 1 := by rw [mul_one]; exact L3V.exp_neg_one_lt_one
  have hQterm : (cdig g 𝔟 v : F) * ((quotLift (v Q) : F) / (g.gen Q.1 : F)) =
      ((ccof g 𝔟 v Q * quotLift (v Q) : SInt 𝔪) : F) := by
    have hcc := congrArg (fun x : SInt 𝔪 => (x : F)) (cfac_mul_ccof g 𝔟 v Q)
    simp only [Subalgebra.coe_mul] at hcc
    have hcf : cfac g 𝔟 v Q = g.gen Q.1 := by unfold cfac; rw [if_neg hQ]
    rw [hcf] at hcc
    rw [← hcc, Subalgebra.coe_mul]
    have := C3B.gen_ne_zero g Q.1 (pidx_ext h𝔟 Q).2
    field_simp
  have hle : ∀ Q' ∈ (Finset.univ : Finset (PIdx 𝔟)),
      w.valuation F ((cdig g 𝔟 v : F) * ((quotLift (v Q') : F) / (g.gen Q'.1 : F))) ≤ 1 := by
    intro Q' _
    by_cases hne : Q' = Q
    · subst hne; rw [hQterm]; exact C3I.val_le_one hg.notS _
    · exact (hterm Q' hne).le
  obtain ⟨h1, h2⟩ := res_sum hg Finset.univ _ hle
  rw [hsum]
  refine ⟨h1, ?_⟩
  rw [h2, Finset.sum_eq_single Q
    (fun Q' _ hne => (L3V.res_eq_zero_iff hg.notS (hterm Q' hne).le).2 (hterm Q' hne))
    (fun h => absurd (Finset.mem_univ _) h), hQterm, L3V.res_of_SInt hg.notS, map_mul,
    C3I.mk_quotLift]

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_D
/-! # WP-HB, file 6: identity (D), prime by prime

MATH3 §3.2.  Standing: `Pk : CubicPkg F`, `hG : Good 𝔪`, `hz6`, all exterior primes good
(`hgood`, as in `H_Tau`), `𝔟` exterior, `v ∈ Dig 𝔪 𝔟`, `c = cdig g 𝔟 v`,
`γ ∈ SL₂(R)` with bottom row `(c, −c x_v)`, `μ, ν ∈ R ∖ 0` with `ν = μ (b / c)²`.

* `vP_of_span`, `eNu_eq`: `e₀(P) = v_P(μ) − 2·[P ∈ D]`;
* `local_D`: at every exterior prime `P`, the four local factors of the left side of (D) multiply
  to `digLoc_P(e₀, t_P)` (`HB.loc_weyl` at `P ∈ D`, sixth powers at the other primes). -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

theorem vPI_mul {P : Ideal (𝓞 F)} (hP : P.IsPrime) (h0 : P ≠ ⊥) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : L3V.vP P (x * y) = L3V.vP P x + L3V.vP P y :=
  L3V.vP_mul (v := ⟨P, hP, h0⟩) hx hy

theorem vPI_inv {P : Ideal (𝓞 F)} (hP : P.IsPrime) (h0 : P ≠ ⊥) (x : F) :
    L3V.vP P x⁻¹ = -L3V.vP P x :=
  L3V.vP_inv (v := ⟨P, hP, h0⟩) x

/-- `v_P(c) = v_P(𝔞)` if `c R = 𝔞 R` (`P` an exterior prime). -/
theorem vP_of_span {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P)
    {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (c : SInt 𝔪)
    (hspan : Ideal.span {c} = 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    L3V.vP P (c : F) = ((normalizedFactors 𝔞).count P : ℤ) := by
  have h1 := L3V.vP_v (v := ⟨P, hP, hPe.1⟩) (c : F)
  change L3V.vP P _ = _ at h1
  rw [h1, val_eq_exp_count ⟨P, hP, hPe.1⟩ (L3V.notS_of_ext hP hPe) h𝔞 c hspan, log_exp, neg_neg]

/-- `v_P(ν)` is the multiplicity of `P` in the ideal of `rowOf ν`. -/
theorem vP_rowOf (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (ν : {x : SInt 𝔪 // x ≠ 0})
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    L3V.vP P ((ν : SInt 𝔪) : F) = ((normalizedFactors (H0.rowOf h𝔪 g ν).1.1).count P : ℤ) :=
  vP_of_span hP hPe (H0.rowOf h𝔪 g ν).1.2.1 ν (H0.span_eq_map_rowOf h𝔪 g ν)

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.T12.L2A_Chk
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.HB_Main
/-! # WP-HB, file 7: identity (D) (the exterior conversion) and its companions

MATH3 §3.2, §6.2.  Standing: `Pk : CubicPkg F`, `hG : Good 𝔪`, `hz6`, all exterior primes good.

* `digCoefNu_eq` — **identity (D)**: for `γ ∈ SL₂(R)` with bottom row `(c_v, −c_v x_v)`,
  `a = γ₀₀`, `μ ∈ R ∖ 0`, `ν = μ (b / c_v)²`:
  `coef^S(μ) · e(μ a / c_v) · κ(γ) · ⟨μ, c_v⟩ = digCoefNu(𝔟, v; ν)`;
* `digCoefNu_eq_zero`: `digCoefNu(𝔟, v; ν) = 0` if `ν` is not of the form `μ (b / c_v)²`, `μ ∈ R`;
* `brk_gen` — (0.1): `⟨μ, p⟩ = χ_P(μ p^{−e})⁴ · ∏_{Q ≠ P} χ_Q(p)^{2 v_Q(μ)}`. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

section D

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)

include hG hz6 hgood

omit hG hz6 hgood in
/-- **The complement**: `digCoefNu(𝔟, v; ν) = 0` unless `ν = μ (b / c_v)²` with `μ ∈ R`. -/
theorem digCoefNu_eq_zero {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    (ν : {x : SInt 𝔪 // x ≠ 0})
    (h : ¬ ∃ μ : SInt 𝔪, ((ν : SInt 𝔪) : F) =
      (μ : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2) :
    digCoefNu h𝔪 g 𝔟 v ν = 0 := by
  have hb := C3B.gen_ne_zero g 𝔟 h𝔟
  have hc := cdig_ne_zero g h𝔟 v
  have hν0 := H0.coe_ne_zero ν
  set x : F := ((ν : SInt 𝔪) : F) * ((cdig g 𝔟 v : F) / (g.gen 𝔟 : F)) ^ 2 with hx
  have hxR : x ∉ (placesOf 𝔪).integer F := by
    intro hmem
    apply h
    refine ⟨⟨x, hmem⟩, ?_⟩
    show ((ν : SInt 𝔪) : F) = x * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2
    rw [hx]; field_simp
  have hex : ∃ w : HeightOneSpectrum (𝓞 F), w ∉ placesOf 𝔪 ∧ ¬ w.valuation F x ≤ 1 := by
    by_contra hcon
    push Not at hcon
    exact hxR fun w hw => hcon w hw
  obtain ⟨w, hw, hval⟩ := hex
  have hPe : IsExterior 𝔪 w.asIdeal := ⟨w.ne_bot, L2A.sup_eq_top_of_not_le w.isMaximal hw⟩
  have hPp : w.asIdeal.IsPrime := w.isPrime
  have hcb : (cdig g 𝔟 v : F) / (g.gen 𝔟 : F) ≠ 0 := div_ne_zero hc hb
  have hx0 : x ≠ 0 := mul_ne_zero hν0 (pow_ne_zero _ hcb)
  -- `v_P(x) < 0`
  have hvx : L3V.vP w.asIdeal x < 0 := by
    have h1 := L3V.val_eq_exp_vP (v := w) hx0
    rw [h1, ← exp_zero, exp_le_exp] at hval
    omega
  have h1 := vP_rowOf h𝔪 g ν hPp hPe
  have h3 := vP_of_span hPp hPe h𝔟.1 (g.gen 𝔟) (g.span_gen 𝔟 h𝔟)
  have h4 := vP_cdig g h𝔟 v hPp hPe
  have h5 : L3V.vP w.asIdeal x = L3V.vP w.asIdeal ((ν : SInt 𝔪) : F) +
      2 * (L3V.vP w.asIdeal (cdig g 𝔟 v : F) - L3V.vP w.asIdeal (g.gen 𝔟 : F)) := by
    rw [hx, pow_two, vPI_mul hPp hPe.1 hν0 (mul_ne_zero hcb hcb), vPI_mul hPp hPe.1 hcb hcb,
      div_eq_mul_inv, vPI_mul hPp hPe.1 hc (inv_ne_zero hb), vPI_inv hPp hPe.1]
    ring
  have heN : eNu h𝔪 g 𝔟 ν w.asIdeal + 2 * (if Dnz 𝔟 v w.asIdeal then 1 else 0) < 0 := by
    unfold eNu
    rw [h4] at h5
    linarith
  have hcnt : 0 < (normalizedFactors 𝔟).count w.asIdeal := by
    unfold eNu at heN
    by_contra hcon
    have h0 : (normalizedFactors 𝔟).count w.asIdeal = 0 := by omega
    have hD : ¬ Dnz 𝔟 v w.asIdeal := by
      rintro ⟨hPb, -⟩
      have := Multiset.count_pos.2 (Multiset.mem_toFinset.1 hPb)
      omega
    rw [if_neg hD, h0] at heN
    have : (0 : ℤ) ≤ ((normalizedFactors (H0.rowOf h𝔪 g ν).1.1).count w.asIdeal : ℤ) :=
      Int.natCast_nonneg _
    omega
  have hPb : w.asIdeal ∈ (normalizedFactors 𝔟).toFinset :=
    Multiset.mem_toFinset.2 (Multiset.count_pos.1 hcnt)
  unfold digCoefNu
  refine Finset.prod_eq_zero (factors_subset_mul h𝔪 g h𝔟 ν hPb) ?_
  unfold H.digLoc
  rw [dif_pos hPb]
  by_cases hy : v ⟨w.asIdeal, hPb⟩ = 0
  · have hD : ¬ Dnz 𝔟 v w.asIdeal := fun ⟨_, h2⟩ => h2 hy
    rw [if_neg hD] at heN
    rw [if_pos hy]
    unfold L3V.Wsph
    rw [if_pos (by omega)]
  · have hD : Dnz 𝔟 v w.asIdeal := ⟨hPb, hy⟩
    rw [if_pos hD] at heN
    rw [if_neg hy]
    unfold L3V.Wweyl
    rw [if_pos (by omega)]

end D

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Refl
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-! # WP-HB, file 8: `γ_v`, and the reflected field from the section-level expansion

* `exists_gamma`: for every digit vector there is `γ_v ∈ SL₂(R)` with bottom row
  `(c_v, −c_v x_v)` (the cusp `x_v = −d/c` of MATH3 §3.1);
* `reflected_reindex`: the section-level reflected expansion, a sum over `μ ∈ R ∖ 0` with
  coefficient `coef^S(μ) · e(μ a / c_v) · κ(γ_v) · ⟨μ, c_v⟩` and argument `μ / c_v²`, is the sum over
  `ν ∈ R ∖ 0` with coefficient `digCoefNu(𝔟, v; ν)` and argument `ν / b²` — the shape of
  `AutInput2.reflected` (identity (D) on the range of `μ ↦ μ (b / c_v)²`, `digCoefNu_eq_zero` off
  it);
* `reflected_of_section`: the same with `G = FmOf κ m J [·] (sEmb(·) − y)`. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- `c_v · (ṽ_Q / p_Q) = ccof Q · ṽ_Q` at a nonzero digit. -/
theorem cdig_mul_term (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (Q : PIdx 𝔟) (hQ : v Q ≠ 0) :
    (cdig g 𝔟 v : F) * ((quotLift (v Q) : F) / (g.gen Q.1 : F)) =
      ((ccof g 𝔟 v Q * quotLift (v Q) : SInt 𝔪) : F) := by
  have hcc := congrArg (fun x : SInt 𝔪 => (x : F)) (cfac_mul_ccof g 𝔟 v Q)
  simp only [Subalgebra.coe_mul] at hcc
  have hcf : cfac g 𝔟 v Q = g.gen Q.1 := by unfold cfac; rw [if_neg hQ]
  rw [hcf] at hcc
  rw [← hcc, Subalgebra.coe_mul]
  have := C3B.gen_ne_zero g Q.1 (pidx_ext h𝔟 Q).2
  field_simp

/-- `c_v x_v ∈ R`. -/
theorem cdig_mul_xdig_mem (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) : (cdig g 𝔟 v : F) * H.xdig g 𝔟 v ∈ (placesOf 𝔪).integer F := by
  unfold H.xdig
  rw [Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun Q _ => ?_
  by_cases hQ : v Q = 0
  · have h0 : quotLift (v Q) ∈ Q.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, C3I.mk_quotLift]; exact hQ
    exact mul_mem (SetLike.coe_mem _) (C3B.div_gen_mem g Q.1 (pidx_ext h𝔟 Q).2 _ h0)
  · rw [cdig_mul_term g h𝔟 v Q hQ]
    exact SetLike.coe_mem _

/-- **The matrix `γ_v`**: bottom row `(c_v, −c_v x_v)`. -/
theorem exists_gamma
    (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
      C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
    (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪), γ.1 1 0 = cdig g 𝔟 v ∧
      ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v) := by
  set d : SInt 𝔪 := ⟨-((cdig g 𝔟 v : F) * H.xdig g 𝔟 v), neg_mem (cdig_mul_xdig_mem g h𝔟 v)⟩
    with hd
  have hdF : (d : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v) := rfl
  have hcop : IsCoprime (cdig g 𝔟 v) d := by
    unfold cdig
    refine IsCoprime.prod_left fun Q _ => ?_
    by_cases hQ : v Q = 0
    · unfold cfac; rw [if_pos hQ]; exact isCoprime_one_left
    · have hp := (pidx_ext h𝔟 Q).1
      have hQe := (pidx_ext h𝔟 Q).2
      have hg := hgood Q.1 hp hQe
      set w : HeightOneSpectrum (𝓞 F) := ⟨Q.1, hp, hQe.1⟩ with hw
      have hmax := C3I.isMaximal_v hg
      letI := Ideal.Quotient.field (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
      have hcf : cfac g 𝔟 v Q = g.gen Q.1 := by unfold cfac; rw [if_neg hQ]
      -- `ccof Q` is a unit at `Q`
      have hvalcc : w.valuation F (ccof g 𝔟 v Q : F) = 1 := by
        have h1 := val_cdig g h𝔟 v w hg.notS
        rw [if_pos ⟨Q.2, hQ⟩] at h1
        have hcc := congrArg (fun x : SInt 𝔪 => (x : F)) (cfac_mul_ccof g 𝔟 v Q)
        simp only [Subalgebra.coe_mul] at hcc
        rw [hcf] at hcc
        rw [← hcc, map_mul, C3I.val_pi g hg] at h1
        have h3 : (exp (-1 : ℤ) : ℤᵐ⁰) ≠ 0 := exp_ne_zero
        exact mul_left_cancel₀ h3 (by rw [mul_one]; exact h1)
      have hccm : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (ccof g 𝔟 v Q) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
        intro hmem
        have := (L3V.mem_iff_val hg.notS _).1 hmem
        rw [hvalcc] at this
        exact absurd this (not_le.2 L3V.exp_neg_one_lt_one)
      obtain ⟨hrv, hrx⟩ := res_cdig_xdig g h𝔟 v Q hQ hp hQe.1 hg
      have hdres : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) d =
          -(Ideal.Quotient.mk _ (ccof g 𝔟 v Q) * v Q) := by
        rw [← L3V.res_of_SInt hg.notS, hdF, res_neg hg hrv, hrx]
      have hdm : d ∉ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hdres, neg_eq_zero]
        exact mul_ne_zero hccm hQ
      obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hdm
      have hi' : i ∈ Ideal.span {g.gen Q.1} := by
        rw [g.span_gen Q.1 hQe]; exact hi
      obtain ⟨j, hj⟩ := Ideal.mem_span_singleton'.1 hi'
      rw [hcf]
      exact ⟨j, y, by rw [hj, add_comm]; exact hyi⟩
  obtain ⟨a', b', hab⟩ := hcop
  refine ⟨⟨!![b', -a'; cdig g 𝔟 v, d], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hab
  · simp
  · simp [hdF]

/-- `b / c_v ∈ R`. -/
theorem gen_div_cdig_mem (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) : (g.gen 𝔟 : F) / (cdig g 𝔟 v : F) ∈ (placesOf 𝔪).integer F := by
  intro w hw
  rw [map_div₀, val_eq_exp_count w hw h𝔟.1 (g.gen 𝔟) (g.span_gen 𝔟 h𝔟), val_cdig g h𝔟 v w hw]
  split_ifs with hD
  · obtain ⟨hPb, -⟩ := hD
    have hpos := Multiset.count_pos.2 (Multiset.mem_toFinset.1 hPb)
    rw [div_le_one₀ (by simp), exp_le_exp]
    omega
  · rw [div_one, ← exp_zero, exp_le_exp]
    omega

section D

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)

include hG hz6 hgood

/-- **Reindexing the section-level reflected expansion** along `μ ↦ ν = μ (b / c_v)²`. -/
theorem reflected_reindex {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (hc : γ.1 1 0 = cdig g 𝔟 v)
    (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
    (G : F → ℂ) :
    ∑' μ : {x : SInt 𝔪 // x ≠ 0},
        (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
          sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
          kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F)) *
        G (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2) =
      ∑' ν : {x : SInt 𝔪 // x ≠ 0},
        digCoefNu h𝔪 g 𝔟 v ν * G (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) := by
  have hb := C3B.gen_ne_zero g 𝔟 h𝔟
  have hc0 := cdig_ne_zero g h𝔟 v
  set q : SInt 𝔪 := ⟨(g.gen 𝔟 : F) / (cdig g 𝔟 v : F), gen_div_cdig_mem g h𝔟 v⟩ with hq
  have hqF : (q : F) = (g.gen 𝔟 : F) / (cdig g 𝔟 v : F) := rfl
  have hq0 : q ≠ 0 := by
    intro h0
    have := congrArg (fun x : SInt 𝔪 => (x : F)) h0
    simp only [hqF, ZeroMemClass.coe_zero] at this
    exact div_ne_zero hb hc0 this
  set φ : {x : SInt 𝔪 // x ≠ 0} → {x : SInt 𝔪 // x ≠ 0} := fun μ =>
    ⟨(μ : SInt 𝔪) * q ^ 2, mul_ne_zero μ.2 (pow_ne_zero _ hq0)⟩ with hφ
  have hφF : ∀ μ, (((φ μ : {x : SInt 𝔪 // x ≠ 0}) : SInt 𝔪) : F) =
      ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2 := fun μ => rfl
  have hφinj : Function.Injective φ := by
    intro μ μ' h
    have h1 : (μ : SInt 𝔪) * q ^ 2 = (μ' : SInt 𝔪) * q ^ 2 := congrArg Subtype.val h
    exact Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ hq0) h1)
  have hsupp : Function.support (fun ν : {x : SInt 𝔪 // x ≠ 0} =>
      digCoefNu h𝔪 g 𝔟 v ν * G (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)) ⊆ Set.range φ := by
    intro ν hν
    rw [Function.mem_support] at hν
    by_contra hnot
    apply hν
    rw [digCoefNu_eq_zero h𝔪 g h𝔟 v ν, zero_mul]
    rintro ⟨μ, hμ⟩
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [ZeroMemClass.coe_zero, zero_mul] at hμ
      exact H0.coe_ne_zero ν hμ
    exact hnot ⟨⟨μ, hμ0⟩, Subtype.ext (Subtype.ext hμ.symm)⟩
  rw [← hφinj.tsum_eq hsupp]
  refine tsum_congr fun μ => ?_
  rw [digCoefNu_eq Pk hG hz6 hgood h𝔪 g h𝔟 v γ hc hd μ (φ μ) (hφF μ)]
  congr 2
  rw [hφF]
  field_simp

/-- The reflected field of `AutInput2` at one digit vector, from the section-level expansion
(MATH3 (2.4) with (4.1), i.e. `G.thetaG_reflected` at `x = −x_v`, `γ = γ_v`). -/
theorem reflected_of_section {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (hc : γ.1 1 0 = cdig g 𝔟 v)
    (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
    (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (y : SModel 𝔪 k)
    (Θv : ℂ)
    (hsec : Θv = ∑' μ : {x : SInt 𝔪 // x ≠ 0},
      (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
        sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
        kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F)) *
      H0.FmOf κ m J
        (QuotientAddGroup.mk (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2)).2.2)
        (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2) - y)) :
    Θv = ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
      digCoefNu h𝔪 g 𝔟 v ν *
        H0.FmOf κ m J
          (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
          (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y) := by
  rw [hsec]
  exact reflected_reindex Pk hG hz6 hgood h𝔪 g h𝔟 v γ hc hd
    (fun x => H0.FmOf κ m J (QuotientAddGroup.mk (sEmb 𝔪 k x).2.2) (sEmb 𝔪 k x - y))

/-- **`AutInput2` from the section level** (MATH3 §6.2 `autInput_of_G`, with `eps = −1`): a
function `Θ` with the forward expansion at every `−x_v` (MATH3 §1.3, `G.thetaG_forward`) and the
section-level reflected expansion at `−x_v` for every `γ` with bottom row `(c_v, −c_v x_v)`
(MATH3 (2.4), (4.1), `G.thetaG_reflected`) gives the repaired contract. -/
theorem autInput2_of_section (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)
    (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (Θ : F → SModel 𝔪 k → ℂ)
    (hfwd : ∀ (𝔟 : Ideal (𝓞 F)) (_ : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟) (y : SModel 𝔪 k),
      Θ (-(H.xdig g 𝔟 v)) y =
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
          sAddChar 𝔪 (((ν : SInt 𝔪) : F) * H.xdig g 𝔟 v) *
            (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g ν) *
              L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y)))
    (hrefl : ∀ (𝔟 : Ideal (𝓞 F)) (_ : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
      (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)), γ.1 1 0 = cdig g 𝔟 v →
      ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v) → ∀ y : SModel 𝔪 k,
      Θ (-(H.xdig g 𝔟 v)) y = ∑' μ : {x : SInt 𝔪 // x ≠ 0},
        (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
          sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
          kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F)) *
        H0.FmOf κ m J
          (QuotientAddGroup.mk (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2)).2.2)
          (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2) - y)) :
    Nonempty (AutInput2 h𝔪 g k κ m J) := by
  have he : ∀ x : F, (((-1 : SInt 𝔪) : SInt 𝔪) : F) * x = -x := fun x => by
    rw [Subalgebra.coe_neg, OneMemClass.coe_one]; ring
  refine ⟨⟨Θ, -1, Or.inr rfl, fun 𝔟 h𝔟 v y => ?_, fun 𝔟 h𝔟 v y => ?_⟩⟩
  · rw [he, hfwd 𝔟 h𝔟 v y]
    refine tsum_congr fun ν => ?_
    rw [mul_neg, neg_neg]
  · obtain ⟨γ, hc, hd⟩ := exists_gamma hgood g h𝔟 v
    rw [he]
    exact reflected_of_section Pk hG hz6 hgood h𝔪 g h𝔟 v γ hc hd κ m J y _
      (hrefl 𝔟 h𝔟 v γ hc hd y)

end D

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Sec
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-! # WP-HB, file 9: the contract at the section level, `SecCut → AutCut2`

`SecCut n F ι` is `AutCut2` with `Nonempty (AutInput2 …)` replaced by what MATH3 §6.1 (6) gives
at the section level: a symbol package `Pk`, a function `Θ`, its forward expansion at every
`−x_v`, and its reflected expansion at the cusp `−x_v` for every `γ ∈ SL₂(R)` with bottom row
`(c_v, −c_v x_v)`, in the variable `μ ∈ R ∖ 0`, with coefficient
`coef^S(μ) · e(μ a / c_v) · κ(γ) · ⟨μ, c_v⟩` and argument `μ / c_v²`.
`autCut2_of_secCut` is the digit conversion (identity (D)); `eps = −1`. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

/-- **`SecCut → AutCut2`**: the digit conversion.  (`Good 𝔪` from `A.exists_cutoff_good`, good
primes from `C3I.good_of_exterior`; the symbol package `Pk` is the one of `SecCut`.) -/
theorem autCut2_of_secCut_oai (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (h : SecCut n F ι) : AutCut2 n F ι := by
  obtain ⟨N₀, hN⟩ := h
  obtain ⟨z6, hz6⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  obtain ⟨N₁, hGood⟩ := A.exists_cutoff_good F
  refine ⟨max N₀ (max N₁ (C3I.cutN F)), fun 𝔪 h𝔪 hs g => ?_⟩
  have hs0 : SmallPrimesDvd N₀ 𝔪 := fun Q hQ hQ0 hle =>
    hs Q hQ hQ0 (hle.trans (le_max_left _ _))
  have hs1 : SmallPrimesDvd N₁ 𝔪 := fun Q hQ hQ0 hle =>
    hs Q hQ hQ0 (hle.trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hG : Good 𝔪 := hGood 𝔪 h𝔪 hs1
  have hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
      C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)) := fun P hP hext =>
    C3I.good_of_exterior n hn0 hn ((le_max_right _ _).trans (le_max_right _ _)) hs hP hext
  obtain ⟨k₀, hk⟩ := hN 𝔪 h𝔪 hs0 g
  refine ⟨k₀, fun k hk' => ?_⟩
  obtain ⟨c, α, hc, hα, hα', hm⟩ := hk k hk'
  refine ⟨c, α, hc, hα, hα', fun m hm' => ?_⟩
  obtain ⟨J, bf, hJ, hbf, Pk, Θ, hfwd, hrefl⟩ := hm m hm'
  exact ⟨J, bf, hJ, hbf,
    autInput2_of_section Pk hG hz6 hgood h𝔪 g (K.kappaB c) m J Θ hfwd hrefl⟩

end

end ArtinKP.HB
end

theorem solution.{u_1} : type_of% @ArtinKP.HB.autCut2_of_secCut_oai.{u_1} := @ArtinKP.HB.autCut2_of_secCut_oai.{u_1}
