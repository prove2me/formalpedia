-- Prove2me | solution 1 for ArtinKP.HB.local_D
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:14.252931+00:00
-- url     : https://prove2.me/submissions/19d62a9f-4e01-4c84-a99c-f8200d3e096e

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
import Theorems.Thm_ArtinKP_HB_loc_weyl

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

end good

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3M_Sum
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

/-! ### Coercions -/

lemma coe_mul' (x y : SInt 𝔪) : ((x * y : SInt 𝔪) : F) = (x : F) * (y : F) := rfl

/-! ### The Poisson summand -/

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

/-! ### Gauss sums -/

end C3M

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3M_Mul
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Change of generators -/

lemma unit_coe_ne_zero (u : (SInt 𝔪)ˣ) : ((u : SInt 𝔪) : F) ≠ 0 := by
  intro h0
  have : ((u : SInt 𝔪) : F) * (((u⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← coe_mul', Units.mul_inv]; rfl
  rw [h0, zero_mul] at this; exact zero_ne_one this

/-! ### Generators and residue symbols -/

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

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

lemma nf_prime' {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

lemma cnt_prime {P Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    cnt P Q = if P = Q then 1 else 0 := by
  unfold cnt; rw [nf_prime' hQ hQ0, Multiset.count_singleton]

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
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma gen_ne_zero' (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) : (g.gen I : F) ≠ 0 := by
  intro h0
  have := val_gen_eq h g I hI
  rw [h0, map_zero] at this
  exact exp_ne_zero this.symm

lemma vP_p : vP v.asIdeal (g.gen v.asIdeal : F) = 1 := by
  rw [vP_v, C3I.val_pi g h, log_exp, neg_neg]

lemma p_ne_zero : (g.gen v.asIdeal : F) ≠ 0 := gen_ne_zero' h g _ h.ext

lemma val_unitPart {x : F} (hx : x ≠ 0) :
    v.valuation F (x * (g.gen v.asIdeal : F) ^ (-(vP v.asIdeal x))) = 1 := by
  rw [map_mul, map_zpow₀, C3I.val_pi g h, val_eq_exp_vP hx, ← exp_zsmul, ← exp_add]
  simp

variable {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include hω

lemma uSym_eq (x : F) :
    uSym g v.asIdeal x = C3I.chi ι h hω (res 𝔪 v (x * (g.gen v.asIdeal : F) ^ (-(vP v.asIdeal x)))) :=
  localSymbol_eq h hω _

lemma uSym_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    uSym g v.asIdeal (x * y) = uSym g v.asIdeal x * uSym g v.asIdeal y := by
  rw [uSym_eq h g hω, uSym_eq h g hω, uSym_eq h g hω, ← map_mul,
    ← res_mul h.notS (val_unitPart h g hx).le (val_unitPart h g hy).le, vP_mul hx hy]
  congr 2
  rw [neg_add, zpow_add₀ (p_ne_zero h g)]; ring

lemma uSym_pow_six {x : F} (hx : x ≠ 0) : uSym g v.asIdeal x ^ 6 = 1 := by
  rw [uSym_eq h g hω]
  exact C3I.chi_pow_six_apply h hω (res_ne_zero_of_val_eq_one h.notS (val_unitPart h g hx))

lemma uSym_pow {x : F} (hx : x ≠ 0) (n : ℕ) : uSym g v.asIdeal (x ^ n) = uSym g v.asIdeal x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, uSym_eq h g hω, vP_v]
    simp only [map_one, log_one, neg_zero, zpow_zero, mul_one]
    rw [res_one h.notS, map_one]
  | succ n ih => rw [pow_succ, uSym_mul h g hω (pow_ne_zero _ hx) hx, ih, pow_succ]

lemma uSym_inv {x : F} (hx : x ≠ 0) : uSym g v.asIdeal x⁻¹ = (uSym g v.asIdeal x)⁻¹ := by
  have h1 := uSym_mul h g hω hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx] at h1
  have h2 : uSym g v.asIdeal (1 : F) = 1 := by
    rw [uSym_eq h g hω, vP_v]
    simp only [map_one, log_one, neg_zero, zpow_zero, mul_one]
    rw [res_one h.notS, map_one]
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

lemma uSym_of_val_one {t : F} (ht : v.valuation F t = 1) :
    uSym g v.asIdeal t = localSymbol ι 𝔪 v.asIdeal t := by
  unfold uSym
  rw [vP_v, ht, log_one, neg_zero, neg_zero, zpow_zero, mul_one]

lemma uSym_SInt {y : SInt 𝔪} (hy : y ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    uSym g v.asIdeal (y : F) = sexticResidueSymbol ι 𝔪 v.asIdeal y := by
  rw [uSym_of_val_one h g hω (C3I.val_eq_one_of_not_mem h hy), localSymbol_eq h hω,
    res_of_SInt h.notS, C3I.chi_mk h hω]

lemma uSym_pow_six_unit (μ : (SInt 𝔪)ˣ) :
    uSym g v.asIdeal (((μ : SInt 𝔪) : F) ^ 6) = 1 := by
  have hμ : ((μ : SInt 𝔪) : F) ≠ 0 := by
    intro h0; have := C3I.val_unit (v := v) h μ; rw [h0, map_zero] at this; exact zero_ne_one this
  rw [uSym_pow h g hω hμ, uSym_pow_six h g hω hμ]

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

/-! ### The coefficient at `ν` -/

/-- `ν = u⁶ · rowElt (rowOf ν)` with `u ∈ U_S`. -/
theorem exists_unit_six (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    ∃ u : (SInt 𝔪)ˣ, ((ν : SInt 𝔪) : F) =
      (rowElt g (H0.rowOf h𝔪 g ν) : F) * ((u : SInt 𝔪) : F) ^ 6 := by
  obtain ⟨δ, hδ⟩ := (H0.gamOf h𝔪 g ν).2
  refine ⟨H0.uInt δ, ?_⟩
  rw [H0.coe_eq_gamOf_mul h𝔪 g ν, ← hδ, mul_comm]
  simp only [powMonoidHom_apply, H0.coe_uInt, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Tame
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-HB, file 3: the tame formula for `brk` in terms of the unit-part symbols `L3V.uSym`

MATH3 (0.1) in a form symmetric in the two arguments.  At a good exterior prime `P`
(`C3I.Good`), with `u_P(x) = L3V.uSym g P x = χ_P(x · p^{−v_P(x)})`, `p = gen P`:

* `iota3_hv_unit`: `ι (t, π)_P = χ_P(t)²` for a `P`-unit `t ∈ F` and a uniformizer `π`;
* `iota3_hv_tame`: `ι (x, y)_P = (u_P(x)²)^{v_P(y)} · ((u_P(y)²)^{v_P(x)})⁻¹` for `x, y ∈ Fˣ`
  (no sign: `−1` is a cube);
* `brk_tame`: `⟨x, y⟩ · ∏_{P ∈ 𝒯} ι (x, y)_P = 1` for every finite set `𝒯` of exterior primes
  outside of which `x`, `y` are units (product formula `CubicPkg.HS_mul_prod'`). -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

section loc

variable {v : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (g : AllowedGen ι 𝔪)

include h hω g

/-- `u_P(p) = 1` for `p = gen P`. -/
theorem uSym_gen : L3V.uSym g v.asIdeal (g.gen v.asIdeal : F) = 1 := by
  unfold L3V.uSym
  rw [L3V.vP_p h g, zpow_neg, zpow_one, mul_inv_cancel₀ (L3V.p_ne_zero h g),
    L3V.localSymbol_eq h hω, L3V.res_one h.notS, map_one]

end loc

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

theorem coe_ccof (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) :
    ((ccof g 𝔟 v P : SInt 𝔪) : F) = ∏ Q ∈ ({P}ᶜ : Finset (PIdx 𝔟)), (cfac g 𝔟 v Q : F) := by
  unfold ccof
  exact map_prod ((placesOf 𝔪).integer F).subtype _ _

theorem cdig_ne_zero (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) : (cdig g 𝔟 v : F) ≠ 0 := by
  rw [coe_cdig]
  exact Finset.prod_ne_zero_iff.2 fun P _ => cfac_ne_zero g h𝔟 v P

theorem ccof_ne_zero (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) : (ccof g 𝔟 v P : F) ≠ 0 := by
  rw [coe_ccof]
  exact Finset.prod_ne_zero_iff.2 fun Q _ => cfac_ne_zero g h𝔟 v Q

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

theorem gen_mem_map (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hPe : IsExterior 𝔪 P) :
    g.gen P ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen P hPe]; exact Ideal.mem_span_singleton_self _

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
-- module Solutions.Artin.T12.L3X_Rev
/-! # L3X_Rev: the reflected orbit unfolding

`∫_{X_l} Φ(y) · (reflected expansion)(y) = Σ_z E_z L(ν_z)⁻¹ H_{[ν_z]}(|ν_z|_S / l)`: the sum over
`γ ∈ Γ` is collapsed by the partition of unity `ρ`, then `y ↦ ν/y` maps the sheet `X_l` to
`X_{|ν|/l}`. Absolute convergence comes from the product majorant of the reflected `S`-function
and `Σ N𝔷^{-2} < ∞`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical ENNReal

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem span_rowElt_R (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    Ideal.span {rowElt g z} = z.1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [rowElt, ← g.span_gen _ z.1.2]
  exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

end

end ArtinPrimitiveRoots.L3X
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

/-- `e₀(P) = v_P(μ) − 2·[P ∈ D]` when `ν = μ (b / c_v)²`. -/
theorem eNu_eq (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (μ ν : {x : SInt 𝔪 // x ≠ 0})
    (hν : ((ν : SInt 𝔪) : F) =
      ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2)
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    eNu h𝔪 g 𝔟 ν P = ((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ) -
      2 * (if Dnz 𝔟 v P then 1 else 0) := by
  have hb := C3B.gen_ne_zero g 𝔟 h𝔟
  have hc := cdig_ne_zero g h𝔟 v
  have hμ := H0.coe_ne_zero μ
  have h1 := vP_rowOf h𝔪 g ν hP hPe
  have h2 := vP_rowOf h𝔪 g μ hP hPe
  have h3 := vP_of_span hP hPe h𝔟.1 (g.gen 𝔟) (g.span_gen 𝔟 h𝔟)
  have h4 := vP_cdig g h𝔟 v hP hPe
  have hbc : (g.gen 𝔟 : F) / (cdig g 𝔟 v : F) ≠ 0 := div_ne_zero hb hc
  have h5 : L3V.vP P ((ν : SInt 𝔪) : F) = L3V.vP P ((μ : SInt 𝔪) : F) +
      2 * (L3V.vP P (g.gen 𝔟 : F) - L3V.vP P (cdig g 𝔟 v : F)) := by
    rw [hν, pow_two, vPI_mul hP hPe.1 hμ (mul_ne_zero hbc hbc), vPI_mul hP hPe.1 hbc hbc,
      div_eq_mul_inv, vPI_mul hP hPe.1 hb (inv_ne_zero hc), vPI_inv hP hPe.1]
    ring
  unfold eNu
  rw [h4] at h5
  linarith

section D

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
  (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
  (hc : γ.1 1 0 = cdig g 𝔟 v)
  (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
  (μ ν : {x : SInt 𝔪 // x ≠ 0})
  (hν : ((ν : SInt 𝔪) : F) = ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2)

include hz6 hgood h𝔟 hc hd hν

/-- **Identity (D) at one exterior prime.** -/
theorem local_D_oai (m : PIdx 𝔟 → SInt 𝔪)
    (hm : ∀ Q : PIdx 𝔟, v Q ≠ 0 →
      m Q * ccof g 𝔟 v Q - 1 ∈ Q.1.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    L3V.Wsph g P ((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ)
        ((rowElt g (H0.rowOf h𝔪 g μ) : F) *
          (g.gen P : F) ^ (-((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ))) *
      (if hPb : P ∈ (normalizedFactors 𝔟).toFinset then
        (if v ⟨P, hPb⟩ = 0 then 1
          else sAddChar 𝔪 ((((μ : SInt 𝔪) * γ.1 0 0 * m ⟨P, hPb⟩ : SInt 𝔪) : F) /
            (g.gen P : F)))
        else 1) *
      (if hPb : P ∈ (normalizedFactors 𝔟).toFinset then
        (if v ⟨P, hPb⟩ = 0 then 1 else sexticResidueSymbol ι 𝔪 P (γ.1 1 1) ^ 2)
        else 1)⁻¹ *
      ((L3V.uSym g P ((μ : SInt 𝔪) : F) ^ 2) ^ (L3V.vP P (cdig g 𝔟 v : F)) *
        ((L3V.uSym g P (cdig g 𝔟 v : F) ^ 2) ^ (L3V.vP P ((μ : SInt 𝔪) : F)))⁻¹)⁻¹ =
    H.digLoc g 𝔟 v P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P) := by
  set w : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩ with hw
  have hg : C3I.Good 𝔪 w := hgood P hP hPe
  haveI := C3I.finite_L hg
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set e : ℕ := (normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P with he
  set c : SInt 𝔪 := cdig g 𝔟 v with hcdef
  have hμ0 : ((μ : SInt 𝔪) : F) ≠ 0 := H0.coe_ne_zero μ
  have hc0 : (c : F) ≠ 0 := cdig_ne_zero g h𝔟 v
  have hb0 : (g.gen 𝔟 : F) ≠ 0 := C3B.gen_ne_zero g 𝔟 h𝔟
  have hp0 : (g.gen P : F) ≠ 0 := C3B.gen_ne_zero g P hPe
  have hvμ : L3V.vP P ((μ : SInt 𝔪) : F) = (e : ℤ) := vP_rowOf h𝔪 g μ hP hPe
  have hvc : L3V.vP P (c : F) = if Dnz 𝔟 v P then 1 else 0 := vP_cdig g h𝔟 v hP hPe
  have heN := eNu_eq h𝔪 g h𝔟 v μ ν hν hP hPe
  rw [← he] at heN
  set U : ℂ := L3V.uSym g P ((μ : SInt 𝔪) : F) with hU
  set Xc : ℂ := L3V.uSym g P (c : F) with hXc
  have hU6 : U ^ 6 = 1 := L3V.uSym_pow_six hg g hz6 hμ0
  have hXc6 : Xc ^ 6 = 1 := L3V.uSym_pow_six hg g hz6 hc0
  -- the level-one coefficient
  have hW1 : L3V.Wsph g P (e : ℤ) ((rowElt g (H0.rowOf h𝔪 g μ) : F) * (g.gen P : F) ^ (-(e : ℤ)))
      = U ^ (2 * e) * L3V.Wv g P e := by
    obtain ⟨u, hu⟩ := exists_unit_six h𝔪 g μ
    have hu0 : (((u : SInt 𝔪) : F)) ^ 6 ≠ 0 := pow_ne_zero _ (C3M.unit_coe_ne_zero u)
    have hr0 : (rowElt g (H0.rowOf h𝔪 g μ) : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hu; exact hμ0 hu
    have hvr : L3V.vP P (rowElt g (H0.rowOf h𝔪 g μ) : F) = (e : ℤ) :=
      vP_of_span hP hPe (H0.rowOf h𝔪 g μ).1.2.1 _ (L3X.span_rowElt_R g _)
    have h1 : L3V.localSymbol ι 𝔪 P
        ((rowElt g (H0.rowOf h𝔪 g μ) : F) * (g.gen P : F) ^ (-(e : ℤ))) =
        L3V.uSym g P (rowElt g (H0.rowOf h𝔪 g μ) : F) := by
      unfold L3V.uSym; rw [hvr]
    have h2 : U = L3V.uSym g P (rowElt g (H0.rowOf h𝔪 g μ) : F) := by
      rw [hU, hu]
      have := L3V.uSym_mul hg g hz6 hr0 hu0
      rw [L3V.uSym_pow_six_unit hg g hz6 u, mul_one] at this
      exact this
    unfold L3V.Wsph
    rw [if_neg (by omega), Int.toNat_natCast, h1, ← h2]
  -- the unit part of the reflected frequency
  have hxν : ((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2 = ((μ : SInt 𝔪) : F) / (c : F) ^ 2 := by
    rw [hν]; field_simp
  have hx0 : ((μ : SInt 𝔪) : F) / (c : F) ^ 2 ≠ 0 := div_ne_zero hμ0 (pow_ne_zero _ hc0)
  have hvx : L3V.vP P (((μ : SInt 𝔪) : F) / (c : F) ^ 2) = eNu h𝔪 g 𝔟 ν P := by
    rw [div_eq_mul_inv, vPI_mul hP hPe.1 hμ0 (inv_ne_zero (pow_ne_zero _ hc0)),
      vPI_inv hP hPe.1, pow_two, vPI_mul hP hPe.1 hc0 hc0, hvμ, hvc, heN]
    ring
  have htx : tNu h𝔪 g 𝔟 ν P = ((μ : SInt 𝔪) : F) / (c : F) ^ 2 *
      (g.gen P : F) ^ (-(L3V.vP P (((μ : SInt 𝔪) : F) / (c : F) ^ 2))) := by
    unfold tNu; rw [hxν, hvx]
  have htval : w.valuation F (tNu h𝔪 g 𝔟 ν P) = 1 := by
    rw [htx]; exact L3V.val_unitPart hg g hx0
  have hls : L3V.localSymbol ι 𝔪 P (tNu h𝔪 g 𝔟 ν P) = U * (Xc ^ 2)⁻¹ := by
    have h1 : L3V.localSymbol ι 𝔪 P (tNu h𝔪 g 𝔟 ν P) =
        L3V.uSym g P (((μ : SInt 𝔪) : F) / (c : F) ^ 2) := by
      rw [htx]; rfl
    rw [h1, div_eq_mul_inv]
    have h2 := L3V.uSym_mul hg g hz6 hμ0 (inv_ne_zero (pow_ne_zero 2 hc0))
    have h3 := L3V.uSym_inv hg g hz6 (pow_ne_zero 2 hc0)
    have h4 := L3V.uSym_pow hg g hz6 hc0 2
    rw [h3, h4] at h2
    exact h2
  have i3 : (Xc ^ 2)⁻¹ = Xc ^ 4 := inv_eq_of_mul_eq_one_left (by rw [← pow_add, hXc6])
  by_cases hD : Dnz 𝔟 v P
  · -- a nonzero digit at `P`
    obtain ⟨hPb, hy⟩ := hD
    have hDnz : Dnz 𝔟 v P := ⟨hPb, hy⟩
    set Q : PIdx 𝔟 := ⟨P, hPb⟩ with hQ
    rw [if_pos hDnz] at hvc heN
    have hcf : cfac g 𝔟 v Q = g.gen P := by unfold cfac; rw [if_neg hy]
    have hcc : (c : F) = (g.gen P : F) * (ccof g 𝔟 v Q : F) := by
      have := congrArg (fun x : SInt 𝔪 => (x : F)) (cfac_mul_ccof g 𝔟 v Q)
      simp only [Subalgebra.coe_mul] at this
      rw [hcf] at this
      exact this.symm
    have hcc0 : (ccof g 𝔟 v Q : F) ≠ 0 := ccof_ne_zero g h𝔟 v Q
    have hvalcc : w.valuation F (ccof g 𝔟 v Q : F) = 1 := by
      have h1 := val_cdig g h𝔟 v w hg.notS
      rw [if_pos hDnz] at h1
      have h2 : w.valuation F (c : F) =
          w.valuation F (g.gen P : F) * w.valuation F (ccof g 𝔟 v Q : F) := by
        rw [hcc, map_mul]
      rw [h1, C3I.val_pi g hg] at h2
      have h3 : (exp (-1 : ℤ) : ℤᵐ⁰) ≠ 0 := exp_ne_zero
      exact (mul_left_cancel₀ h3 (by rw [mul_one]; exact h2)).symm
    have hccm : ccof g 𝔟 v Q ∉ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      intro hmem
      have := (L3V.mem_iff_val hg.notS _).1 hmem
      rw [hvalcc] at this
      exact absurd this (not_le.2 L3V.exp_neg_one_lt_one)
    have hXcc : Xc = sexticResidueSymbol ι 𝔪 P (ccof g 𝔟 v Q) := by
      have h1 := L3V.uSym_mul hg g hz6 hp0 hcc0
      rw [uSym_gen hg hz6 g, one_mul, L3V.uSym_SInt hg g hz6 hccm] at h1
      rw [hXc, hcc]; exact h1
    -- `d ≡ −ccof · y`
    obtain ⟨hrv, hrx⟩ := res_cdig_xdig g h𝔟 v Q hy hP hPe.1 hg
    have hdres : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (γ.1 1 1) =
        -(Ideal.Quotient.mk _ (ccof g 𝔟 v Q) * v Q) := by
      rw [← L3V.res_of_SInt hg.notS, hd, res_neg hg hrv, hrx]
    -- `a d ≡ 1`
    have hcm : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (γ.1 1 0) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, hc, hcdef, ← cfac_mul_ccof g 𝔟 v Q, hcf]
      exact Ideal.mul_mem_right _ _ (gen_mem_map g hPe)
    have had : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (γ.1 0 0) *
        Ideal.Quotient.mk _ (γ.1 1 1) = 1 := by
      have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
        have := γ.2
        rwa [Matrix.det_fin_two] at this
      have := congrArg (Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))) hdet
      rw [map_sub, map_mul, map_mul, hcm, mul_zero, sub_zero, map_one] at this
      exact this
    have hm' : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (m Q) *
        Ideal.Quotient.mk _ (ccof g 𝔟 v Q) = 1 := by
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact hm Q hy
    have hμ0' : e = 0 → L3V.res 𝔪 w (tNu h𝔪 g 𝔟 ν P) *
        Ideal.Quotient.mk _ (ccof g 𝔟 v Q) ^ 2 = Ideal.Quotient.mk _ (μ : SInt 𝔪) := by
      intro he0
      have h1 : tNu h𝔪 g 𝔟 ν P * ((ccof g 𝔟 v Q ^ 2 : SInt 𝔪) : F) = ((μ : SInt 𝔪) : F) := by
        rw [htx, hvx, heN, he0, hcc, Subalgebra.coe_pow]
        simp only [Nat.cast_zero, zero_sub, neg_neg, mul_one]
        rw [zpow_ofNat]
        field_simp
      rw [← map_pow, ← L3V.res_of_SInt hg.notS, ← L3V.res_mul hg.notS htval.le
        (C3I.val_le_one hg.notS _), h1, L3V.res_of_SInt hg.notS]
    have hμ1 : e ≠ 0 →
        Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (μ : SInt 𝔪) = 0 := by
      intro he0
      rw [Ideal.Quotient.eq_zero_iff_mem, L3V.mem_iff_val hg.notS]
      have h1 := L3V.val_eq_exp_vP (v := w) hμ0
      change _ = exp (-(L3V.vP P _)) at h1
      rw [h1, hvμ, exp_le_exp]
      omega
    have key := loc_weyl hg hz6 g (e := e) htval hy (μ : SInt 𝔪) (γ.1 0 0) (γ.1 1 1) (m Q)
      (ccof g 𝔟 v Q) U hU6 (by rw [← hXcc]; exact hls) hdres had hm' hμ0' hμ1
    rw [dif_pos hPb, if_neg hy, dif_pos hPb, if_neg hy, hW1, hvμ, hvc]
    unfold H.digLoc
    rw [dif_pos hPb, if_neg hy, heN, hXcc]
    simp only [mul_one]
    exact key
  · -- no digit, or a zero digit, at `P`
    rw [if_neg hD] at hvc heN
    have hdl : H.digLoc g 𝔟 v P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P) =
        L3V.Wsph g P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P) := by
      unfold H.digLoc
      split_ifs with h1 h2
      · rfl
      · exact absurd ⟨h1, h2⟩ hD
      · rfl
    have hXe : Xc ^ (8 * e) = Xc ^ (2 * e) := by
      rw [show 8 * e = 2 * e + 6 * e by ring, pow_add, pow_mul Xc 6, hXc6, one_pow, mul_one]
    have key : U ^ (2 * e) * L3V.Wv g P e * 1 * (1 : ℂ)⁻¹ *
        ((U ^ 2) ^ (0 : ℤ) * ((Xc ^ 2) ^ (e : ℤ))⁻¹)⁻¹ =
        H.digLoc g 𝔟 v P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P) := by
      rw [hdl, heN]
      unfold L3V.Wsph
      simp only [mul_zero, sub_zero]
      rw [if_neg (by omega), Int.toNat_natCast, hls, i3, zpow_zero, zpow_natCast, one_mul,
        inv_inv, inv_one]
      calc U ^ (2 * e) * L3V.Wv g P e * 1 * 1 * (Xc ^ 2) ^ e
          = U ^ (2 * e) * Xc ^ (2 * e) * L3V.Wv g P e := by ring
        _ = U ^ (2 * e) * Xc ^ (8 * e) * L3V.Wv g P e := by rw [hXe]
        _ = _ := by ring
    rw [hW1, hvμ, hvc]
    by_cases hPb : P ∈ (normalizedFactors 𝔟).toFinset
    · have hv0 : v ⟨P, hPb⟩ = 0 := by
        by_contra h; exact hD ⟨hPb, h⟩
      rw [dif_pos hPb, if_pos hv0, dif_pos hPb, if_pos hv0]
      exact key
    · rw [dif_neg hPb, dif_neg hPb]
      exact key

end D

end

end ArtinKP.HB
end

theorem solution.{u_1} : type_of% @ArtinKP.HB.local_D_oai.{u_1} := @ArtinKP.HB.local_D_oai.{u_1}
