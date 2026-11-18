-- Prove2me | solution 1 for ArtinKP.HB.digCoefNu_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:10.845554+00:00
-- url     : https://prove2.me/submissions/a6b4e1e6-0c2f-4de9-910a-f8e62f7da3b5

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
import Theorems.Thm_ArtinKP_HB_local_D

section
-- module Solutions.Artin.KP.A_Pkg
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-A: the global cubic symbol package and the `S`-Hilbert pairing

`CubicPkg F` is a universe-polymorphic, completion-free form of `C0Y.SymbolPkg F 3`: local cubic
Hilbert symbols `hv v : Fˣ →* Fˣ →* μ₃(F)` evaluated on *global* elements, with Steinberg, the
product formula, triviality on units and the tame formula at places prime to `3`, and local
constancy (`deep`).  Everything in WP-A is derived from a `CubicPkg`.

The orientation is pinned by the field `tame`: `hv v a π ≡ a^{(Nv-1)/3} (mod v)` for a `v`-unit
`a` and a uniformizer `π`.

Main results: `CubicPkg.skew`, `CubicPkg.self`, `CubicPkg.isTame` (the bridge to `A_Local`),
`CubicPkg.tame_zpow` (A1 for a unit against any element), `CubicPkg.tame_formula` (A1),
`CubicPkg.HS` (the pairing `(a,b)_S`), `CubicPkg.HS_mul_prod` (A2, product formula),
`CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`, `CubicPkg.exists_isDeepLevel`,
`CubicPkg.HS_deep_right/left` (A4).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace CubicPkg

variable (P : CubicPkg F)

/-- (A1) **tame formula**: with `v a = exp (-α)`, `v b = exp (-β)` and a uniformizer `π`,
`(a, b)_v = (a^β / b^α, π)_v`; the right side is `≡ (a^β/b^α)^{(Nv-1)/3}` by `tame`.
(The sign `(-1)^{αβ}` of the classical formula is a cube.) -/
theorem tame_formula (v : HeightOneSpectrum (𝓞 F)) (h3 : (3 : 𝓞 F) ∉ v.asIdeal) (a b π : Fˣ)
    (α β : ℤ) (ha : v.valuation F (a : F) = WithZero.exp (-α))
    (hb : v.valuation F (b : F) = WithZero.exp (-β))
    (hπ : v.valuation F (π : F) = WithZero.exp (-1 : ℤ)) :
    P.hv v a b = P.hv v (a ^ β / b ^ α) π := by
  set u : Fˣ := a / π ^ α with hu
  set w : Fˣ := b / π ^ β with hw
  have hπz : ∀ n : ℤ, v.valuation F ((π ^ n : Fˣ) : F) = WithZero.exp (-n) := by
    intro n
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg,
      mul_one]
  have hu1 : v.valuation F (u : F) = 1 := by
    rw [hu, Units.val_div_eq_div_val, map_div₀, ha, hπz, div_self WithZero.exp_ne_zero]
  have hw1 : v.valuation F (w : F) = 1 := by
    rw [hw, Units.val_div_eq_div_val, map_div₀, hb, hπz, div_self WithZero.exp_ne_zero]
  have hau : a = π ^ α * u := by rw [hu, mul_div_cancel]
  have hbw : b = π ^ β * w := by rw [hw, mul_div_cancel]
  have e1 : a ^ β / b ^ α = u ^ β / w ^ α := by
    rw [hau, hbw, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm α β]
    rw [mul_div_mul_left_eq_div]
  have huw : P.hv v u w = 1 := P.unit_unit v h3 u w hu1 hw1
  have hππ : P.hv v π π = 1 := P.self v π
  have hπw : P.hv v π w = (P.hv v w π)⁻¹ := P.skew' v π w
  rw [e1, hau, hbw]
  simp only [map_mul, map_zpow, map_div, MonoidHom.mul_apply, MonoidHom.div_apply,
    MonoidHom.zpow_apply, huw, hππ, hπw, one_zpow, mul_one, one_mul, inv_zpow]
  rw [div_eq_mul_inv, mul_comm]

/-! ### The `S`-part -/

/-! ### Deep units -/

end CubicPkg

end ArtinKP.A
end
end

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
-- module Solutions.Artin.T12.C3I_Add
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma hasWit_add {x x' : F} (h : HasWit 𝔪 x) (h' : HasWit 𝔪 x') : HasWit 𝔪 (x + x') := by
  obtain ⟨y, hy1, hy2⟩ := h
  obtain ⟨y', hy1', hy2'⟩ := h'
  refine ⟨y + y', by rw [show x + x' - (y + y') = (x - y) + (x' - y') by ring]; exact add_mem hy1 hy1',
    fun v hv => (Valuation.map_add _ _ _).trans (max_le (hy2 v hv) (hy2' v hv))⟩

lemma hasWit_of_mem {x : F} (hx : x ∈ (placesOf 𝔪).integer F) : HasWit 𝔪 x :=
  ⟨0, by simpa using hx, fun v _ => by simp⟩

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

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

lemma isCoprime_map {I J : Ideal (𝓞 F)} (h : IsCoprime I J) :
    IsCoprime (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (J.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [← Ideal.map_sup, h, Ideal.map_top]

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

lemma cop_gen (g : AllowedGen ι 𝔪) {𝔟 𝔞 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (h : IsCoprime 𝔟 𝔞) : IsCoprime (Ideal.span {g.gen 𝔟}) (𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  rw [g.span_gen 𝔟 h𝔟]; exact isCoprime_map h

lemma exists_ab {x y : SInt 𝔪} (h : IsCoprime (Ideal.span {x}) (Ideal.span {y})) :
    ∃ α β : SInt 𝔪, α * x + β * y = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.mp hj
  exact ⟨α, β, hij⟩

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots
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

lemma nf_prime' {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) : normalizedFactors Q = {Q} := by
  rw [normalizedFactors_irreducible ((Ideal.prime_of_isPrime hQ0 hQ).irreducible), normalize_eq]

lemma cnt_prime {P Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    cnt P Q = if P = Q then 1 else 0 := by
  unfold cnt; rw [nf_prime' hQ hQ0, Multiset.count_singleton]

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

/-! ### The additive character on finite sums -/

theorem sAddChar_sum {α : Type*} (s : Finset α) (f : α → F)
    (hf : ∀ a ∈ s, C3I.HasWit 𝔪 (f a)) :
    C3I.HasWit 𝔪 (∑ a ∈ s, f a) ∧ sAddChar 𝔪 (∑ a ∈ s, f a) = ∏ a ∈ s, sAddChar 𝔪 (f a) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact ⟨C3I.hasWit_of_mem (zero_mem _), C3B.sAddChar_of_mem 0 (zero_mem _)⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have h1 := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨C3I.hasWit_add h1 ih1, by rw [C3I.sAddChar_add h1 ih1, ih2]⟩

/-! ### Digit vectors -/

end

end ArtinKP.H
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

lemma gen_ne_zero' (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) : (g.gen I : F) ≠ 0 := by
  intro h0
  have := val_gen_eq h g I hI
  rw [h0, map_zero] at this
  exact exp_ne_zero this.symm

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
-- module Solutions.Artin.KP.HB_Tame
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

theorem uSym_zpow {x : F} (hx : x ≠ 0) (n : ℤ) :
    L3V.uSym g v.asIdeal (x ^ n) = L3V.uSym g v.asIdeal x ^ n := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact L3V.uSym_pow h g hω hx n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, L3V.uSym_inv h g hω (pow_ne_zero _ hx),
      L3V.uSym_pow h g hω hx]

/-- `ι (t, π)_P = χ_P(t)²` for a `P`-unit `t ∈ F` and a uniformizer `π`. -/
theorem iota3_hv_unit (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (t π : Fˣ) (ht : v.valuation F (t : F) = 1) (hπ : v.valuation F (π : F) = exp (-1 : ℤ)) :
    iota3 ι (Pk.hv v t π) = L3V.localSymbol ι 𝔪 v.asIdeal (t : F) ^ 2 := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (t : F) ht.le
  set y : SInt 𝔪 := algebraMap (𝓞 F) (SInt 𝔪) n with hy
  set z : SInt 𝔪 := algebraMap (𝓞 F) (SInt 𝔪) d with hz
  have hzm : z ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [show z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ d ∈ v.asIdeal ^ 1 from by
      rw [← C3I.alg_mem_map_pow_iff h.notS 1 d, pow_one]]
    rw [pow_one]; exact hd
  have hzt : (z : F) * (t : F) = (y : F) := by
    rw [mul_comm]; exact hnd
  have hz1 : v.valuation F (z : F) = 1 := L3V.val_of_not_mem h hzm
  have hy1 : v.valuation F (y : F) = 1 := by rw [← hzt, map_mul, hz1, ht, one_mul]
  have hym : y ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    intro hm
    have := (L3V.mem_iff_val h.notS y).1 hm
    rw [hy1] at this
    exact absurd this (not_le.2 L3V.exp_neg_one_lt_one)
  have hz0 : (z : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hz1; exact zero_ne_one hz1
  have hy0 : (y : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy1; exact zero_ne_one hy1
  set yu : Fˣ := Units.mk0 (y : F) hy0 with hyu
  set zu : Fˣ := Units.mk0 (z : F) hz0 with hzu
  have htu : t = yu / zu := by
    rw [eq_div_iff_mul_eq']
    apply Units.ext
    rw [Units.val_mul, hyu, hzu, Units.val_mk0, Units.val_mk0, mul_comm, hzt]
  have h1 := iota3_hv_eq ι Pk hG hz6 v h.notS y yu π rfl hy1 1 hπ
  have h2 := iota3_hv_eq ι Pk hG hz6 v h.notS z zu π rfl hz1 1 hπ
  rw [zpow_one] at h1 h2
  have hls : L3V.localSymbol ι 𝔪 v.asIdeal (t : F) =
      sexticResidueSymbol ι 𝔪 v.asIdeal y * (sexticResidueSymbol ι 𝔪 v.asIdeal z)⁻¹ := by
    rw [← L3V.uSym_of_val_one h g hω ht,
      show (t : F) = (y : F) * (z : F)⁻¹ from by rw [← hzt]; field_simp,
      L3V.uSym_mul h g hω hy0 (inv_ne_zero hz0), L3V.uSym_inv h g hω hz0,
      L3V.uSym_SInt h g hω hym, L3V.uSym_SInt h g hω hzm]
  have hdiv : ∀ A B : rootsOfUnity 3 F, iota3 ι (A / B) = iota3 ι A / iota3 ι B := by
    intro A B
    rw [eq_div_iff (iota3_ne_zero ι B), ← map_mul, div_mul_cancel]
  rw [htu, map_div, MonoidHom.div_apply, hdiv, h1, h2, ← htu, hls, mul_pow, inv_pow,
    div_eq_mul_inv]

/-- **The tame formula at `P`**: `ι (x, y)_P = (u_P(x)²)^{v_P(y)} · ((u_P(y)²)^{v_P(x)})⁻¹`. -/
theorem iota3_hv_tame (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (x y : Fˣ) :
    iota3 ι (Pk.hv v x y) =
      (L3V.uSym g v.asIdeal (x : F) ^ 2) ^ (L3V.vP v.asIdeal (y : F)) *
        ((L3V.uSym g v.asIdeal (y : F) ^ 2) ^ (L3V.vP v.asIdeal (x : F)))⁻¹ := by
  set α := L3V.vP v.asIdeal (x : F) with hα
  set β := L3V.vP v.asIdeal (y : F) with hβ
  have hx : v.valuation F (x : F) = exp (-α) := L3V.val_eq_exp_vP x.ne_zero
  have hy : v.valuation F (y : F) = exp (-β) := L3V.val_eq_exp_vP y.ne_zero
  set π : Fˣ := Units.mk0 (g.gen v.asIdeal : F) (L3V.p_ne_zero h g) with hπdef
  have hπ : v.valuation F (π : F) = exp (-1 : ℤ) := C3I.val_pi g h
  have ht : v.valuation F ((x ^ β / y ^ α : Fˣ) : F) = 1 := by
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
      map_div₀, map_zpow₀, map_zpow₀, hx, hy, ← exp_zsmul, ← exp_zsmul,
      show β • -α = α • -β from by simp only [smul_eq_mul]; ring]
    exact div_self exp_ne_zero
  rw [Pk.tame_formula v (hG.three_notMem v h.notS) x y π α β hx hy hπ,
    iota3_hv_unit h hω g Pk hG hz6 _ π ht hπ, ← L3V.uSym_of_val_one h g hω ht,
    Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
    div_eq_mul_inv, L3V.uSym_mul h g hω (zpow_ne_zero _ x.ne_zero)
      (inv_ne_zero (zpow_ne_zero _ y.ne_zero)),
    L3V.uSym_inv h g hω (zpow_ne_zero _ y.ne_zero), uSym_zpow h hω g x.ne_zero,
    uSym_zpow h hω g y.ne_zero, mul_pow, inv_pow]
  congr 1
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

end loc

open Classical in
/-- **The tame formula for `⟨x, y⟩ = ι (x, y)_S`** (product formula + `iota3_hv_tame`). -/
theorem brk_tame (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (g : AllowedGen ι 𝔪)
    (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
      C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
    (𝒯 : Finset (Ideal (𝓞 F))) (h𝒯 : ∀ P ∈ 𝒯, P.IsPrime ∧ IsExterior 𝔪 P) {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcov : ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal → w.asIdeal ∉ 𝒯 →
      w.valuation F x = 1 ∧ w.valuation F y = 1) :
    brk ι Pk 𝔪 x y *
      ∏ P ∈ 𝒯, ((L3V.uSym g P x ^ 2) ^ (L3V.vP P y) * ((L3V.uSym g P y ^ 2) ^ (L3V.vP P x))⁻¹)
      = 1 := by
  set xu : Fˣ := Units.mk0 x hx with hxu
  set yu : Fˣ := Units.mk0 y hy with hyu
  set φ : {P // P ∈ 𝒯} → HeightOneSpectrum (𝓞 F) := fun P =>
    ⟨P.1, (h𝒯 P.1 P.2).1, (h𝒯 P.1 P.2).2.1⟩ with hφ
  have hφinj : Function.Injective φ := fun P Q hPQ =>
    Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ)
  set T : Finset (HeightOneSpectrum (𝓞 F)) := 𝒯.attach.image φ with hT
  have hnotS : ∀ P : {P // P ∈ 𝒯}, ¬ 𝔪 ≤ (φ P).asIdeal := fun P =>
    (hgood P.1 (h𝒯 P.1 P.2).1 (h𝒯 P.1 P.2).2).notS
  have hprod := Pk.HS_mul_prod' hG.ne_bot hG.three xu yu T
    (fun w hw => by
      obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hw
      exact hnotS P)
    (fun w hw hwT => by
      refine hcov w hw fun hmem => hwT ?_
      exact Finset.mem_image.2 ⟨⟨w.asIdeal, hmem⟩, Finset.mem_attach _ _, rfl⟩)
  have h1 := congrArg (iota3 ι) hprod
  rw [map_mul, map_prod, map_one, hT, Finset.prod_image (fun P _ Q _ hPQ => hφinj hPQ)] at h1
  have hb : brk ι Pk 𝔪 x y = iota3 ι (Pk.HS 𝔪 xu yu) := brk_units xu yu
  rw [hb, ← Finset.prod_attach 𝒯]
  rw [← h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  exact (iota3_hv_tame (v := φ P) (hgood P.1 (h𝒯 P.1 P.2).1 (h𝒯 P.1 P.2).2) hz6 g Pk hG hz6
    xu yu).symm

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_C
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

/-- `(d / c_v) = ∏_{P ∈ D} χ_P(d)²`. -/
theorem cubicExt_cdig (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) (d : SInt 𝔪) :
    cubicExt ι 𝔪 d (cdig g 𝔟 v) =
      ∏ P : PIdx 𝔟, (if v P = 0 then 1 else sexticResidueSymbol ι 𝔪 P.1 d ^ 2) := by
  have hc0 := cdig_ne_zero g h𝔟 v
  set ψ : PIdx 𝔟 → HeightOneSpectrum (𝓞 F) := fun P =>
    ⟨P.1, (pidx_ext h𝔟 P).1, (pidx_ext h𝔟 P).2.1⟩ with hψ
  have hψinj : Function.Injective ψ := fun P Q hPQ =>
    Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ)
  have hnotS : ∀ P : PIdx 𝔟, ¬ 𝔪 ≤ (ψ P).asIdeal := fun P =>
    L3V.notS_of_ext (pidx_ext h𝔟 P).1 (pidx_ext h𝔟 P).2
  have hsupp : CubicPkg.extSupp 𝔪 (cdig g 𝔟 v : F) =
      (Finset.univ.filter fun P : PIdx 𝔟 => ¬ v P = 0).image ψ := by
    ext w
    rw [CubicPkg.mem_extSupp hc0, Finset.mem_image]
    constructor
    · rintro ⟨hw, hne⟩
      rw [val_cdig g h𝔟 v w hw] at hne
      by_cases hD : Dnz 𝔟 v w.asIdeal
      · obtain ⟨hP, hv⟩ := hD
        exact ⟨⟨w.asIdeal, hP⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, rfl⟩
      · rw [if_neg hD] at hne; exact absurd rfl hne
    · rintro ⟨P, hP, rfl⟩
      refine ⟨hnotS P, ?_⟩
      rw [val_cdig g h𝔟 v _ (hnotS P), if_pos ⟨P.2, (Finset.mem_filter.1 hP).2⟩]
      intro h1
      exact absurd h1 (ne_of_lt L3V.exp_neg_one_lt_one)
  have hite : ∀ P : PIdx 𝔟, (if v P = 0 then (1 : ℂ) else sexticResidueSymbol ι 𝔪 P.1 d ^ 2) =
      if ¬ v P = 0 then sexticResidueSymbol ι 𝔪 P.1 d ^ 2 else 1 := fun P => by
    by_cases h : v P = 0 <;> simp [h]
  rw [Finset.prod_congr rfl fun P _ => hite P, ← Finset.prod_filter, cubicExt, hsupp,
    Finset.prod_image fun P _ Q _ hPQ => hψinj hPQ]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hval := val_cdig g h𝔟 v _ (hnotS P)
  rw [if_pos ⟨P.2, (Finset.mem_filter.1 hP).2⟩, val_eq_exp_ordv _ hc0, exp_inj] at hval
  have hord : ordv (ψ P) (cdig g 𝔟 v : F) = 1 := by omega
  rw [hord]
  rfl

/-! ### Partial fractions -/

theorem isCoprime_gen (g : AllowedGen ι 𝔪) {P Q : Ideal (𝓞 F)} (hP : P.IsPrime)
    (hPe : IsExterior 𝔪 P) (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) (hne : P ≠ Q) :
    IsCoprime (g.gen P) (g.gen Q) := by
  have hcop : IsCoprime P Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (hP.isMaximal hPe.1) (hQ.isMaximal hQe.1) hne
  have h1 := C3M.cop_gen g hPe hcop
  rw [← g.span_gen Q hQe] at h1
  exact C3M.exists_ab h1

theorem gen_mem_map (g : AllowedGen ι 𝔪) {P : Ideal (𝓞 F)} (hPe : IsExterior 𝔪 P) :
    g.gen P ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen P hPe]; exact Ideal.mem_span_singleton_self _

/-- **Partial fractions for `e(r / c_v)`.** -/
theorem exists_pf (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟)
    (v : H.Dig 𝔪 𝔟) :
    ∃ m : PIdx 𝔟 → SInt 𝔪,
      (∀ P : PIdx 𝔟, v P ≠ 0 →
        m P * ccof g 𝔟 v P - 1 ∈ P.1.map (algebraMap (𝓞 F) (SInt 𝔪))) ∧
      ∀ r : SInt 𝔪, sAddChar 𝔪 ((r : F) / (cdig g 𝔟 v : F)) =
        ∏ P : PIdx 𝔟, (if v P = 0 then 1
          else sAddChar 𝔪 (((r * m P : SInt 𝔪) : F) / (g.gen P.1 : F))) := by
  by_cases hne : Nonempty (PIdx 𝔟)
  · have hpair : Pairwise (Function.onFun IsCoprime (cfac g 𝔟 v)) := by
      intro P Q hPQ
      show IsCoprime (cfac g 𝔟 v P) (cfac g 𝔟 v Q)
      unfold cfac
      split_ifs
      · exact isCoprime_one_left
      · exact isCoprime_one_left
      · exact isCoprime_one_right
      · exact isCoprime_gen g (pidx_ext h𝔟 P).1 (pidx_ext h𝔟 P).2 (pidx_ext h𝔟 Q).1
          (pidx_ext h𝔟 Q).2 fun h => hPQ (Subtype.ext h)
    obtain ⟨m, hm⟩ := exists_sum_eq_one_iff_pairwise_coprime'.2 hpair
    have hm' : ∑ P : PIdx 𝔟, m P * ccof g 𝔟 v P = 1 := hm
    refine ⟨m, fun P hP => ?_, fun r => ?_⟩
    · have hsplit := Fintype.sum_eq_add_sum_compl P fun Q => m Q * ccof g 𝔟 v Q
      rw [hm'] at hsplit
      have : m P * ccof g 𝔟 v P - 1 =
          -∑ Q ∈ ({P}ᶜ : Finset (PIdx 𝔟)), m Q * ccof g 𝔟 v Q := by
        rw [hsplit]; ring
      rw [this]
      refine neg_mem (Ideal.sum_mem _ fun Q hQ => Ideal.mul_mem_left _ _ ?_)
      have hPQ : P ∈ ({Q}ᶜ : Finset (PIdx 𝔟)) := by
        rw [Finset.mem_compl, Finset.mem_singleton] at hQ ⊢
        exact fun h => hQ h.symm
      have hdvd : cfac g 𝔟 v P ∣ ccof g 𝔟 v Q := Finset.dvd_prod_of_mem _ hPQ
      have hmem : cfac g 𝔟 v P ∈ P.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        unfold cfac; rw [if_neg hP]; exact gen_mem_map g (pidx_ext h𝔟 P).2
      exact Ideal.mem_of_dvd _ hdvd hmem
    · have hsum : (r : F) / (cdig g 𝔟 v : F) =
          ∑ P : PIdx 𝔟, ((r * m P : SInt 𝔪) : F) / (cfac g 𝔟 v P : F) := by
        have h1 : ∀ P : PIdx 𝔟, ((r * m P : SInt 𝔪) : F) / (cfac g 𝔟 v P : F) =
            (r : F) / (cdig g 𝔟 v : F) * ((m P * ccof g 𝔟 v P : SInt 𝔪) : F) := by
          intro P
          have hcc := congrArg (fun x : SInt 𝔪 => (x : F)) (cfac_mul_ccof g 𝔟 v P)
          simp only [Subalgebra.coe_mul] at hcc
          rw [← hcc, Subalgebra.coe_mul, Subalgebra.coe_mul]
          have := cfac_ne_zero g h𝔟 v P
          have := ccof_ne_zero g h𝔟 v P
          field_simp
        rw [Finset.sum_congr rfl fun P _ => h1 P, ← Finset.mul_sum]
        have h2 := congrArg (fun x : SInt 𝔪 => (x : F)) hm'
        simp only [OneMemClass.coe_one] at h2
        have h3 : (((∑ P : PIdx 𝔟, m P * ccof g 𝔟 v P : SInt 𝔪) : SInt 𝔪) : F) =
            ∑ P : PIdx 𝔟, ((m P * ccof g 𝔟 v P : SInt 𝔪) : F) :=
          map_sum ((placesOf 𝔪).integer F).subtype _ _
        rw [← h3, h2, mul_one]
      rw [hsum, (H.sAddChar_sum Finset.univ _ fun P _ => B7.hasWit_all h𝔪 _).2]
      refine Finset.prod_congr rfl fun P _ => ?_
      unfold cfac
      split_ifs
      · rw [OneMemClass.coe_one, div_one]
        exact C3B.sAddChar_of_mem _ (SetLike.coe_mem _)
      · rfl
  · haveI : IsEmpty (PIdx 𝔟) := not_nonempty_iff.1 hne
    refine ⟨fun _ => 0, fun P => isEmptyElim P, fun r => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty, coe_cdig, Finset.univ_eq_empty,
      Finset.prod_empty, div_one]
    exact C3B.sAddChar_of_mem _ (SetLike.coe_mem _)

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

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.H_Tau
/-! # WP-HA, file 6: the forward coefficient of `AutInput` from Theorem E

With the interface of WP-E (`D : E.Kubota S (sAdd 𝔪 h𝔪) Sec`, `T : E.Theta D (4/3)`, cube
periodicity at every exterior prime):

* `tau_eq_coefF'`: for every `ν ∈ R ∖ 0` and every section `Φ`,
  `τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`.
  (`E.theoremE_SInt` at the row representative `ρ = rowElt g (rowOf ν)`, `ν = μ⁶ρ`, and
  `τ_Φ(μ⁶ρ) = τ_{Ã(μ⁶)Φ}(ρ)`, `Ã(ρ)Ã(μ⁶) = ⟨ρ, μ⁶⟩ Ã(ν) = Ã(ν)`.)
* `forward_of_tau`: a Fourier expansion with coefficients `τ_Φ(ν) · Arch(ν)` whose Kirillov
  normalization `N(νR)^{1/3} τ_{Ã(ν)Φ}(1) Arch(ν) = fp(sEmb ν + y)` holds is the forward expansion
  of `AutInput`, term by term. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.B7 ArtinKP.E

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem coefF'_top (g : AllowedGen ι 𝔪) (z : RowClass 𝔪) :
    L3X.coefF' g ⊤ z =
      ∏ P ∈ (normalizedFactors z.1.1).toFinset,
        L3V.Wsph g P ((normalizedFactors z.1.1).count P : ℤ)
          ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ))) := by
  have h1 : residueSymbol ι 𝔪 ⊤ (rowElt g z) = 1 := by
    unfold residueSymbol; rw [C3B.normalizedFactors_top]; simp
  unfold L3X.coefF'
  rw [h1, one_mul]

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.HB_Main
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

/-- A product over the primes of `𝔟` as a product over a larger finite set of ideals. -/
theorem prod_pidx {𝔟 : Ideal (𝓞 F)} (𝒯 : Finset (Ideal (𝓞 F)))
    (hsub : (normalizedFactors 𝔟).toFinset ⊆ 𝒯) (f : PIdx 𝔟 → ℂ) :
    ∏ P : PIdx 𝔟, f P =
      ∏ P ∈ 𝒯, (if hP : P ∈ (normalizedFactors 𝔟).toFinset then f ⟨P, hP⟩ else 1) := by
  rw [← Finset.prod_subset hsub (fun P _ hP => dif_neg hP)]
  refine Eq.trans ?_ (Finset.prod_attach (normalizedFactors 𝔟).toFinset
    (fun P => if hP : P ∈ (normalizedFactors 𝔟).toFinset then f ⟨P, hP⟩ else 1))
  rw [← Finset.univ_eq_attach]
  exact Finset.prod_congr rfl fun P _ => by rw [dif_pos P.2]

section D

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)

include hG hz6 hgood

/-- **Identity (D)** (MATH3 §3.2): the exterior conversion from the section-level reflected
coefficient to the per-digit coefficient `digCoefNu`. -/
theorem digCoefNu_eq_oai {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
    (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (hc : γ.1 1 0 = cdig g 𝔟 v)
    (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
    (μ ν : {x : SInt 𝔪 // x ≠ 0})
    (hν : ((ν : SInt 𝔪) : F) =
      ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2) :
    L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
        sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
        kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F) =
      digCoefNu h𝔪 g 𝔟 v ν := by
  have hzν𝔟 : IsExterior 𝔪 ((H0.rowOf h𝔪 g ν).1.1 * 𝔟) :=
    C3B.isExterior_mul (H0.rowOf h𝔪 g ν).1.2 h𝔟
  have h𝒯 : ∀ P ∈ (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset,
      P.IsPrime ∧ IsExterior 𝔪 P := fun P hP =>
    ⟨(L3V.prime_of_mem_prim hP).1, L3V.exterior_of_prim hzν𝔟 hP⟩
  have hsub𝔟 := factors_subset_mul h𝔪 g h𝔟 ν
  have hsubμ : (normalizedFactors (H0.rowOf h𝔪 g μ).1.1).toFinset ⊆
      (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset := by
    intro P hP
    have hPp := (L3V.prime_of_mem_prim hP).1
    have hPe := L3V.exterior_of_prim (H0.rowOf h𝔪 g μ).1.2 hP
    have h1 := eNu_eq h𝔪 g h𝔟 v μ ν hν hPp hPe
    unfold eNu at h1
    have h2 : 0 < (normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P :=
      Multiset.count_pos.2 (Multiset.mem_toFinset.1 hP)
    have h3 : P ∈ L3V.prim ((H0.rowOf h𝔪 g ν).1.1 * 𝔟) := by
      rw [L3V.mem_prim_iff, L3V.cnt_mul (H0.rowOf h𝔪 g ν).1.2.1 h𝔟.1]
      unfold L3V.cnt
      by_cases hD : Dnz 𝔟 v P
      · obtain ⟨hPb, -⟩ := hD
        have := Multiset.count_pos.2 (Multiset.mem_toFinset.1 hPb)
        omega
      · rw [if_neg hD] at h1
        omega
    exact h3
  have hcov : ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal →
      w.asIdeal ∉ (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset →
      w.valuation F ((μ : SInt 𝔪) : F) = 1 ∧ w.valuation F (cdig g 𝔟 v : F) = 1 := by
    intro w hw hnot
    constructor
    · rw [val_eq_exp_count w hw (H0.rowOf h𝔪 g μ).1.2.1 μ (H0.span_eq_map_rowOf h𝔪 g μ)]
      have : (normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count w.asIdeal = 0 :=
        Multiset.count_eq_zero.2 fun hm => hnot (hsubμ (Multiset.mem_toFinset.2 hm))
      rw [this]; simp
    · rw [val_cdig g h𝔟 v w hw, if_neg]
      rintro ⟨hPb, -⟩
      exact hnot (hsub𝔟 hPb)
  obtain ⟨m, hm1, hm2⟩ := exists_pf h𝔪 g h𝔟 v
  have hW : L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) =
      ∏ P ∈ (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset,
        L3V.Wsph g P ((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ)
          ((rowElt g (H0.rowOf h𝔪 g μ) : F) *
            (g.gen P : F) ^ (-((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ))) := by
    rw [H.coefF'_top]
    refine Finset.prod_subset hsubμ fun P _ hP => ?_
    have h0 : (normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P = 0 :=
      Multiset.count_eq_zero.2 fun hm => hP (Multiset.mem_toFinset.2 hm)
    rw [h0]
    simp [L3V.Wsph, L3V.Wv]
  have hA := hm2 ((μ : SInt 𝔪) * γ.1 0 0)
  rw [Subalgebra.coe_mul, prod_pidx _ hsub𝔟] at hA
  have hK : kappa ι 𝔪 γ =
      (∏ P ∈ (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset,
        (if hP : P ∈ (normalizedFactors 𝔟).toFinset then
          (if v ⟨P, hP⟩ = 0 then 1 else sexticResidueSymbol ι 𝔪 P (γ.1 1 1) ^ 2)
          else 1))⁻¹ := by
    have hc0 : γ.1 1 0 ≠ 0 := by
      rw [hc]; intro h0
      exact cdig_ne_zero g h𝔟 v (by rw [h0]; rfl)
    unfold kappa
    rw [if_neg hc0, hc, cubicExt_cdig g h𝔟 v, prod_pidx _ hsub𝔟]
  have hB := brk_tame Pk hG hz6 g hgood _ h𝒯 (H0.coe_ne_zero μ) (cdig_ne_zero g h𝔟 v) hcov
  have hB' := eq_inv_of_mul_eq_one_left hB
  rw [hW, hA, hK, hB', digCoefNu, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun P hP =>
    local_D hz6 hgood h𝔪 g h𝔟 v γ hc hd μ ν hν m hm1 (h𝒯 P hP).1 (h𝒯 P hP).2

end D

end

end ArtinKP.HB
end

theorem solution.{u_1} : type_of% @ArtinKP.HB.digCoefNu_eq_oai.{u_1} := @ArtinKP.HB.digCoefNu_eq_oai.{u_1}
