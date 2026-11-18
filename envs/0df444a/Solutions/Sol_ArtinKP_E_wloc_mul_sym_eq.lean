-- Prove2me | solution 1 for ArtinKP.E.wloc_mul_sym_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:01.604302+00:00
-- url     : https://prove2.me/submissions/36fdb9b4-0dfb-4456-95e0-f59c7add8207

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
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

lemma chi_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (y) :
    chi ι h hω y = sexFun ι 𝔪 v y := rfl

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

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

/-! ### Characters on the finite field `L` -/

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma chi_pow_mod (n : ℕ) : chi ι h hω ^ n = chi ι h hω ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, chi_pow_six h hω, one_pow, one_mul]

lemma chi_pow_neg_one (j : ℕ) : (chi ι h hω ^ j) (-1) = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero]
    exact MulChar.one_apply (isUnit_one.neg (α := SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
  rw [MulChar.pow_apply' _ hj.ne', chi_neg_one h hω, one_pow]

variable (g : AllowedGen ι 𝔪)

/-- `g(φ, ψ⁻¹) = g(φ, ψ)` for the powers of `χ` (as `χ(-1) = 1`). -/
lemma gs_inv_psi (j : ℕ) :
    gaussSum (chi ι h hω ^ j) (psi g h)⁻¹ = gaussSum (chi ι h hω ^ j) (psi g h) := by
  have h1 := chi_pow_neg_one (ι := ι) h hω j
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := mul_gaussSum_inv_eq_gaussSum (chi ι h hω ^ j) (psi g h)
  rw [h1, one_mul] at this
  exact this

end field

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_HD
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

omit hω in
lemma add_ql (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 (-((quotLift y : F) / (g.gen v.asIdeal : F))) = C3I.psi g h (-y) := by
  have := C3I.psi_mk g h (-(quotLift y))
  rw [map_neg, C3I.mk_quotLift] at this
  rw [this, Subalgebra.coe_neg, neg_div]

lemma chi_zero : C3I.chi ι h hω (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  rw [C3I.chi_apply]; exact C3I.sexFun_zero

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

lemma conj_chi_pow {j : ℕ} (hj : j ≠ 0) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    starRingEnd ℂ (C3I.chi ι h hω y) ^ j = (C3I.chi ι h hω ^ (5 * j)) y := by
  rw [MulChar.pow_apply' _ (by omega)]
  by_cases hy : y = 0
  · rw [hy, chi_zero h hω, map_zero, zero_pow hj, zero_pow (by omega)]
  · rw [conj_chi (ι := ι) h hω hy, ← pow_mul]

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

lemma tau_eq {j : ℕ} (hj : j ≠ 0) :
    tau g v.asIdeal j = gaussSum (C3I.chi ι h hω ^ (5 * j)) (C3I.psi g h) := by
  rw [← C3I.gs_inv_psi h hω g (5 * j)]
  unfold tau
  rw [finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [chi_ql h hω, add_ql h g, conj_chi_pow h hω hj, AddChar.inv_apply]

/-! ### Masks -/

end loc

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.B7_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-! # B7_Link: the Gauss sums over `R = SInt 𝔪` and the normalization of the frozen statement

* `sAdd 𝔪 h𝔪 : AddData (SInt 𝔪) F` is `sAddChar 𝔪` (additive on all of `F`: `sAddChar_add_all`;
  trivial on `R`), so `gauss S (sAdd 𝔪 h𝔪) ν c = ∑_{d mod c} (d/c)⁻¹ sAddChar 𝔪 (ν d / c)`
  (`gauss_sAdd`).
* `finite_quot_span`: `R ⧸ (c)` is finite for `c ≠ 0`.
* At a good exterior prime `P` (`C3I.Good 𝔪 v`, automatic for `SmallPrimesDvd N₀ 𝔪`,
  `N₀ ≥ C3I.cutN F`) with `π = g.gen P` and a symbol with `(d/π) = χ_P(d)²`:
  `gaussP_one_eq_tau : g₁(π) = tau P 2 = conj (√q γ₂(P))`,
  `gaussP_two_eq_tau : g₂(π) = tau P 4 = √q γ₂(P)`, `γ₂(P) = gaussPhase g 2 P`,
  `gaussP_one_mul_two : g₁ g₂ = N P`, and the complete table `gauss_gen_table` in the form of
  `B7_System.tab` with `G = (ν₀/π) tau P 2`, `G' = (ν₀/π)² tau P 4`, `G G' = N P`, `conj G = G'`.
* `theta_ratio`: the solution of the formal system at `x₀ = q^{-4/3}` gives
  `q^{-1/3} C₁ = (ν₀/π)² · Wv P 1 · C₀` with `Wv P 1 = q^{-1/2} gaussPhase g 2 P` exactly as in the
  frozen statement (and `Wv P 0 = 1`, `Wv P 2 = 0 ↔ Ψ₂ = 0`).
-/

open NumberField IsDedekindDomain

namespace ArtinKP.B7

open ArtinPrimitiveRoots

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The additive character -/

/-! ### Transport of residue sums to the quotient by an equal ideal -/

lemma rsum_eq_finsum {R : Type*} [CommRing R] {c : R} {I : Ideal R} (hI : Ideal.span {c} = I)
    (f : R → ℂ) :
    rsum c f = ∑ᶠ y : R ⧸ I, f (Function.surjInv Ideal.Quotient.mk_surjective y) := by
  subst hI; rfl

/-! ### A good exterior prime -/

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma card_quot_gen :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) = Ideal.absNorm v.asIdeal :=
  (congrArg (fun I : Ideal (SInt 𝔪) => Nat.card (SInt 𝔪 ⧸ I)) (span_gen h g)).trans (C3I.natCard_L h)

section fin

variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω hS in
/-- `g_j(π) = g(χ_P^{4j}, ψ_P)` in the notation of `C3I`. -/
lemma gaussP_eq_gs {j : ℕ} (hj : 0 < j) :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) j =
      gaussSum (C3I.chi ι h hω ^ (4 * j)) (C3I.psi g h) := by
  unfold gaussP
  rw [rsum_eq_finsum (span_gen h g), finsum_eq_sum_of_fintype, gaussSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e1 : S.sym (Function.surjInv Ideal.Quotient.mk_surjective y) (g.gen v.asIdeal) =
      C3I.chi ι h hω y ^ 2 := by
    rw [hS]; exact congrArg (· ^ 2) (C3I.chi_mk_quotLift h hω y)
  rw [e1, MulChar.pow_apply' _ (by omega), C3I.psi_apply]
  congr 1
  by_cases hy : y = 0
  · rw [hy, C3I.chi_apply, C3I.sexFun_zero, zero_pow (by norm_num), inv_zero, zero_pow (by omega),
      zero_pow (by omega)]
  · have h6 := C3I.chi_pow_six_apply (ι := ι) h hω hy
    have : (C3I.chi ι h hω y ^ 2)⁻¹ = C3I.chi ι h hω y ^ 4 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h6)
    rw [this, ← pow_mul]

include h hω hS in
theorem gaussP_two_eq :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) 2 =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) * gaussPhase g 2 v.asIdeal := by
  have hs : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ≠ 0 := by
    have := C3I.absNorm_pos v
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast this)).ne'
  rw [gaussP_eq_gs h hω g h𝔪 S hS (by norm_num), C3I.chi_pow_mod h hω,
    C3I.gaussPhase_eq h hω g (by norm_num), ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

include h hω hS in
theorem gaussP_two_eq_tau :
    gaussP S (sAdd 𝔪 h𝔪) (g.gen v.asIdeal) 2 = L3V.tau g v.asIdeal 4 := by
  rw [gaussP_eq_gs h hω g h𝔪 S hS (by norm_num), L3V.tau_eq h hω g (by norm_num),
    C3I.chi_pow_mod h hω, C3I.chi_pow_mod h hω (5 * 4)]

end fin

end prime

end ArtinKP.B7
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

end good

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.E_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # E_Link: Theorem E over `R = SInt 𝔪` in the shape of the frozen statement

* `primeDatum_gen`: at a good exterior prime `P`, `π = g.gen P` satisfies `PrimeDatum` with
  `g₁ = tau P 2`, `g₂ = tau P 4` (B7's table).
* `wloc_eq`: at `s₀ = 4/3`, `w_P(e) = (N P)^{e/3} · Wv P e` (`Wv` of the frozen statement).
* `theoremE_SInt`: `τ_Φ(ν) = N(𝔷)^{1/3} · ∏_{P ∣ 𝔷} Wsph P (v_P 𝔷) (ν / gen(P)^{v_P 𝔷}) · τ_{Ã(ν)Φ}(1)`
  for `νR = 𝔷R`, `𝔷` exterior.
* `exists_cutoff_theoremE`: the same as one cutoff statement with the `let`s of the frozen goal
  copied verbatim.

Of `AllowedGen` only `span_gen` is used (through B7 and `L3V`): `gen_mul` and `reciprocity` are
not needed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinKP.E

open ArtinPrimitiveRoots ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma nrm_gen : nrm (g.gen v.asIdeal) = (Ideal.absNorm v.asIdeal : ℂ) := by
  unfold nrm; rw [card_quot_gen h g]

include h hω hS h𝔪 in
/-- At `s₀ = 4/3` the local weight is `(N P)^{e/3} · Wv P e`. -/
theorem wloc_eq (e : ℕ) :
    Theta.wloc (nrm (g.gen v.asIdeal)) (nrm (g.gen v.asIdeal) ^ (-(4 / 3 : ℂ)))
        (L3V.tau g v.asIdeal 4) e =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ ((e : ℝ) / 3) : ℝ) : ℂ) * L3V.Wv g v.asIdeal e := by
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast C3I.absNorm_pos v
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hnrm : nrm (g.gen v.asIdeal) = (q : ℂ) := by rw [nrm_gen h g, hqdef]; push_cast; rfl
  have := C3I.finite_L h
  let _ : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
  have htau : L3V.tau g v.asIdeal 4 = ((Real.sqrt q : ℝ) : ℂ) * gaussPhase g 2 v.asIdeal :=
    (gaussP_two_eq_tau h hω g h𝔪 S hS).symm.trans (gaussP_two_eq h hω g h𝔪 S hS)
  obtain ⟨m, hm⟩ : ∃ m, e / 3 = m := ⟨_, rfl⟩
  unfold Theta.wloc L3V.Wv
  rw [hm]
  rcases (by omega : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2) with h0 | h1 | h2
  · rw [if_pos h0, if_pos h0, ← Complex.ofReal_mul, ← Real.rpow_add hq]
    have : (e : ℝ) / 3 + -(m : ℝ) = 0 := by
      have : e = 3 * m := by omega
      rw [this]; push_cast; ring
    rw [this, Real.rpow_zero, Complex.ofReal_one]
  · rw [if_neg (by omega), if_pos h1, if_neg (by omega), if_pos h1, htau, hnrm]
    have hc : (q : ℂ) ^ (-(4 / 3 : ℂ)) = ((q ^ (-(4 / 3 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hq.le]; push_cast; rfl
    rw [hc, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast q 2, ← Real.rpow_natCast (q ^ (-(4 / 3 : ℝ))) 2,
      ← Real.rpow_mul hq.le, ← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq]
    congr 1
    have : e = 3 * m + 1 := by omega
    rw [this]; push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_zero]

include h hω in
/-- The frozen `lsym` on an element of `R`. -/
lemma localSymbol_coe (y : SInt 𝔪) :
    L3V.localSymbol ι 𝔪 v.asIdeal (y : F) = sexticResidueSymbol ι 𝔪 v.asIdeal y := by
  rw [L3V.localSymbol_eq h hω, L3V.res_of_SInt h.notS, C3I.chi_mk h hω]

include h hω hS h𝔪 in
/-- One local factor: `w_P(e) · (c/π)^e = (N P)^{e/3} · Wsph P e (ν π^{-e})` when `ν = c π^e`. -/
theorem wloc_mul_sym_eq_oai (e : ℕ) {ν c : SInt 𝔪} (hν : ν = c * g.gen v.asIdeal ^ e) :
    Theta.wloc (nrm (g.gen v.asIdeal)) (nrm (g.gen v.asIdeal) ^ (-(4 / 3 : ℂ)))
        (L3V.tau g v.asIdeal 4) e * S.sym c (g.gen v.asIdeal) ^ e =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ ((e : ℝ) / 3) : ℝ) : ℂ) *
        L3V.Wsph g v.asIdeal (e : ℤ) ((ν : F) * (g.gen v.asIdeal : F) ^ (-(e : ℤ))) := by
  have hp0 : (g.gen v.asIdeal : F) ≠ 0 := L3V.p_ne_zero h g
  have ht : (ν : F) * (g.gen v.asIdeal : F) ^ (-(e : ℤ)) = (c : F) := by
    rw [hν, zpow_neg, zpow_natCast]
    push_cast
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), mul_one]
  rw [wloc_eq h hω g h𝔪 S hS e, ht]
  unfold L3V.Wsph
  rw [if_neg (not_lt.2 (Int.natCast_nonneg e)), Int.toNat_natCast, localSymbol_coe h hω, hS c,
    pow_mul]
  ring

end prime

/-! ### The global statement -/

end ArtinKP.E
end

theorem solution.{u_1} : type_of% @ArtinKP.E.wloc_mul_sym_eq_oai.{u_1} := @ArtinKP.E.wloc_mul_sym_eq_oai.{u_1}
