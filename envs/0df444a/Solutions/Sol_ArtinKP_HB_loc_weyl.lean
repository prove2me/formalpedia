-- Prove2me | solution 1 for ArtinKP.HB.loc_weyl
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:13.226788+00:00
-- url     : https://prove2.me/submissions/fc2aff79-4dba-4042-8d50-6499fc678ba0

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

/-! ### Masks -/

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

end weyl

end L3V

end ArtinPrimitiveRoots
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

variable [Fintype (SInt 𝔪 ⧸ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include hω

/-- **Identity (D) at a prime with a nonzero digit** (MATH3 §3.2, case `P ∈ D`).
`U = u_P(μ)`, `cc = c_v / p`, `m · cc ≡ 1`, `a d ≡ 1`, `d ≡ −cc · y`, `t = t_P`, `e = v_P(μ)`. -/
theorem loc_weyl_oai {e : ℕ} {t : F} (ht : w.valuation F t = 1)
    {y : SInt 𝔪 ⧸ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0)
    (μ a d m cc : SInt 𝔪) (U : ℂ) (hU : U ^ 6 = 1)
    (hls : L3V.localSymbol ι 𝔪 w.asIdeal t =
      U * (sexticResidueSymbol ι 𝔪 w.asIdeal cc ^ 2)⁻¹)
    (hd : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) d =
      -(Ideal.Quotient.mk _ cc * y))
    (had : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) a *
      Ideal.Quotient.mk _ d = 1)
    (hm : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) m *
      Ideal.Quotient.mk _ cc = 1)
    (hμ0 : e = 0 → L3V.res 𝔪 w t * Ideal.Quotient.mk _ cc ^ 2 = Ideal.Quotient.mk _ μ)
    (hμ1 : e ≠ 0 → Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) μ = 0) :
    U ^ (2 * e) * L3V.Wv g w.asIdeal e *
        sAddChar 𝔪 (((μ * a * m : SInt 𝔪) : F) / (g.gen w.asIdeal : F)) *
        (sexticResidueSymbol ι 𝔪 w.asIdeal d ^ 2)⁻¹ *
        ((U ^ 2) ^ (1 : ℤ) * ((sexticResidueSymbol ι 𝔪 w.asIdeal cc ^ 2) ^ (e : ℤ))⁻¹)⁻¹ =
      L3V.Wweyl g w.asIdeal ((e : ℤ) - 2) t y := by
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set C := Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) cc with hCdef
  have hC : C ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hm; exact zero_ne_one hm
  set X := C3I.chi ι h hω C with hX
  set Y := C3I.chi ι h hω y with hY
  have hX6 : X ^ 6 = 1 := C3I.chi_pow_six_apply h hω hC
  have hY6 : Y ^ 6 = 1 := C3I.chi_pow_six_apply h hω hy
  have hχcc : sexticResidueSymbol ι 𝔪 w.asIdeal cc = X := (C3I.chi_mk h hω cc).symm
  have hχd : sexticResidueSymbol ι 𝔪 w.asIdeal d = X * Y := by
    rw [← C3I.chi_mk h hω, hd, show -(C * y) = -1 * (C * y) by ring, map_mul, map_mul,
      C3I.chi_neg_one h hω, one_mul]
  have hψ : sAddChar 𝔪 (((μ * a * m : SInt 𝔪) : F) / (g.gen w.asIdeal : F)) =
      C3I.psi g h (Ideal.Quotient.mk _ (μ * a * m)) := (C3I.psi_mk g h _).symm
  have he2 : ((e : ℤ) - 2 + 2).toNat = e := by omega
  have hx : L3V.res 𝔪 w t * y⁻¹ * y = L3V.res 𝔪 w t := inv_mul_cancel_right₀ hy _
  have hΨ : C3I.psi g h (Ideal.Quotient.mk _ (μ * a * m)) =
      if e = 0 then C3I.psi g h (-(L3V.res 𝔪 w t * y⁻¹)) else 1 := by
    by_cases he : e = 0
    · rw [if_pos he]
      congr 1
      have ha : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) a =
          (Ideal.Quotient.mk _ d)⁻¹ := eq_inv_of_mul_eq_one_left had
      have hm' : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) m = C⁻¹ :=
        eq_inv_of_mul_eq_one_left hm
      rw [map_mul, map_mul, ha, hm', hd, ← hμ0 he]
      field_simp
    · have h0 : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (μ * a * m) = 0 := by
        rw [map_mul, map_mul, hμ1 he, zero_mul, zero_mul]
      rw [if_neg he, h0, AddChar.map_zero_eq_one]
  rw [L3V.Wweyl_eq h hω g ht.le hy (by omega) hx]
  simp only [he2]
  rw [← L3V.localSymbol_eq h hω, hls, hχcc, hχd, hψ, hΨ]
  have i1 : ((X * Y) ^ 2)⁻¹ = (X * Y) ^ 4 :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_add, mul_pow, hX6, hY6, mul_one])
  have i2 : (U ^ 2)⁻¹ = U ^ 4 := inv_eq_of_mul_eq_one_left (by rw [← pow_add, hU])
  have i3 : (X ^ 2)⁻¹ = X ^ 4 := inv_eq_of_mul_eq_one_left (by rw [← pow_add, hX6])
  have hXe : X ^ (16 + 8 * e) = X ^ (4 + 2 * e) := by
    rw [show 16 + 8 * e = (4 + 2 * e) + 6 * (2 + e) by ring, pow_add, pow_mul, hX6, one_pow,
      mul_one]
  rw [zpow_one, zpow_natCast, mul_inv, inv_inv, i1, i2, i3]
  set Ψ : ℂ := if e = 0 then C3I.psi g h (-(L3V.res 𝔪 w t * y⁻¹)) else 1
  calc U ^ (2 * e) * L3V.Wv g w.asIdeal e * Ψ * (X * Y) ^ 4 * (U ^ 4 * (X ^ 2) ^ e)
      = L3V.Wv g w.asIdeal e * Ψ * Y ^ 4 * U ^ (4 + 2 * e) * X ^ (4 + 2 * e) := by ring
    _ = L3V.Wv g w.asIdeal e * Ψ * Y ^ 4 * U ^ (4 + 2 * e) * X ^ (16 + 8 * e) := by rw [hXe]
    _ = _ := by ring

end loc

end

end ArtinKP.HB
end

theorem solution.{u_1} : type_of% @ArtinKP.HB.loc_weyl_oai.{u_1} := @ArtinKP.HB.loc_weyl_oai.{u_1}
