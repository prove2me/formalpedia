-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_prod_gaussPhase_three_span_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:22:46.642533+00:00
-- url     : https://prove2.me/submissions/e8eaee8e-d2c2-4459-8c58-ca09046844de

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_ArtinPrimitiveRoots_exists_cutoff_residueSymbol_span_eq_one_of_isUnit
import Theorems.Thm_ArtinPrimitiveRoots_finsum_cexp_trace_sq_div_eq_sqrt_absNorm
import Mathlib

section
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

/-- `e` is trivial on `R`. -/
lemma sAddChar_of_mem {𝔪 : Ideal (𝓞 F)} (x : F) (hx : x ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 x = 1 := by
  have hex : ∃ y : F, x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1 :=
    ⟨0, by simpa using hx, fun v _ => by simp⟩
  rw [sAddChar, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set y := hex.choose
  have hy : y ∈ (placesOf 𝔪).integer F := by
    have := sub_mem hx h1
    rwa [sub_sub_cancel] at this
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · exact h2 v hv
    · exact hy v hv
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F y hall
  have htr : Algebra.trace ℚ F y = ((Algebra.trace ℤ (𝓞 F) z : ℤ) : ℚ) := by
    rw [← hz, Algebra.coe_trace_int]
  rw [htr]
  have := Complex.exp_int_mul_two_pi_mul_I (-(Algebra.trace ℤ (𝓞 F) z))
  rw [← this]
  congr 1
  push_cast
  ring

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

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

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

end gen

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
end

section
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

/-- `e(a/c + b/c) = e(a/c) e(b/c)` for `c` an allowed generator. -/
lemma sAddChar_div_gen_add (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a b : SInt 𝔪) :
    sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F) + (b : F) / (g.gen 𝔞 : F)) =
      sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F)) * sAddChar 𝔪 ((b : F) / (g.gen 𝔞 : F)) :=
  sAddChar_add (hasWit_div_gen g 𝔞 h𝔞 a) (hasWit_div_gen g 𝔞 h𝔞 b)

/-! ### The inverse different -/

/-- For `P ∤ 𝔇`, some `z ∈ P⁻¹` has non-integral trace. -/
lemma exists_trace_not_int (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ P) :
    ∃ z : F, (∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a) ∧
      ∀ n : ℤ, Algebra.trace ℚ F z ≠ n := by
  rw [differentialIdeal_le_iff (K := ℚ) (L := F) hP0, Submodule.map_le_iff_le_comap] at hD
  rw [SetLike.not_le_iff_exists] at hD
  obtain ⟨z, hz, hz'⟩ := hD
  have hP' : (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using hP0
  have hz2 : z ∈ ((P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹) := hz
  rw [FractionalIdeal.mem_inv_iff hP'] at hz2
  refine ⟨z, fun p hp => ?_, fun n hn => hz' ?_⟩
  · have := hz2 (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨a, ha.symm⟩
  · simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
    exact ⟨n, by rw [hn]; simp⟩

/-- For `P` exterior and `z ∈ P⁻¹` with non-integral trace, `e(z) ≠ 1`. -/
lemma sAddChar_ne_one_of_dual (P : Ideal (𝓞 F)) (hPS : P ⊔ 𝔪 = ⊤) (z : F)
    (hz : ∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    (htr : ∀ n : ℤ, Algebra.trace ℚ F z ≠ n) : sAddChar 𝔪 z ≠ 1 := by
  have hw : ∀ v ∈ placesOf 𝔪, v.valuation F z ≤ 1 := by
    intro v hv
    have hvm : 𝔪 ≤ v.asIdeal := hv
    have hPv : ¬ P ≤ v.asIdeal := by
      intro h
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hPS]
      exact sup_le h hvm
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp hPv
    obtain ⟨a, ha⟩ := hz p hp
    have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
    rw [← ha, map_mul, h1, mul_one] at this
    exact this
  rw [sAddChar_eq_of_wit (y := z) (by simp) hw]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply htr (-n)
  have h2 : ((Algebra.trace ℚ F z : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `z (v R) ⊆ R` for `z ∈ v⁻¹`. -/
lemma mul_mem_of_mem_map (z : F)
    (hz : ∀ p ∈ v.asIdeal, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    {y : SInt 𝔪} (hy : y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    z * (y : F) ∈ (placesOf 𝔪).integer F := by
  rw [Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hz p hp
    rw [coe_alg, ha]
    exact (algebraMap (𝓞 F) (SInt 𝔪) a).2
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_left_comm]
    exact mul_mem a.2 hx

/-- Primitivity of `x ↦ e(x / gen(P^j))` on `R / P^j R`: for `x ∉ P^j R` there is `r ∈ R` with
`e(x r / gen(P^j)) ≠ 1`, when `P ∤ 𝔇`. -/
lemma exists_sAddChar_ne_one (g : AllowedGen ι 𝔪) (hv : v ∉ placesOf 𝔪)
    (hPS : v.asIdeal ⊔ 𝔪 = ⊤) (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) {j : ℕ} (hj : 1 ≤ j)
    (x : SInt 𝔪) (hx : x ∉ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, sAddChar 𝔪 ((x : F) * (r : F) / (g.gen (v.asIdeal ^ j) : F)) ≠ 1 := by
  obtain ⟨z, hz, htr⟩ := exists_trace_not_int v.asIdeal v.ne_bot hD
  have hez := sAddChar_ne_one_of_dual v.asIdeal hPS z hz htr
  have hext : IsExterior 𝔪 (v.asIdeal ^ j) :=
    isExterior_pow ⟨v.ne_bot, hPS⟩ j
  set B := g.gen (v.asIdeal ^ j)
  have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ hext
  have hBmem : B ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen _ hext]; exact Ideal.mem_span_singleton_self _
  have hB1 : B ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have : (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.map_mono (by simpa using Ideal.pow_le_pow_right (I := v.asIdeal) hj)
    exact this hBmem
  -- `w = z B ∈ R`
  have hwR : z * (B : F) ∈ (placesOf 𝔪).integer F := mul_mem_of_mem_map z hz hB1
  set w : SInt 𝔪 := ⟨z * (B : F), hwR⟩
  -- valuations
  have hvz : v.valuation F z ≤ exp (1 : ℤ) := by
    obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : p ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    obtain ⟨a, ha⟩ := hz p hpm
    have h1 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h1
    rw [← ha, map_mul, hp] at h1
    have : v.valuation F z * exp (-1 : ℤ) * exp 1 ≤ 1 * exp 1 := mul_le_mul_left h1 _
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at this
  have hvB := val_le_of_mem hv j hBmem
  have hvw : v.valuation F (w : F) ≤ exp (1 - (j : ℤ)) := by
    change v.valuation F (z * (B : F)) ≤ _
    rw [map_mul, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, exp_add]
    exact mul_le_mul' hvz hvB
  have hvx : exp (1 - (j : ℤ)) ≤ v.valuation F (x : F) := by
    have := exp_le_val_of_not_mem hv (j - 1) x (by rwa [Nat.sub_add_cancel hj])
    convert this using 2
    push_cast [Nat.cast_sub hj]; ring
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact exp_ne_zero (le_antisymm hvx bot_le)
  have hvx0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hx0
  -- `f = w / x` is `v`-integral
  have hvf : v.valuation F ((w : F) / (x : F)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.2 hvx0)]
    exact hvw.trans hvx
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j _ hvf
  -- `w - x a ∈ P^j R`
  set δ : SInt 𝔪 := w - x * algebraMap (𝓞 F) (SInt 𝔪) a
  have hδ : δ ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    apply mem_of_val_le hv j
    have : (δ : F) = (x : F) * ((w : F) / (x : F) - algebraMap (𝓞 F) F a) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg]
      field_simp
    rw [this, map_mul]
    calc v.valuation F (x : F) * v.valuation F ((w : F) / (x : F) - algebraMap (𝓞 F) F a)
        ≤ 1 * exp (-(j : ℤ)) := mul_le_mul' (val_le_one hv x) ha
      _ = _ := one_mul _
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, fun h1 => hez ?_⟩
  have hzeq : z = (x : F) * ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) / (B : F) +
      (δ : F) / (B : F) := by
    simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul]
    change z = _ + (z * (B : F) - _) / (B : F)
    field_simp
    ring
  rw [hzeq, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g _ hext δ hδ), h1]

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
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

lemma Good.ext (h : Good 𝔪 v) : IsExterior 𝔪 v.asIdeal := ⟨v.ne_bot, h.cop⟩

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

/-- `χ` has exact order `6`: `χ^j ≠ 1` unless `6 ∣ j`. -/
lemma chi_pow_ne_one (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) {j : ℕ}
    (hj : ¬ 6 ∣ j) : chi ι h hω ^ j ≠ 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set Q := Ideal.absNorm v.asIdeal
  set e := (Q - 1) / 6
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (SInt 𝔪 ⧸ v.asIdeal.map
    (algebraMap (𝓞 F) (SInt 𝔪)))ˣ)
  have hog : orderOf γ = Q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, natCard_L h]
  obtain ⟨i, hi6, hi⟩ := exists_pow_e h hω
    (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))) γ.ne_zero
  -- `ω^i` is a primitive sixth root
  have hcop : Nat.Coprime i 6 := by
    have hord : orderOf ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) = 6 := by
      have hγ' : orderOf (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Q - 1 := by
        rw [orderOf_units, hog]
      rw [orderOf_pow' _ (by
        have := six_mul_e h; have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
        omega), hγ']
      have := six_mul_e h
      have hQ := absNorm_ne_one v; have hQ0 := absNorm_pos v
      rw [show Q - 1 = 6 * e from (six_mul_e h).symm, Nat.gcd_mul_left_left]
      have he : 0 < e := by omega
      rw [Nat.mul_div_cancel _ he]
    have hprim : IsPrimitiveRoot ((γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ e) 6 := by
      rw [← hord]; exact IsPrimitiveRoot.orderOf _
    rw [hi] at hprim
    exact ((omegaL_prim h hω).pow_iff_coprime (by norm_num) i).1 hprim
  intro hone
  have h1 : chi ι h hω (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ^ j = 1 := by
    rw [← MulChar.pow_apply' _ (by rintro rfl; exact hj (dvd_zero 6)), hone,
      MulChar.one_apply_coe]
  rw [chi_eq_pow h hω (y := (γ : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
    γ.ne_zero hi, ← pow_mul, (iota_omega_prim hω).pow_eq_one_iff_dvd] at h1
  exact hj (hcop.symm.dvd_of_dvd_mul_left h1)

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
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

lemma quotLift_mk_sub {I : Ideal (SInt 𝔪)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq]; exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma mk_quotLift {I : Ideal (SInt 𝔪)} (y : SInt 𝔪 ⧸ I) :
    Ideal.Quotient.mk I (quotLift y) = y :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective _

/-- `e(x / gen 𝔞)` depends only on `x mod 𝔞 R`. -/
lemma sAddChar_div_congr (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (hx : x - x' ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 ((x : F) / (g.gen 𝔞 : F)) = sAddChar 𝔪 ((x' : F) / (g.gen 𝔞 : F)) := by
  have : (x : F) / (g.gen 𝔞 : F) =
      (x' : F) / (g.gen 𝔞 : F) + ((x - x' : SInt 𝔪) : F) / (g.gen 𝔞 : F) := by
    rw [Subalgebra.coe_sub]; ring
  rw [this, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g 𝔞 h𝔞 _ hx)]

/-- The additive character `y ↦ e(y / gen P)` of `L`. -/
noncomputable def psi (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) :
    AddChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun y := sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F))
  map_zero_eq_one' := by
    have h0 : quotLift (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_quotLift]
    exact C3B.sAddChar_of_mem _ (C3B.div_gen_mem g _ h.ext _ h0)
  map_add_eq_mul' := by
    intro a b
    have hab : quotLift (a + b) - (quotLift a + quotLift b) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift, mk_quotLift]
    rw [sAddChar_div_congr g _ h.ext hab, Subalgebra.coe_add, add_div,
      sAddChar_div_gen_add g _ h.ext]

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

lemma psi_isPrimitive (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) : (psi g h).IsPrimitive := by
  intro a ha hone
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ∉ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one]; rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨r, hr⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff le_rfl x hx
  apply hr
  have := congrArg (fun φ => φ (Ideal.Quotient.mk _ r)) hone
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this
  rw [← map_mul, psi_mk, Subalgebra.coe_mul] at this
  rw [pow_one]
  exact this

/-! ### Characters on the finite field `L` -/

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
variable [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include h hω

lemma card_L : Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, natCard_L h]

lemma ringChar_ne_two : ringChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 2 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [Ne, FiniteField.even_card_iff_char_two, card_L h hω]
  obtain ⟨k, hk⟩ := h.twelve
  have := absNorm_pos v
  omega

omit h hω in
lemma iota_omega_cube (hω : IsPrimitiveRoot ω 6) : ι (ω : F) ^ 3 = -1 := by
  have h2 : IsPrimitiveRoot (ι (ω : F) ^ 3) 2 := (iota_omega_prim hω).pow (by norm_num) (by norm_num)
  exact h2.eq_neg_one_of_two_right

/-- `χ³` is the quadratic character. -/
lemma chi_cube_eq_quad [DecidableEq (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
    (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    letI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (chi ι h hω ^ (3 : ℕ)) y = ((quadraticChar _ y : ℤ) : ℂ) := by
  have hc := ringChar_ne_two h hω
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  by_cases hy : y = 0
  · subst hy
    simp only [MulChar.map_zero, Int.cast_zero]
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [MulChar.pow_apply' _ (by norm_num), chi_eq_pow h hω hy hi]
  rw [quadraticChar_eq_pow_of_char_ne_two hc hy]
  have hcard : Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, natCard_L h]
  rw [hcard]
  have hQ : Ideal.absNorm v.asIdeal / 2 = 3 * ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    have := six_mul_e h; have := absNorm_pos v; omega
  rw [hQ, pow_mul', hi, ← pow_mul, ← pow_mul, mul_comm i 3, pow_mul, iota_omega_cube hω]
  have hprim := omegaL_prim (𝔪 := 𝔪) (v := v) h hω
  by_cases hev : Even i
  · rw [hev.neg_one_pow, if_pos]
    · simp
    obtain ⟨k, rfl⟩ := hev
    rw [show 3 * (k + k) = 6 * k by ring, pow_mul, hprim.pow_eq_one, one_pow]
  · rw [(Nat.not_even_iff_odd.1 hev).neg_one_pow, if_neg]
    · simp
    rw [hprim.pow_eq_one_iff_dvd]
    intro h6
    exact hev (by
      obtain ⟨c, hc⟩ := h6
      exact ⟨c, by omega⟩)

lemma chi_cube_isQuadratic : (chi ι h hω ^ (3 : ℕ)).IsQuadratic := by
  classical
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  intro a
  rw [chi_cube_eq_quad h hω]
  rcases quadraticChar_isQuadratic _ a with h0 | h1 | h2
  · left; rw [h0]; simp
  · right; left; rw [h1]; simp
  · right; right; rw [h2]; simp

/-- `#{u | u² = w} = 1 + χ³(w)`. -/
lemma card_sqrt [DecidableEq (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))] (w : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ((Finset.univ.filter fun u => u ^ 2 = w).card : ℂ) = 1 + (chi ι h hω ^ (3 : ℕ)) w := by
  have hc := ringChar_ne_two h hω
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := quadraticChar_card_sqrts hc w
  rw [chi_cube_eq_quad h hω]
  have h2 : ((Finset.univ.filter fun u => u ^ 2 = w).card : ℤ) = quadraticChar _ w + 1 := by
    rw [← this]
    congr 2
    ext u; simp
  rw [add_comm]
  exact_mod_cast h2

lemma chi_pow_mod (n : ℕ) : chi ι h hω ^ n = chi ι h hω ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, chi_pow_six h hω, one_pow, one_mul]

lemma chi_pow_neg_one (j : ℕ) : (chi ι h hω ^ j) (-1) = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero]
    exact MulChar.one_apply (isUnit_one.neg (α := SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))))
  rw [MulChar.pow_apply' _ hj.ne', chi_neg_one h hω, one_pow]

lemma chi_pow_inv (j k : ℕ) (hjk : (j + k) % 6 = 0) : (chi ι h hω ^ j)⁻¹ = chi ι h hω ^ k := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, chi_pow_mod h hω, hjk, pow_zero]

variable (g : AllowedGen ι 𝔪)

lemma gs_three_sq : gaussSum (chi ι h hω ^ (3 : ℕ)) (psi g h) ^ 2 = Ideal.absNorm v.asIdeal := by
  have hχ := chi_pow_ne_one (ι := ι) h hω (j := 3) (by norm_num)
  have hq := chi_cube_isQuadratic (ι := ι) h hω
  have hψ := psi_isPrimitive g h
  have hcard := card_L h hω
  have h1 := chi_pow_neg_one (ι := ι) h hω 3
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := gaussSum_sq hχ hq hψ
  rw [h1, one_mul, hcard] at this
  exact this

end field

end C3I

end ArtinPrimitiveRoots

end
end

section
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

lemma normalizedFactors_v (v : HeightOneSpectrum (𝓞 F)) :
    normalizedFactors v.asIdeal = {v.asIdeal} := by
  have hirr : Irreducible v.asIdeal := (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  rw [normalizedFactors_irreducible hirr, normalize_eq]

lemma residueSymbol_v (x : SInt 𝔪) :
    residueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal x := by
  simp [residueSymbol, normalizedFactors_v]

lemma sqrt_sq_C : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ^ 2 = Ideal.absNorm v.asIdeal := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

section field

variable (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  [Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]
include h hω

lemma chi_mk_quotLift (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (quotLift y) = chi ι h hω y := by
  rw [← chi_mk h hω, mk_quotLift]

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

end C3B

end ArtinPrimitiveRoots

end
end

section
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

end C3B

end ArtinPrimitiveRoots

end
end

section
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

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots

end
end

section
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

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

lemma periodic_eq {I : Ideal (SInt 𝔪)} {f : SInt 𝔪 → ℂ}
    (hf : ∀ x w, w ∈ I → f (x + w) = f x) {x y : SInt 𝔪} (h : x - y ∈ I) : f x = f y := by
  have := hf y (x - y) h
  rwa [add_sub_cancel] at this

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

/-! ### Coercions -/

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

end gs

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3M_Gs: the global quadratic Gauss sum `gs A c = Σ_{x mod A} e(c x²/A)` over `R`

* `phase_per`: the summand is `A`-periodic.
* `Ext 𝔪 A`: `A R = 𝔞 R` for an ideal `𝔞` coprime to `𝔪`; then `a / A` has a witness.
* `fibEquiv`: `R/X × R/Y ≃ R/(XY)`, `(a, b) ↦ ã + X b̃`; `finsum_fib`.
* `gs_mul`: Chinese remainders, `gs (A B) c = gs A (c u) · gs B (c v)` when `u B + v A = 1`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The global quadratic Gauss sum `Σ_{x mod A} e(c x² / A)` over `R = SInt 𝔪`. -/
def gs (𝔪 : Ideal (𝓞 F)) (A c : SInt 𝔪) : ℂ :=
  ∑ᶠ x : SInt 𝔪 ⧸ Ideal.span {A}, sAddChar 𝔪 ((c : F) * (quotLift x : F) ^ 2 / (A : F))

lemma mk_ql {I : Ideal (SInt 𝔪)} (y : SInt 𝔪 ⧸ I) : Ideal.Quotient.mk I (quotLift y) = y :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma ql_mk_sub (I : Ideal (SInt 𝔪)) (x : SInt 𝔪) : quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq, mk_ql]

lemma coe_mem (r : SInt 𝔪) : (r : F) ∈ (placesOf 𝔪).integer F := r.2

/-- A periodic function takes equal values on congruent arguments. -/
lemma per_eq {I : Ideal (SInt 𝔪)} {f : SInt 𝔪 → ℂ} (hf : ∀ x w, w ∈ I → f (x + w) = f x)
    {x y : SInt 𝔪} (h : x - y ∈ I) : f x = f y := by
  have := hf y (x - y) h
  rwa [add_sub_cancel] at this

/-- The summand of `gs` is `A`-periodic. -/
lemma phase_per (A c : SInt 𝔪) (x w : SInt 𝔪) (hw : w ∈ Ideal.span {A}) :
    sAddChar 𝔪 ((c : F) * ((x + w : SInt 𝔪) : F) ^ 2 / (A : F)) =
      sAddChar 𝔪 ((c : F) * (x : F) ^ 2 / (A : F)) := by
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  by_cases hA : (A : F) = 0
  · simp [hA]
  have : (c : F) * ((x + r * A : SInt 𝔪) : F) ^ 2 / (A : F) =
      (c : F) * (x : F) ^ 2 / (A : F) + ((c * (x * r + x * r + r * r * A) : SInt 𝔪) : F) := by
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    field_simp
    ring
  rw [this, C3B.sAddChar_add_mem _ _ (coe_mem _)]

/-- `A R = 𝔞 R` for an ideal `𝔞` of `𝓞` coprime to `𝔪`. -/
def Ext (𝔪 : Ideal (𝓞 F)) (A : SInt 𝔪) : Prop :=
  ∃ 𝔞 : Ideal (𝓞 F), 𝔞 ⊔ 𝔪 = ⊤ ∧ Ideal.span {A} = 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))

lemma Ext.mul {A B : SInt 𝔪} (hA : Ext 𝔪 A) (hB : Ext 𝔪 B) : Ext 𝔪 (A * B) := by
  obtain ⟨𝔞, h𝔞, hA⟩ := hA
  obtain ⟨𝔟, h𝔟, hB⟩ := hB
  refine ⟨𝔞 * 𝔟, ?_, ?_⟩
  · have h1 : IsCoprime 𝔞 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr h𝔞
    have h2 : IsCoprime 𝔟 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr h𝔟
    exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)
  · rw [← Ideal.span_singleton_mul_span_singleton, hA, hB, Ideal.map_mul]

/-- `a / A` has a witness. -/
lemma hasWit_div {A : SInt 𝔪} (hA : Ext 𝔪 A) (a : SInt 𝔪) : C3I.HasWit 𝔪 ((a : F) / (A : F)) := by
  obtain ⟨𝔞, h𝔞, hspan⟩ := hA
  apply C3I.hasWit_of_mul_mem _ 𝔞 h𝔞
  intro i hi
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ Ideal.span {A} := by
    rw [hspan]; exact Ideal.mem_map_of_mem _ hi
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hm
  have hr' : algebraMap (𝓞 F) F i = (r : F) * (A : F) := by
    rw [← C3I.coe_alg, ← hr, Subalgebra.coe_mul]
  by_cases hA0 : (A : F) = 0
  · rw [hA0, div_zero, zero_mul]; exact zero_mem _
  rw [hr', show (a : F) / (A : F) * ((r : F) * (A : F)) = ((a * r : SInt 𝔪) : F) by
    rw [Subalgebra.coe_mul]; field_simp]
  exact coe_mem _

lemma hasWit_mul_div {A : SInt 𝔪} (hA : Ext 𝔪 A) (c x : SInt 𝔪) :
    C3I.HasWit 𝔪 ((c : F) * (x : F) ^ 2 / (A : F)) := by
  have := hasWit_div hA (c * x ^ 2)
  simpa [Subalgebra.coe_mul, Subalgebra.coe_pow] using this

/-! ### The fibration `R/X × R/Y ≃ R/(XY)` -/

/-- `(a, b) ↦ ã + X b̃`. -/
def fibMap (X Y : SInt 𝔪) (p : (SInt 𝔪 ⧸ Ideal.span {X}) × (SInt 𝔪 ⧸ Ideal.span {Y})) :
    SInt 𝔪 ⧸ Ideal.span {X * Y} :=
  Ideal.Quotient.mk _ (quotLift p.1 + X * quotLift p.2)

lemma fibMap_bijective (X Y : SInt 𝔪) (hX : X ≠ 0) : Function.Bijective (fibMap X Y) := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [fibMap, Ideal.Quotient.eq] at h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    have ha : quotLift a - quotLift a' ∈ Ideal.span {X} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨r * Y - (quotLift b - quotLift b'), by linear_combination hr⟩
    have hb : quotLift b - quotLift b' ∈ Ideal.span {Y} := by
      have ha' : quotLift a = quotLift a' := by
        have := congrArg (Ideal.Quotient.mk (Ideal.span {X})) (show quotLift a = quotLift a' from by
          have : Ideal.Quotient.mk (Ideal.span {X}) (quotLift a) =
              Ideal.Quotient.mk (Ideal.span {X}) (quotLift a') := Ideal.Quotient.eq.mpr ha
          rw [mk_ql, mk_ql] at this; rw [this])
        rw [mk_ql, mk_ql] at this
        rw [this]
      rw [ha'] at hr
      rw [Ideal.mem_span_singleton']
      refine ⟨r, ?_⟩
      have : X * (r * Y - (quotLift b - quotLift b')) = 0 := by linear_combination hr
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hX
      · linear_combination h0
    have e1 : a = a' := by
      rw [← mk_ql a, ← mk_ql a']; exact Ideal.Quotient.eq.mpr ha
    have e2 : b = b' := by
      rw [← mk_ql b, ← mk_ql b']; exact Ideal.Quotient.eq.mpr hb
    rw [e1, e2]
  · intro x
    set z := quotLift x
    have hz : z - quotLift (Ideal.Quotient.mk (Ideal.span {X}) z) ∈ Ideal.span {X} := by
      have := ql_mk_sub (Ideal.span {X}) z
      rw [← neg_sub]; exact neg_mem this
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨(Ideal.Quotient.mk _ z, Ideal.Quotient.mk _ r), ?_⟩
    simp only [fibMap]
    rw [← mk_ql x, Ideal.Quotient.eq]
    have hb := ql_mk_sub (Ideal.span {Y}) r
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hb
    rw [Ideal.mem_span_singleton']
    refine ⟨s, ?_⟩
    change _ = quotLift (Ideal.Quotient.mk (Ideal.span {X}) z) +
      X * quotLift (Ideal.Quotient.mk (Ideal.span {Y}) r) - z
    linear_combination X * hs - hr

/-- The fibration as an equivalence. -/
def fibEquiv (X Y : SInt 𝔪) (hX : X ≠ 0) :
    (SInt 𝔪 ⧸ Ideal.span {X}) × (SInt 𝔪 ⧸ Ideal.span {Y}) ≃ SInt 𝔪 ⧸ Ideal.span {X * Y} :=
  Equiv.ofBijective _ (fibMap_bijective X Y hX)

lemma finite_mul (X Y : SInt 𝔪) (hX : X ≠ 0) [Finite (SInt 𝔪 ⧸ Ideal.span {X})]
    [Finite (SInt 𝔪 ⧸ Ideal.span {Y})] : Finite (SInt 𝔪 ⧸ Ideal.span {X * Y}) :=
  Finite.of_equiv _ (fibEquiv X Y hX)

lemma natCard_mul (X Y : SInt 𝔪) (hX : X ≠ 0) :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {X * Y}) =
      Nat.card (SInt 𝔪 ⧸ Ideal.span {X}) * Nat.card (SInt 𝔪 ⧸ Ideal.span {Y}) := by
  rw [← Nat.card_prod]; exact (Nat.card_congr (fibEquiv X Y hX)).symm

/-- Summing over the fibration. -/
lemma finsum_fib (X Y : SInt 𝔪) (hX : X ≠ 0) [Finite (SInt 𝔪 ⧸ Ideal.span {X})]
    [Finite (SInt 𝔪 ⧸ Ideal.span {Y})] (f : SInt 𝔪 → ℂ)
    (hf : ∀ x w, w ∈ Ideal.span {X * Y} → f (x + w) = f x) :
    ∑ᶠ x : SInt 𝔪 ⧸ Ideal.span {X * Y}, f (quotLift x) =
      ∑ᶠ a : SInt 𝔪 ⧸ Ideal.span {X}, ∑ᶠ b : SInt 𝔪 ⧸ Ideal.span {Y},
        f (quotLift a + X * quotLift b) := by
  rw [← finsum_comp_equiv (fibEquiv X Y hX), finsum_curry _ (Set.toFinite _)]
  refine finsum_congr fun a => finsum_congr fun b => ?_
  exact per_eq hf (ql_mk_sub _ _)

/-! ### Chinese remainders -/

lemma finsum_mul_finsum' {α β : Type*} (f : α → ℂ) (g : β → ℂ) :
    ∑ᶠ a, ∑ᶠ b, f a * g b = (∑ᶠ a, f a) * ∑ᶠ b, g b := by
  rw [finsum_mul]
  refine finsum_congr fun a => ?_
  rw [mul_finsum]

lemma gs_mul (A B c u v : SInt 𝔪) (huv : u * B + v * A = 1) (hA : Ext 𝔪 A) (hB : Ext 𝔪 B)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    [Finite (SInt 𝔪 ⧸ Ideal.span {A})] [Finite (SInt 𝔪 ⧸ Ideal.span {B})] :
    gs 𝔪 (A * B) c = gs 𝔪 A (c * u) * gs 𝔪 B (c * v) := by
  unfold gs
  have hAF : (A : F) ≠ 0 := fun h => hA0 (Subtype.ext h)
  have hBF : (B : F) ≠ 0 := fun h => hB0 (Subtype.ext h)
  rw [C3M.finsum_crt (I := Ideal.span {A}) (J := Ideal.span {B}) (K := Ideal.span {A * B})
    (e₁ := u * B) (e₂ := v * A) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self B))
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self A)) huv
    (Ideal.span_singleton_mul_span_singleton A B).symm
    (fun y : SInt 𝔪 => sAddChar 𝔪 ((c : F) * (y : F) ^ 2 / ((A * B : SInt 𝔪) : F)))
    (fun x w hw => phase_per (A * B) c x w hw)]
  rw [← finsum_mul_finsum']
  refine finsum_congr fun x₁ => finsum_congr fun x₂ => ?_
  set y₁ := quotLift x₁
  set y₂ := quotLift x₂
  have huvF : (u : F) * (B : F) + (v : F) * (A : F) = 1 := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) huv
    simpa [Subalgebra.coe_add, Subalgebra.coe_mul] using this
  have key : (c : F) * ((y₁ * (u * B) + y₂ * (v * A) : SInt 𝔪) : F) ^ 2 / ((A * B : SInt 𝔪) : F) =
      ((c * u : SInt 𝔪) : F) * (y₁ : F) ^ 2 / (A : F) +
        ((c * v : SInt 𝔪) : F) * (y₂ : F) ^ 2 / (B : F) +
        ((c * u * v * (y₁ * y₂ + y₁ * y₂ - y₁ ^ 2 - y₂ ^ 2) : SInt 𝔪) : F) := by
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_pow]
    field_simp
    linear_combination (c : F) * ((y₁ : F) ^ 2 * (u : F) * (B : F) +
      (y₂ : F) ^ 2 * (v : F) * (A : F)) * huvF
  rw [key, C3B.sAddChar_add_mem _ _ (coe_mem _),
    C3I.sAddChar_add (hasWit_mul_div hA _ _) (hasWit_mul_div hB _ _)]

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Pk: `gs` at a good prime, and peeling a square

For a good exterior prime `P = v` with allowed generator `π = gen P`:
* `sum_lin`: `Σ_{b mod π} e(t b / π) = [t ∈ π R] · N P`;
* `gs_prime`: `gs π c = χ_P(c)³ √(N P) γ₃(P)` for `c ∉ P R`;
* `gaussPhase_sq`: `γ₃(P)² = 1`; `chi3_sq`: `(χ_P(c)³)² = 1`;
* `gs_peel`: `gs (B π²) c = N P · gs B c` for `c ∉ P R`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}
  {v : HeightOneSpectrum (𝓞 F)}

lemma span_pi (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) :
    Ideal.span {g.gen v.asIdeal} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  g.span_gen _ h.ext

lemma ext_pi (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) : Ext 𝔪 (g.gen v.asIdeal) :=
  ⟨v.asIdeal, h.cop, span_pi g h⟩

lemma pi_ne_zero (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) : g.gen v.asIdeal ≠ 0 := fun h0 =>
  C3B.gen_ne_zero g _ h.ext (by rw [h0]; rfl)

lemma finite_pi (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) :
    Finite (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) := by
  rw [span_pi g h]; exact C3I.finite_L h

lemma natCard_pi (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) = Ideal.absNorm v.asIdeal := by
  rw [span_pi g h]; exact C3I.natCard_L h

open Classical in
/-- The linear character sum. -/
lemma sum_lin (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) (t : SInt 𝔪) :
    ∑ᶠ b : SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal},
        sAddChar 𝔪 ((t : F) * (quotLift b : F) / (g.gen v.asIdeal : F)) =
      if t ∈ Ideal.span {g.gen v.asIdeal} then (Ideal.absNorm v.asIdeal : ℂ) else 0 := by
  rw [span_pi g h]
  haveI := C3I.finite_L h
  letI : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
  classical
  rw [finsum_eq_sum_of_fintype]
  have hterm : ∀ b : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)),
      sAddChar 𝔪 ((t : F) * (quotLift b : F) / (g.gen v.asIdeal : F)) =
        C3I.psi g h (b * Ideal.Quotient.mk _ t) := by
    intro b
    have : b * Ideal.Quotient.mk _ t = Ideal.Quotient.mk _ (quotLift b * t) := by
      rw [map_mul, mk_ql]
    rw [this, C3I.psi_mk, Subalgebra.coe_mul, mul_comm (quotLift b : F)]
  simp_rw [hterm]
  rw [AddChar.sum_mulShift _ (C3I.psi_isPrimitive g h), ← Nat.card_eq_fintype_card,
    C3I.natCard_L h]
  by_cases ht : t ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
  · rw [if_pos ht, if_pos (Ideal.Quotient.eq_zero_iff_mem.mpr ht)]
  · rw [if_neg ht, if_neg (fun h0 => ht (Ideal.Quotient.eq_zero_iff_mem.mp h0)), Nat.cast_zero]

section field

variable (g : AllowedGen ι 𝔪) (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
include h hω

/-- `(χ_P(c)³)² = 1` off `P R`. -/
lemma chi3_sq (c : SInt 𝔪) (hc : c ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    (sexticResidueSymbol ι 𝔪 v.asIdeal c ^ 3) ^ 2 = 1 := by
  rw [← C3I.chi_mk h hω, ← pow_mul]
  exact C3I.chi_pow_six_apply h hω (fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.mp h0))

lemma chi_mul (x y : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal (x * y) =
      sexticResidueSymbol ι 𝔪 v.asIdeal x * sexticResidueSymbol ι 𝔪 v.asIdeal y := by
  rw [← C3I.chi_mk h hω, ← C3I.chi_mk h hω, ← C3I.chi_mk h hω, map_mul, map_mul]

lemma chi_congr {x y : SInt 𝔪} (hxy : x - y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x = sexticResidueSymbol ι 𝔪 v.asIdeal y := by
  rw [← C3I.chi_mk h hω, ← C3I.chi_mk h hω, Ideal.Quotient.eq.mpr hxy]

lemma chi_one : sexticResidueSymbol ι 𝔪 v.asIdeal 1 = 1 := by
  rw [← C3I.chi_mk h hω, map_one, map_one]

/-- `γ₃(P)² = 1`. -/
lemma gaussPhase_sq : gaussPhase g 3 v.asIdeal ^ 2 = 1 := by
  haveI := C3I.finite_L h
  letI : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
  rw [C3I.gaussPhase_eq h hω g (by norm_num), mul_pow, C3I.gs_three_sq h hω g, inv_pow,
    C3I.sqrt_sq_C]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (C3I.absNorm_pos v).ne')

/-- The prime quadratic Gauss sum. -/
lemma gs_prime (c : SInt 𝔪) (hc : c ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    gs 𝔪 (g.gen v.asIdeal) c = sexticResidueSymbol ι 𝔪 v.asIdeal c ^ 3 *
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) * gaussPhase g 3 v.asIdeal := by
  unfold gs
  rw [span_pi g h]
  haveI := C3I.finite_L h
  letI : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
  classical
  rw [finsum_eq_sum_of_fintype, C3I.gaussPhase_eq h hω g (by norm_num)]
  set ψ := C3I.psi g h
  set χ := C3I.chi ι h hω
  set a : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := Ideal.Quotient.mk _ c
  have ha : a ≠ 0 := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hterm : ∀ x : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)), sAddChar 𝔪 ((c : F) * (quotLift x : F) ^ 2 / (g.gen v.asIdeal : F)) =
      ψ (x ^ 2 * a) := by
    intro x
    have : x ^ 2 * a = Ideal.Quotient.mk _ (c * quotLift x ^ 2) := by
      rw [map_mul, map_pow, mk_ql, mul_comm]
    rw [this, C3I.psi_mk, Subalgebra.coe_mul, Subalgebra.coe_pow]
  simp_rw [hterm]
  have hcube := C3I.chi_cube_isQuadratic (ι := ι) h hω
  have hinv := C3I.chi_pow_inv (ι := ι) h hω 3 3 (by norm_num)
  have hsq : ∀ w : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)), ((Finset.univ.filter fun u => u ^ 2 = w).card : ℂ) = 1 + (χ ^ (3 : ℕ)) w :=
    C3I.card_sqrt h hω
  have hfib : ∑ x : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)), ψ (x ^ 2 * a) = ∑ w : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)), (1 + (χ ^ (3 : ℕ)) w) * ψ (w * a) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) => x ^ 2)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hsq w, Finset.sum_congr rfl (g := fun _ => ψ (w * a)) (fun x hx => by
      rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
  rw [hfib]
  simp_rw [add_mul, one_mul]
  rw [Finset.sum_add_distrib, AddChar.sum_mulShift _ (C3I.psi_isPrimitive g h), if_neg ha,
    Nat.cast_zero, zero_add]
  haveI := C3I.isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hg : ∑ w : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)), (χ ^ (3 : ℕ)) w * ψ (w * a) = gaussSum (χ ^ (3 : ℕ)) (ψ.mulShift (Units.mk0 a ha)) := by
    rw [gaussSum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [AddChar.mulShift_apply, Units.val_mk0, mul_comm a]
  rw [hg, gaussSum_mulShift_eq, hinv, Units.val_mk0, MulChar.pow_apply' _ (by norm_num),
    C3I.chi_mk h hω]
  have hN : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast C3I.absNorm_pos v
  field_simp

omit h hω in
/-- Translation invariance of a periodic sum. -/
lemma finsum_translate (B s : SInt 𝔪) [Finite (SInt 𝔪 ⧸ Ideal.span {B})] (f : SInt 𝔪 → ℂ)
    (hf : ∀ x w, w ∈ Ideal.span {B} → f (x + w) = f x) :
    ∑ᶠ b : SInt 𝔪 ⧸ Ideal.span {B}, f (s + quotLift b) =
      ∑ᶠ b : SInt 𝔪 ⧸ Ideal.span {B}, f (quotLift b) := by
  have := finsum_comp_equiv (Equiv.addLeft (Ideal.Quotient.mk (Ideal.span {B}) s))
    (f := fun b => f (quotLift b))
  rw [← this]
  refine finsum_congr fun b => ?_
  simp only [Equiv.coe_addLeft]
  apply per_eq hf
  rw [← Ideal.Quotient.eq]
  simp only [map_add, mk_ql]

open Classical in
/-- Peeling a square: `gs (B π²) c = N P · gs B c`. -/
lemma gs_peel (B c : SInt 𝔪) (hB : Ext 𝔪 B) (hB0 : B ≠ 0) [Finite (SInt 𝔪 ⧸ Ideal.span {B})]
    (hc : c ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    gs 𝔪 (B * g.gen v.asIdeal * g.gen v.asIdeal) c = (Ideal.absNorm v.asIdeal : ℂ) * gs 𝔪 B c := by
  set π := g.gen v.asIdeal with hπdef
  have hπ0 : π ≠ 0 := pi_ne_zero g h
  have hπF : (π : F) ≠ 0 := fun h0 => hπ0 (Subtype.ext h0)
  have hBF : (B : F) ≠ 0 := fun h0 => hB0 (Subtype.ext h0)
  haveI := finite_pi g h
  have hBπ0 : B * π ≠ 0 := mul_ne_zero hB0 hπ0
  haveI : Finite (SInt 𝔪 ⧸ Ideal.span {B * π}) := finite_mul B π hB0
  have hext : Ext 𝔪 (B * π * π) := (hB.mul (ext_pi g h)).mul (ext_pi g h)
  have hprime : (Ideal.span {π}).IsPrime := by
    rw [span_pi g h]; exact (C3I.isMaximal_v h).isPrime
  have hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := span_pi g h
  -- `2 c ∉ π R`
  have h2c : c + c ∉ Ideal.span {π} := by
    haveI := C3I.finite_L h
    letI : Fintype (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := Fintype.ofFinite _
    have hch := C3I.ringChar_ne_two h hω
    haveI := C3I.isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro hmem
    rw [hspan, ← Ideal.Quotient.eq_zero_iff_mem, show c + c = 2 * c by ring, map_mul,
      map_ofNat] at hmem
    rcases mul_eq_zero.mp hmem with h0 | h0
    · exact Ring.two_ne_zero hch h0
    · exact hc (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  unfold gs
  rw [finsum_fib (B * π) π hBπ0
    (fun y : SInt 𝔪 => sAddChar 𝔪 ((c : F) * (y : F) ^ 2 / ((B * π * π : SInt 𝔪) : F)))
    (fun x w hw => phase_per _ c x w hw)]
  -- step 1: the inner sum over `b mod π`
  have step1 : ∀ a : SInt 𝔪 ⧸ Ideal.span {B * π},
      ∑ᶠ b : SInt 𝔪 ⧸ Ideal.span {π},
          sAddChar 𝔪 ((c : F) * ((quotLift a + B * π * quotLift b : SInt 𝔪) : F) ^ 2 /
            ((B * π * π : SInt 𝔪) : F)) =
        (Ideal.absNorm v.asIdeal : ℂ) *
          (if quotLift a ∈ Ideal.span {π} then
            sAddChar 𝔪 ((c : F) * (quotLift a : F) ^ 2 / ((B * π * π : SInt 𝔪) : F)) else 0) := by
    intro a
    set y := quotLift a
    have hexp : ∀ b : SInt 𝔪 ⧸ Ideal.span {π},
        sAddChar 𝔪 ((c : F) * ((y + B * π * quotLift b : SInt 𝔪) : F) ^ 2 /
          ((B * π * π : SInt 𝔪) : F)) =
        sAddChar 𝔪 ((c : F) * (y : F) ^ 2 / ((B * π * π : SInt 𝔪) : F)) *
          sAddChar 𝔪 (((c * y + c * y : SInt 𝔪) : F) * (quotLift b : F) / (π : F)) := by
      intro b
      have key : (c : F) * ((y + B * π * quotLift b : SInt 𝔪) : F) ^ 2 /
          ((B * π * π : SInt 𝔪) : F) =
          (c : F) * (y : F) ^ 2 / ((B * π * π : SInt 𝔪) : F) +
            ((c * y + c * y : SInt 𝔪) : F) * (quotLift b : F) / (π : F) +
            ((c * B * quotLift b * quotLift b : SInt 𝔪) : F) := by
        simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
        field_simp
        ring
      rw [key, C3B.sAddChar_add_mem _ _ (coe_mem _),
        C3I.sAddChar_add (hasWit_mul_div hext _ _)
          (by simpa [Subalgebra.coe_mul] using hasWit_div (ext_pi g h) ((c * y + c * y) * quotLift b))]
    simp_rw [hexp]
    rw [← mul_finsum, sum_lin g h]
    have hiff : c * y + c * y ∈ Ideal.span {π} ↔ y ∈ Ideal.span {π} := by
      rw [show c * y + c * y = (c + c) * y by ring]
      constructor
      · intro hm; exact (hprime.mem_or_mem hm).resolve_left h2c
      · intro hm; exact Ideal.mul_mem_left _ _ hm
    by_cases hy : y ∈ Ideal.span {π}
    · rw [if_pos (hiff.mpr hy), if_pos hy, mul_comm]
    · rw [if_neg (fun hm => hy (hiff.mp hm)), if_neg hy, mul_zero, mul_zero]
  simp_rw [step1]
  rw [← mul_finsum]
  congr 1
  -- step 2: the sum over `a ∈ π R / B π R`
  set H : SInt 𝔪 → ℂ := fun y => if y ∈ Ideal.span {π} then
      sAddChar 𝔪 ((c : F) * (y : F) ^ 2 / ((B * π * π : SInt 𝔪) : F)) else 0 with hH
  have hHper : ∀ x w, w ∈ Ideal.span {π * B} → H (x + w) = H x := by
    intro x w hw
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    have hwπ : r * (π * B) ∈ Ideal.span {π} :=
      Ideal.mem_span_singleton'.mpr ⟨r * B, by ring⟩
    simp only [hH]
    by_cases hx : x ∈ Ideal.span {π}
    · rw [if_pos (add_mem hx hwπ), if_pos hx]
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      have key : (c : F) * ((s * π + r * (π * B) : SInt 𝔪) : F) ^ 2 / ((B * π * π : SInt 𝔪) : F) =
          (c : F) * ((s * π : SInt 𝔪) : F) ^ 2 / ((B * π * π : SInt 𝔪) : F) +
            ((c * (s * r + s * r + r * r * B)) : SInt 𝔪) := by
        simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
        field_simp
        ring
      rw [key, C3B.sAddChar_add_mem _ _ (coe_mem _)]
    · rw [if_neg hx, if_neg (fun hm => hx (by
        have := sub_mem hm hwπ; rwa [add_sub_cancel_right] at this))]
  have hπB0 : π * B ≠ 0 := mul_ne_zero hπ0 hB0
  change ∑ᶠ a : SInt 𝔪 ⧸ Ideal.span {B * π}, H (quotLift a) = _
  rw [show Ideal.span {B * π} = Ideal.span {π * B} by rw [mul_comm],
    finsum_fib π B hπ0 H hHper]
  have hq0 : quotLift (0 : SInt 𝔪 ⧸ Ideal.span {π}) ∈ Ideal.span {π} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, mk_ql]
  rw [finsum_eq_single _ (0 : SInt 𝔪 ⧸ Ideal.span {π}) (fun a ha => by
    refine finsum_eq_zero_of_forall_eq_zero fun b => ?_
    simp only [hH]
    rw [if_neg]
    intro hm
    apply ha
    rw [← mk_ql a, Ideal.Quotient.eq_zero_iff_mem]
    have := sub_mem hm (Ideal.mul_mem_right (quotLift b) _ (Ideal.mem_span_singleton_self π))
    rwa [add_sub_cancel_right] at this)]
  obtain ⟨s₀, hs₀⟩ := Ideal.mem_span_singleton'.mp hq0
  have hval : ∀ b : SInt 𝔪 ⧸ Ideal.span {B},
      H (quotLift (0 : SInt 𝔪 ⧸ Ideal.span {π}) + π * quotLift b) =
        sAddChar 𝔪 ((c : F) * ((s₀ + quotLift b : SInt 𝔪) : F) ^ 2 / (B : F)) := by
    intro b
    simp only [hH]
    rw [if_pos (add_mem hq0 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π))), ← hs₀]
    congr 1
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
    field_simp
  simp_rw [hval]
  exact finsum_translate B s₀ (fun y : SInt 𝔪 => sAddChar 𝔪 ((c : F) * (y : F) ^ 2 / (B : F)))
    (fun x w hw => phase_per B c x w hw)

end field

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Ind: `gs` over a product of allowed prime generators

For a multiset `s` of good exterior primes and `Π_s = ∏_{P∈s} gen P`:
`gs Π_s c = √(N s) · ∏_{P∈s} γ₃(P) χ_P(c)³` whenever `c ∉ P R` for all `P ∈ s`
(`gs_prod`), together with `Π_s R = (∏ s) R`, finiteness and `#(R/Π_s R) = ∏ N P`.
The cross terms of the Chinese remainder step cancel by sextic reciprocity (`AllowedGen`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-- `P` is a good exterior prime. -/
def GoodI (𝔪 : Ideal (𝓞 F)) (P : Ideal (𝓞 F)) : Prop :=
  ∃ hP : P.IsPrime, ∃ h0 : P ≠ ⊥, C3I.Good 𝔪 (⟨P, hP, h0⟩ : HeightOneSpectrum (𝓞 F))

/-- The product of the allowed generators. -/
def piS (g : AllowedGen ι 𝔪) (s : Multiset (Ideal (𝓞 F))) : SInt 𝔪 := (s.map g.gen).prod

/-- The weight `γ₃(P) χ_P(c)³`. -/
def wt (g : AllowedGen ι 𝔪) (c : SInt 𝔪) (P : Ideal (𝓞 F)) : ℂ :=
  gaussPhase g 3 P * sexticResidueSymbol ι 𝔪 P c ^ 3

lemma sqrtC_mul (a b : ℕ) :
    ((Real.sqrt ((a * b : ℕ) : ℝ) : ℝ) : ℂ) =
      ((Real.sqrt (a : ℝ) : ℝ) : ℂ) * ((Real.sqrt (b : ℝ) : ℝ) : ℂ) := by
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

lemma sqrtC_sq (a : ℕ) :
    ((Real.sqrt (a : ℝ) : ℝ) : ℂ) * ((Real.sqrt (a : ℝ) : ℝ) : ℂ) = (a : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl

/-- The trivial quotient. -/
lemma gs_one (c : SInt 𝔪) : gs 𝔪 1 c = 1 := by
  unfold gs
  rw [Ideal.span_singleton_one]
  haveI : Subsingleton (SInt 𝔪 ⧸ (⊤ : Ideal (SInt 𝔪))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [finsum_eq_single _ (0 : SInt 𝔪 ⧸ (⊤ : Ideal (SInt 𝔪)))
    (fun x hx => absurd (Subsingleton.elim x 0) hx)]
  apply C3B.sAddChar_of_mem
  have := coe_mem (c * quotLift (0 : SInt 𝔪 ⧸ (⊤ : Ideal (SInt 𝔪))) ^ 2)
  simpa [Subalgebra.coe_mul, Subalgebra.coe_pow] using this

lemma prod_sup_eq_top (s : Multiset (Ideal (𝓞 F))) (h : ∀ Q ∈ s, Q ⊔ 𝔪 = ⊤) :
    s.prod ⊔ 𝔪 = ⊤ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    have h1 : IsCoprime a 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr (h a (Multiset.mem_cons_self _ _))
    have h2 : IsCoprime s.prod 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr
      (ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ))
    exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma chi_prod {v : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 v) {ω : 𝓞 F}
    (hω : IsPrimitiveRoot ω 6) (s : Multiset (SInt 𝔪)) :
    sexticResidueSymbol ι 𝔪 v.asIdeal s.prod = (s.map (sexticResidueSymbol ι 𝔪 v.asIdeal)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [chi_one (ι := ι) h hω]
  | cons a s ih => rw [Multiset.prod_cons, chi_mul h hω, ih, Multiset.map_cons, Multiset.prod_cons]

/-- `x = y` from `x y = 1` and `y² = 1`. -/
lemma eq_of_mul_eq_one {x y : ℂ} (h1 : x * y = 1) (h2 : y ^ 2 = 1) : x = y := by
  calc x = x * y ^ 2 := by rw [h2, mul_one]
    _ = (x * y) * y := by ring
    _ = y := by rw [h1, one_mul]

lemma map_ne_top_of_good {v : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 v) :
    v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ :=
  (C3I.isMaximal_v h).ne_top

/-- The generator of a different good prime is a unit modulo `P`. -/
lemma gen_not_mem (g : AllowedGen ι 𝔪) {P Q : Ideal (𝓞 F)} (hP : GoodI 𝔪 P) (hQ : GoodI 𝔪 Q)
    (hPQ : P ≠ Q) : g.gen Q ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨hPp, hP0, hGP⟩ := hP
  obtain ⟨hQp, hQ0, hGQ⟩ := hQ
  intro hmem
  have hPm : P.IsMaximal := hPp.isMaximal hP0
  have hQm : Q.IsMaximal := hQp.isMaximal hQ0
  have hsup : P ⊔ Q = ⊤ := by
    by_contra hne
    have h1 : P = P ⊔ Q := hPm.eq_of_le hne le_sup_left
    have h2 : Q = P ⊔ Q := hQm.eq_of_le hne le_sup_right
    exact hPQ (h1.trans h2.symm)
  have hspan : Ideal.span {g.gen Q} = Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    span_pi (v := ⟨Q, hQp, hQ0⟩) g hGQ
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  apply map_ne_top_of_good (v := ⟨P, hPp, hP0⟩) hGP
  change P.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤
  rw [eq_top_iff, ← Ideal.map_top (algebraMap (𝓞 F) (SInt 𝔪)), ← hsup, Ideal.map_sup]
  exact sup_le le_rfl hle

/-- **The product formula for `gs`.** -/
theorem gs_prod (g : AllowedGen ι 𝔪) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    ∀ (n : ℕ) (s : Multiset (Ideal (𝓞 F))), Multiset.card s = n → (∀ P ∈ s, GoodI 𝔪 P) →
      Ideal.span {piS g s} = s.prod.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧ piS g s ≠ 0 ∧
      Finite (SInt 𝔪 ⧸ Ideal.span {piS g s}) ∧
      Nat.card (SInt 𝔪 ⧸ Ideal.span {piS g s}) = (s.map Ideal.absNorm).prod ∧
      ∀ c : SInt 𝔪, (∀ P ∈ s, c ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪))) →
        gs 𝔪 (piS g s) c =
          ((Real.sqrt ((s.map Ideal.absNorm).prod : ℝ) : ℝ) : ℂ) * (s.map (wt g c)).prod := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hcard hs
  rcases Multiset.empty_or_exists_mem s with rfl | ⟨P, hPs⟩
  · have h1 : piS g (0 : Multiset (Ideal (𝓞 F))) = 1 := by simp [piS]
    rw [h1, Ideal.span_singleton_one]
    haveI : Subsingleton (SInt 𝔪 ⧸ (⊤ : Ideal (SInt 𝔪))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    refine ⟨by rw [Multiset.prod_zero, Ideal.one_eq_top, Ideal.map_top], one_ne_zero,
      inferInstance, ?_, fun c _ => ?_⟩
    · simp only [Multiset.map_zero, Multiset.prod_zero]
      haveI : Unique (SInt 𝔪 ⧸ (⊤ : Ideal (SInt 𝔪))) := uniqueOfSubsingleton 0
      exact Nat.card_unique
    · rw [gs_one]; simp
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hPs
  have hGP : GoodI 𝔪 P := hs P (Multiset.mem_cons_self P t)
  obtain ⟨hPp, hP0, hG⟩ := id hGP
  set v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hP0⟩ with hv
  have hvP : v.asIdeal = P := rfl
  set π := g.gen P with hπ
  have hπ0 : π ≠ 0 := pi_ne_zero (v := v) g hG
  haveI : Finite (SInt 𝔪 ⧸ Ideal.span {π}) := finite_pi (v := v) g hG
  have hspanπ : Ideal.span {π} = P.map (algebraMap (𝓞 F) (SInt 𝔪)) := span_pi (v := v) g hG
  have hextπ : Ext 𝔪 π := ext_pi (v := v) g hG
  have hcardπ : Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) = Ideal.absNorm P := natCard_pi (v := v) g hG
  by_cases hPt : P ∈ t
  · -- a repeated prime: peel `π²`
    obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hPt
    have hcard' : Multiset.card t' < n := by
      rw [← hcard]; simp
    obtain ⟨hspan', hne', hfin', hN', hgs'⟩ := ih _ hcard' t' rfl
      (fun Q hQ => hs Q (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hQ)))
    set B := piS g t'
    have hpi : piS g (P ::ₘ P ::ₘ t') = B * π * π := by
      simp only [piS, Multiset.map_cons, Multiset.prod_cons, B, hπ]; ring
    have hextB : Ext 𝔪 B := by
      refine ⟨t'.prod, ?_, hspan'⟩
      exact prod_sup_eq_top t' fun Q hQ => by
        obtain ⟨_, _, hGQ⟩ := hs Q (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hQ))
        exact hGQ.cop
    haveI := hfin'
    haveI : Finite (SInt 𝔪 ⧸ Ideal.span {B * π}) := finite_mul B π hne'
    rw [hpi]
    refine ⟨?_, mul_ne_zero (mul_ne_zero hne' hπ0) hπ0, finite_mul (B * π) π
      (mul_ne_zero hne' hπ0), ?_, fun c hc => ?_⟩
    · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        hspan', hspanπ, Multiset.prod_cons, Multiset.prod_cons, ← Ideal.map_mul, ← Ideal.map_mul]
      congr 1; ring
    · rw [natCard_mul _ _ (mul_ne_zero hne' hπ0), natCard_mul _ _ hne', hN', hcardπ]
      simp only [Multiset.map_cons, Multiset.prod_cons]; ring
    · have hcP : c ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
        hc P (Multiset.mem_cons_self _ _)
      rw [gs_peel g hG hω B c hextB hne' hcP,
        hgs' c (fun Q hQ => hc Q (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hQ)))]
      have hw2 : wt g c P * wt g c P = 1 := by
        have h1 := gaussPhase_sq g hG hω
        have h2 := chi3_sq (ι := ι) hG hω c hcP
        simp only [wt]
        calc gaussPhase g 3 P * sexticResidueSymbol ι 𝔪 P c ^ 3 *
              (gaussPhase g 3 P * sexticResidueSymbol ι 𝔪 P c ^ 3) =
            gaussPhase g 3 P ^ 2 * (sexticResidueSymbol ι 𝔪 P c ^ 3) ^ 2 := by ring
          _ = 1 := by rw [show gaussPhase g 3 P = gaussPhase g 3 v.asIdeal from rfl, h1,
                show sexticResidueSymbol ι 𝔪 P c = sexticResidueSymbol ι 𝔪 v.asIdeal c from rfl, h2,
                one_mul]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [sqrtC_mul, sqrtC_mul, show (Ideal.absNorm v.asIdeal : ℂ) = Ideal.absNorm P from rfl]
      have hsq := sqrtC_sq (Ideal.absNorm P)
      linear_combination (-((Real.sqrt ((t'.map Ideal.absNorm).prod : ℝ) : ℝ) : ℂ) * wt g c P *
        wt g c P * (t'.map (wt g c)).prod) * hsq + (-(Ideal.absNorm P : ℂ) *
        ((Real.sqrt ((t'.map Ideal.absNorm).prod : ℝ) : ℝ) : ℂ) * (t'.map (wt g c)).prod) * hw2
  · -- a new prime: Chinese remainders
    have hcard' : Multiset.card t < n := by
      rw [← hcard]; simp
    have hst : ∀ Q ∈ t, GoodI 𝔪 Q := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hspan', hne', hfin', hN', hgs'⟩ := ih _ hcard' t rfl hst
    set B := piS g t
    haveI := hfin'
    have hpi : piS g (P ::ₘ t) = π * B := by
      simp only [piS, Multiset.map_cons, Multiset.prod_cons, B, hπ]
    have hprime : (Ideal.span {π}).IsMaximal := by rw [hspanπ]; exact C3I.isMaximal_v hG
    have hQnot : ∀ Q ∈ t, g.gen Q ∉ Ideal.span {π} := by
      intro Q hQ
      rw [hspanπ]
      exact gen_not_mem g hGP (hst Q hQ) (fun hPQ => hPt (hPQ ▸ hQ))
    have hBnot : B ∉ Ideal.span {π} := by
      intro hmem
      obtain ⟨x, hx, hxm⟩ := (hprime.isPrime.multiset_prod_mem_iff_exists_mem _).mp hmem
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hx
      exact hQnot Q hQ hxm
    obtain ⟨u, i, hi, hui⟩ := hprime.exists_inv hBnot
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hi
    have hextB : Ext 𝔪 B := by
      refine ⟨t.prod, ?_, hspan'⟩
      exact prod_sup_eq_top t fun Q hQ => by
        obtain ⟨_, _, hGQ⟩ := hst Q hQ
        exact hGQ.cop
    rw [hpi]
    refine ⟨?_, mul_ne_zero hπ0 hne', finite_mul π B hπ0, ?_, fun c hc => ?_⟩
    · rw [← Ideal.span_singleton_mul_span_singleton, hspan', hspanπ, Multiset.prod_cons,
        Ideal.map_mul]
    · rw [natCard_mul _ _ hπ0, hN', hcardπ]
      simp only [Multiset.map_cons, Multiset.prod_cons]
    · have hcP : c ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
        hc P (Multiset.mem_cons_self _ _)
      have huP : u ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        intro hu
        apply hprime.ne_top
        rw [Ideal.eq_top_iff_one, ← hui, hspanπ]
        exact add_mem (Ideal.mul_mem_right _ _ hu)
          (Ideal.mul_mem_left _ _ (hspanπ ▸ Ideal.mem_span_singleton_self π))
      have hprimeP : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsPrime :=
        (C3I.isMaximal_v hG).isPrime
      have hcuP : c * u ∉ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := fun hm =>
        (hprimeP.mem_or_mem hm).elim hcP huP
      -- facts at the other primes
      have hQdata : ∀ Q ∈ t, ∃ hQp : Q.IsPrime, ∃ hQ0 : Q ≠ ⊥,
          C3I.Good 𝔪 (⟨Q, hQp, hQ0⟩ : HeightOneSpectrum (𝓞 F)) ∧
          B ∈ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧ r ∉ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        intro Q hQ
        obtain ⟨hQp, hQ0, hGQ⟩ := hst Q hQ
        have hBQ : B ∈ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
          have hgQ : g.gen Q ∈ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
            rw [← span_pi (v := ⟨Q, hQp, hQ0⟩) g hGQ]; exact Ideal.mem_span_singleton_self _
          obtain ⟨t₀, ht₀⟩ := Multiset.exists_cons_of_mem hQ
          simp only [B, piS, ht₀, Multiset.map_cons, Multiset.prod_cons]
          exact Ideal.mul_mem_right _ _ hgQ
        refine ⟨hQp, hQ0, hGQ, hBQ, fun hrQ => ?_⟩
        apply (C3I.isMaximal_v hGQ).ne_top
        change Q.map (algebraMap (𝓞 F) (SInt 𝔪)) = ⊤
        rw [Ideal.eq_top_iff_one, ← hui]
        exact add_mem (Ideal.mul_mem_left _ _ hBQ) (Ideal.mul_mem_right _ _ hrQ)
      rw [gs_mul π B c u r hui hextπ hextB hπ0 hne', gs_prime g hG hω (c * u) hcuP]
      have hcr : ∀ Q ∈ t, c * r ∉ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
        intro Q hQ hm
        obtain ⟨hQp, hQ0, hGQ, -, hrQ⟩ := hQdata Q hQ
        have hcQ := hc Q (Multiset.mem_cons_of_mem hQ)
        exact ((C3I.isMaximal_v hGQ).isPrime.mem_or_mem hm).elim hcQ hrQ
      rw [hgs' (c * r) hcr]
      -- the weights at `Q ∈ t`
      have hwQ : ∀ Q ∈ t, wt g (c * r) Q = wt g c Q * sexticResidueSymbol ι 𝔪 Q π ^ 3 := by
        intro Q hQ
        obtain ⟨hQp, hQ0, hGQ, hBQ, hrQ⟩ := hQdata Q hQ
        have hmul := chi_mul (ι := ι) (v := ⟨Q, hQp, hQ0⟩) hGQ hω c r
        have h1 : sexticResidueSymbol ι 𝔪 Q r * sexticResidueSymbol ι 𝔪 Q π = 1 := by
          rw [← chi_mul (ι := ι) (v := ⟨Q, hQp, hQ0⟩) hGQ hω,
            chi_congr (ι := ι) (v := ⟨Q, hQp, hQ0⟩) hGQ hω (y := 1) ?_,
            chi_one (ι := ι) (v := ⟨Q, hQp, hQ0⟩) hGQ hω]
          rw [show r * π - 1 = -(u * B) by linear_combination hui]
          exact neg_mem (Ideal.mul_mem_left _ _ hBQ)
        have hπQ : π ∉ Q.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
          gen_not_mem g (hst Q hQ) hGP (fun hQP => hPt (hQP ▸ hQ))
        have h2 := chi3_sq (ι := ι) (v := ⟨Q, hQp, hQ0⟩) hGQ hω π hπQ
        have h3 : sexticResidueSymbol ι 𝔪 Q r ^ 3 = sexticResidueSymbol ι 𝔪 Q π ^ 3 :=
          eq_of_mul_eq_one (by rw [← mul_pow, h1, one_pow]) h2
        simp only [wt]
        change gaussPhase g 3 Q * sexticResidueSymbol ι 𝔪 Q (c * r) ^ 3 = _
        rw [show sexticResidueSymbol ι 𝔪 Q (c * r) =
          sexticResidueSymbol ι 𝔪 Q c * sexticResidueSymbol ι 𝔪 Q r from hmul, mul_pow, h3]
        ring
      rw [Multiset.map_congr rfl hwQ, Multiset.prod_map_mul]
      -- the weight at `P`
      have h1 : sexticResidueSymbol ι 𝔪 P u * sexticResidueSymbol ι 𝔪 P B = 1 := by
        rw [← chi_mul (ι := ι) (v := v) hG hω,
          chi_congr (ι := ι) (v := v) hG hω (y := 1) ?_, chi_one (ι := ι) (v := v) hG hω]
        rw [show u * B - 1 = -(r * π) by linear_combination hui]
        exact neg_mem (Ideal.mul_mem_left _ _ (hspanπ ▸ Ideal.mem_span_singleton_self π))
      have h2 := chi3_sq (ι := ι) (v := v) hG hω B (by rw [← hspanπ]; exact hBnot)
      have h3 : sexticResidueSymbol ι 𝔪 P u ^ 3 = sexticResidueSymbol ι 𝔪 P B ^ 3 :=
        eq_of_mul_eq_one (by rw [← mul_pow, h1, one_pow]) h2
      have hB3 : sexticResidueSymbol ι 𝔪 P B ^ 3 =
          (t.map fun Q => sexticResidueSymbol ι 𝔪 P (g.gen Q) ^ 3).prod := by
        change sexticResidueSymbol ι 𝔪 v.asIdeal (t.map g.gen).prod ^ 3 = _
        rw [chi_prod (ι := ι) hG hω, Multiset.map_map, ← Multiset.prod_map_pow]
        rfl
      -- reciprocity kills the cross terms
      have hcross : sexticResidueSymbol ι 𝔪 P B ^ 3 *
          (t.map fun Q => sexticResidueSymbol ι 𝔪 Q π ^ 3).prod = 1 := by
        rw [hB3, ← Multiset.prod_map_mul]
        refine Multiset.prod_eq_one fun z hz => ?_
        obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hz
        obtain ⟨hQp, hQ0, hGQ, -, -⟩ := hQdata Q hQ
        have hrec := g.reciprocity P Q hPp hQp hG.ext
          (C3I.Good.ext (v := ⟨Q, hQp, hQ0⟩) hGQ) (fun hPQ => hPt (hPQ ▸ hQ))
        rw [← hrec]
        have := chi3_sq (ι := ι) (v := v) hG hω (g.gen Q) (by
          rw [← hspanπ]; exact hQnot Q hQ)
        rw [← this]; ring
      have hcu : sexticResidueSymbol ι 𝔪 P (c * u) ^ 3 =
          sexticResidueSymbol ι 𝔪 P c ^ 3 * sexticResidueSymbol ι 𝔪 P u ^ 3 := by
        rw [show sexticResidueSymbol ι 𝔪 P (c * u) =
          sexticResidueSymbol ι 𝔪 P c * sexticResidueSymbol ι 𝔪 P u from
          chi_mul (ι := ι) (v := v) hG hω c u, mul_pow]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [sqrtC_mul]
      change sexticResidueSymbol ι 𝔪 P (c * u) ^ 3 *
          ((Real.sqrt (Ideal.absNorm P : ℝ) : ℝ) : ℂ) * gaussPhase g 3 P * _ = _
      rw [hcu, h3, show wt g c P = gaussPhase g 3 P * sexticResidueSymbol ι 𝔪 P c ^ 3 from rfl]
      linear_combination (sexticResidueSymbol ι 𝔪 P c ^ 3 *
        ((Real.sqrt (Ideal.absNorm P : ℝ) : ℝ) : ℂ) * gaussPhase g 3 P *
        ((Real.sqrt ((t.map Ideal.absNorm).prod : ℝ) : ℝ) : ℂ) * (t.map (wt g c)).prod) * hcross

end ArtinPrimitiveRoots.L3M

end
end
end

section
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

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
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

end C3M

end ArtinPrimitiveRoots

end
end

section
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
end

section
section
namespace ArtinPrimitiveRoots

open NumberField

/-! L2D: `U_S / U_S^6` is finite (library 4956b3f7, the S-unit count). -/

variable {F : Type*} [Field F] [NumberField F]

lemma L2D_placesOf_finite (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  apply (Ideal.finite_factors h𝔪).subset
  intro v hv
  exact Ideal.dvd_iff_le.2 hv

lemma L2D_SClass_finite (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) : Finite (SClass 𝔪) := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  have hμ : (primitiveRoots 6 F).Nonempty :=
    ⟨_, (mem_primitiveRoots (by norm_num)).2 hζ6⟩
  have : Finite (placesOf 𝔪) := (L2D_placesOf_finite 𝔪 h𝔪).to_subtype
  have hc := NumberField.natCard_sUnit_quotient_range_powMonoidHom F (placesOf 𝔪) hμ
  apply Nat.finite_of_card_ne_zero
  change Nat.card (↥((placesOf 𝔪).unit F) ⧸
    (powMonoidHom 6 : ↥((placesOf 𝔪).unit F) →* ↥((placesOf 𝔪).unit F)).range) ≠ 0
  rw [hc]
  positivity

end ArtinPrimitiveRoots

end
end

section
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

/-- A primitive sixth root of unity in `𝓞 F`. -/
theorem exists_prim_six (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F] :
    ∃ ω : 𝓞 F, IsPrimitiveRoot ω 6 := by
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have h6 : 6 ∣ n := Nat.dvd_trans (by norm_num) hn
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel h6).symm
  exact ⟨hζ6.toInteger, hζ6.toInteger_isPrimitiveRoot⟩

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
end

section
section
/-! # L3M_Red: CutGam from Hecke's quadratic Gauss sum and Kummer (Lemma 3.3 for S-units)

`L3M_CutHecke F`: `Σ_{x ∈ 𝓞/(α)} exp(2πi Tr(x²/α)) = √N(α)` for `α ≡ 1 (mod 4𝔇)`.

`L3M.target_of_hecke`: the CutGam statement from it. For `α ≡ 1 (mod 𝔪^j)`, `Π = ∏_{P | α} gen P = α ε`
(`ε ∈ R^×`); the global sum is `gs Π ε = √Nα ∏ γ₃(P) χ_P(ε)³` (`gs_prod`), it equals `√Nα` by the cut,
and `∏ χ_P(ε) = χ_{(α)}(ε) = 1` by Kummer (`kummer_unif`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

/-- **Hecke's quadratic Gauss sum** (the cut): for `α ≡ 1 (mod 4𝔇)`,
`Σ_{x ∈ 𝓞/(α)} exp(2πi Tr(x²/α)) = √N(α)`. -/
def L3M_CutHecke' (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ α : 𝓞 F, α - 1 ∈ Ideal.span {(4 : 𝓞 F)} * differentIdeal ℤ (𝓞 F) →
    ∑ᶠ x : 𝓞 F ⧸ Ideal.span {α},
        Complex.exp (2 * Real.pi * Complex.I *
          ((Algebra.trace ℚ F (((Quotient.out x : 𝓞 F) : F) ^ 2 / (α : F)) : ℚ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ)

namespace L3M

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

theorem exists_pow_le_of_primes {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔪 I : Ideal R}
    (hI : I ≠ ⊥) (h : ∀ v : HeightOneSpectrum R, I ≤ v.asIdeal → 𝔪 ≤ v.asIdeal) :
    ∃ j : ℕ, 𝔪 ^ j ≤ I := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg_radical ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J ⟨hIJ, hJ⟩ => ?_
  have hJ0 : J ≠ ⊥ := fun h0 => hI (le_bot_iff.1 (h0 ▸ hIJ))
  exact h ⟨J, hJ, hJ0⟩ hIJ

theorem isExterior_of_sub_one_mem {j : ℕ} (hj : 1 ≤ j) {α : 𝓞 F} (hα : α ≠ 0)
    (h : α - 1 ∈ 𝔪 ^ j) : IsExterior 𝔪 (Ideal.span {α}) := by
  refine ⟨by rwa [ne_eq, Ideal.span_singleton_eq_bot], ?_⟩
  rw [eq_top_iff]
  have h1 : α - 1 ∈ 𝔪 := Ideal.pow_le_self (by omega) h
  have : (1 : 𝓞 F) = α - (α - 1) := by ring
  intro z _
  rw [← mul_one z, this]
  exact Ideal.mul_mem_left _ z (Submodule.sub_mem _ (Ideal.mem_sup_left
    (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right h1))

theorem kummer_six {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
    (hχ : C3M.HypChi ι 𝔪) (u : SInt 𝔪) (hu : IsUnit u) {b : F} (hb : b ^ 6 = (u : F))
    {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 u = 1 := by
  have hbR : b ∈ (placesOf 𝔪).integer F := by
    intro v hv
    have hu1 : v.valuation F (u : F) ≤ 1 := u.2 v hv
    rw [← hb, map_pow] at hu1
    exact (pow_le_one_iff (by norm_num)).1 hu1
  set b' : SInt 𝔪 := ⟨b, hbR⟩
  have hb' : b' ^ 6 = u := Subtype.ext (by simp [b', hb])
  unfold residueSymbol
  refine Multiset.prod_eq_one fun z hz => ?_
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hz
  have hPp : P.IsPrime := (Ideal.isPrime_of_prime (prime_of_normalized_factor P hP))
  have hP0 : P ≠ ⊥ := (prime_of_normalized_factor P hP).ne_zero
  have hPe : IsExterior 𝔪 P := by
    refine ⟨hP0, ?_⟩
    rw [eq_top_iff, ← h𝔞.2]
    exact sup_le_sup_right (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)) _
  obtain ⟨hmul, hsix⟩ := hχ P hPp hPe
  have hbP : b' ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    intro hmem
    have : u ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := hb' ▸ Ideal.pow_mem_of_mem _ hmem 6 (by norm_num)
    exact C3M.map_ne_top hPp hPe (Ideal.eq_top_of_isUnit_mem _ this hu)
  have hpow : ∀ k : ℕ, sexticResidueSymbol ι 𝔪 P (b' ^ (k + 1)) =
      sexticResidueSymbol ι 𝔪 P b' ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, hmul, ih, ← pow_succ]
  rw [← hb', hpow 5, hsix b' hbP]




lemma residue_mul (hχ : C3M.HypChi ι 𝔪) {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) (x y : SInt 𝔪) :
    residueSymbol ι 𝔪 𝔞 (x * y) = residueSymbol ι 𝔪 𝔞 x * residueSymbol ι 𝔪 𝔞 y := by
  unfold residueSymbol
  rw [← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun P hP => ?_
  obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors h𝔞 hP
  exact (hχ P hPp hPe).1 x y

/-- Kummer, uniformly over `U_S / U_S⁶`. -/
lemma kummer_unif
    (hK : ∀ u : SInt 𝔪, IsUnit u → ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j →
      residueSymbol ι 𝔪 (Ideal.span {α}) u = 1)
    (hχ : C3M.HypChi ι 𝔪) [Finite (SClass 𝔪)] :
    ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j → IsExterior 𝔪 (Ideal.span {α}) →
      ∀ ε : (SInt 𝔪)ˣ, residueSymbol ι 𝔪 (Ideal.span {α}) (ε : SInt 𝔪) = 1 := by
  classical
  haveI : Fintype (SClass 𝔪) := Fintype.ofFinite _
  choose ju hju using fun υ : SClass 𝔪 => hK υ.rep (Units.isUnit _)
  refine ⟨Finset.univ.sup ju, fun α hα hext ε => ?_⟩
  set e := Set.unitEquivUnitsInteger (placesOf 𝔪) F
  set u : SUnit 𝔪 := e.symm ε
  set υ : SClass 𝔪 := QuotientGroup.mk u
  set s₀ : SUnit 𝔪 := Function.surjInv QuotientGroup.mk_surjective υ
  have hmem : s₀⁻¹ * u ∈ (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range := by
    rw [← QuotientGroup.eq]; exact Function.surjInv_eq QuotientGroup.mk_surjective υ
  obtain ⟨w, hw⟩ := hmem
  have hu : u = s₀ * w ^ 6 := by
    rw [powMonoidHom_apply] at hw; rw [hw]; group
  have hε : (ε : SInt 𝔪) = υ.rep * ((e w : (SInt 𝔪)ˣ) : SInt 𝔪) ^ 6 := by
    have h1 : ε = e u := (e.apply_symm_apply ε).symm
    rw [h1, hu, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [hε, residue_mul hχ hext,
    hju υ α (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ υ)) hα), one_mul]
  exact kummer_six hχ _ ((Units.isUnit _).pow 6)
    (b := (((e w : (SInt 𝔪)ˣ) : SInt 𝔪) : F)) (by rw [Subalgebra.coe_pow]) hext

lemma conj_finsum {α : Type*} [Finite α] (f : α → ℂ) :
    starRingEnd ℂ (∑ᶠ a, f a) = ∑ᶠ a, starRingEnd ℂ (f a) := by
  haveI := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]

/-- `v(α) = 1` at the places of `S` when `α ≡ 1 (mod 𝔪)`. -/
lemma val_alpha_eq_one {α : 𝓞 F} (hα : α - 1 ∈ 𝔪) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∈ placesOf 𝔪) : v.valuation F (algebraMap (𝓞 F) F α) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hαv
  have hle : 𝔪 ≤ v.asIdeal := hv
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    have := sub_mem hαv (hle hα); rwa [sub_sub_cancel] at this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- `𝓞/(α) → R/(α)R` is injective for `α ≡ 1 (mod 𝔪)`. -/
lemma quotHom_injective {α : 𝓞 F} (hα : α - 1 ∈ 𝔪) :
    Function.Injective (C3I.quotHom 𝔪 (Ideal.span {α})) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [C3I.quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton'] at hx
  obtain ⟨r, hr⟩ := hx
  have hrF : algebraMap (𝓞 F) F a = (r : F) * algebraMap (𝓞 F) F α := by
    rw [← C3I.coe_alg, ← C3I.coe_alg, ← hr, Subalgebra.coe_mul]
  have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (r : F) ≤ 1 := by
    intro v
    by_cases hv : v ∈ placesOf 𝔪
    · have h1 : v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 := v.valuation_le_one a
      rw [hrF, map_mul, val_alpha_eq_one hα v hv, mul_one] at h1
      exact h1
    · exact r.2 v hv
  obtain ⟨r', hr'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hall
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  refine ⟨r', ?_⟩
  exact IsFractionRing.injective (𝓞 F) F
    (by rw [map_mul, hr', hrF] : algebraMap (𝓞 F) F (r' * α) = algebraMap (𝓞 F) F a)

end L3M

open L3M in
/-- **CutGam from Hecke's quadratic Gauss sum.** -/
theorem L3M.target_of_cuts (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ)
    (hK : ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ u : SInt 𝔪, IsUnit u → ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j →
        residueSymbol ι 𝔪 (Ideal.span {α}) u = 1)
    (hH : L3M_CutHecke' F) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∃ j : ℕ, ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
      ((normalizedFactors (Ideal.span {α})).map fun P => gaussPhase g 3 P).prod = 1 := by
  classical
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six n hn0 hn (F := F)
  obtain ⟨NK, hNK⟩ := hK
  obtain ⟨Nχ, hNχ⟩ := C3M.hypChiAll n hn0 hn ι
  set I4 : Ideal (𝓞 F) := Ideal.span {(4 : 𝓞 F)} * differentIdeal ℤ (𝓞 F) with hI4def
  have h40 : Ideal.span {(4 : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h; have := congrArg (fun x : 𝓞 F => (x : F)) h; norm_num at this
  have hI4 : I4 ≠ ⊥ := mul_ne_zero h40 differentIdeal_ne_bot
  set N₀ := max (max (C3I.cutN F) NK) (max Nχ (Ideal.absNorm I4))
  refine ⟨N₀, fun 𝔪 h𝔪 hsm g => ?_⟩
  have hsm' : ∀ N, N ≤ N₀ → SmallPrimesDvd N 𝔪 :=
    fun N hN P hP hP0 hPN => hsm P hP hP0 (hPN.trans hN)
  have hχ := hNχ 𝔪 h𝔪 (hsm' Nχ (by omega))
  haveI := L2D_SClass_finite n hn0 hn 𝔪 h𝔪
  obtain ⟨jK, hjK⟩ := kummer_unif (hNK 𝔪 h𝔪 (hsm' NK (by omega)) g) hχ
  obtain ⟨j4, hj4⟩ := exists_pow_le_of_primes (𝔪 := 𝔪) hI4 (fun v hv => by
    have hN : Ideal.absNorm v.asIdeal ≤ Ideal.absNorm I4 :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
        (Ideal.absNorm_dvd_absNorm_of_le hv)
    exact hsm' (Ideal.absNorm I4) (by omega) _ v.isPrime v.ne_bot hN)
  refine ⟨max (max jK j4) 1, fun α hα0 hαj => ?_⟩
  have hαK : α - 1 ∈ 𝔪 ^ jK := Ideal.pow_le_pow_right (by omega) hαj
  have hα4 : α - 1 ∈ I4 := hj4 (Ideal.pow_le_pow_right (by omega) hαj)
  have hα1 : α - 1 ∈ 𝔪 := Ideal.pow_le_self (by omega) hαj
  have hext : IsExterior 𝔪 (Ideal.span {α}) := isExterior_of_sub_one_mem (by omega) hα0 hαj
  set s := normalizedFactors (Ideal.span {α}) with hsdef
  have hs : ∀ P ∈ s, GoodI 𝔪 P := fun P hP => by
    obtain ⟨hPp, hPe⟩ := C3M.exterior_of_mem_factors hext hP
    exact ⟨hPp, hPe.1, C3I.good_of_exterior n hn0 hn (N₀ := N₀) (by omega) hsm hPp hPe⟩
  obtain ⟨hspan, hne, hfin, hcard, hgs⟩ := gs_prod g hω _ s rfl hs
  have hprod : s.prod = Ideal.span {α} := Ideal.prod_normalizedFactors_eq_self hext.1
  set α' : SInt 𝔪 := algebraMap (𝓞 F) (SInt 𝔪) α with hα'
  have hmapα : (Ideal.span {α}).map (algebraMap (𝓞 F) (SInt 𝔪)) = Ideal.span {α'} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hspan' : Ideal.span {piS g s} = Ideal.span {α'} := by rw [hspan, hprod, hmapα]
  obtain ⟨ε, hε⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan'.symm
  -- `N(α)`
  have hNα : (s.map Ideal.absNorm).prod = Ideal.absNorm (Ideal.span {α}) := by
    rw [← map_multiset_prod, hprod]
  have hNα0 : Ideal.absNorm (Ideal.span {α}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hext.1
  -- the bijection `𝓞/(α) ≃ R/(α)R`
  haveI : Finite (SInt 𝔪 ⧸ (Ideal.span {α}).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
    rw [hmapα, ← hspan']; exact hfin
  have hbij : Function.Bijective (C3I.quotHom 𝔪 (Ideal.span {α})) := by
    refine (quotHom_injective hα1).bijective_of_nat_card_le ?_
    rw [hmapα, ← hspan', hcard, hNα, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  set φ := Equiv.ofBijective _ hbij
  haveI : Finite (𝓞 F ⧸ Ideal.span {α}) := Finite.of_equiv _ φ.symm
  -- the global sum through `R`
  set T := ∑ᶠ x : 𝓞 F ⧸ Ideal.span {α}, Complex.exp (-(2 * Real.pi * Complex.I) *
      ((Algebra.trace ℚ F (((Quotient.out x : 𝓞 F) : F) ^ 2 / (α : F)) : ℚ) : ℂ)) with hT
  have hTgs : T = gs 𝔪 (piS g s) ε := by
    unfold gs
    rw [hspan', ← hmapα, ← finsum_comp_equiv φ]
    refine finsum_congr fun x => ?_
    set y : 𝓞 F := Quotient.out x
    have hφx : φ x = Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) y) := by
      change C3I.quotHom 𝔪 (Ideal.span {α}) x = _
      rw [← C3I.quotHom_mk, show Ideal.Quotient.mk (Ideal.span {α}) y = x from Quotient.out_eq x]
    have hεF : ((ε : SInt 𝔪) : F) ≠ 0 := by
      intro h0
      exact ε.ne_zero (Subtype.ext h0)
    have hαF : (α' : F) ≠ 0 := by
      rw [hα', C3I.coe_alg]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hα0
    rw [← hε, hφx]
    have hper := per_eq (I := Ideal.span {α'})
      (f := fun z : SInt 𝔪 => sAddChar 𝔪 ((1 : SInt 𝔪) * (z : F) ^ 2 / (α' : F)))
      (fun z w hw => by simpa using phase_per α' 1 z w hw)
      (x := quotLift (Ideal.Quotient.mk ((Ideal.span {α}).map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) y)))
      (y := algebraMap (𝓞 F) (SInt 𝔪) y) (by rw [← hmapα]; exact ql_mk_sub _ _)
    simp only [Subalgebra.coe_one, one_mul] at hper
    rw [show (((ε : SInt 𝔪) : F) * ((quotLift (Ideal.Quotient.mk ((Ideal.span {α}).map
        (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) y)) : SInt 𝔪) : F) ^ 2 /
        ((α' * ε : SInt 𝔪) : F)) = ((quotLift (Ideal.Quotient.mk ((Ideal.span {α}).map
        (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) y)) : SInt 𝔪) : F) ^ 2 /
        (α' : F) by rw [Subalgebra.coe_mul]; field_simp, hper]
    have hwit := C3I.sAddChar_eq_of_wit (𝔪 := 𝔪)
      (x := ((algebraMap (𝓞 F) (SInt 𝔪) y : SInt 𝔪) : F) ^ 2 / (α' : F))
      (y := ((algebraMap (𝓞 F) (SInt 𝔪) y : SInt 𝔪) : F) ^ 2 / (α' : F))
      (by rw [sub_self]; exact zero_mem _) (fun v hv => by
        rw [hα', C3I.coe_alg, C3I.coe_alg, map_div₀, map_pow, val_alpha_eq_one hα1 v hv, div_one]
        exact pow_le_one₀ zero_le (v.valuation_le_one y))
    rw [hwit, hα', C3I.coe_alg, C3I.coe_alg]
  -- Hecke
  have hHα := hH α hα4
  have hTval : T = ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ) := by
    have h1 := congrArg (starRingEnd ℂ) hHα
    rw [conj_finsum, Complex.conj_ofReal] at h1
    rw [hT, ← h1]
    refine finsum_congr fun x => ?_
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    ring
  -- the product formula
  have hεnot : ∀ P ∈ s, (ε : SInt 𝔪) ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    intro P hP hmem
    obtain ⟨hPp, hP0, hG⟩ := hs P hP
    exact (C3I.isMaximal_v hG).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ε.isUnit)
  have hmain := hgs ε hεnot
  rw [← hTgs, hTval, hNα] at hmain
  have hsq0 : ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast Nat.pos_of_ne_zero hNα0
  have hwt : (s.map (wt g (ε : SInt 𝔪))).prod = 1 := by
    have := hmain
    field_simp at this
    exact this.symm
  have hsplit : (s.map (wt g (ε : SInt 𝔪))).prod =
      (s.map fun P => gaussPhase g 3 P).prod *
        residueSymbol ι 𝔪 (Ideal.span {α}) (ε : SInt 𝔪) ^ 3 := by
    unfold wt residueSymbol
    rw [Multiset.prod_map_mul, Multiset.prod_map_pow]
  rw [hsplit, hjK α hαK hext ε, one_pow, mul_one] at hwt
  exact hwt

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3M_DevG: CutGam from the seams `finsum_cexp_trace_sq_div_eq_sqrt_absNorm` (Hecke) and
`exists_cutoff_residueSymbol_span_eq_one_of_isUnit` (Kummer) -/

set_option linter.style.haveILetI false

namespace ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

theorem exists_cutoff_prod_gaussPhase_three_span_eq_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∃ j : ℕ, ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
      ((normalizedFactors (Ideal.span {α})).map fun P => gaussPhase g 3 P).prod = 1
  := by
  haveI : NeZero n := ⟨hn0.ne'⟩
  haveI : IsTotallyComplex F := IsCyclotomicExtension.Rat.isTotallyComplex (n := n) F
    (by have := Nat.le_of_dvd hn0 hn; omega)
  exact L3M.target_of_cuts n hn0 hn F ι
    (exists_cutoff_residueSymbol_span_eq_one_of_isUnit n hn0 hn F ι)
    (fun α hα => finsum_cexp_trace_sq_div_eq_sqrt_absNorm F α hα)

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField UniqueFactorizationMonoid

theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∃ j : ℕ, ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j →
      ((normalizedFactors (Ideal.span {α})).map fun P => gaussPhase g 3 P).prod = 1
  := by
  exact ArtinPrimitiveRoots.exists_cutoff_prod_gaussPhase_three_span_eq_one n hn0 hn F ι

end
