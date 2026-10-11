-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_gaussPhase_mul_gaussPhase_mul_conj_gaussLambda_mul_conj_gaussG_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T19:41:08.626637+00:00
-- url     : https://prove2.me/submissions/73657adb-6bbb-4b8d-82bc-3408a9f63ce7

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta

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

lemma omegaP_prim (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
  hω.idealQuotient_mk (absNorm_ne_one v) h.coprime_six

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

/-- Davenport–Hasse via Jacobi sums: `χ(4) J(χ, χ) = J(χ³, χ)`. -/
lemma jacobi_dh : chi ι h hω 4 * jacobiSum (chi ι h hω) (chi ι h hω) =
    jacobiSum (chi ι h hω ^ (3 : ℕ)) (chi ι h hω) := by
  classical
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  set χ := chi ι h hω
  have h2 : (2 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ≠ 0 := by
    intro h0
    apply ringChar_ne_two h hω
    exact absurd h0 (Ring.two_ne_zero (ringChar_ne_two h hω))
  -- `χ(4) J(χ,χ) = ∑_x χ(1 - (2x-1)²)`
  have e1 : χ 4 * jacobiSum χ χ = ∑ u, χ (1 - u ^ 2) := by
    rw [jacobiSum, Finset.mul_sum]
    have hb : Function.Bijective (fun x : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) =>
        2 * x - 1) := by
      constructor
      · intro a b hab
        have : 2 * (a - b) = 0 := by simp only at hab; linear_combination hab
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)
      · intro y; exact ⟨(y + 1) / 2, by field_simp; ring⟩
    conv_rhs => rw [← (Equiv.ofBijective _ hb).sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.ofBijective_apply]
    rw [← map_mul, ← map_mul]
    congr 1; ring
  -- fibre over `w = u²`
  have e2 : ∑ u, χ (1 - u ^ 2) = ∑ w, (1 + (χ ^ 3) w) * χ (1 - w) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun u => u ^ 2) (fun u => χ (1 - u ^ 2))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.1 hu).2]), Finset.sum_const,
      nsmul_eq_mul, card_sqrt h hω]
  have e3 : ∑ w, χ (1 - w) = 0 := by
    have hχ : χ ≠ 1 := by
      have := chi_pow_ne_one (ι := ι) h hω (j := 1) (by norm_num)
      rwa [pow_one] at this
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    exact Fintype.sum_equiv (Equiv.subLeft 1) _ _ (fun w => rfl)
  rw [e1, e2]
  simp only [add_mul, one_mul, Finset.sum_add_distrib, e3, zero_add, jacobiSum]

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

lemma card_ne_zero_C :
    ((Fintype.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ)) ≠ 0 := by
  rw [card_L h hω, Nat.cast_ne_zero]; exact (absNorm_pos v).ne'

lemma gs_ne_zero {j : ℕ} (hj : ¬ 6 ∣ j) : gaussSum (chi ι h hω ^ j) (psi g h) ≠ 0 := by
  have hc := card_ne_zero_C h hω
  have hχ := chi_pow_ne_one (ι := ι) h hω hj
  have hψ := psi_isPrimitive g h
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  exact gaussSum_ne_zero_of_nontrivial hc hχ hψ

/-- `g(φ, ψ⁻¹) = g(φ, ψ)` for the powers of `χ` (as `χ(-1) = 1`). -/
lemma gs_inv_psi (j : ℕ) :
    gaussSum (chi ι h hω ^ j) (psi g h)⁻¹ = gaussSum (chi ι h hω ^ j) (psi g h) := by
  have h1 := chi_pow_neg_one (ι := ι) h hω j
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := mul_gaussSum_inv_eq_gaussSum (chi ι h hω ^ j) (psi g h)
  rw [h1, one_mul] at this
  exact this

/-- `g_j g_k = N P` for `j + k ≡ 0 (mod 6)`, `6 ∤ j`. -/
lemma gs_mul_gs {j k : ℕ} (hj : ¬ 6 ∣ j) (hjk : (j + k) % 6 = 0) :
    gaussSum (chi ι h hω ^ j) (psi g h) * gaussSum (chi ι h hω ^ k) (psi g h) =
      Ideal.absNorm v.asIdeal := by
  have hχ := chi_pow_ne_one (ι := ι) h hω hj
  have hψ := psi_isPrimitive g h
  have hcard := card_L h hω
  have hinv := chi_pow_inv (ι := ι) h hω j k hjk
  have hk := gs_inv_psi h hω g k
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [hinv, hk, hcard] at this
  exact this

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

/-- `conj g_j = g_k` for `j + k ≡ 0 (mod 6)`. -/
lemma star_gs (j k : ℕ) (hjk : (j + k) % 6 = 0) :
    starRingEnd ℂ (gaussSum (chi ι h hω ^ j) (psi g h)) = gaussSum (chi ι h hω ^ k) (psi g h) := by
  have hinv := chi_pow_inv (ι := ι) h hω j k hjk
  have hk := gs_inv_psi h hω g k
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have := star_gaussSum_eq (chi ι h hω ^ j) (psi g h)
  rw [hinv, hk] at this
  exact this

lemma jac_mul {j k : ℕ} (h6 : ¬ 6 ∣ (j + k)) :
    gaussSum (chi ι h hω ^ (j + k)) (psi g h) * jacobiSum (chi ι h hω ^ j) (chi ι h hω ^ k) =
      gaussSum (chi ι h hω ^ j) (psi g h) * gaussSum (chi ι h hω ^ k) (psi g h) := by
  have hne := chi_pow_ne_one (ι := ι) h hω h6
  rw [pow_add] at hne ⊢
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  exact jacobiSum_mul_nontrivial hne _

/-- **Davenport–Hasse** for `m = 2`: `χ(4) g₁ g₃ = g₂²`. -/
theorem dh : chi ι h hω 4 * gaussSum (chi ι h hω) (psi g h) *
    gaussSum (chi ι h hω ^ (3 : ℕ)) (psi g h) = gaussSum (chi ι h hω ^ (2 : ℕ)) (psi g h) ^ 2 := by
  have E1 : gaussSum (chi ι h hω ^ (2 : ℕ)) (psi g h) * jacobiSum (chi ι h hω) (chi ι h hω) =
      gaussSum (chi ι h hω) (psi g h) * gaussSum (chi ι h hω) (psi g h) := by
    have := jac_mul h hω g (j := 1) (k := 1) (by norm_num)
    rw [pow_one] at this
    exact this
  have E2 : gaussSum (chi ι h hω ^ (4 : ℕ)) (psi g h) *
      jacobiSum (chi ι h hω ^ (3 : ℕ)) (chi ι h hω) =
      gaussSum (chi ι h hω ^ (3 : ℕ)) (psi g h) * gaussSum (chi ι h hω) (psi g h) := by
    have := jac_mul h hω g (j := 3) (k := 1) (by norm_num)
    rw [pow_one] at this
    exact this
  have E3 := jacobi_dh (ι := ι) h hω
  have E4 := gs_mul_gs h hω g (j := 2) (k := 4) (by norm_num) (by norm_num)
  have E5 := gs_three_sq h hω g
  have hg1 : gaussSum (chi ι h hω) (psi g h) ≠ 0 := by
    have := gs_ne_zero h hω g (j := 1) (by norm_num)
    rwa [pow_one] at this
  have hQ : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (absNorm_pos v).ne'
  set c := chi ι h hω 4
  set g1 := gaussSum (chi ι h hω) (psi g h)
  set g2 := gaussSum (chi ι h hω ^ (2 : ℕ)) (psi g h)
  set g3 := gaussSum (chi ι h hω ^ (3 : ℕ)) (psi g h)
  set g4 := gaussSum (chi ι h hω ^ (4 : ℕ)) (psi g h)
  set J1 := jacobiSum (chi ι h hω) (chi ι h hω)
  set J3 := jacobiSum (chi ι h hω ^ (3 : ℕ)) (chi ι h hω)
  have X : c * g1 * g4 = g2 * g3 := by
    apply mul_left_cancel₀ hg1
    linear_combination (-(c * g4)) * E1 + g2 * E2 + (g4 * g2) * E3
  apply mul_left_cancel₀ hQ
  linear_combination (g3 * g2) * X - (c * g1 * g3) * E4 + g2 ^ 2 * E5

end field

end C3I

end ArtinPrimitiveRoots
end

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

/-- `G(P) = conj(χ(4)) γ₃(P)`. -/
lemma gaussG_eq (g : AllowedGen ι 𝔪) :
    gaussG g v.asIdeal = starRingEnd ℂ (chi ι h hω 4) * gaussPhase g 3 v.asIdeal := by
  have h4 : sexticResidueSymbol ι 𝔪 v.asIdeal 4 = chi ι h hω 4 := by
    rw [← chi_mk h hω, map_ofNat]
  simp only [gaussG, normalizedFactors_v, Multiset.map_singleton, Multiset.prod_singleton, h4]

/-- `ρ_P(x) = χ²(θ x)`. -/
lemma cubicResidueChar_eq (x : 𝓞 F ⧸ v.asIdeal) :
    cubicResidueChar ι v.asIdeal x = (chi ι h hω ^ (2 : ℕ)) (quotHom 𝔪 v.asIdeal x) := by
  classical
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hθ := quotHom_bijective_one (𝔪 := 𝔪) h.notS
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, MulChar.map_zero]
    simp [cubicResidueChar]
  have hθx : quotHom 𝔪 v.asIdeal x ≠ 0 := by
    rw [Ne, ← map_zero (quotHom 𝔪 v.asIdeal)]
    exact fun h' => hx (hθ.1 h')
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hθx
  rw [MulChar.pow_apply' _ (by norm_num), chi_eq_pow h hω hθx hi, ← pow_mul]
  -- the cube root
  have he : (Ideal.absNorm v.asIdeal - 1) / 3 = 2 * ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    have := six_mul_e h; omega
  have hxe : x ^ ((Ideal.absNorm v.asIdeal - 1) / 3) =
      Ideal.Quotient.mk v.asIdeal (ω ^ 2) ^ i := by
    have hθω : quotHom 𝔪 v.asIdeal (Ideal.Quotient.mk v.asIdeal ω) = omegaL ω := quotHom_mk _ _
    apply hθ.1
    simp only [map_pow, hθω]
    rw [he, pow_mul', hi, ← pow_mul, ← pow_mul, mul_comm]
  have hω3 : IsPrimitiveRoot (ω ^ 2) 3 := hω.pow (by norm_num) (by norm_num)
  have hωP3 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal (ω ^ 2)) 3 := by
    rw [map_pow]; exact (omegaP_prim h hω).pow (by norm_num) (by norm_num)
  have hex : ∃ ζ : 𝓞 F, ζ ^ 3 = 1 ∧
      Ideal.Quotient.mk v.asIdeal ζ = x ^ ((Ideal.absNorm v.asIdeal - 1) / 3) :=
    ⟨(ω ^ 2) ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω3.pow_eq_one, one_pow], by
      rw [map_pow, hxe]⟩
  simp only [cubicResidueChar, if_neg hx, dif_pos hex]
  obtain ⟨k1, k2⟩ := hex.choose_spec
  have := iota_eq_pow_of_map ι (Ideal.Quotient.mk v.asIdeal) (by norm_num) hω3 hωP3 k1
    (k2.trans hxe)
  rw [this, show ((ω ^ 2 : 𝓞 F) : F) = (ω : F) ^ 2 from map_pow (algebraMap (𝓞 F) F) ω 2,
    map_pow, ← pow_mul, mul_comm]

/-- `J(ρ_P, ρ_P) = J(χ², χ²)`. -/
lemma cubicJacobiSum_eq :
    cubicJacobiSum ι v.asIdeal = jacobiSum (chi ι h hω ^ (2 : ℕ)) (chi ι h hω ^ (2 : ℕ)) := by
  have hθ := quotHom_bijective_one (𝔪 := 𝔪) h.notS
  rw [cubicJacobiSum, jacobiSum, ← finsum_eq_sum_of_fintype,
    ← finsum_comp_equiv (Equiv.ofBijective _ hθ)]
  refine finsum_congr fun x => ?_
  rw [cubicResidueChar_eq h hω, cubicResidueChar_eq h hω, Equiv.ofBijective_apply, map_sub,
    map_one]

/-- `Λ(P) = −(N P)^{-1/2} J(χ², χ²)`. -/
lemma gaussLambda_eq :
    gaussLambda ι v.asIdeal = -(((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)⁻¹ *
      jacobiSum (chi ι h hω ^ (2 : ℕ)) (chi ι h hω ^ (2 : ℕ))) := by
  simp only [gaussLambda, normalizedFactors_v, Multiset.map_singleton, Multiset.prod_singleton,
    cubicJacobiSum_eq h hω]

/-- `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1`. -/
theorem hd_good (g : AllowedGen ι 𝔪) :
    gaussPhase g 1 v.asIdeal * gaussPhase g 2 v.asIdeal *
      starRingEnd ℂ (gaussLambda ι v.asIdeal) * starRingEnd ℂ (gaussG g v.asIdeal) = -1 := by
  rw [gaussG_eq h hω g, gaussLambda_eq h hω, gaussPhase_eq h hω g (j := 1) (by norm_num),
    gaussPhase_eq h hω g (j := 2) (by norm_num), gaussPhase_eq h hω g (j := 3) (by norm_num),
    pow_one]
  have DH := dh h hω g
  have E4 := gs_mul_gs h hω g (j := 2) (k := 4) (by norm_num) (by norm_num)
  have C3 := star_gs h hω g 3 3 (by norm_num)
  -- `conj J(χ², χ²) = J(χ⁴, χ⁴)` and `g₂ · conj J = g₄²`
  have hstar : starRingEnd ℂ (jacobiSum (chi ι h hω ^ (2 : ℕ)) (chi ι h hω ^ (2 : ℕ))) =
      jacobiSum (chi ι h hω ^ (4 : ℕ)) (chi ι h hω ^ (4 : ℕ)) := by
    have hinv := chi_pow_inv (ι := ι) h hω 2 4 (by norm_num)
    haveI := finite_L h
    have hst : star (chi ι h hω ^ (2 : ℕ)) = chi ι h hω ^ (4 : ℕ) := by
      haveI : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))ˣ := inferInstance
      rw [MulChar.star_eq_inv, hinv]
    rw [← hst]
    exact (jacobiSum_ringHomComp _ _ (starRingEnd ℂ)).symm
  have J44 : gaussSum (chi ι h hω ^ (2 : ℕ)) (psi g h) *
      jacobiSum (chi ι h hω ^ (4 : ℕ)) (chi ι h hω ^ (4 : ℕ)) =
      gaussSum (chi ι h hω ^ (4 : ℕ)) (psi g h) * gaussSum (chi ι h hω ^ (4 : ℕ)) (psi g h) := by
    have := jac_mul h hω g (j := 4) (k := 4) (by norm_num)
    rw [chi_pow_mod h hω (4 + 4)] at this
    exact this
  have hs := sqrt_sq_C (v := v)
  have hQ : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact (absNorm_pos v).ne'
  have hs0 : ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) ≠ 0 := by
    intro h0; rw [h0] at hs; exact hQ (by rw [← hs]; ring)
  have hsr : starRingEnd ℂ (((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)⁻¹) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  simp only [map_mul, map_neg, hsr, Complex.conj_conj, C3, hstar]
  set s := ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ)
  set c := chi ι h hω 4
  set g1 := gaussSum (chi ι h hω) (psi g h)
  set g2 := gaussSum (chi ι h hω ^ (2 : ℕ)) (psi g h)
  set g3 := gaussSum (chi ι h hω ^ (3 : ℕ)) (psi g h)
  set g4 := gaussSum (chi ι h hω ^ (4 : ℕ)) (psi g h)
  set J := jacobiSum (chi ι h hω ^ (4 : ℕ)) (chi ι h hω ^ (4 : ℕ))
  have ht : s⁻¹ ^ 2 * (Ideal.absNorm v.asIdeal : ℂ) = 1 := by
    rw [← hs, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs0)]
  linear_combination (-(s⁻¹ ^ 4) * c * g1 * g3) * J44 - (s⁻¹ ^ 4 * g4 ^ 2) * DH -
    (s⁻¹ ^ 4 * (g2 * g4 + (Ideal.absNorm v.asIdeal : ℂ))) * E4 -
    (s⁻¹ ^ 2 * (Ideal.absNorm v.asIdeal : ℂ) + 1) * ht

end field

end C3I

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

section
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open ArtinPrimitiveRoots
open NumberField
theorem solution
    (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
        gaussPhase g 1 P * gaussPhase g 2 P * starRingEnd ℂ (gaussLambda ι P) *
          starRingEnd ℂ (gaussG g P) = -1 := by
  refine ⟨C3I.cutN F, fun 𝔪 _ hsm g P hP hext => ?_⟩
  have h := C3I.good_of_exterior n hn0 hn le_rfl hsm hP hext
  obtain ⟨ω, hω⟩ := C3I.exists_prim_six (F := F) n hn0 hn
  haveI := C3I.finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)))
  exact C3I.hd_good h hω g
end
