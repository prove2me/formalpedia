-- Prove2me | solution 1 for AutomorphicForm.HeckeEigensystem.hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d768052a-e2d5-598f-9782-7056c8884a14

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial Deep.NTSupply AutomorphicForm Filter Topology Finset
open scoped Classical

noncomputable section

namespace RS9

section CommRing
variable {R : Type*} [CommRing R]

theorem satakePow_add_mul (x y : R) : ∀ n : ℕ, satakePow n (x + y) (x * y) = x ^ n + y ^ n
  | 0 => by simp; norm_num
  | 1 => by simp
  | n + 2 => by
    rw [satakePow_add_two, satakePow_add_mul x y (n + 1), satakePow_add_mul x y n]
    ring

theorem rsEulerPoly_zero_eq_prod (x₁ x₂ y₁ y₂ : R) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly (x₁ + x₂) (x₁ * x₂) (y₁ + y₂) (y₁ * y₂) 0 =
      (C 1 - C (x₁ * y₁) * X) * (C 1 - C (x₁ * y₂) * X) *
        ((C 1 - C (x₂ * y₁) * X) * (C 1 - C (x₂ * y₂) * X)) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat, map_one, map_zero]
  ring

theorem eval_rsEulerPoly_scale (c a b e₁ e₂ e₃ x : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (c * a) (c ^ 2 * b) e₁ e₂ e₃).eval x =
      (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).eval (c * x) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

theorem prod_range_mul_of_periodic (u : ℕ → R) (f : ℕ) (hu : ∀ i, u (i + f) = u i) :
    ∀ g : ℕ, ∏ i ∈ range (g * f), u i = (∏ i ∈ range f, u i) ^ g
  | 0 => by simp
  | g + 1 => by
    have hper : ∀ i, u (g * f + i) = u i := by
      intro i
      induction g with
      | zero => simp
      | succ g ih => rw [show (g + 1) * f + i = (g * f + i) + f by ring, hu, ih]
    rw [show (g + 1) * f = g * f + f by ring, prod_range_add, prod_range_mul_of_periodic u f hu g,
      pow_succ]
    congr 1
    exact prod_congr rfl fun i _ => hper i

end CommRing

theorem exists_roots (a b : ℂ) : ∃ α β : ℂ, α + β = a ∧ α * β = b := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (a ^ 2 - 4 * b)
  exact ⟨(a + r) / 2, (a - r) / 2, by ring, by linear_combination (1 / 4 : ℂ) * hr⟩

theorem prod_range_pow_eq_prod_nthRootsFinset {ζ : ℂ} {f : ℕ} (hf : 0 < f) (hζ : IsPrimitiveRoot ζ f)
    (h : ℂ → ℂ) : ∏ j ∈ range f, h (ζ ^ j) = ∏ μ ∈ nthRootsFinset f (1 : ℂ), h μ := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (range f : Set ℕ) := by
    intro i hi j hj hij
    exact hζ.pow_inj (by simpa using hi) (by simpa using hj) hij
  have himg : (range f).image (fun j : ℕ => ζ ^ j) = nthRootsFinset f (1 : ℂ) := by
    apply eq_of_subset_of_card_le
    · intro μ hμ
      obtain ⟨j, -, rfl⟩ := mem_image.mp hμ
      rw [mem_nthRootsFinset hf, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, card_image_of_injOn hinj, card_range]
  rw [← himg, prod_image hinj]

theorem eval_rsEulerPoly_satakePow_pow_eq_prod_range
    (a b a' b' ω T : ℂ) (hb : b ≠ 0) (f g : ℕ) (hf : 0 < f) (hω : IsPrimitiveRoot ω f) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (satakePow f a b / b ^ f) (b ^ f)⁻¹
        (satakePow f a' b') (b' ^ f) 0).eval (T ^ f) ^ g =
      ∏ i ∈ range (g * f),
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (ω ^ i * a / ((ω ^ i) ^ 2 * b)) (((ω ^ i) ^ 2 * b)⁻¹)
          a' b' 0).eval T := by

  obtain ⟨α, β, hsum, hprod⟩ := exists_roots a b
  obtain ⟨α', β', hsum', hprod'⟩ := exists_roots a' b'
  have hα0 : α ≠ 0 := by rintro rfl; apply hb; rw [← hprod]; ring
  have hβ0 : β ≠ 0 := by rintro h0; apply hb; rw [← hprod, h0]; ring

  set ω' := ω⁻¹ with hω'
  have hω'prim : IsPrimitiveRoot ω' f := hω.inv
  have hωunit : ω ≠ 0 := hω.ne_zero hf.ne'

  set Q := LanglandsTunnell.RankinSelberg.rsEulerPoly (a / b) b⁻¹ a' b' 0 with hQ

  have step1 : ∀ i, (LanglandsTunnell.RankinSelberg.rsEulerPoly (ω ^ i * a / ((ω ^ i) ^ 2 * b))
      (((ω ^ i) ^ 2 * b)⁻¹) a' b' 0).eval T = Q.eval (ω' ^ i * T) := by
    intro i
    have e1 : ω ^ i * a / ((ω ^ i) ^ 2 * b) = ω' ^ i * (a / b) := by
      rw [hω', inv_pow]; field_simp
    have e2 : ((ω ^ i) ^ 2 * b)⁻¹ = (ω' ^ i) ^ 2 * b⁻¹ := by
      rw [hω', inv_pow, mul_inv, inv_pow]
    rw [e1, e2, hQ, eval_rsEulerPoly_scale]

  have hQroots : Q = (C 1 - C (α⁻¹ * α') * X) * (C 1 - C (α⁻¹ * β') * X) *
      ((C 1 - C (β⁻¹ * α') * X) * (C 1 - C (β⁻¹ * β') * X)) := by
    rw [hQ, ← rsEulerPoly_zero_eq_prod]
    congr 1
    · rw [← hsum, ← hprod]; field_simp; ring
    · rw [← hprod, mul_inv]
    · rw [hsum']
    · rw [hprod']

  have step3 : ∏ j ∈ range f, Q.eval (ω' ^ j * T) =
      (1 - (α⁻¹ * α' * T) ^ f) * (1 - (α⁻¹ * β' * T) ^ f) *
        ((1 - (β⁻¹ * α' * T) ^ f) * (1 - (β⁻¹ * β' * T) ^ f)) := by
    have key : ∀ c : ℂ, ∏ j ∈ range f, (1 - c * (ω' ^ j * T)) = 1 - (c * T) ^ f := by
      intro c
      rw [prod_range_pow_eq_prod_nthRootsFinset hf hω'prim (fun μ => 1 - c * (μ * T))]
      have := hω'prim.pow_sub_pow_eq_prod_sub_mul (1 : ℂ) (c * T) hf
      rw [one_pow] at this
      rw [this]
      exact prod_congr rfl fun μ _ => by ring
    simp only [hQroots, eval_mul, eval_sub, eval_C, eval_X, prod_mul_distrib, key]

  have step4 : ∏ i ∈ range (g * f), Q.eval (ω' ^ i * T) = (∏ j ∈ range f, Q.eval (ω' ^ j * T)) ^ g :=
    prod_range_mul_of_periodic (fun i => Q.eval (ω' ^ i * T)) f
      (fun i => by simp only [pow_add, hω'prim.pow_eq_one, mul_one]) g

  have hL : LanglandsTunnell.RankinSelberg.rsEulerPoly (satakePow f a b / b ^ f) (b ^ f)⁻¹
      (satakePow f a' b') (b' ^ f) 0 =
      (C 1 - C ((α⁻¹) ^ f * α' ^ f) * X) * (C 1 - C ((α⁻¹) ^ f * β' ^ f) * X) *
        ((C 1 - C ((β⁻¹) ^ f * α' ^ f) * X) * (C 1 - C ((β⁻¹) ^ f * β' ^ f) * X)) := by
    rw [← rsEulerPoly_zero_eq_prod]
    congr 1
    · rw [← hsum, ← hprod, satakePow_add_mul, mul_pow, inv_pow, inv_pow]; field_simp; ring
    · rw [← hprod, mul_pow, mul_inv, inv_pow, inv_pow]
    · rw [← hsum', ← hprod', satakePow_add_mul]
    · rw [← hprod', mul_pow]

  rw [prod_congr rfl fun i _ => step1 i, step4, step3, hL]
  simp only [eval_mul, eval_sub, eval_C, eval_X]
  ring

end RS9

namespace RS9R4

def rsFactor {K : Type} [Field K] [NumberField K] (σ τ : HeckeEigensystem K ℂ)
    (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v / σ.b v) (σ.b v)⁻¹ (τ.a v) (τ.b v) 0).eval
    (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

def chiPow {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (i : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ i) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0

theorem exists_forall_eval_cpow_neg_ne_zero (P : ℂ[X]) (hP : P.coeff 0 = 1) (N : ℕ) (hN : 2 ≤ N) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → P.eval (((N : ℕ) : ℂ) ^ (-s)) ≠ 0 := by

  have h0 : P.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero]; exact hP
  have hcont : ContinuousAt (fun x : ℂ => P.eval x) 0 := P.continuous.continuousAt
  obtain ⟨δ, hδ, hδP⟩ := (Metric.continuousAt_iff.mp hcont) (1 / 2) (by norm_num)
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNr
  refine ⟨Real.logb N (1 / δ), fun s hs => ?_⟩
  have hsmall : ‖((N : ℕ) : ℂ) ^ (-s)‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos (lt_of_lt_of_le (by norm_num) hN), Complex.neg_re]
    calc (N : ℝ) ^ (-s.re) < (N : ℝ) ^ (-Real.logb N (1 / δ)) :=
          Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)
      _ = δ := by
          rw [Real.rpow_neg hNpos.le, Real.rpow_logb hNpos hNr.ne' (by positivity), one_div, inv_inv]
  intro hzero
  have := hδP (x := ((N : ℕ) : ℂ) ^ (-s)) (by simpa [dist_zero_right] using hsmall)
  rw [hzero, h0, dist_eq_norm] at this
  norm_num at this

theorem rsEulerPoly_coeff_zero {R : Type*} [CommRing R] (a b e₁ e₂ e₃ : R) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly a b e₁ e₂ e₃).coeff 0 = 1 := by
  simp [LanglandsTunnell.RankinSelberg.rsEulerPoly, coeff_one, coeff_X, coeff_C, coeff_X_pow]

theorem hasProd_units_iff {ι : Type*} (g : ι → ℂˣ) (c : ℂˣ) :
    HasProd g c ↔ HasProd (fun i => (g i : ℂ)) (c : ℂ) := by
  unfold HasProd
  rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.coe_prod]

theorem hasProd_subtype_of_hasProd_subtype_of_subset {β : Type*} (f : β → ℂ) (S T : Finset β) (hST : S ⊆ T)
    (a : ℂ) (ha : a ≠ 0) (hf : ∀ b, f b ≠ 0)
    (h : HasProd (fun x : {x // x ∉ S} => f x) a) :
    HasProd (fun x : {x // x ∉ T} => f x) (a / ∏ b ∈ T \ S, f b) := by
  set u : β → ℂˣ := fun b => Units.mk0 (f b) (hf b) with hu
  have huval : ∀ b, (u b : ℂ) = f b := fun b => rfl
  set A : ℂˣ := Units.mk0 a ha with hA

  have hS : HasProd (fun x : {x // x ∉ S} => u x) A := by
    rw [hasProd_units_iff]; (simp only [huval] at h ⊢; exact h)
  rw [Finset.hasProd_compl_iff] at hS

  set B : ℂˣ := A * (∏ i ∈ S, u i) * (∏ i ∈ T, u i)⁻¹ with hB
  have hT : HasProd (fun x : {x // x ∉ T} => u x) B := by
    rw [Finset.hasProd_compl_iff]
    convert hS using 1
    rw [hB]; group
  have hTval := (hasProd_units_iff _ _).mp hT
  simp only [huval] at hTval
  convert hTval using 1

  rw [hB, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_prod, Units.coe_prod]
  simp only [huval, hA, Units.val_mk0]
  rw [← Finset.prod_sdiff hST]
  have hne : (∏ x ∈ S, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hf b
  have hne' : (∏ x ∈ T \ S, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hf b
  field_simp

theorem cpow_natCast_pow_neg (N f : ℕ) (hN : 0 < N) (s : ℂ) :
    (((N ^ f : ℕ) : ℂ)) ^ (-s) = ((((N : ℕ) : ℂ)) ^ (-s)) ^ f := by
  rw [Nat.cast_pow, ← Complex.cpow_natCast, ← Complex.cpow_nat_mul]
  have hreal : (Complex.log (N : ℂ) * (f : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg N),
      ← Complex.ofReal_mul, Complex.ofReal_im]
  rw [← Complex.cpow_mul]
  · rw [hreal]; exact neg_lt_zero.mpr Real.pi_pos
  · rw [hreal]; exact Real.pi_pos.le

theorem prod_fibre_rsFactor_eq
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔣 : Ideal (𝓞 F)) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (π π' : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (W : Finset (HeightOneSpectrum (𝓞 E))) (hW : ∀ w ∈ W, w.under (𝓞 F) = v)
    (hbc : ∀ w ∈ W, IsBaseChangeAt π Ψ w) (hbc' : ∀ w ∈ W, IsBaseChangeAt π' Ψ w)
    (f : ℕ) (hf : 0 < f) (hfW : ∀ w ∈ W, v.asIdeal.inertiaDeg' w.asIdeal = f)
    (hord : IsPrimitiveRoot ((η (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) f)
    (m : ℕ) (hcard : W.card * f = m) (hb : π.b v ≠ 0)
    (hN : ∀ w ∈ W, Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f) (s : ℂ) :
    ∏ w ∈ W, rsFactor Ψ Ψ w s = ∏ i ∈ Finset.range m, rsFactor (π.twist (chiPow 𝔣 η i)) π' v s := by
  set T : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) with hT
  set ω : ℂ := ((η (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) with hω

  set PE := LanglandsTunnell.RankinSelberg.rsEulerPoly (satakePow f (π.a v) (π.b v) / π.b v ^ f) (π.b v ^ f)⁻¹
      (satakePow f (π'.a v) (π'.b v)) (π'.b v ^ f) 0 with hPE
  have hEw : ∀ w ∈ W, rsFactor Ψ Ψ w s = ((PE.eval (T ^ f)))⁻¹ := by
    intro w hw
    obtain ⟨ha, hbb⟩ := hbc w hw
    obtain ⟨ha', hbb'⟩ := hbc' w hw
    have hu : w.under (𝓞 F) = v := hW w hw
    rw [hu] at ha hbb ha' hbb'
    rw [hfW w hw] at ha hbb ha' hbb'
    have hNv : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    have hpoly : LanglandsTunnell.RankinSelberg.rsEulerPoly (Ψ.a w / Ψ.b w) (Ψ.b w)⁻¹ (Ψ.a w) (Ψ.b w) 0 = PE := by
      conv_lhs => enter [3]; rw [ha']
      conv_lhs => enter [4]; rw [hbb']
      rw [ha, hbb]
    simp only [rsFactor, hN w hw, cpow_natCast_pow_neg _ _ hNv, ← hT, hpoly]
  rw [Finset.prod_congr rfl hEw, Finset.prod_const]

  have hFi : ∀ i ∈ Finset.range m, rsFactor (π.twist (chiPow 𝔣 η i)) π' v s =
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (ω ^ i * π.a v / ((ω ^ i) ^ 2 * π.b v))
        (((ω ^ i) ^ 2 * π.b v)⁻¹) (π'.a v) (π'.b v) 0).eval T)⁻¹ := by
    intro i _
    simp only [rsFactor, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b, chiPow, dif_pos hv, MonoidHom.pow_apply,
      Units.val_pow_eq_pow_val, ← hω, ← hT]
  rw [Finset.prod_congr rfl hFi, Finset.prod_inv_distrib, ← hcard,
    ← RS9.eval_rsEulerPoly_satakePow_pow_eq_prod_range (π.a v) (π.b v) (π'.a v) (π'.b v) ω T hb f W.card hf hord,
    inv_pow]

theorem exists_finset_forall_ramificationIdx_eq_one
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ R : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ R, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  classical
  let _ : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := FractionRing.liftAlgebra _ _
  have hfin : {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 E)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine ⟨hfin.toFinset.image (fun w => w.under (𝓞 F)), fun v hv w hwv => ?_⟩
  have hw : ¬ w.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 E) := fun hd =>
    hv (Finset.mem_image.mpr ⟨w, hfin.mem_toFinset.mpr hd, hwv⟩)
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := not_dvd_differentIdeal_iff.mp hw
  have h1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 F) (p := w.asIdeal)
  rw [← hwv]
  haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 F)).ne_bot]
  exact h1

theorem finite_fibre (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v}.Finite := by
  refine Set.Finite.subset (Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) ?_) ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact v.ne_bot
  · intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hw]
    exact le_of_eq rfl

theorem rsEulerPoly_zero_zero {R : Type*} [CommRing R] (e₁ e₂ : R) :
    LanglandsTunnell.RankinSelberg.rsEulerPoly 0 0 e₁ e₂ 0 = 1 := by
  simp [LanglandsTunnell.RankinSelberg.rsEulerPoly]

theorem G4_fibre_regroup
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (hη : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
      orderOf (η (primeClass F 𝔣 (w.under (𝓞 F)) hw)) =
        (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)
    (π π' : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ)
    (h : IsBaseChangeOf π Ψ) (h' : IsBaseChangeOf π' Ψ) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ SF : Finset (HeightOneSpectrum (𝓞 F)), S₂ ⊆ SF →
      ∀ SE : Finset (HeightOneSpectrum (𝓞 E)), (∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) →
        ∀ (s : ℂ) (LE : ℂ) (L : Fin (Module.finrank F E) → ℂ),
          HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ SE} => rsFactor Ψ Ψ w.1 s) LE →
          (∀ i : Fin (Module.finrank F E),
            HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} => rsFactor (π.twist (chiPow 𝔣 η i)) π' v.1 s) (L i)) →
          LE = ∏ i : Fin (Module.finrank F E), L i := by
  classical
  set m := Module.finrank F E with hm
  obtain ⟨SEh, hSEh⟩ := h
  obtain ⟨SEh', hSEh'⟩ := h'
  obtain ⟨RAM, hRAM⟩ := exists_finset_forall_ramificationIdx_eq_one F E
  haveI hfinNR : Finite (NarrowRayClassGroup F 𝔣) := Deep.NTSupply.finite F h𝔣
  refine ⟨(SEh ∪ SEh').image (fun w => w.under (𝓞 F)) ∪ (Ideal.finite_factors h𝔣).toFinset ∪ RAM, ?_⟩
  intro SF hSF SE hSE s LE L hE hF

  haveI hfib : ∀ v : HeightOneSpectrum (𝓞 F), Fintype {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v} :=
    fun v => (finite_fibre F E v).fintype

  have hgood : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ SF →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ SEh ∧ w ∉ SEh') ∧
      ¬ v.asIdeal ∣ 𝔣 ∧ v ∉ RAM := by
    intro v hv
    refine ⟨fun w hw => ⟨fun hm' => hv (hSF ?_), fun hm' => hv (hSF ?_)⟩, fun hd => hv (hSF ?_), fun hr => hv (hSF ?_)⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hm', hw⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hm', hw⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hd))
    · exact Finset.mem_union_right _ hr

  have key : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ SF →
      ∏ c : {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v}, rsFactor Ψ Ψ c.1 s =
        ∏ i : Fin m, rsFactor (π.twist (chiPow 𝔣 η i)) π' v s := by
    intro v hv
    obtain ⟨hexc, hvf, hvram⟩ := hgood v hv
    set W : Finset (HeightOneSpectrum (𝓞 E)) := (finite_fibre F E v).toFinset with hWdef
    have hWmem : ∀ w, w ∈ W ↔ w.under (𝓞 F) = v := fun w => by rw [hWdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [← Finset.prod_subtype W hWmem (fun w => rsFactor Ψ Ψ w s), Fin.prod_univ_eq_prod_range (fun i => rsFactor (π.twist (chiPow 𝔣 η i)) π' v s)]
    have hbc : ∀ w ∈ W, IsBaseChangeAt π Ψ w := fun w hw => hSEh w (hexc w ((hWmem w).mp hw)).1
    have hbc' : ∀ w ∈ W, IsBaseChangeAt π' Ψ w := fun w hw => hSEh' w (hexc w ((hWmem w).mp hw)).2
    by_cases hb : π.b v = 0
    ·
      have hE1 : ∀ w ∈ W, rsFactor Ψ Ψ w s = 1 := by
        intro w hw
        have hu : w.under (𝓞 F) = v := (hWmem w).mp hw
        obtain ⟨-, hbb⟩ := hbc w hw
        have hfpos : 0 < (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal := by
          haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
          haveI := (w.under (𝓞 F)).isMaximal
          exact Ideal.inertiaDeg'_pos _ _
        have hbb0 : Ψ.b w = 0 := by
          rw [hbb, hu, hb]
          exact zero_pow (by rw [← hu]; exact hfpos.ne')
        simp only [rsFactor, hbb0, div_zero, inv_zero, rsEulerPoly_zero_zero, eval_one, inv_one]
      have hF1 : ∀ i ∈ Finset.range m, rsFactor (π.twist (chiPow 𝔣 η i)) π' v s = 1 := by
        intro i _
        simp only [rsFactor, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b, hb, mul_zero, div_zero, inv_zero,
          rsEulerPoly_zero_zero, eval_one, inv_one]
      rw [Finset.prod_eq_one hE1, Finset.prod_eq_one hF1]
    ·
      set f : ℕ := orderOf (η (primeClass F 𝔣 v hvf)) with hfdef
      have hfin : IsOfFinOrder (η (primeClass F 𝔣 v hvf)) := MonoidHom.isOfFinOrder η (isOfFinOrder_of_finite (primeClass F 𝔣 v hvf))
      have hf : 0 < f := hfin.orderOf_pos
      have hfW : ∀ w ∈ W, v.asIdeal.inertiaDeg' w.asIdeal = f := by
        intro w hw
        have hu : w.under (𝓞 F) = v := (hWmem w).mp hw
        have := hη w (by rw [hu]; exact hvf)
        rw [hfdef]
        subst hu
        exact this.symm
      have hord : IsPrimitiveRoot ((η (primeClass F 𝔣 v hvf) : ℂˣ) : ℂ) f :=
        IsPrimitiveRoot.coe_units_iff.mpr (hfdef ▸ IsPrimitiveRoot.orderOf _)
      have hN : ∀ w ∈ W, Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
        intro w hw
        have hu : w.under (𝓞 F) = v := (hWmem w).mp hw
        haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu]; rfl⟩
        rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot, hfW w hw]
      have hcard : W.card * f = m := by
        haveI : v.asIdeal.IsMaximal := v.isMaximal
        have hsum := Ideal.sum_ramification_inertia (R := 𝓞 F) (𝓞 E) F E (p := v.asIdeal) v.ne_bot
        have himg : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = W.image (fun w => w.asIdeal) := by
          ext P
          rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot, Finset.mem_image]
          constructor
          · rintro ⟨hP1, hP2⟩
            haveI := hP1
            haveI := hP2
            have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
            refine ⟨⟨P, hP1, hPne⟩, (hWmem _).mpr ?_, rfl⟩
            ext1
            exact hP2.over.symm
          · rintro ⟨w, hw, rfl⟩
            exact ⟨w.isPrime, ⟨by rw [← (hWmem w).mp hw]; rfl⟩⟩
        have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) W :=
          fun a _ b _ hab => HeightOneSpectrum.ext hab
        rw [himg, Finset.sum_image hinj] at hsum
        rw [Finset.sum_congr rfl (fun w hw => by
          rw [hRAM v hvram w ((hWmem w).mp hw), one_mul, hfW w hw])] at hsum
        rw [Finset.sum_const, smul_eq_mul] at hsum
        rw [hm]
        exact hsum
      exact prod_fibre_rsFactor_eq F E 𝔣 η π π' Ψ v hvf W (fun w hw => (hWmem w).mp hw) hbc hbc' f hf hfW hord m hcard hb hN s

  have hFprod : HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} =>
      ∏ i : Fin m, rsFactor (π.twist (chiPow 𝔣 η i)) π' v.1 s) (∏ i : Fin m, L i) :=
    hasProd_prod (s := Finset.univ) fun i _ => hF i

  set e := Equiv.sigmaSubtypeFiberEquivSubtype (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))
    (p := fun w => w ∉ SE) (q := fun v => v ∉ SF) (fun w => not_congr (hSE w)) with he
  have hE' := (Equiv.hasProd_iff e).mpr hE
  have hEsig : HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} =>
      ∏ c : {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v.1}, rsFactor Ψ Ψ c.1 s) LE := by
    refine HasProd.sigma hE' fun v => ?_
    convert hasProd_fintype (fun c : {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v.1} => rsFactor Ψ Ψ c.1 s) using 1
    rfl

  have hfun : (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} =>
      ∏ c : {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v.1}, rsFactor Ψ Ψ c.1 s) =
      fun v => ∏ i : Fin m, rsFactor (π.twist (chiPow 𝔣 η i)) π' v.1 s :=
    funext fun v => key v.1 v.2
  rw [hfun] at hEsig
  exact HasProd.unique hEsig hFprod

end RS9R4

end

theorem solution
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (η : NarrowRayClassGroup F 𝔣 →* ℂˣ)
    (hη : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
      orderOf (η (primeClass F 𝔣 (w.under (𝓞 F)) hw)) =
        (w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)
    (π π' : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ)
    (h : IsBaseChangeOf π Ψ) (h' : IsBaseChangeOf π' Ψ) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ SF : Finset (HeightOneSpectrum (𝓞 F)), S₂ ⊆ SF →
      ∀ SE : Finset (HeightOneSpectrum (𝓞 E)), (∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) →
        ∀ (s : ℂ) (LE : ℂ) (L : Fin (Module.finrank F E) → ℂ),
          HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ SE} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Ψ.a w.1 / Ψ.b w.1) (Ψ.b w.1)⁻¹ (Ψ.a w.1) (Ψ.b w.1) 0).eval
              (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) LE →
          (∀ i : Fin (Module.finrank F E),
            HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ SF} =>
              ((LanglandsTunnell.RankinSelberg.rsEulerPoly
                  ((π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).a v.1 /
                    (π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).b v.1)
                  ((π.twist (fun v => if hv : ¬ v.asIdeal ∣ 𝔣 then (((η ^ (i : ℕ)) (primeClass F 𝔣 v hv) : ℂˣ) : ℂ) else 0)).b v.1)⁻¹
                  (π'.a v.1) (π'.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (L i)) →
          LE = ∏ i : Fin (Module.finrank F E), L i := by
  have h__af := RS9R4.G4_fibre_regroup F E 𝔣 h𝔣 η hη π π' Ψ h h'
  simp only [RS9R4.rsFactor, RS9R4.chiPow] at h__af
  exact h__af

end S_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf
end P2MW
export P2MW.S_AutomorphicForm_HeckeEigensystem_hasProd_rsEulerPoly_contragredient_fibre_eq_prod_twist_of_isBaseChangeOf (solution)
