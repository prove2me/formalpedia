-- Prove2me | Definitions.Def_RPLib_S1_FinDim
-- name    : RPLib_S1_FinDim
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:14:03.004614+00:00
-- url     : https://prove2.me/theorems/ece90b6f-4fd0-413a-8e22-3ec8ab9ee63f
-- title:
--   A Sturm-type bound and finite dimensionality of spaces of modular forms
-- statement:
--   Let $\Gamma$ be an arithmetic subgroup of $\mathrm{SL}_2(\mathbb{R})$ with cusp width $h$ at $\infty$ and $f$ a modular form of weight $k$ on $\Gamma$. If the $q$-expansion coefficients $a_n(f)$ vanish for all $n \le B$, where $B + 1 > h \lfloor k [\mathrm{SL}_2(\mathbb{Z}) : \Gamma]/12 \rfloor$, then $f = 0$. Consequently the spaces $M_k(\Gamma)$ and $S_k(\Gamma)$ are finite-dimensional over $\mathbb{C}$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Sturm, On the congruence of modular forms, Lecture Notes in Math. 1240, Springer 1987, 275-280, doi:10.1007/BFb0072985; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 3.5

import Mathlib

/-!
# S1-FINDIM: Sturm-type bound and finite dimensionality for arithmetic levels
(Ramanujan-Petersson project, unit S1-FINDIM)

Main results (namespace `RamanujanPetersson.FinDim`):
* `isBigO_exp_of_coeff_eq_zero`: if the first `m` coefficients of `qExpansion h f` vanish then
  `f = O(exp(-2π m im τ / h))` at `i∞`.
* `qExpansion_coeff_eq_zero_of_isBigO`: conversely, `f = O(exp(-2π m im τ / h))` forces the
  coefficients of index `n < m` to vanish.
* `norm_isBigO`: the norm `ModularForm.norm 𝒮ℒ f` inherits the decay of `f` (the other factors
  are bounded at `i∞`).
* `eq_zero_of_coeff_eq_zero` (Sturm bound, any arithmetic `𝒢`, any positive strict period `h`):
  if `(qExpansion h f).coeff n = 0` for `n ≤ B` with `((k * [𝒮ℒ : 𝒢]).toNat / 12) * h < B + 1`
  then `f = 0`.
* `relIndex_coe_SL`: for `Γ ≤ SL(2, ℤ)`, `(Γ : Subgroup GL(2, ℝ)).relIndex 𝒮ℒ = Γ.index`;
  `eq_zero_of_coeff_eq_zero_SL`, `_Gamma0`, `_Gamma1` (width 1, `B = (k * index).toNat / 12`),
  `_Gamma` (width `N`).
* `finiteDimensional_modularForm`, `finiteDimensional_cuspForm`: `FiniteDimensional ℂ` for every
  arithmetic `𝒢` (theorems, to be used with `haveI`), plus the coefficient maps `coeffMap`,
  `coeffMapCusp` and their injectivity.
-/

open UpperHalfPlane ModularForm Filter Asymptotics Function
open scoped Real MatrixGroups Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.FinDim

/-! ## Step 1: vanishing coefficients give exponential decay -/

section decay

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}

theorem cuspFunction_isBigO_pow [ModularFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (m : ℕ) (hf : ∀ n < m, (qExpansion h f).coeff n = 0) :
    cuspFunction h f =O[𝓝 0] fun q : ℂ ↦ q ^ m := by
  have hA := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hord : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA]
    intro i hi
    have := hf i hi
    rw [qExpansion_coeff] at this
    simpa [Nat.factorial_ne_zero] using this
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt hA).mp hord
  have hg1 : g =O[𝓝 0] (fun _ : ℂ ↦ (1 : ℂ)) := hg.continuousAt.tendsto.isBigO_one ℂ
  have h2 : (fun q : ℂ ↦ q ^ m * g q) =O[𝓝 0] fun q : ℂ ↦ q ^ m * 1 :=
    (isBigO_refl (fun q : ℂ ↦ q ^ m) _).mul hg1
  simp only [mul_one] at h2
  refine h2.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hfg] with q hq
  rw [hq, sub_zero, smul_eq_mul]

theorem isBigO_exp_of_coeff_eq_zero [ModularFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (m : ℕ) (hf : ∀ n < m, (qExpansion h f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ Real.exp (-2 * π * m * τ.im / h) := by
  have h1 : (fun τ : ℍ ↦ cuspFunction h f (Periodic.qParam h τ)) =O[atImInfty]
      fun τ : ℍ ↦ (Periodic.qParam h τ) ^ m :=
    (cuspFunction_isBigO_pow f hh hΓ m hf).comp_tendsto (qParam_tendsto_atImInfty hh)
  have h2 : (fun τ : ℍ ↦ cuspFunction h f (Periodic.qParam h τ)) = (f : ℍ → ℂ) := by
    funext τ
    exact SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne'
  rw [h2] at h1
  refine h1.trans (isBigO_of_le _ fun τ ↦ le_of_eq ?_)
  rw [norm_pow, Periodic.norm_qParam, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  congr 1
  simp only [UpperHalfPlane.coe_im]
  ring

end decay

/-! ## Step 2: exponential decay forces vanishing coefficients -/

section coeff

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}

theorem qExpansion_coeff_eq_zero_of_isBigO [ModularFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {m : ℝ}
    (hdecay : (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ Real.exp (-2 * π * m * τ.im / h))
    (n : ℕ) (hn : (n : ℝ) < m) : (qExpansion h f).coeff n = 0 := by
  obtain ⟨C, hC⟩ := hdecay.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  set c : ℝ := 2 * π * (m - n) / h with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    have : 0 < m - n := by linarith
    positivity
  -- pointwise bound on the horizontal line `im τ = t`
  have hpt : ∀ t : ℝ, A ≤ t → ∀ τ : ℍ, τ.im = t →
      ‖f τ‖ ≤ C * Real.exp (-2 * π * m * t / h) := by
    intro t htA τ hτ
    have := hA τ (hτ ▸ htA)
    simp only [Set.mem_ofPred_eq] at this
    rwa [Real.norm_of_nonneg (Real.exp_pos _).le, hτ] at this
  -- bound for every large `t`
  have key : ∀ t : ℝ, max A 1 ≤ t → ‖(qExpansion h f).coeff n‖ ≤ C * Real.exp (-(c * t)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right A 1).trans ht)
    have htA : A ≤ t := (le_max_left A 1).trans ht
    have hq : ∀ z : ℂ, z.im = t →
        ‖1 / Periodic.qParam h z ^ n‖ = Real.exp (2 * π * n * t / h) := by
      intro z hz
      rw [norm_div, norm_one, norm_pow, Periodic.norm_qParam, hz, ← Real.exp_nat_mul, one_div,
        ← Real.exp_neg]
      congr 1
      ring
    rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral f hh hΓ n ht0, norm_mul]
    refine (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C * Real.exp (-(c * t))) fun u _ ↦ ?_) (norm_nonneg _)).trans (le_of_eq ?_)
    · rw [norm_mul, hq _ (by simp)]
      refine (mul_le_mul_of_nonneg_left (hpt t htA _ (by simp [← UpperHalfPlane.coe_im]))
        (Real.exp_pos _).le).trans (le_of_eq ?_)
      rw [mul_left_comm, ← Real.exp_add, hc_def]
      congr 2
      ring
    · rw [sub_zero, abs_of_pos hh, norm_div, norm_one, Complex.norm_real,
        Real.norm_of_nonneg hh.le]
      field_simp
  have hlim : Tendsto (fun t : ℝ ↦ C * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hc)).const_mul C
    simpa [Function.comp_def] using this
  have hle : ‖(qExpansion h f).coeff n‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨max A 1, key⟩)
  exact norm_le_zero_iff.mp hle

end coeff

/-! ## Step 3: the norm to `𝒮ℒ` inherits the decay -/

section norm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

theorem quotientFunc_isBoundedAtImInfty [ModularFormClass F 𝒢 k] (f : F)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    IsBoundedAtImInfty (SlashInvariantForm.quotientFunc (k := k) f q) := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨γ, hγ⟩ := r.2
  have hr : (r : GL (Fin 2) ℝ)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ := by
    rw [map_inv, hγ]
  have : SlashInvariantForm.quotientFunc (k := k) f (r : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) =
      (f : ℍ → ℂ) ∣[k] γ⁻¹ := by
    show (f : ℍ → ℂ) ∣[k] (r : GL (Fin 2) ℝ)⁻¹ = _
    rw [hr]
    rfl
  rw [this]
  exact ModularFormClass.bdd_at_infty_slash f γ⁻¹

omit [𝒢.IsArithmetic] in
theorem quotientFunc_one [ModularFormClass F 𝒢 k] (f : F) :
    SlashInvariantForm.quotientFunc (k := k) f ((1 : 𝒮ℒ) : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) =
      (f : ℍ → ℂ) := by
  show (f : ℍ → ℂ) ∣[k] ((1 : 𝒮ℒ) : GL (Fin 2) ℝ)⁻¹ = _
  simp

theorem norm_isBigO [ModularFormClass F 𝒢 k] (f : F) {g : ℍ → ℝ}
    (hf : (f : ℍ → ℂ) =O[atImInfty] g) :
    (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] g := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)
  set q₁ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ := ((1 : 𝒮ℒ) : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) with hq₁
  have hcoe : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) = fun τ ↦
      SlashInvariantForm.quotientFunc (k := k) f q₁ τ *
        ∏ q ∈ Finset.univ.erase q₁, SlashInvariantForm.quotientFunc (k := k) f q τ := by
    funext τ
    rw [Finset.mul_prod_erase _ (fun q ↦ SlashInvariantForm.quotientFunc (k := k) f q τ)
      (Finset.mem_univ q₁)]
    simp [ModularForm.coe_norm, Finset.prod_apply]
  rw [hcoe, quotientFunc_one]
  have hrest : (fun τ ↦ ∏ q ∈ Finset.univ.erase q₁,
      SlashInvariantForm.quotientFunc (k := k) f q τ) =O[atImInfty]
      (fun τ ↦ ∏ q ∈ Finset.univ.erase q₁, (fun _ : ℍ ↦ (1 : ℝ)) τ) :=
    IsBigO.finsetProd fun q _ ↦ quotientFunc_isBoundedAtImInfty f q
  simp only [Finset.prod_const_one] at hrest
  simpa using hf.mul hrest

end norm

/-! ## Step 4: the Sturm-type bound -/

section sturm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- **Sturm-type bound** for an arithmetic subgroup `𝒢` and any positive strict period `h`:
a modular form whose first `B + 1` coefficients vanish is zero, as soon as
`((k * [𝒮ℒ : 𝒢 ∩ 𝒮ℒ]).toNat / 12) * h < B + 1`. -/
theorem eq_zero_of_coeff_eq_zero [ModularFormClass F 𝒢 k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ 𝒢.strictPeriods) (B : ℕ)
    (hB : (((k * (𝒢.relIndex 𝒮ℒ : ℤ)).toNat / 12 : ℕ) : ℝ) * h < B + 1)
    (hf : ∀ n ≤ B, (qExpansion h f).coeff n = 0) : (f : ℍ → ℂ) = 0 := by
  set K : ℕ := (k * (𝒢.relIndex 𝒮ℒ : ℤ)).toNat / 12 with hK
  have hdec := isBigO_exp_of_coeff_eq_zero f hh hΓ (B + 1) fun n hn ↦ hf n (by omega)
  have hdec' : (f : ℍ → ℂ) =O[atImInfty]
      fun τ ↦ Real.exp (-2 * π * (((B + 1 : ℕ) : ℝ) / h) * τ.im / 1) := by
    refine hdec.trans (isBigO_of_le _ fun τ ↦ le_of_eq ?_)
    congr 2
    ring
  have hN := norm_isBigO f hdec'
  have hcoef : ∀ n < K + 1, (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).coeff n = 0 := by
    intro n hn
    refine qExpansion_coeff_eq_zero_of_isBigO (ModularForm.norm 𝒮ℒ f) one_pos
      one_mem_strictPeriods_SL hN n ?_
    have hnK : (n : ℝ) ≤ K := by exact_mod_cast (Nat.lt_succ_iff.mp hn)
    rw [lt_div_iff₀ hh]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hnK hh.le]
  have hord : ((K : ℕ) : ℕ∞) < (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order :=
    lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self K)
      (PowerSeries.nat_le_order _ (K + 1) hcoef)
  have hzero : ModularForm.norm 𝒮ℒ f = 0 := ModularForm.sturm_bound_levelOne hord
  exact (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hzero

end sturm

/-! ## Step 5: subgroups of `SL(2, ℤ)` -/

section SL

theorem relIndex_coe_SL (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index := by
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ) :=
    Matrix.SpecialLinearGroup.mapGL_injective
  show (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
    (Matrix.SpecialLinearGroup.mapGL ℝ).range = Γ.index
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
    Subgroup.relIndex_top_right]

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- Sturm-type bound for a finite-index `Γ ≤ SL(2, ℤ)`, any positive strict period `h`. -/
theorem eq_zero_of_coeff_eq_zero_SL (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) (B : ℕ)
    (hB : (((k * (Γ.index : ℤ)).toNat / 12 : ℕ) : ℝ) * h < B + 1)
    (hf : ∀ n ≤ B, (qExpansion h f).coeff n = 0) : (f : ℍ → ℂ) = 0 := by
  refine eq_zero_of_coeff_eq_zero f hh hΓ B ?_ hf
  rwa [relIndex_coe_SL]

/-- Sturm-type bound at width one: if `1` is a strict period of `Γ`, the coefficients up to
`(k * [SL₂(ℤ) : Γ]).toNat / 12` determine the form. -/
theorem eq_zero_of_coeff_eq_zero_of_one_mem (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : ∀ n ≤ (k * (Γ.index : ℤ)).toNat / 12, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) = 0 := by
  refine eq_zero_of_coeff_eq_zero_SL Γ f one_pos h1 _ ?_ hf
  rw [mul_one]
  exact lt_add_one _

theorem eq_zero_of_coeff_eq_zero_Gamma1 (M : ℕ) [NeZero M]
    [ModularFormClass F ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : ∀ n ≤ (k * ((CongruenceSubgroup.Gamma1 M).index : ℤ)).toNat / 12,
      (qExpansion 1 f).coeff n = 0) : (f : ℍ → ℂ) = 0 := by
  refine eq_zero_of_coeff_eq_zero_of_one_mem _ ?_ f hf
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem eq_zero_of_coeff_eq_zero_Gamma0 (M : ℕ) [NeZero M]
    [ModularFormClass F ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : ∀ n ≤ (k * ((CongruenceSubgroup.Gamma0 M).index : ℤ)).toNat / 12,
      (qExpansion 1 f).coeff n = 0) : (f : ℍ → ℂ) = 0 := by
  refine eq_zero_of_coeff_eq_zero_of_one_mem _ ?_ f hf
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-- Sturm-type bound for `Γ(N)` (width `N`). -/
theorem eq_zero_of_coeff_eq_zero_Gamma (N : ℕ) [NeZero N]
    [ModularFormClass F ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hf : ∀ n ≤ N * ((k * ((CongruenceSubgroup.Gamma N).index : ℤ)).toNat / 12),
      (qExpansion N f).coeff n = 0) : (f : ℍ → ℂ) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine eq_zero_of_coeff_eq_zero_SL _ f hN ?_ _ ?_ hf
  · rw [CongruenceSubgroup.strictPeriods_Gamma]
    exact AddSubgroup.mem_zmultiples _
  · push_cast
    linarith

end SL

/-! ## Step 6: finite dimensionality -/

section findim

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] {k : ℤ} {h : ℝ}

/-- The first `B + 1` coefficients of the `q`-expansion, as a linear map on modular forms. -/
def coeffMap (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) (k : ℤ) (B : ℕ) :
    ModularForm 𝒢 k →ₗ[ℂ] (Fin (B + 1) → ℂ) where
  toFun f i := (qExpansion h f).coeff i
  map_add' f g := by
    funext i
    show (qExpansion h ⇑(f + g)).coeff i = (qExpansion h f).coeff i + (qExpansion h g).coeff i
    rw [FunLike.coe_add, ModularForm.qExpansion_add hh hΓ f g, map_add]
  map_smul' a f := by
    funext i
    show (qExpansion h ⇑(a • f)).coeff i = a • (qExpansion h f).coeff i
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul hh hΓ a f, PowerSeries.coeff_smul]

/-- The first `B + 1` coefficients of the `q`-expansion, as a linear map on cusp forms. -/
def coeffMapCusp (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) (k : ℤ) (B : ℕ) :
    CuspForm 𝒢 k →ₗ[ℂ] (Fin (B + 1) → ℂ) where
  toFun f i := (qExpansion h f).coeff i
  map_add' f g := by
    funext i
    show (qExpansion h ⇑(f + g)).coeff i = (qExpansion h f).coeff i + (qExpansion h g).coeff i
    rw [FunLike.coe_add, ModularForm.qExpansion_add hh hΓ f g, map_add]
  map_smul' a f := by
    funext i
    show (qExpansion h ⇑(a • f)).coeff i = a • (qExpansion h f).coeff i
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul hh hΓ a f, PowerSeries.coeff_smul]

theorem coeffMap_apply (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) (B : ℕ) (f : ModularForm 𝒢 k)
    (i : Fin (B + 1)) : coeffMap hh hΓ k B f i = (qExpansion h f).coeff i := rfl

theorem coeffMapCusp_apply (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) (B : ℕ) (f : CuspForm 𝒢 k)
    (i : Fin (B + 1)) : coeffMapCusp hh hΓ k B f i = (qExpansion h f).coeff i := rfl

variable [𝒢.IsArithmetic]

theorem coeffMap_injective (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) (B : ℕ)
    (hB : (((k * (𝒢.relIndex 𝒮ℒ : ℤ)).toNat / 12 : ℕ) : ℝ) * h < B + 1) :
    Function.Injective (coeffMap hh hΓ k B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h0 := eq_zero_of_coeff_eq_zero f hh hΓ B hB fun n hn ↦ by
    have := congr_fun hf ⟨n, by omega⟩
    simpa [coeffMap_apply] using this
  ext τ
  simpa using congr_fun h0 τ

theorem coeffMapCusp_injective (hh : 0 < h) (hΓ : h ∈ 𝒢.strictPeriods) (B : ℕ)
    (hB : (((k * (𝒢.relIndex 𝒮ℒ : ℤ)).toNat / 12 : ℕ) : ℝ) * h < B + 1) :
    Function.Injective (coeffMapCusp hh hΓ k B) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h0 := eq_zero_of_coeff_eq_zero f hh hΓ B hB fun n hn ↦ by
    have := congr_fun hf ⟨n, by omega⟩
    simpa [coeffMapCusp_apply] using this
  ext τ
  simpa using congr_fun h0 τ

omit [𝒢.HasDetOne] in
/-- A Sturm bound exists at the strict width at `∞`. -/
theorem exists_sturm_bound (𝒢 : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    ∃ B : ℕ, (((k * (𝒢.relIndex 𝒮ℒ : ℤ)).toNat / 12 : ℕ) : ℝ) * 𝒢.strictWidthInfty < B + 1 :=
  ⟨⌈(((k * (𝒢.relIndex 𝒮ℒ : ℤ)).toNat / 12 : ℕ) : ℝ) * 𝒢.strictWidthInfty⌉₊,
    (Nat.le_ceil _).trans_lt (lt_add_one _)⟩

/-- `M_k(𝒢)` is finite dimensional for every arithmetic `𝒢` with determinant one
(use with `haveI`). -/
theorem finiteDimensional_modularForm (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒢 k) := by
  have hh : 0 < 𝒢.strictWidthInfty := 𝒢.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := 𝒢.strictWidthInfty_mem_strictPeriods
  obtain ⟨B, hB⟩ := exists_sturm_bound 𝒢 k
  exact Module.Finite.of_injective _ (coeffMap_injective hh hΓ B hB)

/-- `S_k(𝒢)` is finite dimensional for every arithmetic `𝒢` with determinant one
(use with `haveI`). -/
theorem finiteDimensional_cuspForm (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by
  have hh : 0 < 𝒢.strictWidthInfty := 𝒢.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := 𝒢.strictWidthInfty_mem_strictPeriods
  obtain ⟨B, hB⟩ := exists_sturm_bound 𝒢 k
  exact Module.Finite.of_injective _ (coeffMapCusp_injective hh hΓ B hB)

/-- Finite dimensionality for a finite-index `Γ ≤ SL(2, ℤ)` (covers `Γ(N)`, `Γ₀(M)`, `Γ₁(M)`). -/
theorem finiteDimensional_modularForm_SL (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) :
    FiniteDimensional ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :=
  finiteDimensional_modularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k

theorem finiteDimensional_cuspForm_SL (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :=
  finiteDimensional_cuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k

theorem finiteDimensional_cuspForm_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ
      (CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :=
  finiteDimensional_cuspForm_SL _ k

theorem finiteDimensional_modularForm_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ
      (ModularForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k) :=
  finiteDimensional_modularForm_SL _ k

end findim

end RamanujanPetersson.FinDim


