-- Prove2me | Definitions.Def_RPLib_S1_QExp
-- name    : RPLib_S1_QExp
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:14:06.395206+00:00
-- url     : https://prove2.me/theorems/d368374d-0cdd-4c7a-b215-1ce02ee72056
-- title:
--   Width-one $q$-expansions of cusp forms and their behaviour under simple matrices
-- statement:
--   For a cusp form $f$ on a group containing $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ write $f(\tau) = \sum_{n} a_n(f)\, e^{2\pi i n\tau}$. The file shows that $f$ is determined by its coefficients, identifies the coefficients of any convergent expansion with those of $f$, and computes $$a_n(f(d\,\cdot)) = [d \mid n]\, a_{n/d}(f), \qquad a_n\Big(\tfrac1p\sum_{j<p} f\big(\tfrac{\tau+j}{p}\big)\Big) = a_{pn}(f),$$ together with the effect of translations $\tau \mapsto \tau + r$. These are the coefficient rules behind Hecke operators and level-raising maps.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Sections 1.2 and 5.3

import Mathlib

/-!
# S1-QEXP: q-expansion toolkit at width 1 (Ramanujan-Petersson project, unit S1-QEXP)

Main results (namespace `RamanujanPetersson.QExp`):
* (a) `one_mem_strictPeriods_of_T_mem`, `one_mem_strictPeriods_Gamma1`, `one_mem_strictPeriods_Gamma0`,
  `one_mem_strictPeriods_of_le`, `one_mem_strictPeriods_of_Gamma1_le`.
* (b) `HasQExpansion f c` (`f τ = Σ c n e(nτ)` with `HasSum` at every `τ`);
  `qExpansion_coeff_of_hasSum` (any width `h`, bare functions, no modularity needed),
  `HasQExpansion.qExpansion_coeff`, `hasQExpansion_of_modularFormClass`.
* (c) `qExpansionLinearMap` (`CuspForm Γ k →ₗ[ℂ] PowerSeries ℂ`), `qExpansionLinearMap_injective`,
  `cuspForm_eq_zero_of_coeff`, `cuspForm_ext_of_coeff` (all coefficients zero / equal ⇒ equal forms).
* (d) the upper-triangular matrices `upperTri a b d = [[a, b], [0, d]]` with the slash formula
  `upperTri_slash`; coefficient formulas
  `HasQExpansion.comp_mul` / `qExpansion_coeff_slash_diag` (`f(dτ)`, i.e. `d^(1-k) • f ∣[k] diag(d,1)`):
    coeff n = if d ∣ n then a(n/d) else 0;
  `HasQExpansion.U` / `qExpansion_coeff_sum_slash_U` (`(1/p) Σ_{j<p} f((τ+j)/p)`, i.e.
    `Σ_{j<p} f ∣[k] [[1, j], [0, p]]`): coeff n = a(p n);
  `HasQExpansion.translate` / `qExpansion_coeff_slash_translate` / `qExpansion_coeff_slash_translate_div`
    (`f(τ + r)`, i.e. `f ∣[k] [[1, r], [0, 1]]`): coeff n = e(n r) a(n), and e(n j / p) a(n) for r = j/p.
-/

open ModularForm Complex Filter Function
open UpperHalfPlane hiding I
open scoped Real MatrixGroups Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.QExp

/-! ## (a) `1` is a strict period -/

section strictPeriods

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_Gamma1 (M : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_Gamma0 (M : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

theorem one_mem_strictPeriods_of_le {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ ≤ Γ')
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : (1 : ℝ) ∈ Γ'.strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact hle h1

theorem one_mem_strictPeriods_of_Gamma1_le {M : ℕ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ) :
    (1 : ℝ) ∈ Γ.strictPeriods :=
  one_mem_strictPeriods_of_le hle (one_mem_strictPeriods_Gamma1 M)

end strictPeriods

/-! ## (b) uniqueness of q-expansion coefficients -/

section uniqueness

theorem qParam_one_pow (z : ℂ) (n : ℕ) :
    Periodic.qParam 1 z ^ n = cexp (2 * π * I * n * z) := by
  rw [Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `f τ = Σ c n · exp(2πi n τ)`, with the series converging (unconditionally) at every `τ ∈ ℍ`. -/
def HasQExpansion (f : ℍ → ℂ) (c : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ c n * cexp (2 * π * I * n * (τ : ℂ))) (f τ)

theorem hasQExpansion_iff_qParam {f : ℍ → ℂ} {c : ℕ → ℂ} :
    HasQExpansion f c ↔ ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (f τ) := by
  simp only [HasQExpansion, smul_eq_mul, qParam_one_pow]

theorem hasSum_cuspFunction_of_hasSum_punctured' {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam h τ ^ m) (f τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := (Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1)
  have : cuspFunction h f q = f τ := by
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1] using! h2
  grind [hf τ, Periodic.qParam_right_inv]

theorem hasFPowerSeriesOnBall_update' {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • Periodic.qParam h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [smul_eq_mul, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hasSum_cuspFunction_of_hasSum_punctured' hh hf (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured' hh hf hy hy'

/-- A convergent expansion pins down the value of the cusp function at `0`. -/
theorem cuspFunction_zero_eq_of_hasSum {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam h τ ^ m) (f τ)) :
    cuspFunction h f 0 = c 0 := by
  have H1 := hasFPowerSeriesOnBall_update' hh hf
  have ht : Tendsto (update (cuspFunction h f) 0 (c 0)) (𝓝[≠] 0) (𝓝 (c 0)) := by
    have := H1.hasFPowerSeriesAt.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa [update_self] using this
  have ht2 : Tendsto (cuspFunction h f) (𝓝[≠] 0) (𝓝 (c 0)) := by
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact update_of_ne hq _ _
  rw [UpperHalfPlane.cuspFunction, Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
  exact ht2.limUnder_eq

theorem hasFPowerSeriesOnBall_cuspFunction_of_hasSum {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    {c : ℕ → ℂ} (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (.ofScalars ℂ c) 0 1 := by
  have H1 := hasFPowerSeriesOnBall_update' hh hf
  rwa [← cuspFunction_zero_eq_of_hasSum hh hf, update_eq_self] at H1

theorem analyticAt_cuspFunction_of_hasSum {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam h τ ^ m) (f τ)) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  (hasFPowerSeriesOnBall_cuspFunction_of_hasSum hh hf).analyticAt

/-- **Uniqueness** (any width `h`, any function): if `f τ = Σ c m Periodic.qParam_h(τ)^m` at every `τ`, then
the `q`-expansion coefficients of `f` are the `c m`. -/
theorem qExpansion_coeff_of_hasSum {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam h τ ^ m) (f τ)) (m : ℕ) :
    (qExpansion h f).coeff m = c m := by
  have hA := analyticAt_cuspFunction_of_hasSum hh hf
  have h1 := (hasFPowerSeriesOnBall_cuspFunction_of_hasSum hh hf).hasFPowerSeriesAt
  have h2 := hA.hasFPowerSeriesAt
  have h3 := congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at h3
  rw [qExpansion_coeff, h3, div_eq_mul_inv, mul_comm]

/-- **Uniqueness at width 1**: if `f τ = Σ c n exp(2πi n τ)` at every `τ`, then
`(qExpansion 1 f).coeff n = c n`. -/
theorem HasQExpansion.qExpansion_coeff {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : HasQExpansion f c)
    (n : ℕ) : (qExpansion 1 f).coeff n = c n :=
  qExpansion_coeff_of_hasSum one_pos (hasQExpansion_iff_qParam.mp hf) n

theorem HasQExpansion.qExpansion_eq {f : ℍ → ℂ} {c : ℕ → ℂ} (hf : HasQExpansion f c) :
    qExpansion 1 f = PowerSeries.mk c := by
  ext n
  rw [hf.qExpansion_coeff n, PowerSeries.coeff_mk]

/-- A modular form (or cusp form) with strict period `1` has its own width-1 expansion. -/
theorem hasQExpansion_of_modularFormClass {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) :
    HasQExpansion f (fun n ↦ (qExpansion 1 f).coeff n) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos h1⟩
  intro τ
  have := ModularForm.hasSum_qExpansion f one_pos h1 τ
  simpa only [qParam_one_pow] using this

end uniqueness

/-! ## (c) the q-expansion as a linear map; injectivity -/

section linear

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}

/-- `f ↦ qExpansion h f` as a `ℂ`-linear map on cusp forms. -/
def qExpansionLinearMap [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    CuspForm Γ k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion h f
  map_add' f g := by
    have e : (⇑(f + g) : ℍ → ℂ) = ⇑f + ⇑g := by ext τ; simp
    rw [e]
    exact ModularForm.qExpansion_add hh hΓ f g
  map_smul' c f := by
    have e : (⇑(c • f) : ℍ → ℂ) = c • ⇑f := by ext τ; simp
    rw [e, RingHom.id_apply]
    exact ModularForm.qExpansion_smul hh hΓ c f

@[simp] theorem qExpansionLinearMap_apply [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : CuspForm Γ k) : qExpansionLinearMap hh hΓ k f = qExpansion h f := rfl

/-- `f ↦ qExpansion h f` as a `ℂ`-linear map on modular forms. -/
def qExpansionLinearMapMF [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ModularForm Γ k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion h f
  map_add' f g := by
    have e : (⇑(f + g) : ℍ → ℂ) = ⇑f + ⇑g := by ext τ; simp
    rw [e]
    exact ModularForm.qExpansion_add hh hΓ f g
  map_smul' c f := by
    have e : (⇑(c • f) : ℍ → ℂ) = c • ⇑f := by ext τ; simp
    rw [e, RingHom.id_apply]
    exact ModularForm.qExpansion_smul hh hΓ c f

theorem cuspForm_eq_zero_of_qExpansion_eq_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : CuspForm Γ k) (hf : qExpansion h f = 0) : f = 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have h0 : (⇑f : ℍ → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f)).mp hf
  ext τ
  simpa using congr_fun h0 τ

/-- All `q`-expansion coefficients zero ⇒ the cusp form is zero. -/
theorem cuspForm_eq_zero_of_coeff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : CuspForm Γ k)
    (hf : ∀ n, (qExpansion h f).coeff n = 0) : f = 0 :=
  cuspForm_eq_zero_of_qExpansion_eq_zero hh hΓ f (PowerSeries.ext fun n ↦ by simpa using hf n)

/-- Two cusp forms with the same `q`-expansion coefficients are equal. -/
theorem cuspForm_ext_of_coeff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f g : CuspForm Γ k)
    (hfg : ∀ n, (qExpansion h f).coeff n = (qExpansion h g).coeff n) : f = g := by
  have h0 := cuspForm_eq_zero_of_coeff hh hΓ (f - g) (fun n ↦ by
    have e : (⇑(f - g) : ℍ → ℂ) = ⇑f - ⇑g := by ext τ; simp
    rw [e, ModularForm.qExpansion_sub hh hΓ f g, map_sub, hfg n, sub_self])
  exact sub_eq_zero.mp h0

theorem qExpansionLinearMap_injective [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Function.Injective (qExpansionLinearMap hh hΓ k) := by
  intro f g hfg
  simp only [qExpansionLinearMap_apply] at hfg
  exact cuspForm_ext_of_coeff hh hΓ f g (fun n ↦ by rw [hfg])

end linear

/-! ## (d) upper-triangular matrices and coefficient formulas -/

section upperTri

/-- The matrix `[[a, b], [0, d]]` as an element of `GL(2, ℝ)`. -/
def upperTri (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by simpa [Matrix.det_fin_two_of] using had)

theorem upperTri_val (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTri a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] := rfl

theorem upperTri_det (a b d : ℝ) (had : a * d ≠ 0) : (upperTri a b d had).det.val = a * d := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperTri_val, Matrix.det_fin_two_of]
  ring

theorem upperTri_smul (a b d : ℝ) (had : a * d ≠ 0) (hpos : 0 < a * d) (τ : ℍ) :
    ((upperTri a b d had • τ : ℍ) : ℂ) = (a * τ + b) / d := by
  rw [coe_smul_of_det_pos (by rw [upperTri_det]; exact hpos)]
  simp [num, denom, upperTri_val]

/-- The weight-`k` slash by `[[a, b], [0, d]]` with `a d > 0`:
`(F ∣[k] g) τ = (a d)^(k-1) d^(-k) F((a τ + b)/d)`. -/
theorem upperTri_slash (a b d : ℝ) (had : a * d ≠ 0) (hpos : 0 < a * d) (k : ℤ) (F : ℍ → ℂ)
    (τ : ℍ) :
    (F ∣[k] upperTri a b d had) τ =
      ((a * d : ℝ) : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) * F (upperTri a b d had • τ) := by
  rw [slash_apply]
  have hden : denom (upperTri a b d had) τ = d := by simp [denom, upperTri_val]
  have hdet : 0 < (upperTri a b d had).det.val := by rw [upperTri_det]; exact hpos
  rw [hden, σ, if_pos hdet, ContinuousAlgEquiv.refl_apply, upperTri_det, abs_of_pos hpos]
  push_cast
  ring

end upperTri

section coeffFormulas

/-- `f(dτ)`: coefficient `n` is `a(n/d)` if `d ∣ n`, else `0`. -/
theorem HasQExpansion.comp_mul {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQExpansion f a) (d : ℕ)
    (hd : 0 < d) (φ : ℍ → ℍ) (hφ : ∀ τ, (φ τ : ℂ) = d * τ) :
    HasQExpansion (fun τ ↦ f (φ τ)) (fun n ↦ if d ∣ n then a (n / d) else 0) := by
  intro τ
  dsimp only
  have H := hf (φ τ)
  rw [hφ τ] at H
  have hinj : Function.Injective (fun m : ℕ ↦ d * m) :=
    fun x y hxy ↦ Nat.eq_of_mul_eq_mul_left hd hxy
  have hzero : ∀ n ∉ Set.range (fun m : ℕ ↦ d * m),
      (fun n : ℕ ↦ (if d ∣ n then a (n / d) else 0) * cexp (2 * π * I * n * (τ : ℂ))) n = 0 := by
    intro n hn
    have : ¬ d ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [this]
  refine (hinj.hasSum_iff hzero).mp ?_
  convert H using 1
  funext m
  rw [Function.comp_apply, if_pos (dvd_mul_right d m), Nat.mul_div_cancel_left m hd]
  congr 1
  congr 1
  push_cast
  ring

/-- `(1/p) Σ_{j<p} f((τ + j)/p)`: coefficient `n` is `a(p n)`. -/
theorem HasQExpansion.U {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQExpansion f a) (p : ℕ) (hp : 0 < p)
    (φ : ℕ → ℍ → ℍ) (hφ : ∀ j τ, (φ j τ : ℂ) = (τ + j) / p) :
    HasQExpansion (fun τ ↦ (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (φ j τ)) (fun n ↦ a (p * n)) := by
  intro τ
  dsimp only
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hprim : IsPrimitiveRoot (cexp (2 * π * I / p)) p := Complex.isPrimitiveRoot_exp p hp.ne'
  have H : HasSum (fun m : ℕ ↦ (p : ℂ)⁻¹ *
      ∑ j ∈ Finset.range p, a m * cexp (2 * π * I * m * ((τ + j) / p)))
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (φ j τ)) := by
    apply HasSum.mul_left
    apply hasSum_sum
    intro j _
    have := hf (φ j τ)
    rwa [hφ j τ] at this
  have key : ∀ m : ℕ, (p : ℂ)⁻¹ *
      ∑ j ∈ Finset.range p, a m * cexp (2 * π * I * m * ((τ + j) / p)) =
      if p ∣ m then a m * cexp (2 * π * I * ((m : ℂ) / p) * τ) else 0 := by
    intro m
    have hsplit : ∀ j : ℕ, cexp (2 * π * I * m * ((τ + j) / p)) =
        cexp (2 * π * I * ((m : ℂ) / p) * τ) * (cexp (2 * π * I / p) ^ m) ^ j := by
      intro j
      rw [← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
    simp_rw [hsplit]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    by_cases hdm : p ∣ m
    · rw [if_pos hdm]
      have h1 : cexp (2 * π * I / p) ^ m = 1 := (hprim.pow_eq_one_iff_dvd m).mpr hdm
      rw [h1]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
    · rw [if_neg hdm]
      have h1 : cexp (2 * π * I / p) ^ m ≠ 1 := fun h ↦ hdm ((hprim.pow_eq_one_iff_dvd m).mp h)
      have h2 : (cexp (2 * π * I / p) ^ m) ^ p = 1 := by
        rw [← pow_mul, mul_comm m p, pow_mul, hprim.pow_eq_one, one_pow]
      rw [geom_sum_eq h1, h2, sub_self, zero_div]
      simp
  simp_rw [key] at H
  have hinj : Function.Injective (fun n : ℕ ↦ p * n) :=
    fun x y hxy ↦ Nat.eq_of_mul_eq_mul_left hp hxy
  have hzero : ∀ m ∉ Set.range (fun n : ℕ ↦ p * n),
      (fun m : ℕ ↦ if p ∣ m then a m * cexp (2 * π * I * ((m : ℂ) / p) * τ) else 0) m = 0 := by
    intro m hm
    have : ¬ p ∣ m := by
      rintro ⟨n, rfl⟩
      exact hm ⟨n, rfl⟩
    simp [this]
  have H2 := (hinj.hasSum_iff hzero).mpr H
  convert H2 using 1
  funext n
  rw [Function.comp_apply, if_pos (dvd_mul_right p n)]
  congr 1
  congr 1
  push_cast
  field_simp

/-- `f(τ + r)`: coefficient `n` is `e(n r) a(n)`. -/
theorem HasQExpansion.translate {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQExpansion f a) (r : ℝ)
    (φ : ℍ → ℍ) (hφ : ∀ τ, (φ τ : ℂ) = τ + r) :
    HasQExpansion (fun τ ↦ f (φ τ)) (fun n ↦ cexp (2 * π * I * n * r) * a n) := by
  intro τ
  dsimp only
  have H := hf (φ τ)
  rw [hφ τ] at H
  convert H using 1
  funext n
  rw [mul_add, Complex.exp_add]
  ring

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- `d^(1-k) • f ∣[k] diag(d, 1)` is `τ ↦ f(dτ)`. -/
theorem slash_diag_eq (d : ℕ) (hd : 0 < d) (had : (d : ℝ) * 1 ≠ 0) (G : ℍ → ℂ) :
    ((d : ℂ) ^ (1 - k)) • (G ∣[k] upperTri d 0 1 had) =
      fun τ ↦ G (upperTri d 0 1 had • τ) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  funext τ
  rw [Pi.smul_apply, upperTri_slash _ _ _ had (by simpa using hdR), smul_eq_mul]
  have e : (d : ℂ) ^ (1 - k) * (d : ℂ) ^ (k - 1) = 1 := by
    rw [← zpow_add₀ hd0]
    simp
  push_cast
  simp only [mul_one, one_zpow]
  rw [← mul_assoc, e, one_mul]

theorem upperTri_diag_smul (d : ℕ) (hd : 0 < d) (had : (d : ℝ) * 1 ≠ 0) (τ : ℍ) :
    ((upperTri d 0 1 had • τ : ℍ) : ℂ) = d * τ := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [upperTri_smul _ _ _ had (by simpa using hdR)]
  simp

/-- **`V_d`**: coefficients of `f(dτ) = d^(1-k) • (f ∣[k] diag(d, 1))`. -/
theorem qExpansion_coeff_slash_diag [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (d : ℕ) (hd : 0 < d) (had : (d : ℝ) * 1 ≠ 0) (n : ℕ) :
    (qExpansion 1 (((d : ℂ) ^ (1 - k)) • ((f : ℍ → ℂ) ∣[k] upperTri d 0 1 had))).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  rw [slash_diag_eq d hd had]
  exact ((hasQExpansion_of_modularFormClass f h1).comp_mul d hd _
    (upperTri_diag_smul d hd had)).qExpansion_coeff n

/-- `Σ_{j<p} f ∣[k] [[1, j], [0, p]]` is `τ ↦ (1/p) Σ_{j<p} f((τ + j)/p)`. -/
theorem sum_slash_U_eq (p : ℕ) (hp : 0 < p) (had : (1 : ℝ) * p ≠ 0) (G : ℍ → ℂ) :
    (∑ j ∈ Finset.range p, G ∣[k] upperTri 1 j p had) =
      fun τ ↦ (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, G (upperTri 1 j p had • τ) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  funext τ
  rw [Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [upperTri_slash _ _ _ had (by simpa using hpR)]
  have e : (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-k) = (p : ℂ)⁻¹ := by
    rw [← zpow_add₀ hp0, show k - 1 + -k = -1 by ring, zpow_neg_one]
  push_cast
  rw [one_mul, e]

theorem upperTri_U_smul (p : ℕ) (hp : 0 < p) (had : (1 : ℝ) * p ≠ 0) (j : ℕ) (τ : ℍ) :
    ((upperTri 1 j p had • τ : ℍ) : ℂ) = (τ + j) / p := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  rw [upperTri_smul _ _ _ had (by simpa using hpR)]
  simp

/-- **`U_p`**: coefficients of `Σ_{j<p} f ∣[k] [[1, j], [0, p]] = (1/p) Σ_{j<p} f((τ+j)/p)`. -/
theorem qExpansion_coeff_sum_slash_U [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (p : ℕ) (hp : 0 < p) (had : (1 : ℝ) * p ≠ 0) (n : ℕ) :
    (qExpansion 1 (∑ j ∈ Finset.range p, (f : ℍ → ℂ) ∣[k] upperTri 1 j p had)).coeff n =
      (qExpansion 1 f).coeff (p * n) := by
  rw [sum_slash_U_eq p hp had]
  exact ((hasQExpansion_of_modularFormClass f h1).U p hp (fun j τ ↦ upperTri 1 j p had • τ)
    (fun j τ ↦ upperTri_U_smul p hp had j τ)).qExpansion_coeff n

/-- Function form of `U_p` for an arbitrary choice of points `φ j τ = (τ + j)/p`. -/
theorem qExpansion_coeff_U_fun [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (p : ℕ) (hp : 0 < p) (φ : ℕ → ℍ → ℍ)
    (hφ : ∀ j τ, (φ j τ : ℂ) = (τ + j) / p) (n : ℕ) :
    (qExpansion 1 (fun τ ↦ (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (φ j τ))).coeff n =
      (qExpansion 1 f).coeff (p * n) :=
  ((hasQExpansion_of_modularFormClass f h1).U p hp φ hφ).qExpansion_coeff n

/-- Function form of `V_d` for an arbitrary choice of points `φ τ = d τ`. -/
theorem qExpansion_coeff_V_fun [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (d : ℕ) (hd : 0 < d) (φ : ℍ → ℍ)
    (hφ : ∀ τ, (φ τ : ℂ) = d * τ) (n : ℕ) :
    (qExpansion 1 (fun τ ↦ f (φ τ))).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 :=
  ((hasQExpansion_of_modularFormClass f h1).comp_mul d hd φ hφ).qExpansion_coeff n

/-- `f ∣[k] [[1, r], [0, 1]]` is `τ ↦ f(τ + r)`. -/
theorem slash_translate_eq (r : ℝ) (had : (1 : ℝ) * 1 ≠ 0) (G : ℍ → ℂ) :
    G ∣[k] upperTri 1 r 1 had = fun τ ↦ G (upperTri 1 r 1 had • τ) := by
  funext τ
  rw [upperTri_slash _ _ _ had (by norm_num)]
  simp

theorem upperTri_translate_smul (r : ℝ) (had : (1 : ℝ) * 1 ≠ 0) (τ : ℍ) :
    ((upperTri 1 r 1 had • τ : ℍ) : ℂ) = τ + r := by
  rw [upperTri_smul _ _ _ had (by norm_num)]
  simp

/-- **Translation**: coefficients of `f(τ + r) = (f ∣[k] [[1, r], [0, 1]]) τ`. -/
theorem qExpansion_coeff_slash_translate [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (r : ℝ) (had : (1 : ℝ) * 1 ≠ 0) (n : ℕ) :
    (qExpansion 1 ((f : ℍ → ℂ) ∣[k] upperTri 1 r 1 had)).coeff n =
      cexp (2 * π * I * n * r) * (qExpansion 1 f).coeff n := by
  rw [slash_translate_eq r had]
  exact ((hasQExpansion_of_modularFormClass f h1).translate r _
    (upperTri_translate_smul r had)).qExpansion_coeff n

/-- **Translation by `j/p`**: coefficient `n` of `f(τ + j/p)` is `e(n j / p) a(n)`. -/
theorem qExpansion_coeff_slash_translate_div [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) (j p : ℕ) (had : (1 : ℝ) * 1 ≠ 0) (n : ℕ) :
    (qExpansion 1 ((f : ℍ → ℂ) ∣[k] upperTri 1 ((j : ℝ) / p) 1 had)).coeff n =
      cexp (2 * π * I * (n * j / p)) * (qExpansion 1 f).coeff n := by
  rw [qExpansion_coeff_slash_translate f h1 _ had n]
  congr 2
  push_cast
  ring

end coeffFormulas

/-! ## Specialisation to `Γ₁(M)` -/

section Gamma1

variable (M : ℕ) (k : ℤ)

/-- The width-1 `q`-expansion on `S_k(Γ₁(M))` as a `ℂ`-linear map. -/
def qExpansionGamma1 :
    CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k
      →ₗ[ℂ] PowerSeries ℂ :=
  qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1 M) k

theorem qExpansionGamma1_apply
    (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansionGamma1 M k f = qExpansion 1 f := rfl

theorem qExpansionGamma1_injective : Function.Injective (qExpansionGamma1 M k) :=
  qExpansionLinearMap_injective one_pos (one_mem_strictPeriods_Gamma1 M)

theorem cuspForm_Gamma1_eq_zero_of_coeff
    (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n, (qExpansion 1 f).coeff n = 0) : f = 0 :=
  cuspForm_eq_zero_of_coeff one_pos (one_mem_strictPeriods_Gamma1 M) f hf

theorem hasQExpansion_cuspForm_Gamma1
    (f : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    HasQExpansion f (fun n ↦ (qExpansion 1 f).coeff n) :=
  hasQExpansion_of_modularFormClass f (one_mem_strictPeriods_Gamma1 M)

end Gamma1

end RamanujanPetersson.QExp

end


