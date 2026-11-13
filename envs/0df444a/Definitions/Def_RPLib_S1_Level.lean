-- Prove2me | Definitions.Def_RPLib_S1_Level
-- name    : RPLib_S1_Level
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:14:04.162166+00:00
-- url     : https://prove2.me/theorems/45731ca7-21ee-4731-af9d-6b37b803f51f
-- title:
--   Level-raising maps $S_k(\Gamma_1(L)) \to S_k(\Gamma_1(M))$
-- statement:
--   For $dL \mid M$ the maps $\mathrm{incl}: f \mapsto f$ and $\iota_d : f \mapsto f(d\tau)$ send $S_k(\Gamma_1(L))$ into $S_k(\Gamma_1(M))$. The file constructs them as injective linear maps, proves $a_n(\iota_d f) = [d\mid n]\,a_{n/d}(f)$, the composition rule $\iota_d\circ\iota_e = \iota_{de}$, and that a form with nebentypus $\chi$ modulo $L$ goes to a form whose nebentypus is $\chi$ lifted to modulus $M$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.6

import Mathlib

/-!
# S1-LEVEL: level-change maps between `Γ₁` levels (Ramanujan-Petersson project, unit S1-LEVEL)

Pure Mathlib (0df444a). Namespace `RamanujanPetersson.Level`. Write `G1 N` for `Γ₁(N)` viewed in
`GL(2, ℝ)` (a reducible abbreviation of Mathlib's coercion).

Main definitions
* `restrictCF`, `restrictMF` : a cusp/modular form on `Γ` viewed on a smaller group `Γ' ≤ Γ`.
* `inclCF hLM k`, `inclMF hLM k` (`L ∣ M`) : the `ℂ`-linear inclusions `S_k(Γ₁ L) → S_k(Γ₁ M)` and
  `M_k(Γ₁ L) → M_k(Γ₁ M)` (same function).
* `dg d = diag(d, 1) ∈ GL(2, ℝ)` (`[NeZero d]`), acting by `τ ↦ d τ`.
* `iotaCF d hdLM k`, `iotaMF d hdLM k` (`d * L ∣ M`) : the `ℂ`-linear maps `f ↦ f(d ·)`,
  defined as `d^(1-k) • CuspForm.translate f (dg d)` (resp. `ModularForm.translate`) restricted to
  `Γ₁(M)`, which lies in the conjugate group (`G1_le_conj`).

Main results
* `G1_le_conj` : `Γ₁(M) ≤ (dg d)⁻¹ Γ₁(L) (dg d)` when `d * L ∣ M`.
* `iotaCF_apply` : `iotaCF d hdLM k f τ = f (dg d • τ)` and `coe_dg_smul` : `↑(dg d • τ) = d * τ`.
* `coeff_inclCF`, `coeff_iotaCF` (and `MF` versions) : coefficients at width 1:
  `incl` keeps them, `ι_d` has `coeff n = if d ∣ n then a (n / d) else 0`.
* `iotaCF_comp_iotaCF` : `ι_d ∘ ι_e = ι_{d e}`; `iotaCF_one` : `ι_1 = incl`;
  `inclCF_comp_iotaCF`, `iotaCF_comp_inclCF`, `inclCF_comp_inclCF`, `inclCF_refl`;
  `iotaCF_injective`, `inclCF_injective` (and `MF` versions).
* `inclCF_nebentypus`, `iotaCF_nebentypus` (and `MF` versions) : a form with nebentypus `χ` mod `L`
  (`f ∣[k] γ = χ(γ₁₁) • f` for `γ ∈ Γ₀(L)`) is sent to a form with nebentypus
  `χ.changeLevel` mod `M`.
-/

open UpperHalfPlane ModularForm Complex
open scoped Real MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Level

open CongruenceSubgroup ConjAct
open scoped Pointwise

/-- `Γ₁(N)` as a subgroup of `GL(2, ℝ)`. -/
abbrev G1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-! ## Arithmetic of congruence conditions -/

section arith

lemma zmod_intCast_eq_one_of_dvd {m n : ℕ} (h : n ∣ m) {a : ℤ} (ha : (a : ZMod m) = 1) :
    (a : ZMod n) = 1 := by
  have := congrArg (ZMod.castHom h (ZMod n)) ha
  rwa [map_intCast, map_one] at this

lemma zmod_intCast_eq_zero_of_dvd {m n : ℕ} (h : n ∣ m) {a : ℤ} (ha : (a : ZMod m) = 0) :
    (a : ZMod n) = 0 := by
  have := congrArg (ZMod.castHom h (ZMod n)) ha
  simpa using this

lemma Gamma1_le_of_dvd {n m : ℕ} (h : n ∣ m) : Gamma1 m ≤ Gamma1 n := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  exact ⟨zmod_intCast_eq_one_of_dvd h hA.1, zmod_intCast_eq_one_of_dvd h hA.2.1,
    zmod_intCast_eq_zero_of_dvd h hA.2.2⟩

lemma Gamma0_le_of_dvd {n m : ℕ} (h : n ∣ m) : Gamma0 m ≤ Gamma0 n := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  exact zmod_intCast_eq_zero_of_dvd h hA

lemma G1_le_of_dvd {n m : ℕ} (h : n ∣ m) : G1 m ≤ G1 n := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Gamma1_le_of_dvd h hx, rfl⟩

/-- The lower-right entry of an element of `Γ₀(N)` is coprime to `N`. -/
lemma isCoprime_of_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    IsCoprime (γ 1 1) (N : ℤ) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  exact ⟨γ 0 0, -(γ 0 1 * t), by linear_combination hdet + (γ 0 1) * ht⟩

lemma dvd_of_mul_dvd' {d L M : ℕ} (h : d * L ∣ M) : L ∣ M :=
  (dvd_mul_left L d).trans h

lemma mul_mul_dvd_of_dvd {d e L M' M : ℕ} (he : e * L ∣ M') (hd : d * M' ∣ M) :
    d * e * L ∣ M := by
  rw [mul_assoc]
  exact (mul_dvd_mul_left d he).trans hd

/-- If `d * L ∣ M` and `M ∣ c`, then `c = d * c'` with `L ∣ c'`. -/
lemma exists_eq_mul_of_zmod_eq_zero {d L M : ℕ} (hdLM : d * L ∣ M) {c : ℤ}
    (hc : (c : ZMod M) = 0) : ∃ c' : ℤ, c = d * c' ∧ (c' : ZMod L) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨u, hu⟩ := hdLM
  obtain ⟨t, ht⟩ := hc
  refine ⟨L * (u * t), ?_, ?_⟩
  · rw [ht, hu]
    push_cast
    ring
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨u * t, rfl⟩

lemma one_mem_strictPeriods_G1 (N : ℕ) : (1 : ℝ) ∈ (G1 N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

end arith

/-! ## Restriction to a smaller group -/

section restrict

variable {F : Type*} [FunLike F ℍ ℂ] {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- A cusp form on `Γ` viewed as a cusp form on a smaller group `Γ' ≤ Γ`. -/
def restrictCF [CuspFormClass F Γ k] (hle : Γ' ≤ Γ) (f : F) : CuspForm Γ' k where
  toFun := ⇑f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f (hc.mono hle)

@[simp]
lemma coe_restrictCF [CuspFormClass F Γ k] (hle : Γ' ≤ Γ) (f : F) :
    ⇑(restrictCF hle f) = ⇑f := rfl

/-- A modular form on `Γ` viewed as a modular form on a smaller group `Γ' ≤ Γ`. -/
def restrictMF [ModularFormClass F Γ k] (hle : Γ' ≤ Γ) (f : F) : ModularForm Γ' k where
  toFun := ⇑f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := fun hc => ModularFormClass.bdd_at_cusps f (hc.mono hle)

@[simp]
lemma coe_restrictMF [ModularFormClass F Γ k] (hle : Γ' ≤ Γ) (f : F) :
    ⇑(restrictMF hle f) = ⇑f := rfl

end restrict

/-! ## The inclusion `S_k(Γ₁ L) → S_k(Γ₁ M)` for `L ∣ M` -/

section incl

variable {L M : ℕ}

/-- The inclusion `S_k(Γ₁(L)) → S_k(Γ₁(M))` for `L ∣ M` (same function). -/
def inclCF (hLM : L ∣ M) (k : ℤ) : CuspForm (G1 L) k →ₗ[ℂ] CuspForm (G1 M) k where
  toFun f := restrictCF (G1_le_of_dvd hLM) f
  map_add' _ _ := CuspForm.ext fun _ => rfl
  map_smul' _ _ := CuspForm.ext fun _ => rfl

/-- The inclusion `M_k(Γ₁(L)) → M_k(Γ₁(M))` for `L ∣ M` (same function). -/
def inclMF (hLM : L ∣ M) (k : ℤ) : ModularForm (G1 L) k →ₗ[ℂ] ModularForm (G1 M) k where
  toFun f := restrictMF (G1_le_of_dvd hLM) f
  map_add' _ _ := ModularForm.ext fun _ => rfl
  map_smul' _ _ := ModularForm.ext fun _ => rfl

@[simp]
lemma coe_inclCF (hLM : L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) : ⇑(inclCF hLM k f) = ⇑f := rfl

@[simp]
lemma coe_inclMF (hLM : L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) : ⇑(inclMF hLM k f) = ⇑f :=
  rfl

lemma inclCF_apply (hLM : L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (τ : ℍ) :
    inclCF hLM k f τ = f τ := rfl

lemma inclMF_apply (hLM : L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) (τ : ℍ) :
    inclMF hLM k f τ = f τ := rfl

/-- `incl` keeps the `q`-expansion (any width). -/
theorem qExpansion_inclCF (hLM : L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (h : ℝ) :
    qExpansion h (inclCF hLM k f) = qExpansion h f := rfl

theorem qExpansion_inclMF (hLM : L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) (h : ℝ) :
    qExpansion h (inclMF hLM k f) = qExpansion h f := rfl

theorem coeff_inclCF (hLM : L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (n : ℕ) :
    (qExpansion 1 (inclCF hLM k f)).coeff n = (qExpansion 1 f).coeff n := rfl

theorem coeff_inclMF (hLM : L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) (n : ℕ) :
    (qExpansion 1 (inclMF hLM k f)).coeff n = (qExpansion 1 f).coeff n := rfl

theorem inclCF_refl (L : ℕ) (k : ℤ) : inclCF (dvd_refl L) k = LinearMap.id :=
  LinearMap.ext fun _ => CuspForm.ext fun _ => rfl

theorem inclMF_refl (L : ℕ) (k : ℤ) : inclMF (dvd_refl L) k = LinearMap.id :=
  LinearMap.ext fun _ => ModularForm.ext fun _ => rfl

theorem inclCF_comp_inclCF {L M N : ℕ} (hLM : L ∣ M) (hMN : M ∣ N) (k : ℤ) :
    (inclCF hMN k).comp (inclCF hLM k) = inclCF (hLM.trans hMN) k :=
  LinearMap.ext fun _ => CuspForm.ext fun _ => rfl

theorem inclMF_comp_inclMF {L M N : ℕ} (hLM : L ∣ M) (hMN : M ∣ N) (k : ℤ) :
    (inclMF hMN k).comp (inclMF hLM k) = inclMF (hLM.trans hMN) k :=
  LinearMap.ext fun _ => ModularForm.ext fun _ => rfl

theorem inclCF_injective (hLM : L ∣ M) (k : ℤ) : Function.Injective (inclCF hLM k) :=
  fun _ _ hfg => CuspForm.ext fun τ => DFunLike.congr_fun hfg τ

theorem inclMF_injective (hLM : L ∣ M) (k : ℤ) : Function.Injective (inclMF hLM k) :=
  fun _ _ hfg => ModularForm.ext fun τ => DFunLike.congr_fun hfg τ

/-- The nebentypus condition transfers to `Γ₀(M)` (for `L ∣ M`) with `χ.changeLevel`
(function level). -/
theorem nebentypus_changeLevel (hLM : L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (f : ℍ → ℂ)
    (hχ : ∀ γ ∈ Gamma0 L, (f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • f) :
    ∀ γ ∈ Gamma0 M, (f ∣[k] γ) =
      DirichletCharacter.changeLevel hLM χ ((γ 1 1 : ℤ) : ZMod M) • f := by
  intro γ hγ
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hLM (isCoprime_of_mem_Gamma0 hγ)]
  exact hχ γ (Gamma0_le_of_dvd hLM hγ)

theorem inclCF_nebentypus (hLM : L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (f : CuspForm (G1 L) k)
    (hχ : ∀ γ ∈ Gamma0 L, (⇑f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑f) :
    ∀ γ ∈ Gamma0 M, (⇑(inclCF hLM k f) ∣[k] γ) =
      DirichletCharacter.changeLevel hLM χ ((γ 1 1 : ℤ) : ZMod M) • ⇑(inclCF hLM k f) :=
  nebentypus_changeLevel hLM χ _ hχ

theorem inclMF_nebentypus (hLM : L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (f : ModularForm (G1 L) k)
    (hχ : ∀ γ ∈ Gamma0 L, (⇑f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑f) :
    ∀ γ ∈ Gamma0 M, (⇑(inclMF hLM k f) ∣[k] γ) =
      DirichletCharacter.changeLevel hLM χ ((γ 1 1 : ℤ) : ZMod M) • ⇑(inclMF hLM k f) :=
  nebentypus_changeLevel hLM χ _ hχ

end incl

/-! ## The matrix `diag(d, 1)` -/

section dg

variable (d : ℕ) [NeZero d]

/-- `diag(d, 1)` as an element of `GL(2, ℝ)`. -/
def dg : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(d : ℝ), 0; 0, 1]
    (by simpa [Matrix.det_fin_two_of] using NeZero.ne d)

lemma dg_val : ((dg d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ), 0; 0, 1] := rfl

lemma dg_det : (dg d).det.val = d := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, dg_val, Matrix.det_fin_two_of]
  ring

lemma natCast_pos_real : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))

lemma dg_det_pos : 0 < (dg d).det.val := by
  rw [dg_det]
  exact natCast_pos_real d

lemma coe_dg_smul (τ : ℍ) : ((dg d • τ : ℍ) : ℂ) = (d : ℂ) * τ := by
  rw [coe_smul_of_det_pos (dg_det_pos d)]
  simp [num, denom, dg_val]

lemma dg_slash (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] dg d) τ = (d : ℂ) ^ (k - 1) * F (dg d • τ) := by
  rw [slash_apply]
  have hden : denom (dg d) τ = 1 := by simp [denom, dg_val]
  rw [hden, σ, if_pos (dg_det_pos d), ContinuousAlgEquiv.refl_apply, dg_det,
    abs_of_pos (natCast_pos_real d)]
  simp only [_root_.one_zpow, mul_one]
  push_cast
  ring

lemma dg_smul_dg_smul (e : ℕ) [NeZero e] (τ : ℍ) : dg e • (dg d • τ) = dg (d * e) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_dg_smul, coe_dg_smul, coe_dg_smul]
  push_cast
  ring

lemma dg_one_smul (τ : ℍ) : dg 1 • τ = τ := by
  apply UpperHalfPlane.ext
  rw [coe_dg_smul]
  simp

/-- `(d • τ)` in terms of `qParam`: `𝕢₁(d τ) = 𝕢₁(τ)^d`. -/
lemma qParam_dg_smul (τ : ℍ) :
    Function.Periodic.qParam 1 ((dg d • τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ d := by
  rw [coe_dg_smul]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- Conjugating `x = [[a, b], [d c', e]]` by `diag(d, 1)` gives `[[a, d b], [c', e]]`. -/
lemma exists_conj_dg (x : SL(2, ℤ)) {c' : ℤ} (hc : x 1 0 = d * c') :
    ∃ y : SL(2, ℤ), y 0 0 = x 0 0 ∧ y 0 1 = d * x 0 1 ∧ y 1 0 = c' ∧ y 1 1 = x 1 1 ∧
      Matrix.SpecialLinearGroup.mapGL ℝ y =
        dg d * Matrix.SpecialLinearGroup.mapGL ℝ x * (dg d)⁻¹ := by
  have hdet : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
    have := x.det_coe
    rwa [Matrix.det_fin_two] at this
  let y : SL(2, ℤ) := ⟨!![x 0 0, d * x 0 1; c', x 1 1], by
    rw [Matrix.det_fin_two_of]
    rw [hc] at hdet
    linear_combination hdet⟩
  have hy00 : y 0 0 = x 0 0 := rfl
  have hy01 : y 0 1 = d * x 0 1 := rfl
  have hy10 : y 1 0 = c' := rfl
  have hy11 : y 1 1 = x 1 1 := rfl
  refine ⟨y, hy00, hy01, hy10, hy11, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, dg_val, Matrix.mul_apply,
      Fin.sum_univ_two, hy00, hy01, hy10, hy11, hc]
  all_goals ring

variable {d}

lemma exists_conj_dg_Gamma1 {L M : ℕ} (hdLM : d * L ∣ M) {x : SL(2, ℤ)} (hx : x ∈ Gamma1 M) :
    ∃ y ∈ Gamma1 L, Matrix.SpecialLinearGroup.mapGL ℝ y =
      dg d * Matrix.SpecialLinearGroup.mapGL ℝ x * (dg d)⁻¹ := by
  rw [Gamma1_mem] at hx
  obtain ⟨hx00, hx11, hx10⟩ := hx
  obtain ⟨c', hc', hc'L⟩ := exists_eq_mul_of_zmod_eq_zero hdLM hx10
  obtain ⟨y, hy00, -, hy10, hy11, hy⟩ := exists_conj_dg d x hc'
  have hLM := dvd_of_mul_dvd' hdLM
  refine ⟨y, ?_, hy⟩
  rw [Gamma1_mem, hy00, hy10, hy11]
  exact ⟨zmod_intCast_eq_one_of_dvd hLM hx00, zmod_intCast_eq_one_of_dvd hLM hx11, hc'L⟩

lemma exists_conj_dg_Gamma0 {L M : ℕ} (hdLM : d * L ∣ M) {x : SL(2, ℤ)} (hx : x ∈ Gamma0 M) :
    ∃ y ∈ Gamma0 L, y 1 1 = x 1 1 ∧ Matrix.SpecialLinearGroup.mapGL ℝ y =
      dg d * Matrix.SpecialLinearGroup.mapGL ℝ x * (dg d)⁻¹ := by
  rw [Gamma0_mem] at hx
  obtain ⟨c', hc', hc'L⟩ := exists_eq_mul_of_zmod_eq_zero hdLM hx
  obtain ⟨y, -, -, hy10, hy11, hy⟩ := exists_conj_dg d x hc'
  refine ⟨y, ?_, hy11, hy⟩
  rw [Gamma0_mem, hy10]
  exact hc'L

/-- **The conjugate group contains `Γ₁(M)`**: for `d * L ∣ M`,
`Γ₁(M) ≤ diag(d,1)⁻¹ Γ₁(L) diag(d,1)`. -/
theorem G1_le_conj {L M : ℕ} (hdLM : d * L ∣ M) :
    G1 M ≤ toConjAct (dg d)⁻¹ • G1 L := by
  rintro _ ⟨x, hx, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  obtain ⟨y, hyΓ, hy⟩ := exists_conj_dg_Gamma1 hdLM hx
  exact ⟨y, hyΓ, hy⟩

/-- Nebentypus under `F ↦ F ∣[k] diag(d, 1)` (function level): `χ` mod `L` becomes
`χ.changeLevel` mod `M` for `d * L ∣ M`. -/
theorem slash_dg_nebentypus {L M : ℕ} (hdLM : d * L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (F : ℍ → ℂ) (hχ : ∀ γ ∈ Gamma0 L, (F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • F) :
    ∀ γ ∈ Gamma0 M, ((F ∣[k] dg d) ∣[k] γ) =
      DirichletCharacter.changeLevel (dvd_of_mul_dvd' hdLM) χ ((γ 1 1 : ℤ) : ZMod M) •
        (F ∣[k] dg d) := by
  intro γ hγ
  obtain ⟨y, hyΓ, hy11, hy⟩ := exists_conj_dg_Gamma0 hdLM hγ
  have hmul : dg d * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ y * dg d := by
    rw [hy, inv_mul_cancel_right]
  have e1 : (F ∣[k] dg d) ∣[k] γ = (F ∣[k] dg d) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) :=
    rfl
  have e2 : F ∣[k] y = F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ y) := rfl
  rw [e1, ← SlashAction.slash_mul, hmul, SlashAction.slash_mul, ← e2, hχ y hyΓ,
    ModularForm.smul_slash, hy11, σ, if_pos (dg_det_pos d), ContinuousAlgEquiv.refl_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (dvd_of_mul_dvd' hdLM)
      (isCoprime_of_mem_Gamma0 hγ)]

/-- Reindexing: if `f τ = Σ a m 𝕢₁(τ)^m` for all `τ`, then
`f (d τ) = Σ_n (if d ∣ n then a (n / d) else 0) 𝕢₁(τ)^n`. -/
theorem hasSum_comp_dg {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ a m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ))
    (τ : ℍ) :
    HasSum (fun n ↦ (if d ∣ n then a (n / d) else 0) • Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (f (dg d • τ)) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have H := hf (dg d • τ)
  have hinj : Function.Injective (fun m : ℕ ↦ d * m) :=
    fun x y hxy ↦ Nat.eq_of_mul_eq_mul_left hdpos hxy
  have hzero : ∀ n ∉ Set.range (fun m : ℕ ↦ d * m),
      (fun n : ℕ ↦ (if d ∣ n then a (n / d) else 0) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ n) n = 0 := by
    intro n hn
    have : ¬ d ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [this]
  refine (hinj.hasSum_iff hzero).mp ?_
  convert H using 1
  funext m
  show (if d ∣ d * m then a (d * m / d) else 0) • Function.Periodic.qParam 1 (τ : ℂ) ^ (d * m) =
    a m * Function.Periodic.qParam 1 ((dg d • τ : ℍ) : ℂ) ^ m
  rw [if_pos (dvd_mul_right d m), Nat.mul_div_cancel_left m hdpos, qParam_dg_smul, ← pow_mul,
    smul_eq_mul]

end dg

/-! ## The maps `ι_d : f ↦ f(d ·)` -/

section iota

variable (d : ℕ) [NeZero d] {L M : ℕ}

/-- `ι_d f = f(d ·)` on cusp forms, as a cusp form on `Γ₁(M)` (`d * L ∣ M`). -/
def iotaCuspForm (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) : CuspForm (G1 M) k :=
  restrictCF (G1_le_conj hdLM) (((d : ℝ) ^ (1 - k)) • CuspForm.translate f (dg d))

/-- `ι_d f = f(d ·)` on modular forms, as a modular form on `Γ₁(M)` (`d * L ∣ M`). -/
def iotaModularForm (hdLM : d * L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) :
    ModularForm (G1 M) k :=
  restrictMF (G1_le_conj hdLM) (((d : ℝ) ^ (1 - k)) • ModularForm.translate f (dg d))

lemma coe_iotaCuspForm (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) :
    ⇑(iotaCuspForm d hdLM f) = ((d : ℝ) ^ (1 - k)) • (⇑f ∣[k] dg d) := rfl

lemma coe_iotaModularForm (hdLM : d * L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) :
    ⇑(iotaModularForm d hdLM f) = ((d : ℝ) ^ (1 - k)) • (⇑f ∣[k] dg d) := rfl

/-- `d^(1-k) • (F ∣[k] diag(d, 1))` is `τ ↦ F (d τ)`. -/
lemma smul_slash_dg_apply {k : ℤ} (F : ℍ → ℂ) (τ : ℍ) :
    (((d : ℝ) ^ (1 - k)) • (F ∣[k] dg d)) τ = F (dg d • τ) := by
  rw [Pi.smul_apply, dg_slash, Complex.real_smul]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  push_cast
  rw [← mul_assoc, ← zpow_add₀ hd0]
  simp

lemma iotaCuspForm_apply (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (τ : ℍ) :
    iotaCuspForm d hdLM f τ = f (dg d • τ) := by
  rw [coe_iotaCuspForm, smul_slash_dg_apply]

lemma iotaModularForm_apply (hdLM : d * L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) (τ : ℍ) :
    iotaModularForm d hdLM f τ = f (dg d • τ) := by
  rw [coe_iotaModularForm, smul_slash_dg_apply]

/-- `ι_d : S_k(Γ₁(L)) →ₗ S_k(Γ₁(M))`, `f ↦ f(d ·)`, for `d * L ∣ M`. -/
def iotaCF (hdLM : d * L ∣ M) (k : ℤ) : CuspForm (G1 L) k →ₗ[ℂ] CuspForm (G1 M) k where
  toFun := iotaCuspForm d hdLM
  map_add' _ _ := CuspForm.ext fun τ => by simp [iotaCuspForm_apply]
  map_smul' _ _ := CuspForm.ext fun τ => by simp [iotaCuspForm_apply]

/-- `ι_d : M_k(Γ₁(L)) →ₗ M_k(Γ₁(M))`, `f ↦ f(d ·)`, for `d * L ∣ M`. -/
def iotaMF (hdLM : d * L ∣ M) (k : ℤ) : ModularForm (G1 L) k →ₗ[ℂ] ModularForm (G1 M) k where
  toFun := iotaModularForm d hdLM
  map_add' _ _ := ModularForm.ext fun τ => by simp [iotaModularForm_apply]
  map_smul' _ _ := ModularForm.ext fun τ => by simp [iotaModularForm_apply]

theorem iotaCF_apply (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (τ : ℍ) :
    iotaCF d hdLM k f τ = f (dg d • τ) :=
  iotaCuspForm_apply d hdLM f τ

theorem iotaMF_apply (hdLM : d * L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) (τ : ℍ) :
    iotaMF d hdLM k f τ = f (dg d • τ) :=
  iotaModularForm_apply d hdLM f τ

theorem coe_iotaCF (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) :
    ⇑(iotaCF d hdLM k f) = ((d : ℝ) ^ (1 - k)) • (⇑f ∣[k] dg d) := rfl

theorem coe_iotaMF (hdLM : d * L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) :
    ⇑(iotaMF d hdLM k f) = ((d : ℝ) ^ (1 - k)) • (⇑f ∣[k] dg d) := rfl

/-- `ι_d f (τ) = f (d τ)` in `ℂ`-coordinates. -/
theorem iotaCF_apply_coe (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (τ : ℍ)
    (σ' : ℍ) (hσ : (σ' : ℂ) = d * τ) : iotaCF d hdLM k f τ = f σ' := by
  rw [iotaCF_apply]
  congr 1
  apply UpperHalfPlane.ext
  rw [coe_dg_smul, hσ]

/-! ### Coefficients -/

/-- **Coefficients of `ι_d`** (cusp forms): `coeff n = if d ∣ n then a(n / d) else 0`. -/
theorem coeff_iotaCF (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (n : ℕ) :
    (qExpansion 1 (iotaCF d hdLM k f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have h1L := one_mem_strictPeriods_G1 L
  have : Fact (IsCusp OnePoint.infty (G1 L)) :=
    ⟨(G1 L).isCusp_of_mem_strictPeriods one_pos h1L⟩
  refine (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_G1 M)
    (c := fun n => if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0)
    (f := iotaCF d hdLM k f) (fun τ => ?_) n).symm
  rw [iotaCF_apply]
  exact hasSum_comp_dg (fun τ => ModularForm.hasSum_qExpansion (f := f) one_pos h1L τ) τ

/-- **Coefficients of `ι_d`** (modular forms): `coeff n = if d ∣ n then a(n / d) else 0`. -/
theorem coeff_iotaMF (hdLM : d * L ∣ M) {k : ℤ} (f : ModularForm (G1 L) k) (n : ℕ) :
    (qExpansion 1 (iotaMF d hdLM k f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have h1L := one_mem_strictPeriods_G1 L
  have : Fact (IsCusp OnePoint.infty (G1 L)) :=
    ⟨(G1 L).isCusp_of_mem_strictPeriods one_pos h1L⟩
  refine (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_G1 M)
    (c := fun n => if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0)
    (f := iotaMF d hdLM k f) (fun τ => ?_) n).symm
  rw [iotaMF_apply]
  exact hasSum_comp_dg (fun τ => ModularForm.hasSum_qExpansion (f := f) one_pos h1L τ) τ

theorem coeff_iotaCF_mul (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) (n : ℕ) :
    (qExpansion 1 (iotaCF d hdLM k f)).coeff (d * n) = (qExpansion 1 f).coeff n := by
  rw [coeff_iotaCF, if_pos (dvd_mul_right d n),
    Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero (NeZero.ne d))]

theorem coeff_iotaCF_of_not_dvd (hdLM : d * L ∣ M) {k : ℤ} (f : CuspForm (G1 L) k) {n : ℕ}
    (hn : ¬ d ∣ n) : (qExpansion 1 (iotaCF d hdLM k f)).coeff n = 0 := by
  rw [coeff_iotaCF, if_neg hn]

/-! ### Composition, `ι_1`, injectivity -/

/-- `ι_d ∘ ι_e = ι_{d e}`. -/
theorem iotaCF_comp_iotaCF (e : ℕ) [NeZero e] {L M' M : ℕ} (he : e * L ∣ M') (hd : d * M' ∣ M)
    (k : ℤ) : (iotaCF d hd k).comp (iotaCF e he k) = iotaCF (d * e) (mul_mul_dvd_of_dvd he hd) k :=
  LinearMap.ext fun f => CuspForm.ext fun τ => by
    rw [LinearMap.comp_apply, iotaCF_apply, iotaCF_apply, iotaCF_apply, dg_smul_dg_smul]

theorem iotaMF_comp_iotaMF (e : ℕ) [NeZero e] {L M' M : ℕ} (he : e * L ∣ M') (hd : d * M' ∣ M)
    (k : ℤ) : (iotaMF d hd k).comp (iotaMF e he k) = iotaMF (d * e) (mul_mul_dvd_of_dvd he hd) k :=
  LinearMap.ext fun f => ModularForm.ext fun τ => by
    rw [LinearMap.comp_apply, iotaMF_apply, iotaMF_apply, iotaMF_apply, dg_smul_dg_smul]

/-- `ι_1 = incl`. -/
theorem iotaCF_one (hLM : L ∣ M) (k : ℤ) :
    iotaCF 1 (by rwa [one_mul]) k = inclCF hLM k :=
  LinearMap.ext fun f => CuspForm.ext fun τ => by
    rw [iotaCF_apply, dg_one_smul, inclCF_apply]

theorem iotaMF_one (hLM : L ∣ M) (k : ℤ) :
    iotaMF 1 (by rwa [one_mul]) k = inclMF hLM k :=
  LinearMap.ext fun f => ModularForm.ext fun τ => by
    rw [iotaMF_apply, dg_one_smul, inclMF_apply]

theorem inclCF_comp_iotaCF {N : ℕ} (hdLM : d * L ∣ M) (hMN : M ∣ N) (k : ℤ) :
    (inclCF hMN k).comp (iotaCF d hdLM k) = iotaCF d (hdLM.trans hMN) k :=
  LinearMap.ext fun f => CuspForm.ext fun τ => by
    rw [LinearMap.comp_apply, inclCF_apply, iotaCF_apply, iotaCF_apply]

theorem iotaCF_comp_inclCF {L' : ℕ} (hLL' : L ∣ L') (hdL'M : d * L' ∣ M) (k : ℤ) :
    (iotaCF d hdL'M k).comp (inclCF hLL' k) =
      iotaCF d ((mul_dvd_mul_left d hLL').trans hdL'M) k :=
  LinearMap.ext fun f => CuspForm.ext fun τ => by
    rw [LinearMap.comp_apply, iotaCF_apply, inclCF_apply, iotaCF_apply]

theorem inclMF_comp_iotaMF {N : ℕ} (hdLM : d * L ∣ M) (hMN : M ∣ N) (k : ℤ) :
    (inclMF hMN k).comp (iotaMF d hdLM k) = iotaMF d (hdLM.trans hMN) k :=
  LinearMap.ext fun f => ModularForm.ext fun τ => by
    rw [LinearMap.comp_apply, inclMF_apply, iotaMF_apply, iotaMF_apply]

theorem iotaMF_comp_inclMF {L' : ℕ} (hLL' : L ∣ L') (hdL'M : d * L' ∣ M) (k : ℤ) :
    (iotaMF d hdL'M k).comp (inclMF hLL' k) =
      iotaMF d ((mul_dvd_mul_left d hLL').trans hdL'M) k :=
  LinearMap.ext fun f => ModularForm.ext fun τ => by
    rw [LinearMap.comp_apply, iotaMF_apply, inclMF_apply, iotaMF_apply]

theorem iotaCF_injective (hdLM : d * L ∣ M) (k : ℤ) : Function.Injective (iotaCF d hdLM k) := by
  intro f g hfg
  ext σ'
  have := DFunLike.congr_fun hfg ((dg d)⁻¹ • σ')
  rwa [iotaCF_apply, iotaCF_apply, smul_inv_smul] at this

theorem iotaMF_injective (hdLM : d * L ∣ M) (k : ℤ) : Function.Injective (iotaMF d hdLM k) := by
  intro f g hfg
  ext σ'
  have := DFunLike.congr_fun hfg ((dg d)⁻¹ • σ')
  rwa [iotaMF_apply, iotaMF_apply, smul_inv_smul] at this

/-! ### Nebentypus -/

/-- `ι_d` sends nebentypus `χ` mod `L` to nebentypus `χ.changeLevel` mod `M` (cusp forms). -/
theorem iotaCF_nebentypus (hdLM : d * L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (f : CuspForm (G1 L) k)
    (hχ : ∀ γ ∈ Gamma0 L, (⇑f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑f) :
    ∀ γ ∈ Gamma0 M, (⇑(iotaCF d hdLM k f) ∣[k] γ) =
      DirichletCharacter.changeLevel (dvd_of_mul_dvd' hdLM) χ ((γ 1 1 : ℤ) : ZMod M) •
        ⇑(iotaCF d hdLM k f) := by
  intro γ hγ
  rw [coe_iotaCF, ModularForm.SL_smul_slash, slash_dg_nebentypus hdLM χ _ hχ γ hγ, smul_comm]

/-- `ι_d` sends nebentypus `χ` mod `L` to nebentypus `χ.changeLevel` mod `M` (modular forms). -/
theorem iotaMF_nebentypus (hdLM : d * L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (f : ModularForm (G1 L) k)
    (hχ : ∀ γ ∈ Gamma0 L, (⇑f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑f) :
    ∀ γ ∈ Gamma0 M, (⇑(iotaMF d hdLM k f) ∣[k] γ) =
      DirichletCharacter.changeLevel (dvd_of_mul_dvd' hdLM) χ ((γ 1 1 : ℤ) : ZMod M) •
        ⇑(iotaMF d hdLM k f) := by
  intro γ hγ
  rw [coe_iotaMF, ModularForm.SL_smul_slash, slash_dg_nebentypus hdLM χ _ hχ γ hγ, smul_comm]

end iota

end RamanujanPetersson.Level

end


