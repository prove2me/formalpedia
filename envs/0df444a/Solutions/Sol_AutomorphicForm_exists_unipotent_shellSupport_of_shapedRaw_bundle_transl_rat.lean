-- Prove2me | solution 1 for AutomorphicForm.exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/47609116-9ef4-52a8-92ea-3d638da1d472

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 0

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace P2mOnePrimeShape

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

theorem v_add_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem ne_zero_of_v_eq_one {x : F} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem exp_neg_natCast_le_one (c : ℕ) : WithZero.exp (-(c : ℤ)) ≤ (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem v_eq_one_of_sub_one_lt {x : F} (hx : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ hx

theorem v_eq_one_of_sub_one_le_exp {x : F} {m : ℕ} (hm : 1 ≤ m)
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-(m : ℤ))) : Valued.v x = 1 := by
  refine v_eq_one_of_sub_one_lt (lt_of_le_of_lt hx ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem v_inv_sub_one {x : F} (h1 : Valued.v x = 1) : Valued.v (x⁻¹ - 1) = Valued.v (x - 1) := by
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]

theorem v_le_one_of_sub_one_le {x : F} {γ : ℤᵐ⁰} (hγ : γ ≤ 1) (hx : Valued.v (x - 1) ≤ γ) :
    Valued.v x ≤ 1 := by
  have : x = (x - 1) + 1 := by ring
  rw [this]
  exact v_add_le (hx.trans hγ) (by rw [Valuation.map_one])

theorem v_zpow_unif {π : F} (hπv : Valued.v π = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v (π ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, hπv, ← WithZero.exp_zsmul]; congr 1; ring

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : G) : Mat) = !![a, b; c, d] := rfl

theorem unipotent_coe (x : F) : ((UnramifiedWhittaker.unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem diagZ_coe (π : F) (hπ : π ≠ 0) (n : ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ n : G) : Mat) = !![π ^ n, 0; 0, 1] := rfl

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_eq_of_mul {g h : G} (hgh : g * h = 1) : g⁻¹ = h :=
  inv_eq_of_mul_eq_one_right hgh

structure IsLv (γ : ℤᵐ⁰) (m : Mat) : Prop where
  integral : ∀ i j, Valued.v (m i j) ≤ 1
  lowerLeft : Valued.v (m 1 0) ≤ γ
  lowerRight : Valued.v (m 1 1 - 1) ≤ γ

theorem isLocalLevelOne_iff {N : Ideal (𝓞 ℚ)} {γ : ℤᵐ⁰} (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = γ)
    (m : Mat) : AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m ↔ IsLv γ m := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h1 i j), ?_, ?_⟩
    · rwa [hγ] at h2
    · rwa [hγ] at h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h1 i j), ?_, ?_⟩
    · rwa [hγ]
    · rwa [hγ]

theorem mem_lv_iff {N : Ideal (𝓞 ℚ)} {γ : ℤᵐ⁰} (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = γ) (k : G) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N ↔ IsLv γ (k : Mat) ∧ IsLv γ ((k⁻¹ : G) : Mat) := by
  rw [AdelicDock.mem_localLevelOne_iff, isLocalLevelOne_iff hγ, isLocalLevelOne_iff hγ]

theorem idealBound_pow (c : ℕ) :
    AdelicLevel.idealBound (𝓞 ℚ) (p.asIdeal ^ c) p = WithZero.exp (-(c : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (pow_ne_zero c p.ne_bot), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr p.ne_bot) (Associates.irreducible_mk.mpr p.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr p.irreducible), mul_one]

theorem idealBound_eq_exp_count {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    AdelicLevel.idealBound (𝓞 ℚ) N p =
      WithZero.exp (-(((Associates.mk p.asIdeal).count (Associates.mk N).factors : ℕ) : ℤ)) := by
  classical
  exact AdelicLevel.idealBound_of_ne_bot hN p

theorem gl2_mem_of_entries {N : Ideal (𝓞 ℚ)} {γ : ℤᵐ⁰} (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = γ)
    (hγ1 : γ ≤ 1)
    {a b c d : F} (h : a * d - b * c ≠ 0) {a' b' c' d' : F} (h' : a' * d' - b' * c' ≠ 0)
    (hinv : gl2 a b c d h * gl2 a' b' c' d' h' = 1)
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hc : Valued.v c ≤ γ) (hd : Valued.v (d - 1) ≤ γ)
    (ha' : Valued.v a' ≤ 1) (hb' : Valued.v b' ≤ 1) (hc' : Valued.v c' ≤ γ) (hd' : Valued.v (d' - 1) ≤ γ) :
    gl2 a b c d h ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  rw [mem_lv_iff hγ, inv_eq_of_mul hinv]
  refine ⟨⟨fun i j => ?_, by simpa using hc, by simpa using hd⟩,
    ⟨fun i j => ?_, by simpa using hc', by simpa using hd'⟩⟩
  · fin_cases i <;> fin_cases j
    · simpa using ha
    · simpa using hb
    · simpa using hc.trans hγ1
    · simpa using v_le_one_of_sub_one_le hγ1 hd
  · fin_cases i <;> fin_cases j
    · simpa using ha'
    · simpa using hb'
    · simpa using hc'.trans hγ1
    · simpa using v_le_one_of_sub_one_le hγ1 hd'

theorem unipotent_mem {N : Ideal (𝓞 ℚ)} {γ : ℤᵐ⁰} (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = γ)
    (hγ1 : γ ≤ 1) {s : F} (hs : Valued.v s ≤ 1) :
    (UnramifiedWhittaker.unipotent s : G) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  have h1 : (1 : F) * 1 - s * 0 ≠ 0 := by simp
  have h2 : (1 : F) * 1 - (-s) * 0 ≠ 0 := by simp
  have heq : (UnramifiedWhittaker.unipotent s : G) = gl2 1 s 0 1 h1 := rfl
  rw [heq]
  refine gl2_mem_of_entries hγ hγ1 h1 h2 ?_ (by simp) hs (by simp) (by simp) (by simp)
    (by rwa [Valuation.map_neg]) (by simp) (by simp)
  apply gl_eq_of_entries <;> simp [mul_coe_apply]

theorem lowU_mem {N : Ideal (𝓞 ℚ)} {γ : ℤᵐ⁰} (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = γ)
    (hγ1 : γ ≤ 1) {t : F} (ht : Valued.v t ≤ γ) (h1 : (1 : F) * 1 - 0 * t ≠ 0) :
    gl2 1 0 t 1 h1 ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  have h2 : (1 : F) * 1 - 0 * (-t) ≠ 0 := by simp
  refine gl2_mem_of_entries hγ hγ1 h1 h2 ?_ (by simp) (by simp) ht (by simp) (by simp) (by simp)
    (by rwa [Valuation.map_neg]) (by simp)
  apply gl_eq_of_entries <;> simp [mul_coe_apply]

theorem scalar_mem {N : Ideal (𝓞 ℚ)} {γ : ℤᵐ⁰} (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = γ)
    (hγ1 : γ ≤ 1) {d : F} (hd1 : Valued.v d = 1) (hd : Valued.v (d - 1) ≤ γ)
    (h1 : d * d - 0 * 0 ≠ 0) :
    gl2 d 0 0 d h1 ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  have hd0 : d ≠ 0 := ne_zero_of_v_eq_one hd1
  have h2 : d⁻¹ * d⁻¹ - 0 * 0 ≠ 0 := by simp [hd0]
  refine gl2_mem_of_entries hγ hγ1 h1 h2 ?_ hd1.le (by simp) (by simp) hd
    (by rw [map_inv₀, hd1, inv_one]) (by simp) (by simp) (by rwa [v_inv_sub_one hd1])
  apply gl_eq_of_entries <;> simp [mul_coe_apply, hd0]

theorem conjLowU_mem {N : Ideal (𝓞 ℚ)} {c : ℕ}
    (hγ : AdelicLevel.idealBound (𝓞 ℚ) N p = WithZero.exp (-(c : ℤ)))
    {m : ℕ} (hm : c + 2 ≤ m) {t x₀ : F} (ht : Valued.v t ≤ WithZero.exp (-(m : ℤ)))
    (hx₀ : Valued.v x₀ ≤ WithZero.exp (1 : ℤ))
    (h1 : (1 - x₀ * t) * (1 + t * x₀) - (-(x₀ ^ 2 * t)) * t ≠ 0) :
    gl2 (1 - x₀ * t) (-(x₀ ^ 2 * t)) t (1 + t * x₀) h1 ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  have hγ1 : WithZero.exp (-(c : ℤ)) ≤ 1 := exp_neg_natCast_le_one c

  have hxt : Valued.v (x₀ * t) ≤ WithZero.exp (-(c : ℤ)) := by
    rw [Valuation.map_mul]
    calc Valued.v x₀ * Valued.v t ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-(m : ℤ)) := mul_le_mul' hx₀ ht
      _ = WithZero.exp (1 + -(m : ℤ)) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(c : ℤ)) := by rw [WithZero.exp_le_exp]; omega
  have htx : Valued.v (t * x₀) ≤ WithZero.exp (-(c : ℤ)) := by rwa [mul_comm]
  have hxt1 : Valued.v (x₀ * t) ≤ 1 := hxt.trans hγ1
  have hx2t : Valued.v (x₀ ^ 2 * t) ≤ 1 := by
    rw [Valuation.map_mul, Valuation.map_pow]
    calc Valued.v x₀ ^ 2 * Valued.v t
        ≤ WithZero.exp (1 : ℤ) ^ 2 * WithZero.exp (-(m : ℤ)) := mul_le_mul' (pow_le_pow_left' hx₀ 2) ht
      _ = WithZero.exp ((2 : ℕ) • (1 : ℤ) + -(m : ℤ)) := by rw [WithZero.exp_add, WithZero.exp_nsmul]
      _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; simp; omega
  have htc : Valued.v t ≤ WithZero.exp (-(c : ℤ)) :=
    ht.trans (by rw [WithZero.exp_le_exp]; omega)
  have h2 : (1 + x₀ * t) * (1 - t * x₀) - (x₀ ^ 2 * t) * (-t) ≠ 0 := by
    have : (1 + x₀ * t) * (1 - t * x₀) - (x₀ ^ 2 * t) * (-t) = 1 := by ring
    rw [this]; exact one_ne_zero
  refine gl2_mem_of_entries hγ hγ1 h1 h2 ?_
    (v_sub_le (by rw [Valuation.map_one]) hxt1) (by rw [Valuation.map_neg]; exact hx2t) htc
    (by rw [add_sub_cancel_left]; exact htx)
    (v_add_le (by rw [Valuation.map_one]) hxt1) hx2t (by rw [Valuation.map_neg]; exact htc)
    (by rw [show (1 : F) - t * x₀ - 1 = -(t * x₀) by ring, Valuation.map_neg]; exact htx)
  apply gl_eq_of_entries <;> simp [mul_coe_apply] <;> ring

theorem v_det_of_mem {m : ℕ} {k : G} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ m)) :
    Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) = 1 := by
  rw [mem_lv_iff (idealBound_pow m)] at hk
  have h1 : Valued.v (k : Mat).det ≤ 1 := by
    rw [Matrix.det_fin_two]
    exact v_sub_le (by rw [Valuation.map_mul]; exact mul_le_one' (hk.1.integral 0 0) (hk.1.integral 1 1))
      (by rw [Valuation.map_mul]; exact mul_le_one' (hk.1.integral 0 1) (hk.1.integral 1 0))
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := by
    rw [Matrix.det_fin_two]
    exact v_sub_le (by rw [Valuation.map_mul]; exact mul_le_one' (hk.2.integral 0 0) (hk.2.integral 1 1))
      (by rw [Valuation.map_mul]; exact mul_le_one' (hk.2.integral 0 1) (hk.2.integral 1 0))
  have hprod : (k : Mat).det * ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.det_one]
  have hv : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← Valuation.map_mul, hprod, Valuation.map_one]
  rw [← Matrix.det_fin_two]
  exact le_antisymm h1 (by
    calc (1 : ℤᵐ⁰) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hv.symm
      _ ≤ Valued.v (k : Mat).det * 1 := mul_le_mul_right h2 _
      _ = Valued.v (k : Mat).det := mul_one _)

theorem local_shell (ψ : AddChar (HeightOneSpectrum.adicCompletion ℚ p) ℂ)
    (hψO : ∀ s : F, Valued.v s ≤ 1 → ψ s = 1)
    (x₀ : F) (hx₀v : Valued.v x₀ ≤ WithZero.exp (1 : ℤ)) (hx₀ψ : ψ x₀ ≠ 1)
    (π : F) (hπ0 : π ≠ 0) (hπv : Valued.v π = WithZero.exp (-1 : ℤ))
    (N : Ideal (𝓞 ℚ)) (c : ℕ) (hNc : AdelicLevel.idealBound (𝓞 ℚ) N p = WithZero.exp (-(c : ℤ)))
    (W : G → ℂ)
    (hWE : ∀ (t : F) (y : G), W (UnramifiedWhittaker.unipotent t * y) = ψ t * W y)
    (hWK : ∀ (y : G), ∀ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, W (y * k') = W y)
    {m : ℕ} (hm : c + 2 ≤ m) {k : G} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ m))
    (x : F) {n : ℤ} (hn : n ≠ 0) :
    W (UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.diagZ π hπ0 n * k * UnramifiedWhittaker.unipotent x₀) -
      W (UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.diagZ π hπ0 n * k) = 0 := by
  have hγ1 : WithZero.exp (-(c : ℤ)) ≤ 1 := exp_neg_natCast_le_one c
  have hm1 : 1 ≤ m := by omega

  have hkm := (mem_lv_iff (idealBound_pow m) k).1 hk
  set a : F := (k : Mat) 0 0 with ha_def
  set b : F := (k : Mat) 0 1 with hb_def
  set c' : F := (k : Mat) 1 0 with hc_def
  set d : F := (k : Mat) 1 1 with hd_def
  have ha1 : Valued.v a ≤ 1 := hkm.1.integral 0 0
  have hb1 : Valued.v b ≤ 1 := hkm.1.integral 0 1
  have hcm : Valued.v c' ≤ WithZero.exp (-(m : ℤ)) := hkm.1.lowerLeft
  have hdm : Valued.v (d - 1) ≤ WithZero.exp (-(m : ℤ)) := hkm.1.lowerRight
  have hd1 : Valued.v d = 1 := v_eq_one_of_sub_one_le_exp hm1 hdm
  have hd0 : d ≠ 0 := ne_zero_of_v_eq_one hd1
  have hΔ : Valued.v (a * d - b * c') = 1 := v_det_of_mem hk

  set t : F := c' / d with ht_def
  set α' : F := a - b * t with hα_def
  have htm : Valued.v t ≤ WithZero.exp (-(m : ℤ)) := by
    rw [ht_def, map_div₀, hd1, div_one]; exact hcm
  have hα'd : α' * d = a * d - b * c' := by
    rw [hα_def, ht_def]; field_simp
  have hα1 : Valued.v α' = 1 := by
    have h := congrArg Valued.v hα'd
    rw [Valuation.map_mul, hd1, mul_one, hΔ] at h
    exact h
  have hα0 : α' ≠ 0 := ne_zero_of_v_eq_one hα1
  set y : F := π ^ n * α' / d with hy_def
  have hyv : Valued.v y = WithZero.exp (-n) := by
    rw [hy_def, map_div₀, Valuation.map_mul, v_zpow_unif hπv, hα1, hd1, mul_one, div_one]
  have hy0 : y ≠ 0 := by
    rw [hy_def]; exact div_ne_zero (mul_ne_zero (zpow_ne_zero n hπ0) hα0) hd0
  set x'' : F := x + π ^ n * b / d with hx_def

  have hL : (1 : F) * 1 - 0 * t ≠ 0 := by simp
  have hL' : (1 - x₀ * t) * (1 + t * x₀) - (-(x₀ ^ 2 * t)) * t ≠ 0 := by
    have : (1 - x₀ * t) * (1 + t * x₀) - (-(x₀ ^ 2 * t)) * t = 1 := by ring
    rw [this]; exact one_ne_zero
  have hT : y * 1 - 0 * 0 ≠ 0 := by simpa using hy0
  have hD : d * d - 0 * 0 ≠ 0 := by simpa using hd0
  have hLmem : gl2 1 0 t 1 hL ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N :=
    lowU_mem hNc hγ1 (htm.trans (by rw [WithZero.exp_le_exp]; omega)) hL
  have hL'mem : gl2 (1 - x₀ * t) (-(x₀ ^ 2 * t)) t (1 + t * x₀) hL' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N :=
    conjLowU_mem hNc hm htm hx₀v hL'
  have hDmem : gl2 d 0 0 d hD ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N :=
    scalar_mem hNc hγ1 hd1 (hdm.trans (by rw [WithZero.exp_le_exp]; omega)) hD

  have hI1 : UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.diagZ π hπ0 n * k =
      UnramifiedWhittaker.unipotent x'' * (gl2 y 0 0 1 hT * gl2 d 0 0 d hD * gl2 1 0 t 1 hL) := by
    apply gl_eq_of_entries <;>
      simp only [mul_coe_apply, unipotent_coe, diagZ_coe, gl2_coe, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ← ha_def, ← hb_def, ← hc_def, ← hd_def, hy_def, hx_def, hα_def, ht_def] <;>
      field_simp <;> ring

  have hI2 : UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.diagZ π hπ0 n * k *
        UnramifiedWhittaker.unipotent x₀ =
      UnramifiedWhittaker.unipotent (x'' + y * x₀) *
        (gl2 y 0 0 1 hT * gl2 d 0 0 d hD * gl2 (1 - x₀ * t) (-(x₀ ^ 2 * t)) t (1 + t * x₀) hL') := by
    apply gl_eq_of_entries <;>
      simp only [mul_coe_apply, unipotent_coe, diagZ_coe, gl2_coe, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ← ha_def, ← hb_def, ← hc_def, ← hd_def, hy_def, hx_def, hα_def, ht_def] <;>
      field_simp <;> ring

  have hW2 : W (UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.diagZ π hπ0 n * k) =
      ψ x'' * W (gl2 y 0 0 1 hT) := by
    rw [hI1, hWE, hWK _ _ hLmem, hWK _ _ hDmem]
  have hW1 : W (UnramifiedWhittaker.unipotent x * UnramifiedWhittaker.diagZ π hπ0 n * k *
        UnramifiedWhittaker.unipotent x₀) = ψ x'' * ψ (y * x₀) * W (gl2 y 0 0 1 hT) := by
    rw [hI2, hWE, hWK _ _ hL'mem, hWK _ _ hDmem, AddChar.map_add_eq_mul]
  rw [hW1, hW2]

  suffices hkey : (ψ (y * x₀) - 1) * W (gl2 y 0 0 1 hT) = 0 by
    have : ψ x'' * ψ (y * x₀) * W (gl2 y 0 0 1 hT) - ψ x'' * W (gl2 y 0 0 1 hT) =
        ψ x'' * ((ψ (y * x₀) - 1) * W (gl2 y 0 0 1 hT)) := by ring
    rw [this, hkey, mul_zero]
  rcases lt_or_gt_of_ne hn with hneg | hpos
  ·
    have hs : Valued.v (x₀ / y) ≤ 1 := by
      rw [map_div₀, hyv, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
      calc Valued.v x₀ * WithZero.exp n ≤ WithZero.exp (1 : ℤ) * WithZero.exp n := mul_le_mul_left hx₀v _
        _ = WithZero.exp (1 + n) := (WithZero.exp_add _ _).symm
        _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hcomm : gl2 y 0 0 1 hT * UnramifiedWhittaker.unipotent (x₀ / y) =
        UnramifiedWhittaker.unipotent x₀ * gl2 y 0 0 1 hT := by
      apply gl_eq_of_entries <;>
        simp only [mul_coe_apply, unipotent_coe, gl2_coe, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
        field_simp <;> ring
    have hval : W (gl2 y 0 0 1 hT) = ψ x₀ * W (gl2 y 0 0 1 hT) := by
      conv_lhs => rw [← hWK (gl2 y 0 0 1 hT) _ (unipotent_mem hNc hγ1 hs), hcomm, hWE]
    have hzero : W (gl2 y 0 0 1 hT) = 0 := by
      have h1 : (1 - ψ x₀) * W (gl2 y 0 0 1 hT) = 0 := by rw [sub_mul, one_mul, ← hval, sub_self]
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (sub_eq_zero.1 h).symm hx₀ψ
      · exact h
    rw [hzero, mul_zero]
  ·
    have hyx : Valued.v (y * x₀) ≤ 1 := by
      rw [Valuation.map_mul, hyv]
      calc WithZero.exp (-n) * Valued.v x₀ ≤ WithZero.exp (-n) * WithZero.exp (1 : ℤ) := mul_le_mul_right hx₀v _
        _ = WithZero.exp (-n + 1) := (WithZero.exp_add _ _).symm
        _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    rw [hψO _ hyx, sub_self, zero_mul]

end P2mOnePrimeShape
p2m_reactivate "P2MW.S_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat.P2mOnePrimeShape"

namespace P2mOnePrimeShapeAdelic

open AutomorphicForm NumberField.AdelicLevel AdelicDock UnramifiedWhittaker LanglandsTunnell RSCarrier

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem localAt_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem glArch_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = 1 :=
  glArch_finEmbed (𝓞 ℚ) ℚ _

theorem ext_of_glArch_localAt {g h : AdelicGL2 (𝓞 ℚ) ℚ} (harch : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v g = localAt ℚ v h) : g = h := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_)
  · exact congrArg Units.val harch
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    exact congrArg Units.val (hfin w)

theorem conj_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)) :
    Y⁻¹ * placeEmbed ℚ p u * Y = placeEmbed ℚ p ((localAt ℚ p Y)⁻¹ * u * localAt ℚ p Y) := by
  refine ext_of_glArch_localAt ?_ fun v => ?_
  · rw [map_mul, map_mul, glArch_placeEmbed, glArch_placeEmbed, mul_one, map_inv, inv_mul_cancel]
  · by_cases hv : v = p
    · subst hv
      rw [map_mul, map_mul, localAt_placeEmbed, localAt_placeEmbed, map_inv]
    · rw [map_mul, map_mul, localAt_placeEmbed_of_ne p hv, localAt_placeEmbed_of_ne p hv, mul_one, map_inv,
        inv_mul_cancel]

theorem placeEmbed_mul_comm {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : localAt ℚ p g = 1)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  have h := conj_placeEmbed p g x
  rw [hg, inv_one, one_mul, mul_one] at h
  calc placeEmbed ℚ p x * g = g * (g⁻¹ * placeEmbed ℚ p x * g) := by group
    _ = g * placeEmbed ℚ p x := by rw [h]

theorem ratArchGL2_of_mem {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  simp only [ratArchGL2, (mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one]

theorem finFactor_coe (g : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
  refine Subtype.ext ?_
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ *
      (g : AdelicGL2 (𝓞 ℚ) ℚ) = g
  rw [ratArchGL2_of_mem g.2, map_one, inv_one, one_mul]

theorem finFactor_one : RSCarrier.finFactor (1 : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  have h := finFactor_coe (1 : finiteAdelicGL2Subgroup ℚ)
  rwa [OneMemClass.coe_one] at h

end P2mOnePrimeShapeAdelic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat.P2mOnePrimeShape"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat.P2mOnePrimeShape"

set_option maxHeartbeats 3200000 in
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel in
open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain in
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates in
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker in
theorem solution
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hloc : (∀ p : HeightOneSpectrum (𝓞 ℚ),
              ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                  W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                    fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
              (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
                ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                  ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ₀,
                    (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                      W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
              (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                  ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))))
    (WA₀ : GL (Fin 2) ℝ → ℂ) (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hinv : Continuous φ ∧
        IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ ∧
        (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
        (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ g) ∧
        (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 0 g = 0) ∧
        (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g‖) ∧
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g)) ∧
        Measurable Wf ∧
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf g‖) ∧
        (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf (g * u) = Wf g) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
          (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
          (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
          (∃ r : v.adicCompletionIntegers ℚ,
            ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
              algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
          ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
        (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
          (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ p h))) ∈
            AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
        (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ g) ∧
        (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
          (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ) ∧
        (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g))
    (hlevel : ∀ (k : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level → Wf (finFactor (g * placeEmbed ℚ p k)) = Wf (finFactor g))
    (hW1 : Wf 1 ≠ 0) :
    ∃ x₀ : p.adicCompletion ℚ, Valued.v x₀ ≤ WithZero.exp (1 : ℤ) ∧
      let Wf' : finiteAdelicGL2Subgroup ℚ → ℂ := (fun g : finiteAdelicGL2Subgroup ℚ => Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g)
      Wf' 1 ≠ 0 ∧
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m' : ℕ, m₀ ≤ m' →
        (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : p.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ m') → n ≠ 0 →
          localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k →
          Wf' g = 0) := by
  classical

  obtain ⟨ψ, -, hψO, ⟨r, hr⟩, hE⟩ := hinv.2.2.2.2.2.2.2.2.2.2.1 p
  have hπ0 : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0 := hπall p
  have hπv := hϖ p
  have hψO' : ∀ s : p.adicCompletion ℚ, Valued.v s ≤ 1 → ψ s = 1 := fun s hs =>
    hψO ⟨s, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hs⟩
  have hr1 : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp r.2

  set cN : ℕ := (Associates.mk p.asIdeal).count (Associates.mk Θ.level).factors with hcN_def
  have hNc : AdelicLevel.idealBound (𝓞 ℚ) Θ.level p = WithZero.exp (-(cN : ℤ)) :=
    P2mOnePrimeShape.idealBound_eq_exp_count Θ.level_ne_bot

  refine ⟨algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p), ?_, ?_⟩
  · rw [map_div₀, hπv, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
    calc Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) * WithZero.exp (1 : ℤ)
        ≤ 1 * WithZero.exp (1 : ℤ) := mul_le_mul_left hr1 _
      _ = WithZero.exp (1 : ℤ) := one_mul _
  set x₀ : p.adicCompletion ℚ := algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r /
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) with hx₀_def
  have hx₀v : Valued.v x₀ ≤ WithZero.exp (1 : ℤ) := by
    rw [hx₀_def, map_div₀, hπv, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
    calc Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) r) * WithZero.exp (1 : ℤ)
        ≤ 1 * WithZero.exp (1 : ℤ) := mul_le_mul_left hr1 _
      _ = WithZero.exp (1 : ℤ) := one_mul _
  have hx₀ψ : ψ x₀ ≠ 1 := hr
  intro Wf'
  refine ⟨?_, cN + 2, by omega, ?_⟩
  ·
    show Wf (finFactor (((1 : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) -
        Wf 1 ≠ 0
    have h1 : Wf (finFactor (placeEmbed ℚ p (unipotent x₀))) = ψ x₀ * Wf 1 := by
      have h := hE x₀ 1
      rwa [mul_one, P2mOnePrimeShapeAdelic.finFactor_one] at h
    rw [OneMemClass.coe_one, one_mul, h1, ← sub_one_mul]
    exact mul_ne_zero (sub_ne_zero.2 hx₀ψ) hW1
  · intro m' hm' g x n k hk hn hg
    show Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g = 0

    set h : GL (Fin 2) (p.adicCompletion ℚ) :=
      unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k
      with hh_def
    set G₀ : AdelicGL2 (𝓞 ℚ) ℚ := (g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p h⁻¹ with hG₀_def
    have hG₀ : localAt ℚ p G₀ = 1 := by
      rw [hG₀_def, map_mul, hg, P2mOnePrimeShapeAdelic.localAt_placeEmbed, mul_inv_cancel]
    have hGe : (g : AdelicGL2 (𝓞 ℚ) ℚ) = G₀ * placeEmbed ℚ p h := by
      rw [hG₀_def, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

    set W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun y => Wf (finFactor (G₀ * placeEmbed ℚ p y)) with hW_def
    have hWg : Wf g = W h := by
      show Wf g = Wf (finFactor (G₀ * placeEmbed ℚ p h))
      rw [← hGe, P2mOnePrimeShapeAdelic.finFactor_coe]
    have hWg' : Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) = W (h * unipotent x₀) := by
      show _ = Wf (finFactor (G₀ * placeEmbed ℚ p (h * unipotent x₀)))
      rw [map_mul, ← mul_assoc, ← hGe]
    have hWE : ∀ (t : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)),
        W (unipotent t * y) = ψ t * W y := by
      intro t y
      show Wf (finFactor (G₀ * placeEmbed ℚ p (unipotent t * y))) = ψ t * Wf (finFactor (G₀ * placeEmbed ℚ p y))
      rw [map_mul, ← mul_assoc, ← P2mOnePrimeShapeAdelic.placeEmbed_mul_comm p hG₀ (unipotent t), mul_assoc]
      exact hE t _
    have hWK : ∀ (y : GL (Fin 2) (p.adicCompletion ℚ)), ∀ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level,
        W (y * k') = W y := by
      intro y k' hk'
      show Wf (finFactor (G₀ * placeEmbed ℚ p (y * k'))) = Wf (finFactor (G₀ * placeEmbed ℚ p y))
      rw [map_mul, ← mul_assoc]
      exact hlevel k' _ hk'
    rw [hWg', hWg, hh_def]
    exact P2mOnePrimeShape.local_shell ψ hψO' x₀ hx₀v hx₀ψ _ hπ0 hπv Θ.level cN hNc W hWE hWK hm' hk x hn

end S_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat (solution)
