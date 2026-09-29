-- Prove2me | solution 1 for AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/06d12e28-bca6-5eed-81b0-92a45b9e0d7d

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
import Theorems.Thm_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace P2mCentralDensity

section LocalField

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem charZero_adicCompletion : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

theorem norm_eq_toNNReal (x : v.adicCompletion K) :
    ‖x‖ = (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) : ℝ≥0) :=
  NumberField.FinitePlace.norm_def v x

theorem valued_eq_of_norm_eq {x y : v.adicCompletion K} (h : ‖x‖ = ‖y‖) : Valued.v x = Valued.v y := by
  rw [norm_eq_toNNReal, norm_eq_toNNReal, NNReal.coe_inj] at h
  exact (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).injective h

theorem exists_uniformizer :
    ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨algebraMap K (v.adicCompletion K) π, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  change Valued.v (((WithVal.equiv (v.valuation K)).symm π : v.adicCompletion K)) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hπ

variable {K v}

theorem uniformizer_ne_zero {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h
  rw [h, map_zero] at hϖ
  exact WithZero.coe_ne_zero hϖ.symm

theorem norm_uniformizer_lt_one {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ‖ϖ‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

theorem parity_uniformizer {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    ∀ a t : v.adicCompletion K, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2 := by
  intro a t ht h
  have hϖ0 := uniformizer_ne_zero hϖ
  by_cases ha : a = 0
  · rw [ha, norm_zero, zero_pow two_ne_zero] at h
    have : ‖ϖ‖ * ‖t‖ ^ 2 ≠ 0 :=
      mul_ne_zero (norm_ne_zero_iff.2 hϖ0) (pow_ne_zero _ (norm_ne_zero_iff.2 ht))
    exact this h.symm
  · rw [← norm_pow, ← norm_pow, ← norm_mul] at h
    have hval := valued_eq_of_norm_eq K v h
    rw [map_pow, map_mul, map_pow, hϖ] at hval
    have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
    have := congrArg WithZero.log hval
    have hexp : (WithZero.exp (-1 : ℤ)) ≠ 0 := WithZero.coe_ne_zero
    rw [WithZero.log_pow, WithZero.log_mul hexp (pow_ne_zero _ hvt), WithZero.log_pow,
      WithZero.log_exp] at this
    have h2 : (2 : ℕ) • (Valued.v a).log = 2 * (Valued.v a).log := by simp [two_mul]
    have h3 : (2 : ℕ) • (Valued.v t).log = 2 * (Valued.v t).log := by simp [two_mul]
    rw [h2, h3] at this
    omega

end LocalField

section Algebra

variable {F : Type*} [Field F]

def Xmat (ϖ : F) : Matrix (Fin 2) (Fin 2) F := !![0, 1; ϖ, 0]

def torusMat (ϖ p r : F) : Matrix (Fin 2) (Fin 2) F := !![p, r; ϖ * r, p]

theorem det_torusMat (ϖ p r : F) : (torusMat ϖ p r).det = p ^ 2 - ϖ * r ^ 2 := by
  simp [torusMat, Matrix.det_fin_two]; ring

def sMat (α β : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; α, β]

theorem det_sMat (α β : F) : (sMat α β).det = β := by
  simp [sMat, Matrix.det_fin_two]

def sGL (α : F) (β : Fˣ) : GL (Fin 2) F where
  val := sMat α β
  inv := !![1, 0; -α * (β⁻¹ : Fˣ), (β⁻¹ : Fˣ)]
  val_inv := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_comm α, ← mul_assoc, mul_inv_cancel₀ β.ne_zero, one_mul, add_neg_cancel]
  inv_val := by
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [sMat, Matrix.mul_apply, Fin.sum_univ_two]
    try rw [mul_comm ((β : F)⁻¹) α, neg_add_cancel]

@[scoped simp] theorem sGL_coe (α : F) (β : Fˣ) : ((sGL α β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = sMat α β := rfl

theorem sGL_mul (α α' : F) (β β' : Fˣ) : sGL α β * sGL α' β' = sGL (α + β * α') (β * β') := by
  apply Units.ext
  simp only [Units.val_mul, sGL_coe, sMat, Units.val_mul]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sGL_zero_one : sGL (0 : F) 1 = 1 := by
  apply Units.ext
  simp only [sGL_coe, sMat, Units.val_one]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp

def torusGL (ϖ p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) : GL (Fin 2) F where
  val := torusMat ϖ p r
  inv := !![p / (p ^ 2 - ϖ * r ^ 2), -r / (p ^ 2 - ϖ * r ^ 2);
    -(ϖ * r) / (p ^ 2 - ϖ * r ^ 2), p / (p ^ 2 - ϖ * r ^ 2)]
  val_inv := by
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  inv_val := by
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

@[scoped simp] theorem torusGL_coe (ϖ p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) :
    ((torusGL ϖ p r h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = torusMat ϖ p r := rfl

theorem torusGL_inv_coe (ϖ p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) :
    (((torusGL ϖ p r h)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![p / (p ^ 2 - ϖ * r ^ 2), -r / (p ^ 2 - ϖ * r ^ 2);
        -(ϖ * r) / (p ^ 2 - ϖ * r ^ 2), p / (p ^ 2 - ϖ * r ^ 2)] := rfl

theorem sGL_inv_coe (α : F) (β : Fˣ) :
    (((sGL α β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -α * (β⁻¹ : Fˣ), (β⁻¹ : Fˣ)] := rfl

def XGL (ϖ : F) (hϖ : ϖ ≠ 0) : GL (Fin 2) F := torusGL ϖ 0 1 (by simpa using hϖ)

theorem XGL_coe (ϖ : F) (hϖ : ϖ ≠ 0) : ((XGL ϖ hϖ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Xmat ϖ := by
  rw [XGL, torusGL_coe]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp [torusMat, Xmat]

theorem commute_Xmat_iff (ϖ : F) (M : Matrix (Fin 2) (Fin 2) F) :
    M * Xmat ϖ = Xmat ϖ * M ↔ M 1 1 = M 0 0 ∧ M 1 0 = ϖ * M 0 1 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Xmat, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    exact ⟨h01.symm, by rw [← h00, mul_comm]⟩
  · rintro ⟨h1, h2⟩
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [Xmat, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, mul_comm]

theorem eq_torusMat_of_commute {ϖ : F} {M : Matrix (Fin 2) (Fin 2) F} (h : M * Xmat ϖ = Xmat ϖ * M) :
    M = torusMat ϖ (M 0 0) (M 0 1) := by
  obtain ⟨h1, h2⟩ := (commute_Xmat_iff ϖ M).1 h
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [torusMat, h1, h2]

theorem torusMat_commute (ϖ p r : F) : torusMat ϖ p r * Xmat ϖ = Xmat ϖ * torusMat ϖ p r := by
  rw [commute_Xmat_iff]; simp [torusMat]

theorem mem_centralizer_XGL_iff (ϖ : F) (hϖ : ϖ ≠ 0) (g : GL (Fin 2) F) :
    g ∈ Subgroup.centralizer ({XGL ϖ hϖ} : Set (GL (Fin 2) F)) ↔
      (g : Matrix (Fin 2) (Fin 2) F) * Xmat ϖ = Xmat ϖ * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Units.val_mul, XGL_coe] using this
  · intro h
    apply Units.ext
    simp only [Units.val_mul, XGL_coe]
    exact h

theorem sGL_mem_centralizer_iff (ϖ : F) (hϖ : ϖ ≠ 0) (α : F) (β : Fˣ) :
    sGL α β ∈ Subgroup.centralizer ({XGL ϖ hϖ} : Set (GL (Fin 2) F)) ↔ α = 0 ∧ β = 1 := by
  rw [mem_centralizer_XGL_iff, sGL_coe, commute_Xmat_iff]
  simp only [sMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, Units.ext (by simpa using h1)⟩
    simpa using h2
  · rintro ⟨rfl, rfl⟩; simp

end Algebra

section TopologyPart

variable {F : Type*} [NormedField F]

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → GL (Fin 2) F}
    (hval : ∀ i j, Continuous fun x => ((f x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

theorem continuous_entry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_det : Continuous fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det :=
  Units.continuous_val.matrix_det

theorem continuous_sGL : Continuous fun q : Fˣ × F => sGL q.2 q.1 := by
  have hb : Continuous fun q : Fˣ × F => ((q.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have hbi : Continuous fun q : Fˣ × F => (((q.1⁻¹ : Fˣ) : Fˣ) : F) := Units.continuous_val.comp continuous_fst.inv
  have ha : Continuous fun q : Fˣ × F => q.2 := continuous_snd
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact ha
    · exact hb
  · simp only [sGL_inv_coe]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact (ha.neg).mul hbi
    · exact hbi

end TopologyPart

section Elements

variable {F : Type*} [Field F]

theorem coe_scalar (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  change Matrix.scalar (Fin 2) (c : F) = _
  rw [Matrix.scalar_apply]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem coe_scalar_mul (c : Fˣ) (g : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

theorem scalar_mul_comm (c : Fˣ) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  rw [coe_scalar_mul, Units.val_mul, coe_scalar, Matrix.mul_smul, Matrix.mul_one]

theorem torusMat_eq_smul_add (ϖ p r : F) : torusMat ϖ p r = p • (1 : Matrix (Fin 2) (Fin 2) F) + r • Xmat ϖ := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [torusMat, Xmat, mul_comm]

variable (ϖ : F) (hϖ : ϖ ≠ 0) (hns : ∀ p r : F, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

include hns in
theorem one_sub_ne_zero (s : F) : 1 - ϖ * s ^ 2 ≠ 0 := by
  intro h
  have := hns 1 s (by rw [one_pow]; exact h)
  rw [this] at h; simp at h

def pOf (s : F) : F := (1 + ϖ * s ^ 2) / (1 - ϖ * s ^ 2)

def rOf (s : F) : F := 2 * s / (1 - ϖ * s ^ 2)

include hns in
theorem pOf_sq_sub (s : F) : pOf ϖ s ^ 2 - ϖ * rOf ϖ s ^ 2 = 1 := by
  have h := one_sub_ne_zero ϖ hns s
  simp only [pOf, rOf]
  field_simp
  ring

include hns in
theorem pOf_sq_sub_ne_zero (s : F) : pOf ϖ s ^ 2 - ϖ * rOf ϖ s ^ 2 ≠ 0 := by
  rw [pOf_sq_sub ϖ hns]; exact one_ne_zero

def uEl (s : F) : GL (Fin 2) F := torusGL ϖ (pOf ϖ s) (rOf ϖ s) (pOf_sq_sub_ne_zero ϖ hns s)

theorem uEl_zero : uEl ϖ hns 0 = 1 := by
  apply Units.ext
  simp only [uEl, torusGL_coe, torusMat, pOf, rOf, Units.val_one]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp

theorem det_uEl (s : F) : Matrix.GeneralLinearGroup.det (uEl ϖ hns s) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, uEl, torusGL_coe, det_torusMat, pOf_sq_sub ϖ hns, Units.val_one]

def gammaPR (c : Fˣ) (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) c * torusGL ϖ p r h

theorem coe_gammaPR (c : Fˣ) (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) :
    ((gammaPR ϖ c p r h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (c : F) • torusMat ϖ p r := by
  rw [gammaPR, coe_scalar_mul, torusGL_coe]

def gammaEl (c : Fˣ) (s : F) : GL (Fin 2) F := gammaPR ϖ c (pOf ϖ s) (rOf ϖ s) (pOf_sq_sub_ne_zero ϖ hns s)

theorem gammaEl_eq (c : Fˣ) (s : F) :
    gammaEl ϖ hns c s = Matrix.GeneralLinearGroup.scalar (Fin 2) c * uEl ϖ hns s := rfl

theorem det_gammaEl (c : Fˣ) (s : F) : Matrix.GeneralLinearGroup.det (gammaEl ϖ hns c s) = c ^ 2 := by
  rw [gammaEl_eq, map_mul, det_uEl, mul_one]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_scalar]
  simp [sq]

theorem coe_gammaEl (c : Fˣ) (s : F) :
    ((gammaEl ϖ hns c s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • torusMat ϖ (pOf ϖ s) (rOf ϖ s) :=
  coe_gammaPR ϖ c _ _ _

include hns in
theorem rOf_ne_zero (h2 : (2 : F) ≠ 0) {s : F} (hs : s ≠ 0) : rOf ϖ s ≠ 0 := by
  simp only [rOf]
  intro h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact (mul_ne_zero h2 hs) h
  · exact one_sub_ne_zero ϖ hns s h

include hϖ in

theorem isRegularSemisimple_gammaEl (h2 : (2 : F) ≠ 0) (c : Fˣ) {s : F} (hs : s ≠ 0) :
    AutomorphicForm.IsRegularSemisimple (gammaEl ϖ hns c s) := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, coe_gammaEl]
  have h1 := pOf_sq_sub ϖ hns s
  have ht : Matrix.trace ((c : F) • torusMat ϖ (pOf ϖ s) (rOf ϖ s)) = 2 * (c : F) * pOf ϖ s := by
    simp [Matrix.trace_fin_two, torusMat]; ring
  have hd : Matrix.det ((c : F) • torusMat ϖ (pOf ϖ s) (rOf ϖ s)) =
      (c : F) ^ 2 * (pOf ϖ s ^ 2 - ϖ * rOf ϖ s ^ 2) := by
    simp [Matrix.det_fin_two, torusMat]; ring
  have key : (2 * (c : F) * pOf ϖ s) ^ 2 - 4 * ((c : F) ^ 2 * (pOf ϖ s ^ 2 - ϖ * rOf ϖ s ^ 2)) =
      4 * (c : F) ^ 2 * (ϖ * rOf ϖ s ^ 2) := by
    linear_combination (4 * (c : F) ^ 2) * h1 - (4 * (c : F) ^ 2) * h1 + (0 : F) * h1
  rw [ht, hd, key]
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  exact mul_ne_zero (mul_ne_zero h4 (pow_ne_zero _ c.ne_zero)) (mul_ne_zero hϖ (pow_ne_zero _ (rOf_ne_zero ϖ hns h2 hs)))

theorem sGL_inv_Xmat_sGL (α : F) (β : Fˣ) :
    (((sGL α β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Xmat ϖ * sMat α β =
      !![α, (β : F); (ϖ - α ^ 2) / β, -α] := by
  rw [sGL_inv_coe]
  have hb : (β : F) ≠ 0 := β.ne_zero
  ext i j : 1; fin_cases i <;> fin_cases j <;>
    simp [Xmat, sMat, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem coe_conj_gammaPR (c : Fˣ) {p r : F} (hD : p ^ 2 - ϖ * r ^ 2 ≠ 0) (α : F) (β : Fˣ) :
    (((sGL α β)⁻¹ * gammaPR ϖ c p r hD * sGL α β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (p • (1 : Matrix (Fin 2) (Fin 2) F) + r • !![α, (β : F); (ϖ - α ^ 2) / β, -α]) := by
  rw [Units.val_mul, Units.val_mul, coe_gammaPR, torusMat_eq_smul_add, ← sGL_inv_Xmat_sGL ϖ α β, sGL_coe]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, smul_add]
  congr 1
  have : (((sGL α β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * sMat α (β : F) = 1 := by
    rw [← sGL_coe α β, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this]

end Elements

section Limits

variable {F : Type*} [NormedField F] (ϖ : F) (hns : ∀ p r : F, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

include hns in
theorem continuous_pOf : Continuous (pOf ϖ) :=
  (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).div
    (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))) (one_sub_ne_zero ϖ hns)

include hns in
theorem continuous_rOf : Continuous (rOf ϖ) :=
  (continuous_const.mul continuous_id).div
    (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))) (one_sub_ne_zero ϖ hns)

theorem continuous_uEl : Continuous (uEl ϖ hns) := by
  have hp := continuous_pOf ϖ hns
  have hr := continuous_rOf ϖ hns
  have hD : Continuous fun s : F => pOf ϖ s ^ 2 - ϖ * rOf ϖ s ^ 2 := (hp.pow 2).sub (continuous_const.mul (hr.pow 2))
  have hD0 := pOf_sq_sub_ne_zero ϖ hns
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [uEl, torusGL_coe]
    fin_cases i <;> fin_cases j
    · exact hp
    · exact hr
    · exact continuous_const.mul hr
    · exact hp
  · simp only [uEl, torusGL_inv_coe]
    fin_cases i <;> fin_cases j
    · exact hp.div hD hD0
    · exact hr.neg.div hD hD0
    · exact (continuous_const.mul hr).neg.div hD hD0
    · exact hp.div hD hD0

theorem tendsto_gammaEl (c : Fˣ) :
    Tendsto (fun s : F => gammaEl ϖ hns c s) (𝓝 0) (𝓝 (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := by
  have h := ((continuous_uEl ϖ hns).tendsto 0).const_mul (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  rw [uEl_zero, mul_one] at h
  exact h

end Limits

section Lift

variable {F : Type*} [NormedField F]

open Classical in

def liftFn (fv : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F → ℂ :=
  fun M => if h : M.det = 0 then 0 else fv (z * Matrix.GeneralLinearGroup.mkOfDetNeZero M h)

theorem liftFn_of_det_eq_zero (fv : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) {M : Matrix (Fin 2) (Fin 2) F}
    (h : M.det = 0) : liftFn fv z M = 0 := by
  simp only [liftFn, h, dif_pos]

theorem liftFn_of_det_ne_zero (fv : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) {M : Matrix (Fin 2) (Fin 2) F}
    (h : M.det ≠ 0) : liftFn fv z M = fv (z * Matrix.GeneralLinearGroup.mkOfDetNeZero M h) := by
  simp only [liftFn, h, dif_neg, not_false_eq_true]

theorem liftFn_coe (fv : GL (Fin 2) F → ℂ) (z g : GL (Fin 2) F) :
    liftFn fv z (g : Matrix (Fin 2) (Fin 2) F) = fv (z * g) := by
  have h : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [liftFn_of_det_ne_zero fv z h]
  congr 2
  exact Units.ext rfl

theorem isCompact_liftSupport (fv : GL (Fin 2) F → ℂ) (hfv : HasCompactSupport fv) (z : GL (Fin 2) F) :
    IsCompact (((↑) : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) '' ((fun g => z⁻¹ * g) '' tsupport fv)) :=
  (hfv.isCompact.image (continuous_const.mul continuous_id)).image Units.continuous_val

theorem liftFn_eq_zero_of_not_mem (fv : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) {M : Matrix (Fin 2) (Fin 2) F}
    (hM : M ∉ ((↑) : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) '' ((fun g => z⁻¹ * g) '' tsupport fv)) :
    liftFn fv z M = 0 := by
  by_cases h : M.det ≠ 0
  · rw [liftFn_of_det_ne_zero fv z h]
    by_contra hne
    apply hM
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M h, ⟨z * Matrix.GeneralLinearGroup.mkOfDetNeZero M h,
      subset_tsupport _ (Function.mem_support.2 hne), by group⟩, rfl⟩
  · rw [not_ne_iff] at h; exact liftFn_of_det_eq_zero fv z h

theorem hasCompactSupport_liftFn (fv : GL (Fin 2) F → ℂ) (hfv : HasCompactSupport fv) (z : GL (Fin 2) F) :
    HasCompactSupport (liftFn fv z) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F))
  exact HasCompactSupport.intro (isCompact_liftSupport fv hfv z) (fun M hM => liftFn_eq_zero_of_not_mem fv z hM)

theorem continuous_mkOfDetNeZero_subtype :
    Continuous fun M : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0} =>
      Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 M.2 := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · exact (continuous_subtype_val.matrix_elem i j)
  · have h : ∀ M : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0},
        (((Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 M.2)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (M.1.det)⁻¹ • M.1.adjugate := by
      intro M
      rw [Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.inv_def, Ring.inverse_eq_inv']
    simp_rw [h]
    exact ((continuous_subtype_val.matrix_det.inv₀ (fun M => M.2)).smul
      continuous_subtype_val.matrix_adjugate).matrix_elem i j

theorem isLocallyConstant_liftFn (fv : GL (Fin 2) F → ℂ) (hlc : IsLocallyConstant fv) (hfv : HasCompactSupport fv)
    (z : GL (Fin 2) F) : IsLocallyConstant (liftFn fv z) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F))
  rw [IsLocallyConstant.iff_exists_open]
  intro M
  by_cases hM : M.det ≠ 0
  ·
    have hlc' : IsLocallyConstant fun g : GL (Fin 2) F => fv (z * g) :=
      hlc.comp_continuous (continuous_const.mul continuous_id)
    obtain ⟨V, hV, hgV, hconst⟩ := hlc'.exists_open (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)
    set O : Set (Matrix (Fin 2) (Fin 2) F) := {M | M.det ≠ 0} with hO
    have hOopen : IsOpen O := isOpen_ne_fun (continuous_id.matrix_det) continuous_const
    set U : Set (Matrix (Fin 2) (Fin 2) F) := ((↑) : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0} → _) ''
      ((fun M : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0} => Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 M.2) ⁻¹' V)
      with hU
    refine ⟨U, hOopen.isOpenMap_subtype_val _ (hV.preimage continuous_mkOfDetNeZero_subtype), ⟨⟨M, hM⟩, hgV, rfl⟩,
      ?_⟩
    rintro M' ⟨⟨M'', hM''⟩, hV', rfl⟩
    change liftFn fv z M'' = liftFn fv z M
    rw [liftFn_of_det_ne_zero fv z hM'', liftFn_of_det_ne_zero fv z hM]
    exact hconst _ hV'
  ·
    rw [not_ne_iff] at hM
    set Kc := ((↑) : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) '' ((fun g => z⁻¹ * g) '' tsupport fv) with hKc
    have hKcl : IsClosed Kc := (isCompact_liftSupport fv hfv z).isClosed
    have hMK : M ∉ Kc := by
      rintro ⟨g, -, rfl⟩
      have : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
      exact this hM
    refine ⟨Kcᶜ, hKcl.isOpen_compl, hMK, fun M' hM' => ?_⟩
    rw [liftFn_eq_zero_of_not_mem fv z hM', liftFn_eq_zero_of_not_mem fv z hMK]

theorem liftFn_smul (fv : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) (p : Fˣ) (M : Matrix (Fin 2) (Fin 2) F) :
    liftFn fv z ((p : F) • M) = liftFn (fun g => fv (Matrix.GeneralLinearGroup.scalar (Fin 2) p * g)) z M := by
  by_cases h : M.det ≠ 0
  · have hp : ((p : F) • M).det ≠ 0 := by
      rw [Matrix.det_smul, Fintype.card_fin]; exact mul_ne_zero (pow_ne_zero _ p.ne_zero) h
    rw [liftFn_of_det_ne_zero fv z hp, liftFn_of_det_ne_zero _ z h]
    congr 1
    rw [← mul_assoc, scalar_mul_comm, mul_assoc]
    congr 1
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, coe_scalar_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  · rw [not_ne_iff] at h
    rw [liftFn_of_det_eq_zero _ z h, liftFn_of_det_eq_zero fv z]
    rw [Matrix.det_smul, h, mul_zero]

end Lift

section Annulus

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isCompact_units_annulus' {r₁ : ℝ} (r₂ : ℝ) (hr₁ : 0 < r₁) :
    IsCompact {b : (v.adicCompletion K)ˣ | r₁ ≤ ‖(b : v.adicCompletion K)‖ ∧ ‖(b : v.adicCompletion K)‖ ≤ r₂} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himg : ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) ''
      {b : (v.adicCompletion K)ˣ | r₁ ≤ ‖(b : v.adicCompletion K)‖ ∧ ‖(b : v.adicCompletion K)‖ ≤ r₂} =
      {x : v.adicCompletion K | r₁ ≤ ‖x‖} ∩ Metric.closedBall (0 : v.adicCompletion K) r₂ := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨b, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hx : x ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact lt_irrefl _ (hr₁.trans_le h1)
      exact ⟨Units.mk0 x hx, ⟨h1, h2⟩, rfl⟩
  rw [himg]
  exact (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)

end Annulus

section ChangeOfVariables

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μF : Measure (v.adicCompletion K)) [μF.IsAddHaarMeasure]
  (μU : Measure (v.adicCompletion K)ˣ) [μU.IsHaarMeasure]

theorem secondCountableTopology_units' : SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

attribute [local instance] secondCountableTopology_units'

theorem exists_integral_comp_mul (t : (v.adicCompletion K)ˣ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ h : v.adicCompletion K → ℂ,
      ∫ a, h ((t : v.adicCompletion K) * a) ∂μF = (θ : ℂ) * ∫ a, h a ∂μF := by
  set e : v.adicCompletion K ≃+ v.adicCompletion K := AddAut.mulLeft' t with he
  have hecoe : ∀ a, e a = (t : v.adicCompletion K) * a := fun a => rfl
  have hec : Continuous e := continuous_const.mul continuous_id
  have hesc : Continuous e.symm := by
    have : (e.symm : v.adicCompletion K → v.adicCompletion K) = fun a => ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * a := by
      funext a
      apply e.injective
      rw [e.apply_symm_apply, hecoe, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact continuous_const.mul continuous_id
  haveI : (Measure.map e μF).IsAddHaarMeasure := e.isAddHaarMeasure_map μF hec hesc
  set θ := (Measure.map e μF).addHaarScalarFactor μF with hθ
  have hmap : Measure.map e μF = θ • μF := Measure.isAddLeftInvariant_eq_smul _ _
  have hθpos : 0 < θ := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨θ, hθpos, fun h => ?_⟩
  have hme : MeasurableEmbedding e := by
    have : (e : v.adicCompletion K → v.adicCompletion K) =
        (Homeomorph.mulLeft₀ (t : v.adicCompletion K) t.ne_zero : v.adicCompletion K → v.adicCompletion K) := by
      funext a; rfl
    rw [this]; exact (Homeomorph.mulLeft₀ (t : v.adicCompletion K) t.ne_zero).measurableEmbedding
  calc ∫ a, h ((t : v.adicCompletion K) * a) ∂μF = ∫ a, h a ∂(Measure.map e μF) := by
        rw [hme.integral_map]; rfl
    _ = (θ : ℂ) * ∫ a, h a ∂μF := by
        rw [hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem integral_chart_change (Θ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) (ϖ : v.adicCompletion K)
    (t : (v.adicCompletion K)ˣ)
    (hint : Integrable (fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      Θ (1 + (t : v.adicCompletion K) • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2])) (μU.prod μF)) :
    ∃ θ : ℝ, 0 < θ ∧
      ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
        Θ (1 + (t : v.adicCompletion K) • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(μU.prod μF) =
      (θ : ℂ) * ∫ b, ∫ a, Θ (1 + !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) ∂μF ∂μU := by
  obtain ⟨θ, hθ, hscale⟩ := exists_integral_comp_mul K v μF t
  refine ⟨θ, hθ, ?_⟩

  have hmat : ∀ (β : (v.adicCompletion K)ˣ) (α : v.adicCompletion K),
      (t : v.adicCompletion K) • !![α, ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ - α ^ 2) / ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K), -α] =
        !![(t : v.adicCompletion K) * α, (((t * β : (v.adicCompletion K)ˣ)) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - ((t : v.adicCompletion K) * α) ^ 2) /
            (((t * β : (v.adicCompletion K)ˣ)) : v.adicCompletion K), -((t : v.adicCompletion K) * α)] := by
    intro β α
    have hb : ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := β.ne_zero
    have ht : (t : v.adicCompletion K) ≠ 0 := t.ne_zero
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Units.val_mul] <;> field_simp <;> ring
  have hptw : ∀ (b : (v.adicCompletion K)ˣ) (a : v.adicCompletion K),
      Θ (1 + (t : v.adicCompletion K) • !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) =
        Θ (1 + !![(t : v.adicCompletion K) * a, (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - ((t : v.adicCompletion K) * a) ^ 2) /
            (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K), -((t : v.adicCompletion K) * a)]) :=
    fun b a => by rw [hmat b a]
  rw [integral_prod _ hint]
  simp_rw [hptw]
  have hin : ∀ b : (v.adicCompletion K)ˣ,
      ∫ a, Θ (1 + !![(t : v.adicCompletion K) * a, (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - ((t : v.adicCompletion K) * a) ^ 2) /
            (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K), -((t : v.adicCompletion K) * a)]) ∂μF =
        (θ : ℂ) * ∫ a, Θ (1 + !![a, (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - a ^ 2) / (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K), -a]) ∂μF :=
    fun b => hscale (fun a => Θ (1 + !![a, (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - a ^ 2) / (((t * b : (v.adicCompletion K)ˣ)) : v.adicCompletion K), -a]))
  simp_rw [hin]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self (fun b : (v.adicCompletion K)ˣ => ∫ a, Θ (1 + !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ * (t : v.adicCompletion K) ^ 2 - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) ∂μF) t

end ChangeOfVariables

section Main

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem t2Space_GL : T2Space (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space

attribute [local instance] t2Space_GL locallyCompactSpace_localGL secondCountableTopology_units'

theorem continuous_scalar : Continuous fun p : (v.adicCompletion K)ˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) p := by
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [coe_scalar]
    exact (Units.continuous_val.smul continuous_const).matrix_elem i j
  · simp only [← map_inv, coe_scalar]
    exact ((Units.continuous_val.comp continuous_inv).smul continuous_const).matrix_elem i j

variable {K v}
variable (ϖ : v.adicCompletion K) (hϖ0 : ϖ ≠ 0) (hns : ∀ p r : v.adicCompletion K, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

theorem apply_conj_eq_liftFn (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (c : (v.adicCompletion K)ˣ)
    (s : v.adicCompletion K) (α : v.adicCompletion K) (β : (v.adicCompletion K)ˣ) :
    fv ((sGL α β)⁻¹ * gammaEl ϖ hns c s * sGL α β) =
      liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
        (pOf ϖ s • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) +
          rOf ϖ s • !![α, ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K);
            (ϖ - α ^ 2) / ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K), -α]) := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hz
  set w := (sGL α β)⁻¹ * gammaEl ϖ hns c s * sGL α β with hw
  have hcoe : ((w : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = _ :=
    coe_conj_gammaPR ϖ c (pOf_sq_sub_ne_zero ϖ hns s) α β
  have hval : (((z⁻¹ * w : GL (Fin 2) (v.adicCompletion K))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      pOf ϖ s • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) +
        rOf ϖ s • !![α, ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ - α ^ 2) / ((β : (v.adicCompletion K)ˣ) : v.adicCompletion K), -α] := by
    rw [hz, ← map_inv, coe_scalar_mul, hcoe, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ c.ne_zero, one_smul]
  calc fv w = fv (z * (z⁻¹ * w)) := by rw [mul_inv_cancel_left]
    _ = _ := by rw [← liftFn_coe fv z (z⁻¹ * w), hval]

theorem hasCompactSupport_chart (Θ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) (hΘc : HasCompactSupport Θ)
    (hpar : ∀ a t : v.adicCompletion K, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2) {t : v.adicCompletion K} (ht : t ≠ 0) :
    HasCompactSupport fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      Θ (1 + t • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) := by

  obtain ⟨B, hB1, hB⟩ : ∃ B : ℝ, 1 ≤ B ∧ ∀ M, Θ M ≠ 0 → ∀ i j, ‖M i j‖ ≤ B := by
    have hbd : ∀ i j : Fin 2, ∃ B : ℝ, ∀ M ∈ tsupport Θ, ‖M i j‖ ≤ B := fun i j =>
      hΘc.isCompact.exists_bound_of_continuousOn ((continuous_id.matrix_elem i j).continuousOn (s := tsupport Θ))
    choose Bf hBf using hbd
    refine ⟨max (max (max (Bf 0 0) (Bf 0 1)) (max (Bf 1 0) (Bf 1 1))) 1, le_max_right _ _, fun M hM i j => ?_⟩
    have h := hBf i j M (subset_tsupport _ (Function.mem_support.2 hM))
    refine h.trans (le_trans ?_ (le_max_left _ _))
    fin_cases i <;> fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hB0 : 0 < B := one_pos.trans_le hB1
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hϖn : 0 < ‖ϖ‖ := by
    have := hpar 0 1 one_ne_zero
    rw [norm_zero, norm_one, one_pow, mul_one, zero_pow two_ne_zero] at this
    exact lt_of_le_of_ne (norm_nonneg _) this
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_units_annulus' K v (B / ‖t‖) (r₁ := ‖t‖ * ‖ϖ‖ / B)
      (div_pos (mul_pos htn hϖn) hB0)).prod (isCompact_closedBall (0 : v.adicCompletion K) (B / ‖t‖))) ?_
  rintro ⟨β, α⟩ hq
  rw [Function.mem_support] at hq
  have hE := hB _ hq
  have hβn : 0 < ‖((β : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ := norm_pos_iff.2 β.ne_zero
  have e00 : ‖1 + t * α‖ ≤ B := by simpa [Matrix.add_apply, Matrix.smul_apply] using hE 0 0
  have e01 : ‖t‖ * ‖((β : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ B := by
    simpa [Matrix.add_apply, Matrix.smul_apply, norm_mul] using hE 0 1
  have e10 : ‖t‖ * (‖ϖ - α ^ 2‖ / ‖((β : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖) ≤ B := by
    simpa [Matrix.add_apply, Matrix.smul_apply, norm_mul, norm_div] using hE 1 0
  have hparα : ‖ϖ‖ ≤ ‖ϖ - α ^ 2‖ := by
    have hne : ‖ϖ‖ ≠ ‖-(α ^ 2)‖ := by
      rw [norm_neg, norm_pow]; intro h; exact hpar α 1 one_ne_zero (by rw [← h]; simp)
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]; exact le_max_left _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_iff₀ hB0]
    have h1 : ‖t‖ * (‖ϖ‖ / ‖((β : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖) ≤ B :=
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hparα hβn.le) htn.le).trans e10
    rw [mul_div_assoc', div_le_iff₀ hβn] at h1
    linarith
  · rw [le_div_iff₀ htn, mul_comm]; exact e01
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rw [le_div_iff₀ htn]
    have : ‖t * α‖ ≤ B := by
      have heq' : t * α = (1 + t * α) - 1 := by ring
      rw [heq', sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le e00 ?_)
      rw [norm_neg, norm_one]; exact hB1
    rw [mul_comm, ← norm_mul]; exact this

def sSeq (n : ℕ) : v.adicCompletion K := ϖ ^ (n + 1)

def tSeq (n : ℕ) : v.adicCompletion K := rOf ϖ (sSeq ϖ n) / pOf ϖ (sSeq ϖ n)

include hϖ0 in
theorem sSeq_ne_zero (n : ℕ) : sSeq ϖ n ≠ 0 := pow_ne_zero _ hϖ0

theorem tendsto_sSeq (hϖ1 : ‖ϖ‖ < 1) : Tendsto (sSeq ϖ) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1).comp (tendsto_add_atTop_nat 1)

theorem norm_one_add_sSeq (hϖ1 : ‖ϖ‖ < 1) (n : ℕ) : ‖1 + ϖ * sSeq ϖ n ^ 2‖ = 1 := by
  have hlt : ‖ϖ * sSeq ϖ n ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, sSeq, norm_pow]
    calc ‖ϖ‖ * (‖ϖ‖ ^ (n + 1)) ^ 2 ≤ ‖ϖ‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (pow_nonneg (norm_nonneg _) _)
            (pow_le_one₀ (norm_nonneg _) hϖ1.le)) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hϖ1
  have hne : ‖(1 : v.adicCompletion K)‖ ≠ ‖ϖ * sSeq ϖ n ^ 2‖ := by rw [norm_one]; exact (ne_of_gt hlt)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hlt.le]

theorem one_add_sSeq_ne_zero (hϖ1 : ‖ϖ‖ < 1) (n : ℕ) : 1 + ϖ * sSeq ϖ n ^ 2 ≠ 0 := fun h => by
  have := norm_one_add_sSeq ϖ hϖ1 n; rw [h, norm_zero] at this; exact zero_ne_one this

include hns in
theorem pOf_sSeq_ne_zero (hϖ1 : ‖ϖ‖ < 1) (n : ℕ) : pOf ϖ (sSeq ϖ n) ≠ 0 :=
  div_ne_zero (one_add_sSeq_ne_zero ϖ hϖ1 n) (one_sub_ne_zero ϖ hns _)

include hns in
theorem tSeq_eq (hϖ1 : ‖ϖ‖ < 1) (n : ℕ) : tSeq ϖ n = 2 * sSeq ϖ n / (1 + ϖ * sSeq ϖ n ^ 2) := by
  simp only [tSeq, rOf, pOf]
  rw [div_div_div_cancel_right₀ (one_sub_ne_zero ϖ hns (sSeq ϖ n))]

include hns in
theorem norm_tSeq (hϖ1 : ‖ϖ‖ < 1) (n : ℕ) : ‖tSeq ϖ n‖ = ‖(2 : v.adicCompletion K)‖ * ‖ϖ‖ ^ (n + 1) := by
  rw [tSeq_eq ϖ hns hϖ1, norm_div, norm_one_add_sSeq ϖ hϖ1, div_one, norm_mul, sSeq, norm_pow]

include hϖ0 hns in
theorem tSeq_ne_zero (hϖ1 : ‖ϖ‖ < 1) (h2 : (2 : v.adicCompletion K) ≠ 0) (n : ℕ) : tSeq ϖ n ≠ 0 := by
  rw [← norm_pos_iff, norm_tSeq ϖ hns hϖ1]
  exact mul_pos (norm_pos_iff.2 h2) (pow_pos (norm_pos_iff.2 hϖ0) _)

include hϖ0 hns in
theorem norm_tSeq_lt (hϖ1 : ‖ϖ‖ < 1) (h2 : (2 : v.adicCompletion K) ≠ 0) (n : ℕ) : ‖tSeq ϖ (n + 1)‖ < ‖tSeq ϖ n‖ := by
  rw [norm_tSeq ϖ hns hϖ1, norm_tSeq ϖ hns hϖ1, pow_succ]
  have : ‖ϖ‖ ^ (n + 1) * ‖ϖ‖ < ‖ϖ‖ ^ (n + 1) * 1 :=
    mul_lt_mul_of_pos_left hϖ1 (pow_pos (norm_pos_iff.2 hϖ0) _)
  rw [mul_one] at this
  exact mul_lt_mul_of_pos_left this (norm_pos_iff.2 h2)

include hns in
theorem tendsto_norm_tSeq (hϖ1 : ‖ϖ‖ < 1) : Tendsto (fun n => ‖tSeq ϖ n‖) atTop (𝓝 0) := by
  simp_rw [norm_tSeq ϖ hns hϖ1]
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg ϖ) hϖ1).comp (tendsto_add_atTop_nat 1)).const_mul
    ‖(2 : v.adicCompletion K)‖
  simpa using this

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μF : Measure (v.adicCompletion K)) [μF.IsAddHaarMeasure]
  (μU : Measure (v.adicCompletion K)ˣ) [μU.IsHaarMeasure]

include hϖ0 in

theorem chart_integral_eq_zero (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : IsLocalTestFn K v fv)
    (c : (v.adicCompletion K)ˣ) (hpar : ∀ a t : v.adicCompletion K, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (h2 : (2 : v.adicCompletion K) ≠ 0)
    {V : Set (GL (Fin 2) (v.adicCompletion K))} (hV1 : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ V)
    (hV : ∀ u ∈ V, ∀ u' ∈ V, ∀ g, fv (u * g * u') = fv g)
    {s : v.adicCompletion K} (hs : s ≠ 0) (pu : (v.adicCompletion K)ˣ) (hpu : (pu : v.adicCompletion K) = pOf ϖ s)
    (hpV : Matrix.GeneralLinearGroup.scalar (Fin 2) pu ∈ V)
    (hvan : ∀ τ : @Measure (localCentralizer K v (gammaEl ϖ hns c s)) (localCentralizerBorel K v (gammaEl ϖ hns c s)),
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (gammaEl ϖ hns c s)) τ →
        ∀ I : ℂ, IsOrbitalIntegral K v (gammaEl ϖ hns c s) τ fv I → I = 0) :
    ∫ b, ∫ a, liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (1 + !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ * (rOf ϖ s / pOf ϖ s) ^ 2 - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) ∂μF ∂μU = 0 := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hz
  set Θ := liftFn fv z with hΘ
  set t := rOf ϖ s / pOf ϖ s with htdef
  have hp0 : pOf ϖ s ≠ 0 := by rw [← hpu]; exact pu.ne_zero
  have ht0 : t ≠ 0 := div_ne_zero (rOf_ne_zero ϖ hns h2 hs) hp0

  have hcoord := AutomorphicForm.integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero K v fv hfv c
    ϖ hϖ0 hpar (pOf ϖ s) (rOf ϖ s) (pOf_sq_sub_ne_zero ϖ hns s) (rOf_ne_zero ϖ hns h2 hs)
    (uEl ϖ hns s) rfl (fun a b => sGL a b) (fun a b => rfl) μF μU hvan

  have habs : ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Θ ((pu : v.adicCompletion K) • M) = Θ M := by
    intro M
    rw [hΘ, liftFn_smul]
    congr 1
    funext g
    have := hV _ hpV 1 hV1 g
    rwa [mul_one] at this
  have hint_eq : ∀ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      fv ((sGL q.2 q.1)⁻¹ * (z * uEl ϖ hns s) * sGL q.2 q.1) =
        Θ (1 + t • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) := by
    intro q
    calc fv ((sGL q.2 q.1)⁻¹ * (z * uEl ϖ hns s) * sGL q.2 q.1)
        = Θ (pOf ϖ s • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) +
            rOf ϖ s • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
              (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) := by
          rw [hΘ, hz]; exact apply_conj_eq_liftFn ϖ hns fv c s q.2 q.1
      _ = Θ ((pu : v.adicCompletion K) • (1 + t • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
              (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2])) := by
          have hM : (pu : v.adicCompletion K) • ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) +
              t • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) =
              pOf ϖ s • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) +
                rOf ϖ s • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
                  (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2] := by
            ext i j : 1
            simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hpu, htdef]
            rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hp0]
          rw [hM]
      _ = _ := habs _

  have hcont : Continuous fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      fv ((sGL q.2 q.1)⁻¹ * (z * uEl ϖ hns s) * sGL q.2 q.1) :=
    hfv.1.continuous.comp ((continuous_sGL.inv.mul continuous_const).mul continuous_sGL)
  have heqfun : (fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      Θ (1 + t • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2])) =
      fun q => fv ((sGL q.2 q.1)⁻¹ * (z * uEl ϖ hns s) * sGL q.2 q.1) := by
    funext q; exact (hint_eq q).symm
  have hint : Integrable (fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      Θ (1 + ((Units.mk0 t ht0 : (v.adicCompletion K)ˣ) : v.adicCompletion K) •
        !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
          (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2])) (μU.prod μF) := by
    simp only [Units.val_mk0]
    have hcs := hasCompactSupport_chart ϖ Θ (hΘ ▸ hasCompactSupport_liftFn fv hfv.2 z) hpar ht0
    rw [heqfun] at hcs ⊢
    exact hcont.integrable_of_hasCompactSupport hcs

  obtain ⟨θ, hθ, hchange⟩ := integral_chart_change K v μF μU Θ ϖ (Units.mk0 t ht0) hint
  simp only [Units.val_mk0] at hchange
  have hzero : ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      Θ (1 + t • !![q.2, ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ - q.2 ^ 2) / ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K), -q.2]) ∂(μU.prod μF) = 0 := by
    rw [heqfun]; exact hcoord
  rw [hzero] at hchange
  have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  exact (mul_eq_zero.1 hchange.symm).resolve_left hθc

variable (K v)

open scoped Valued in
include μF μU in
set_option maxHeartbeats 1600000 in

theorem main' (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : IsLocalTestFn K v fv) (c : (v.adicCompletion K)ˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ),
          @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
            ∀ I : ℂ, IsOrbitalIntegral K v γ τ fv I → I = 0) :
    fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 := by
  obtain ⟨U, hU, hvan⟩ := hvan
  set z := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hz

  obtain ⟨ϖ, hϖv⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := uniformizer_ne_zero hϖv
  have hϖ1 : ‖ϖ‖ < 1 := norm_uniformizer_lt_one hϖv
  have hpar := parity_uniformizer hϖv
  have hns : ∀ p r : v.adicCompletion K, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0 := by
    intro p' r' h
    by_contra hr'
    apply hpar p' r' hr'
    rw [sub_eq_zero] at h
    rw [← norm_pow, h, norm_mul, norm_pow]
  haveI := charZero_adicCompletion K v
  have h2 : (2 : v.adicCompletion K) ≠ 0 := two_ne_zero

  obtain ⟨V, hV1, hV⟩ := hfv.1.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hfv.2

  set Θ := liftFn fv z with hΘ
  have hΘlc : IsLocallyConstant Θ := isLocallyConstant_liftFn fv hfv.1 hfv.2 z
  have hΘc : HasCompactSupport Θ := hasCompactSupport_liftFn fv hfv.2 z

  have hs0 := sSeq_ne_zero ϖ hϖ0
  have hslim := tendsto_sSeq ϖ hϖ1
  have hp0 := pOf_sSeq_ne_zero ϖ hns hϖ1
  have htt0 := tSeq_ne_zero ϖ hϖ0 hns hϖ1 h2
  have htt_lt := norm_tSeq_lt ϖ hϖ0 hns hϖ1 h2
  have htt_lim := tendsto_norm_tSeq ϖ hns hϖ1

  have hγlim : Tendsto (fun n => gammaEl ϖ hns c (sSeq ϖ n)) atTop (𝓝 z) := (tendsto_gammaEl ϖ hns c).comp hslim
  have hplim : Tendsto (fun n => Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (pOf ϖ (sSeq ϖ n)) (hp0 n)))
      atTop (𝓝 1) := by
    have hpu1 : Tendsto (fun n => Units.mk0 (pOf ϖ (sSeq ϖ n)) (hp0 n)) atTop (𝓝 1) := by
      rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
      change Tendsto (fun n => pOf ϖ (sSeq ϖ n)) atTop (𝓝 ((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K))
      rw [Units.val_one]
      have := ((continuous_pOf ϖ hns).tendsto 0).comp hslim
      have h0 : pOf ϖ 0 = 1 := by simp [pOf]
      rw [h0] at this
      exact this
    have := ((continuous_scalar K v).tendsto 1).comp hpu1
    rwa [map_one] at this
  obtain ⟨N, hN⟩ := ((hγlim.eventually_mem hU).and (hplim.eventually_mem hV1)).exists_forall_of_atTop

  have hstep : ∀ n, N ≤ n →
      ∫ b, ∫ a, Θ (1 + !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ * tSeq ϖ n ^ 2 - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) ∂μF ∂μU = 0 := by
    intro n hn
    obtain ⟨hγU, hpV⟩ := hN n hn
    exact chart_integral_eq_zero ϖ hϖ0 hns μF μU fv hfv c hpar h2 (mem_of_mem_nhds hV1) hV (hs0 n)
      (Units.mk0 (pOf ϖ (sSeq ϖ n)) (hp0 n)) (Units.val_mk0 _) hpV
      (fun τ hτ I hI => hvan _ hγU (det_gammaEl ϖ hns c (sSeq ϖ n))
        (isRegularSemisimple_gammaEl ϖ hϖ0 hns h2 c (hs0 n)) τ hτ I hI)

  have hex : ∀ ε : ℝ, 0 < ε → ∃ r r' : v.adicCompletion K, r' ≠ 0 ∧ ‖r'‖ < ‖r‖ ∧ ‖r‖ < ε ∧
      (∫ b, ∫ a, Θ (1 + !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ * r ^ 2 - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) ∂μF ∂μU) = 0 ∧
      (∫ b, ∫ a, Θ (1 + !![a, ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K);
        (ϖ * r' ^ 2 - a ^ 2) / ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K), -a]) ∂μF ∂μU) = 0 := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_nhds.1 htt_lim ε hε).exists_forall_of_atTop
    have hnε : ‖tSeq ϖ (max N N₁)‖ < ε := by
      have := hN₁ (max N N₁) (le_max_right _ _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
      exact this
    exact ⟨tSeq ϖ (max N N₁), tSeq ϖ (max N N₁ + 1), htt0 (max N N₁ + 1), htt_lt (max N N₁), hnε,
      hstep (max N N₁) (le_max_left _ _), hstep (max N N₁ + 1) ((le_max_left _ _).trans (Nat.le_succ _))⟩
  have hgerm : Θ 1 = 0 :=
    AutomorphicForm.apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
      μF μU Θ hΘlc hΘc ϖ hϖ1 hpar hex

  have h1 : Θ 1 = fv z := by
    have := liftFn_coe fv z 1
    rw [Units.val_one, mul_one] at this
    rw [hΘ]; exact this
  rw [← h1]; exact hgerm

end Main

section Final

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in

theorem main (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : IsLocalTestFn K v fv) (c : (v.adicCompletion K)ˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → IsRegularSemisimple γ →
        ∀ τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ),
          @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
            ∀ I : ℂ, IsOrbitalIntegral K v γ τ fv I → I = 0) :
    fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 := by
  letI : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  letI : MeasurableSpace (v.adicCompletion K)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion K)ˣ := ⟨rfl⟩
  exact main' K v Measure.addHaar Measure.haar fv hfv c hvan

end Final

end P2mCentralDensity
p2m_reactivate "P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero.P2mCentralDensity"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (c : (v.adicCompletion K)ˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → AutomorphicForm.IsRegularSemisimple γ →
        ∀ τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ),
          @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
            ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I = 0) :
    fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 :=
  P2mCentralDensity.main K v fv hfv c hvan

end
end S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero (solution)
