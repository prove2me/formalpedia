-- Prove2me | solution 1 for AutomorphicForm.exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d529cd83-3a36-5630-9e5b-0ea7e130bd5c

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_AutomorphicForm_eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
import Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
import Theorems.Thm_AutomorphicForm_exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter
open scoped Topology NNReal ENNReal Pointwise

noncomputable section

namespace KcEllTorusGerm

section Algebra

variable {F : Type*} [Field F]

def Ymat (s a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; (s - a ^ 2) / b, -a]

def sMat (a b : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; a, b]

def sGL (a : F) (b : Fˣ) : GL (Fin 2) F where
  val := sMat a b
  inv := !![1, 0; -a * (b⁻¹ : Fˣ), (b⁻¹ : Fˣ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul, add_neg_cancel]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sMat, Matrix.mul_apply, Fin.sum_univ_two]
    try rw [mul_comm ((b : F)⁻¹) a, neg_add_cancel]

@[scoped simp] theorem sGL_coe (a : F) (b : Fˣ) : ((sGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = sMat a b := rfl

theorem sGL_inv_coe (a : F) (b : Fˣ) :
    (((sGL a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -a * (b⁻¹ : Fˣ), (b⁻¹ : Fˣ)] := rfl

theorem mkOfDetNeZero_eq_sGL (a b : F) (h : (!![1, 0; a, b] : Matrix (Fin 2) (Fin 2) F).det ≠ 0) (hb : b ≠ 0) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ h = sGL a (Units.mk0 b hb) :=
  Units.ext rfl

theorem det_sMat_ne_zero_iff (a b : F) : (!![1, 0; a, b] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 ↔ b ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  simp

theorem coe_scalar (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  change Matrix.scalar (Fin 2) (c : F) = _
  rw [Matrix.scalar_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem coe_scalar_mul (c : Fˣ) (g : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

theorem scalar_mul_comm (c : Fˣ) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  rw [coe_scalar_mul, Units.val_mul, coe_scalar, Matrix.mul_smul, Matrix.mul_one]

theorem scalar_apply_00 (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
  rw [coe_scalar]; simp

theorem scalar_apply_01 (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  rw [coe_scalar]; simp

theorem coe_conj_torus {u : GL (Fin 2) F} {d P R : F}
    (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![P, R; d * R, P]) (a : F) (b : Fˣ) :
    (((sGL a b)⁻¹ * u * sGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      P • (1 : Matrix (Fin 2) (Fin 2) F) + R • Ymat d a b := by
  rw [Units.val_mul, Units.val_mul, hu, sGL_inv_coe, sGL_coe]
  have hb : (b : F) ≠ 0 := b.ne_zero
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Ymat, sMat, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem coe_conj_unipotent (a : F) (b : Fˣ) :
    (((sGL a b)⁻¹ * AutomorphicForm.unipotentGL2 (1 : F) * sGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 + Ymat 0 a b := by
  rw [Units.val_mul, Units.val_mul, AutomorphicForm.unipotentGL2_coe, sGL_inv_coe, sGL_coe]
  have hb : (b : F) ≠ 0 := b.ne_zero
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Ymat, sMat, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem smul_Ymat (d t a : F) (b : Fˣ) (ht : t ≠ 0) :
    t • Ymat d a b = Ymat (d * t ^ 2) (t * a) ((t : F) * b) := by
  have hb : (b : F) ≠ 0 := b.ne_zero
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ymat] <;> field_simp

theorem inv_smul_torus_eq {c P : F} (hP : P ≠ 0) (R : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    c⁻¹ • (P • (1 : Matrix (Fin 2) (Fin 2) F) + R • Y) = (c⁻¹ * P) • (1 + (R / P) • Y) := by
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_assoc, mul_div_cancel₀ R hP]

theorem coe_eq_of_commute {d : F} {u γ : GL (Fin 2) F} (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![0, 1; d, 0])
    (h : γ * u = u * γ) :
    (γ : Matrix (Fin 2) (Fin 2) F) =
      !![(γ : Matrix (Fin 2) (Fin 2) F) 0 0, (γ : Matrix (Fin 2) (Fin 2) F) 0 1;
        d * (γ : Matrix (Fin 2) (Fin 2) F) 0 1, (γ : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  set M : Matrix (Fin 2) (Fin 2) F := (γ : Matrix (Fin 2) (Fin 2) F) with hM
  have hm : M * !![0, 1; d, 0] = !![0, 1; d, 0] * M := by
    rw [hM, ← hu, ← Units.val_mul, h, Units.val_mul]
  have h00 := congr_fun (congr_fun hm 0) 0
  have h01 := congr_fun (congr_fun hm 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, mul_one, zero_add, add_zero,
    zero_mul, one_mul] at h00 h01

  ext i j; fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · show M 1 0 = d * M 0 1
    rw [← h00, mul_comm]
  · show M 1 1 = M 0 0
    exact h01.symm

theorem entry_ne_zero_of_isRegularSemisimple {d P R : F} {γ : GL (Fin 2) F}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![P, R; d * R, P]) (hreg : AutomorphicForm.IsRegularSemisimple γ) :
    R ≠ 0 := by
  intro hR
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero] at hreg
  apply hreg
  rw [hγ, hR, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  ring

theorem torus_decomp {d P R : F} {u γ : GL (Fin 2) F} (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![0, 1; d, 0])
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![P, R; d * R, P]) :
    (γ : Matrix (Fin 2) (Fin 2) F) = P • (1 : Matrix (Fin 2) (Fin 2) F) + R • (u : Matrix (Fin 2) (Fin 2) F) := by
  rw [hγ, hu]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem not_isSquare_sq_mul {t s : F} (ht : ¬ IsSquare t) (hs : s ≠ 0) : ¬ IsSquare (s ^ 2 * t) := by
  rintro ⟨r, hr⟩
  apply ht
  refine ⟨r / s, ?_⟩
  field_simp
  linear_combination hr

theorem centralizer_eq_of_coe_eq {d P R : F} {u γ : GL (Fin 2) F}
    (hu : (u : Matrix (Fin 2) (Fin 2) F) = !![0, 1; d, 0])
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) = !![P, R; d * R, P]) (hR : R ≠ 0) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) F)) = Subgroup.centralizer {u} := by
  have hdec := torus_decomp hu hγ
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, Units.ext_iff,
    Units.ext_iff, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hdec, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  constructor
  · intro h
    have h' : R • ((g : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F)) =
        R • ((u : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) := add_left_cancel h
    have h'' := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => R⁻¹ • N) h'
    simp only [smul_smul, inv_mul_cancel₀ hR, one_smul] at h''
    exact h''
  · intro h
    rw [h]

end Algebra

section Instances

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem t2Space_GL : T2Space (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    @BorelSpace (localCentralizer K v γ) _ (localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (localCentralizerBorel K v γ) rfl

theorem charZero_adicCompletion : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

theorem exists_norm_pos_lt_one : ∃ π : v.adicCompletion K, π ≠ 0 ∧ ‖π‖ < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨((algebraMap (𝓞 K) K x : K) : v.adicCompletion K), ?_, ?_⟩
  · intro h
    apply hx0
    have h' : (algebraMap K (v.adicCompletion K)) (algebraMap (𝓞 K) K x) = 0 := h
    rw [map_eq_zero] at h'
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h'
  · exact (NumberField.FinitePlace.norm_lt_one_iff_mem K v x).2 hxv

theorem exists_small_sq_mul (d : v.adicCompletion K) {m : ℝ} (hm : 0 < m) :
    ∃ ρ : v.adicCompletion K, ρ ≠ 0 ∧ ‖ρ‖ ≤ 1 ∧ ‖ρ ^ 2 * d‖ < m := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_pos_lt_one K v
  have hm' : 0 < m / (‖d‖ + 1) := div_pos hm (by positivity)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hm' hπ1
  refine ⟨π ^ n, pow_ne_zero _ hπ0, ?_, ?_⟩
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ1.le
  · rw [norm_mul, norm_pow, norm_pow, ← pow_mul]
    have h1 : ‖π‖ ^ (n * 2) ≤ ‖π‖ ^ n :=
      pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.le_mul_of_pos_right n two_pos)
    have hd1 : ‖d‖ < ‖d‖ + 1 := lt_add_one _
    calc ‖π‖ ^ (n * 2) * ‖d‖ ≤ ‖π‖ ^ n * ‖d‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ m / (‖d‖ + 1) * ‖d‖ := mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
      _ < m := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          exact mul_lt_mul_of_pos_left hd1 hm

end Instances

section SmallMatrices

variable {F : Type*} [NormedField F]

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → GL (Fin 2) F}
    (hval : ∀ i j, Continuous fun x => ((f x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

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

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable [IsUltrametricDist F]

theorem det_one_add_ne_zero {δ : ℝ} (hδ1 : δ < 1) (hδ0 : 0 ≤ δ) {E : Matrix (Fin 2) (Fin 2) F}
    (hE : ∀ i j, ‖E i j‖ ≤ δ) : (1 + E).det ≠ 0 := by
  intro h0
  have hexp : (1 + E).det = 1 + (E 0 0 + E 1 1 + (E 0 0 * E 1 1 - E 0 1 * E 1 0)) := by
    rw [Matrix.det_fin_two]
    simp [Matrix.add_apply]
    ring
  rw [hexp] at h0
  have hr : ‖E 0 0 + E 1 1 + (E 0 0 * E 1 1 - E 0 1 * E 1 0)‖ ≤ δ := by
    have hprod : ∀ a b : F, ‖a‖ ≤ δ → ‖b‖ ≤ δ → ‖a * b‖ ≤ δ := by
      intro a b ha hb
      rw [norm_mul]
      calc ‖a‖ * ‖b‖ ≤ δ * 1 := mul_le_mul ha (hb.trans hδ1.le) (norm_nonneg _) hδ0
        _ = δ := mul_one δ
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE 0 0) (hE 1 1))
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hprod _ _ (hE 0 0) (hE 1 1)) ?_)
      rw [norm_neg]; exact hprod _ _ (hE 0 1) (hE 1 0)
  have : (1 : F) = -(E 0 0 + E 1 1 + (E 0 0 * E 1 1 - E 0 1 * E 1 0)) := eq_neg_of_add_eq_zero_left h0
  have h1 : ‖(1 : F)‖ ≤ δ := by rw [this, norm_neg]; exact hr
  rw [norm_one] at h1
  exact not_lt.2 h1 hδ1

theorem exists_delta_of_isOpen (U : Subgroup (GL (Fin 2) F)) (hUo : IsOpen (U : Set (GL (Fin 2) F))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ E : Matrix (Fin 2) (Fin 2) F, (∀ i j, ‖E i j‖ ≤ δ₀) →
      ∃ hE : (1 + E).det ≠ 0, Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + E) hE ∈ U := by
  set Ξ : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0} → GL (Fin 2) F :=
    fun M => Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 M.2 with hΞ
  have hcont : Continuous Ξ := continuous_mkOfDetNeZero_subtype
  have hopen : IsOpen (Ξ ⁻¹' (U : Set (GL (Fin 2) F))) := hUo.preimage hcont
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 hopen
  have h1O : (1 : Matrix (Fin 2) (Fin 2) F) ∈ O := by
    have h1 : (⟨1, by simp⟩ : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0}) ∈ Ξ ⁻¹' (U : Set (GL (Fin 2) F)) := by
      rw [Set.mem_preimage, hΞ]
      have : Matrix.GeneralLinearGroup.mkOfDetNeZero (1 : Matrix (Fin 2) (Fin 2) F) (by simp) = 1 :=
        Units.ext rfl
      simp only [this]
      exact U.one_mem
    rw [← hOeq] at h1
    exact h1
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hO 1 h1O
  refine ⟨min (η / 2) (1 / 2), lt_min (half_pos hη) one_half_pos, (min_le_right _ _).trans_lt one_half_lt_one,
    fun E hE => ?_⟩
  have hδ0 : 0 ≤ min (η / 2) (1 / 2) := (lt_min (half_pos hη) one_half_pos).le
  have hdet : (1 + E).det ≠ 0 :=
    det_one_add_ne_zero ((min_le_right _ _).trans_lt one_half_lt_one) hδ0 hE
  refine ⟨hdet, ?_⟩
  have hmemO : (1 : Matrix (Fin 2) (Fin 2) F) + E ∈ O := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖E‖ ≤ min (η / 2) (1 / 2) := (Matrix.norm_le_iff hδ0).2 hE
      _ ≤ η / 2 := min_le_left _ _
      _ < η := half_lt_self hη
  have : (⟨1 + E, hdet⟩ : {M : Matrix (Fin 2) (Fin 2) F // M.det ≠ 0}) ∈ Ξ ⁻¹' (U : Set (GL (Fin 2) F)) := by
    rw [← hOeq]; exact hmemO
  exact this

omit [IsUltrametricDist F] in

theorem scalar_mem_of_norm_sub_one_le (U : Subgroup (GL (Fin 2) F)) {δ₀ : ℝ}
    (hUδ : ∀ E : Matrix (Fin 2) (Fin 2) F, (∀ i j, ‖E i j‖ ≤ δ₀) →
      ∃ hE : (1 + E).det ≠ 0, Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + E) hE ∈ U)
    (pu : Fˣ) (hp : ‖(pu : F) - 1‖ ≤ δ₀) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) pu ∈ U := by
  set E : Matrix (Fin 2) (Fin 2) F := ((pu : F) - 1) • (1 : Matrix _ _ _) with hE
  have hEle : ∀ i j, ‖E i j‖ ≤ δ₀ := by
    intro i j
    have hδ : 0 ≤ δ₀ := (norm_nonneg _).trans hp
    fin_cases i <;> fin_cases j <;> simp [hE, hp, hδ]
  obtain ⟨hdet, hmem⟩ := hUδ E hEle
  have heq : Matrix.GeneralLinearGroup.scalar (Fin 2) pu = Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + E) hdet := by
    apply Units.ext
    rw [coe_scalar, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hE, sub_smul, one_smul, add_sub_cancel]
  rw [heq]; exact hmem

end SmallMatrices

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

theorem exists_of_liftFn_ne_zero (fv : GL (Fin 2) F → ℂ) (z : GL (Fin 2) F) {M : Matrix (Fin 2) (Fin 2) F}
    (hM : liftFn fv z M ≠ 0) :
    ∃ g₁ : GL (Fin 2) F, (g₁ : Matrix (Fin 2) (Fin 2) F) = M ∧ z * g₁ ∈ Function.support fv := by
  by_cases h : M.det = 0
  · exact absurd (liftFn_of_det_eq_zero fv z h) hM
  · rw [liftFn_of_det_ne_zero fv z h] at hM
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M h, rfl, hM⟩

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

theorem exists_entry_bound (z : GL (Fin 2) F) {C : Set (GL (Fin 2) F)} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g₁ : GL (Fin 2) F, z * g₁ ∈ C →
      ∀ i j, ‖(g₁ : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B ∧ ‖((g₁⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B := by
  set φ : GL (Fin 2) F → ℝ := fun g => ∑ i : Fin 2, ∑ j : Fin 2,
    (‖((z⁻¹ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ +
      ‖(((z⁻¹ * g)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖) with hφ
  have hcont : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine ((Units.continuous_val.matrix_elem i j).comp (continuous_const.mul continuous_id)).norm.add ?_
    exact ((Units.continuous_coe_inv.matrix_elem i j).comp (continuous_const.mul continuous_id)).norm
  obtain ⟨B₀, hB₀⟩ := hC.exists_bound_of_continuousOn (f := φ) hcont.continuousOn
  refine ⟨max B₀ 1, le_max_right _ _, fun g₁ hg₁ i j => ?_⟩
  have hb := hB₀ _ hg₁
  have hzg : z⁻¹ * (z * g₁) = g₁ := by group
  simp only [hφ, hzg] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    add_nonneg (norm_nonneg _) (norm_nonneg _))] at hb
  have hij : ‖(g₁ : Matrix (Fin 2) (Fin 2) F) i j‖ + ‖((g₁⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B₀ := by
    refine le_trans ?_ hb
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin 2,
      (‖(g₁ : Matrix (Fin 2) (Fin 2) F) i j‖ + ‖((g₁⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖))
      (fun i _ => Finset.sum_nonneg fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j =>
      ‖(g₁ : Matrix (Fin 2) (Fin 2) F) i j‖ + ‖((g₁⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖)
      (fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ j)
  exact ⟨((le_add_of_nonneg_right (norm_nonneg _)).trans hij).trans (le_max_left _ _),
    ((le_add_of_nonneg_left (norm_nonneg _)).trans hij).trans (le_max_left _ _)⟩

variable [IsUltrametricDist F]

theorem entry_mul_le {E N : Matrix (Fin 2) (Fin 2) F} {δ B : ℝ} (_hB : 0 ≤ B) (hE : ∀ i j, ‖E i j‖ ≤ δ)
    (hN : ∀ i j, ‖N i j‖ ≤ B) (i j : Fin 2) : ‖(E * N) i j‖ ≤ δ * B := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hE 0 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_mul (hE _ _) (hN _ _) (norm_nonneg _) hδ

theorem liftFn_add_of_ne_zero (fv : GL (Fin 2) F → ℂ) (c : Fˣ) (U : Subgroup (GL (Fin 2) F))
    (hfU : ∀ g : GL (Fin 2) F, ∀ u₁ ∈ U, ∀ u₂ ∈ U, fv (u₁ * g * u₂) = fv g)
    {δ₀ : ℝ} (hUδ : ∀ E : Matrix (Fin 2) (Fin 2) F, (∀ i j, ‖E i j‖ ≤ δ₀) →
      ∃ hE : (1 + E).det ≠ 0, Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + E) hE ∈ U)
    {B : ℝ} (hB : 0 < B)
    (hinv : ∀ M : Matrix (Fin 2) (Fin 2) F, liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) M ≠ 0 →
      M.det ≠ 0 ∧ ∀ i j, ‖M⁻¹ i j‖ ≤ B)
    {M E : Matrix (Fin 2) (Fin 2) F} (hM : liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) M ≠ 0)
    (hE : ∀ i j, ‖E i j‖ ≤ δ₀ / B) :
    liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (M + E) =
      liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) M := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hz
  obtain ⟨hdetM, hMinv⟩ := hinv M hM
  set E' := E * M⁻¹ with hE'
  have hE'le : ∀ i j, ‖E' i j‖ ≤ δ₀ := by
    intro i j
    have := entry_mul_le hB.le hE hMinv i j
    rwa [div_mul_cancel₀ _ hB.ne'] at this
  obtain ⟨h1, hmem⟩ := hUδ E' hE'le
  have hprod : (1 + E') * M = M + E := by
    rw [Matrix.add_mul, Matrix.one_mul, hE', Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdetM), Matrix.mul_one]
  have hdet' : (M + E).det ≠ 0 := by
    rw [← hprod, Matrix.det_mul]; exact mul_ne_zero h1 hdetM
  rw [liftFn_of_det_ne_zero fv z hdet', liftFn_of_det_ne_zero fv z hdetM]
  have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero (M + E) hdet' =
      Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + E') h1 * Matrix.GeneralLinearGroup.mkOfDetNeZero M hdetM := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hprod.symm
  rw [hmk, ← mul_assoc, hz, scalar_mul_comm, mul_assoc]
  have := hfU (Matrix.GeneralLinearGroup.scalar (Fin 2) c * Matrix.GeneralLinearGroup.mkOfDetNeZero M hdetM)
    _ hmem 1 U.one_mem
  rwa [mul_one] at this

theorem liftFn_add (fv : GL (Fin 2) F → ℂ) (c : Fˣ) (U : Subgroup (GL (Fin 2) F))
    (hfU : ∀ g : GL (Fin 2) F, ∀ u₁ ∈ U, ∀ u₂ ∈ U, fv (u₁ * g * u₂) = fv g)
    {δ₀ : ℝ} (hUδ : ∀ E : Matrix (Fin 2) (Fin 2) F, (∀ i j, ‖E i j‖ ≤ δ₀) →
      ∃ hE : (1 + E).det ≠ 0, Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + E) hE ∈ U)
    {B : ℝ} (hB : 0 < B)
    (hinv : ∀ M : Matrix (Fin 2) (Fin 2) F, liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) M ≠ 0 →
      M.det ≠ 0 ∧ ∀ i j, ‖M⁻¹ i j‖ ≤ B)
    (M E : Matrix (Fin 2) (Fin 2) F) (hE : ∀ i j, ‖E i j‖ ≤ δ₀ / B) :
    liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (M + E) =
      liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) M := by
  by_cases hM : liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) M ≠ 0
  · exact liftFn_add_of_ne_zero fv c U hfU hUδ hB hinv hM hE
  · rw [not_ne_iff] at hM
    by_cases hME : liftFn fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (M + E) ≠ 0
    · have hnE : ∀ i j, ‖(-E) i j‖ ≤ δ₀ / B := fun i j => by rw [Matrix.neg_apply, norm_neg]; exact hE i j
      have := liftFn_add_of_ne_zero fv c U hfU hUδ hB hinv hME hnE
      rw [add_neg_cancel_right] at this
      rw [this]
    · rw [not_ne_iff] at hME
      rw [hM, hME]

end Lift

section Measures

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

attribute [local instance] secondCountableTopology_units

theorem measure_smul_eq (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {s : v.adicCompletion K}
    (hs : s ≠ 0) (E : Set (v.adicCompletion K)) : μ (s • E) = (‖s‖₊ : ℝ≥0∞) * μ E := by
  have h1 : (Units.mk0 s hs : (v.adicCompletion K)ˣ) • E = s • E := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_mk0]
  rw [← h1, ← distribHaarChar_mul μ (Units.mk0 s hs) E]
  congr 2
  have := LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v s
  rwa [LanglandsTunnell.TateLocal.modulus_of_ne_zero hs] at this

theorem map_mul_left_eq_smul (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] {s : v.adicCompletion K}
    (hs : s ≠ 0) : Measure.map (fun y => s * y) μ = ((‖s‖₊ : ℝ≥0∞)⁻¹) • μ := by
  refine Measure.ext fun E hE => ?_
  rw [Measure.map_apply (measurable_const_mul s) hE, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun y => s * y) ⁻¹' E = s⁻¹ • E := by
    have : (fun y : v.adicCompletion K => s * y) = fun y => s • y := rfl
    rw [this, Set.preimage_smul₀ hs]
  rw [hpre, measure_smul_eq K v μ (inv_ne_zero hs), nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hs)]

variable [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
  (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]

theorem integral_comp_dilate {t : v.adicCompletion K} (ht : t ≠ 0)
    (G : (v.adicCompletion K)ˣ × v.adicCompletion K → ℂ) :
    ∫ q, G (Units.mk0 t ht * q.1, t * q.2) ∂(ν.prod μ) = ((‖t‖⁻¹ : ℝ) : ℂ) * ∫ q, G q ∂(ν.prod μ) := by
  set e : (v.adicCompletion K)ˣ × v.adicCompletion K ≃ₜ (v.adicCompletion K)ˣ × v.adicCompletion K :=
    (Homeomorph.mulLeft (Units.mk0 t ht)).prodCongr (Homeomorph.mulLeft₀ t ht) with he
  have he' : ∀ q, e q = (Units.mk0 t ht * q.1, t * q.2) := fun q => rfl
  have hmap : Measure.map e (ν.prod μ) = ((‖t‖₊ : ℝ≥0∞)⁻¹) • (ν.prod μ) := by
    have h1 : (e : (v.adicCompletion K)ˣ × v.adicCompletion K → (v.adicCompletion K)ˣ × v.adicCompletion K) =
        Prod.map (fun b => Units.mk0 t ht * b) (fun a => t * a) := by
      funext q; rfl
    rw [h1, ← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_left_eq_smul K v μ ht, Measure.prod_smul_right]
  have h2 : ∫ q, G (e q) ∂(ν.prod μ) = ∫ q, G q ∂(Measure.map e (ν.prod μ)) := by
    rw [← Homeomorph.toMeasurableEquiv_coe, integral_map_equiv]
  simp_rw [← he']
  rw [h2, hmap, integral_smul_measure, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnnorm, Complex.real_smul]

theorem chart_change {t : v.adicCompletion K} (ht : t ≠ 0)
    (Θ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → ℂ) (d : v.adicCompletion K) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, Θ (1 + t • Ymat d q.2 q.1) ∂(ν.prod μ) =
      ((‖t‖⁻¹ : ℝ) : ℂ) * ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
        Θ (1 + Ymat (d * t ^ 2) q.2 q.1) ∂(ν.prod μ) := by
  have hpt : ∀ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      Θ (1 + t • Ymat d q.2 q.1) =
        (fun q' : (v.adicCompletion K)ˣ × v.adicCompletion K => Θ (1 + Ymat (d * t ^ 2) q'.2 q'.1))
          (Units.mk0 t ht * q.1, t * q.2) := by
    intro q
    simp only [Units.val_mul, Units.val_mk0]
    rw [smul_Ymat d t q.2 q.1 ht]
  simp_rw [hpt]
  exact integral_comp_dilate K v μ ν ht
    (fun q' : (v.adicCompletion K)ˣ × v.adicCompletion K => Θ (1 + Ymat (d * t ^ 2) q'.2 q'.1))

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] in
theorem range_units_val : Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem measurableEmbedding_units_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
  refine Units.isEmbedding_val₀.measurableEmbedding ?_
  rw [range_units_val]
  exact (measurableSet_singleton 0).compl

theorem integral_units_prod_eq (H : v.adicCompletion K × v.adicCompletion K → ℂ) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, H ((q.1 : v.adicCompletion K), q.2)
        ∂((Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure μ)).prod μ) =
      ∫ p : v.adicCompletion K × v.adicCompletion K, (‖p.1‖⁻¹ : ℝ) • H p ∂(μ.prod μ) := by
  set mm : Measure (v.adicCompletion K) := LanglandsTunnell.TateLocal.mulMeasure μ with hmm
  set νx : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val mm with hνx
  haveI : νx.IsHaarMeasure := LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure K v μ
  have hmod : (fun x : v.adicCompletion K => ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0∞))⁻¹) =
      fun x => ‖x‖ₑ⁻¹ := by
    funext x; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x, enorm_eq_nnnorm]
  have hmm' : mm = (μ.restrict {0}ᶜ).withDensity fun x => ‖x‖ₑ⁻¹ := by
    rw [hmm, LanglandsTunnell.TateLocal.mulMeasure, hmod]
  have hemb := measurableEmbedding_units_val K v

  have hmapval : Measure.map Units.val νx = mm := by
    rw [hνx, hemb.map_comap, range_units_val]
    rw [hmm', ← restrict_withDensity (measurableSet_singleton 0).compl, Measure.restrict_restrict
      (measurableSet_singleton 0).compl, Set.inter_self]

  have hembP : MeasurableEmbedding (Prod.map (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K)
      (id : v.adicCompletion K → v.adicCompletion K)) := hemb.prodMap MeasurableEmbedding.id
  have hmapP : Measure.map (Prod.map (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K)
      (id : v.adicCompletion K → v.adicCompletion K)) (νx.prod μ) = mm.prod μ := by
    rw [← Measure.map_prod_map _ _ hemb.measurable measurable_id, hmapval, Measure.map_id]
  have step1 : ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, H ((q.1 : v.adicCompletion K), q.2) ∂(νx.prod μ) =
      ∫ p, H p ∂(mm.prod μ) := by
    rw [← hmapP, hembP.integral_map]
    rfl

  have step2 : ∫ p, H p ∂(mm.prod μ) =
      ∫ p, H p ∂(((μ.prod μ).restrict ({0}ᶜ ×ˢ Set.univ)).withDensity fun p => ‖p.1‖ₑ⁻¹) := by
    rw [hmm']
    erw [prod_withDensity_left (measurable_enorm.inv)]
    rw [Measure.restrict_prod_eq_prod_univ]
    rfl
  have step3 : ∫ p, H p ∂(((μ.prod μ).restrict ({0}ᶜ ×ˢ Set.univ)).withDensity fun p => ‖p.1‖ₑ⁻¹) =
      ∫ p in {0}ᶜ ×ˢ Set.univ, (‖p.1‖ₑ⁻¹).toReal • H p ∂(μ.prod μ) := by
    refine integral_withDensity_eq_integral_toReal_smul (measurable_fst.enorm.inv) ?_ H
    rw [ae_restrict_iff' ((measurableSet_singleton 0).compl.prod MeasurableSet.univ)]
    refine ae_of_all _ fun p hp => ?_
    have hp0 : p.1 ≠ 0 := hp.1
    show ‖p.1‖ₑ⁻¹ < ∞
    rw [ENNReal.inv_lt_top, enorm_pos]
    exact hp0
  have step4 : ∫ p in {0}ᶜ ×ˢ Set.univ, (‖p.1‖ₑ⁻¹).toReal • H p ∂(μ.prod μ) =
      ∫ p, (‖p.1‖⁻¹ : ℝ) • H p ∂(μ.prod μ) := by
    rw [← integral_indicator ((measurableSet_singleton 0).compl.prod MeasurableSet.univ)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show ({0}ᶜ ×ˢ Set.univ : Set (v.adicCompletion K × v.adicCompletion K)).indicator
        (fun p => (‖p.1‖ₑ⁻¹).toReal • H p) p = (‖p.1‖⁻¹ : ℝ) • H p
    by_cases hp : p.1 = 0
    · have hnot : p ∉ ({0}ᶜ ×ˢ Set.univ : Set (v.adicCompletion K × v.adicCompletion K)) := by
        simp [hp]
      rw [Set.indicator_of_notMem hnot, hp, norm_zero, inv_zero, zero_smul]
    · have hmem : p ∈ ({0}ᶜ ×ˢ Set.univ : Set (v.adicCompletion K × v.adicCompletion K)) := by
        simp [hp]
      rw [Set.indicator_of_mem hmem]
      show (‖p.1‖ₑ⁻¹).toReal • H p = (‖p.1‖⁻¹ : ℝ) • H p
      rw [ENNReal.toReal_inv, toReal_enorm]
  rw [step1, step2, step3, step4]

theorem integral_units_prod_eq_swap (H : v.adicCompletion K × v.adicCompletion K → ℂ) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, H (q.2, (q.1 : v.adicCompletion K))
        ∂((Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure μ)).prod μ) =
      ∫ p : v.adicCompletion K × v.adicCompletion K, (‖p.2‖⁻¹ : ℝ) • H p ∂(μ.prod μ) := by
  have h1 := integral_units_prod_eq K v μ (fun p => H (p.2, p.1))
  simp only at h1
  rw [h1]
  have h2 := integral_prod_swap (μ := μ) (ν := μ) (fun p : v.adicCompletion K × v.adicCompletion K =>
    (‖p.2‖⁻¹ : ℝ) • H p)
  simp only [Prod.swap] at h2
  rw [← h2]

end Measures

section Centralizer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem isClosed_subgroup_centralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K))) := by
  haveI := t2Space_GL K v
  have hset : ((localCentralizer K v γ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K))) = {g | g * γ = γ * g} := by
    ext g
    exact Subgroup.mem_centralizer_singleton_iff
  rw [hset]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem measurableEmbedding_val_of_isClosed (H : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hH : IsClosed (H : Set (GL (Fin 2) (v.adicCompletion K)))) :
    @MeasurableEmbedding H (GL (Fin 2) (v.adicCompletion K)) (borel H) (localGLBorel K v) Subtype.val := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  have h1 := MeasurableEmbedding.subtype_coe (α := GL (Fin 2) (v.adicCompletion K))
    (s := (H : Set (GL (Fin 2) (v.adicCompletion K)))) hH.measurableSet
  have hms : borel H = (Subtype.instMeasurableSpace : MeasurableSpace H) :=
    (@BorelSpace.measurable_eq H _ Subtype.instMeasurableSpace
      (Subtype.borelSpace (H : Set (GL (Fin 2) (v.adicCompletion K))))).symm
  rw [hms]
  exact h1

theorem lintegral_comap_eq_of_map_eq {H₁ H₂ : Subgroup (GL (Fin 2) (v.adicCompletion K))} (hH : H₁ = H₂)
    (hc : IsClosed (H₁ : Set (GL (Fin 2) (v.adicCompletion K))))
    (τ : @Measure H₁ (borel H₁)) (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hmap : @Measure.map _ _ (borel H₁) (localGLBorel K v) Subtype.val τ = νT)
    (Hf : GL (Fin 2) (v.adicCompletion K) → ℝ≥0∞) :
    @lintegral H₂ (borel H₂) (@Measure.comap H₂ _ (borel H₂) (localGLBorel K v) Subtype.val νT)
        (fun t => Hf (t : GL (Fin 2) (v.adicCompletion K))) =
      @lintegral H₁ (borel H₁) τ (fun t => Hf (t : GL (Fin 2) (v.adicCompletion K))) := by
  subst hH
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  letI : MeasurableSpace H₁ := borel H₁
  have hemb := measurableEmbedding_val_of_isClosed K v H₁ hc
  rw [← hmap, hemb.comap_map]

theorem isHaarMeasure_comap_of_map_eq {H₁ H₂ : Subgroup (GL (Fin 2) (v.adicCompletion K))} (hH : H₁ = H₂)
    (hc : IsClosed (H₁ : Set (GL (Fin 2) (v.adicCompletion K))))
    (τ : @Measure H₁ (borel H₁)) (hτ : @Measure.IsHaarMeasure H₁ _ _ (borel H₁) τ)
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (hmap : @Measure.map _ _ (borel H₁) (localGLBorel K v) Subtype.val τ = νT) :
    @Measure.IsHaarMeasure H₂ _ _ (borel H₂) (@Measure.comap H₂ _ (borel H₂) (localGLBorel K v) Subtype.val νT) := by
  subst hH
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  letI : MeasurableSpace H₁ := borel H₁
  have hemb := measurableEmbedding_val_of_isClosed K v H₁ hc
  rw [← hmap, hemb.comap_map]
  exact hτ

end Centralizer

section Main

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm
open scoped Classical

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  AutomorphicForm.localCentralizerBorel borelSpace_localCentralizer

def chartFn (γ : GL (Fin 2) (v.adicCompletion K)) (f : GL (Fin 2) (v.adicCompletion K) → ℂ) :
    v.adicCompletion K × v.adicCompletion K → ℂ :=
  fun p => if h : p.2 ≠ 0 then f ((sGL p.1 (Units.mk0 p.2 h))⁻¹ * γ * sGL p.1 (Units.mk0 p.2 h)) else 0

theorem chartFn_units (γ : GL (Fin 2) (v.adicCompletion K)) (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ) :
    chartFn K v γ f (a, (b : v.adicCompletion K)) = f ((sGL a b)⁻¹ * γ * sGL a b) := by
  unfold chartFn
  rw [dif_pos b.ne_zero]
  simp only [Units.mk0_val]

theorem chart_integrand_eq (γ : GL (Fin 2) (v.adicCompletion K)) (f : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (q : v.adicCompletion K × v.adicCompletion K) :
    (‖q.2‖⁻¹ • (if h : (!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
        f ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)⁻¹ * γ *
          Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) : ℂ) =
      (‖q.2‖⁻¹ : ℝ) • chartFn K v γ f q := by
  unfold chartFn
  by_cases hb : q.2 = 0
  · have hdet : ¬ ((!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0) := by
      rw [det_sMat_ne_zero_iff]; exact fun h => h hb
    rw [dif_neg hdet, dif_neg (fun h => h hb)]
  · have hdet : ((!![1, 0; q.1, q.2] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0) := by
      rw [det_sMat_ne_zero_iff]; exact hb
    rw [dif_pos hdet, dif_pos hb, mkOfDetNeZero_eq_sGL q.1 q.2 hdet hb]

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem main' (c : (v.adicCompletion K)ˣ)
    (d : v.adicCompletion K) (hd : ¬ IsSquare d)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; d, 0])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (νT : Measure (GL (Fin 2) (v.adicCompletion K))) :
    ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), IsLocalTestFn K v f →
        ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          ∀ γ ∈ W, γ ∈ localCentralizer K v u → IsRegularSemisimple γ →
          ∀ (τ : Measure (localCentralizer K v γ)), τ.IsHaarMeasure →
            Measure.map Subtype.val τ = νT →
            ∀ I : ℂ, IsOrbitalIntegral K v γ τ f I →
              I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) +
                B γ * (∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                  (∫ x, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                    (k⁻¹ * unipotentGL2 x * k)) ∂μ) ∂(localHaar K v))) ∧
      ((Measure.comap Subtype.val νT : Measure (localCentralizer K v u)).IsHaarMeasure → A ≠ 0) := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hz
  haveI := charZero_adicCompletion K v
  have hd0 : d ≠ 0 := fun h => hd ⟨0, by rw [h, mul_zero]⟩
  have hcn : 0 < ‖(c : v.adicCompletion K)‖ := norm_pos_iff.2 c.ne_zero

  by_cases H0 : (Measure.comap Subtype.val νT : Measure (localCentralizer K v u)).IsHaarMeasure
  swap
  · refine ⟨1, fun _ => 0, fun f _ => ⟨Set.univ, Filter.univ_mem, ?_⟩, fun h => absurd h H0⟩
    intro γ _ hγT hreg τ hτ hmap I _
    exfalso
    apply H0
    have hcomm : γ * u = u * γ := Subgroup.mem_centralizer_singleton_iff.1 hγT
    have hγmat := coe_eq_of_commute hu hcomm
    have hR := entry_ne_zero_of_isRegularSemisimple hγmat hreg
    have hCent : localCentralizer K v γ = localCentralizer K v u := centralizer_eq_of_coe_eq hu hγmat hR
    exact isHaarMeasure_comap_of_map_eq K v hCent (isClosed_subgroup_centralizer K v γ) τ hτ νT hmap

  haveI := H0
  set τ₀ : Measure (localCentralizer K v u) := Measure.comap Subtype.val νT with hτ₀

  letI : MeasurableSpace (v.adicCompletion K)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion K)ˣ := ⟨rfl⟩
  set νx : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure μ)
    with hνx
  haveI : νx.IsHaarMeasure := LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure K v μ

  obtain ⟨cG, hcG, hcG', hG⟩ := AutomorphicForm.exists_forall_lintegral_localHaar_eq_mul_lintegral_pi_norm_det_inv_sq K v μ
  have hu' : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; d * 1, 0] := by rw [mul_one]; exact hu
  obtain ⟨cT, hcT, hcT', hT₀⟩ :=
    AutomorphicForm.exists_forall_lintegral_localCentralizer_eq_mul_lintegral_prod_norm_inv_of_not_isSquare K v μ
      d hd 0 1 one_ne_zero u hu' τ₀ H0
  set κ : ℝ := (cG / cT).toReal with hκ
  have hκpos : 0 < κ := ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨hcG, hcT'⟩).ne' (ENNReal.div_ne_top hcG' hcT)

  obtain ⟨α, ⟨ε₀, hε₀, hhom⟩, hgerm⟩ :=
    AutomorphicForm.exists_forall_sq_mul_eq_norm_mul_and_forall_integral_affineChart_eq_add_mul_apply_one_of_not_isSquare
      K v μ νx
  obtain ⟨c₀, hc₀, hunip⟩ :=
    AutomorphicForm.exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
      K v (fun a b => sGL a b) (fun a b => rfl) μ νx
  obtain ⟨ε₁, hε₁, hgerm₁⟩ := hgerm 1 1 one_pos

  obtain ⟨ρ₁, hρ₁0, hρ₁1, hρ₁d⟩ := exists_small_sq_mul K v d (lt_min hε₀ hε₁)
  have hρ₁n : 0 < ‖ρ₁‖ := norm_pos_iff.2 hρ₁0
  have hns₁ : ¬ IsSquare (ρ₁ ^ 2 * d) := not_isSquare_sq_mul hd hρ₁0
  have hα₁ : α (ρ₁ ^ 2 * d) ≠ 0 := (hgerm₁ (ρ₁ ^ 2 * d) (hρ₁d.trans_le (min_le_right _ _)) hns₁).1
  set L : ℂ := ((‖ρ₁‖⁻¹ : ℝ) : ℂ) * α (ρ₁ ^ 2 * d) with hL

  refine ⟨(κ : ℂ) * L,
    fun γ => (κ : ℂ) * ((‖(γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 /
      (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖⁻¹ : ℝ) : ℂ) / (c₀ : ℂ), ?_, ?_⟩
  swap
  · intro _
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκpos.ne'
    have hρc : ((‖ρ₁‖⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hρ₁n).ne'
    exact mul_ne_zero hκc (mul_ne_zero hρc hα₁)

  intro f hf
  obtain ⟨U, hUo, -, hbi⟩ :=
    AutomorphicForm.exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn K v f hf
  obtain ⟨δ₀, hδ₀, hδ₀1, hUδ⟩ := exists_delta_of_isOpen U hUo
  obtain ⟨Bd, hB1, hBnd⟩ := exists_entry_bound z hf.2.isCompact
  have hBpos : 0 < Bd := one_pos.trans_le hB1
  have hδF : 0 < δ₀ / Bd := div_pos hδ₀ hBpos
  obtain ⟨ε₂, hε₂, hgerm₂⟩ := hgerm (δ₀ / Bd) Bd hδF
  obtain ⟨ρ₂, hρ₂0, -, hρ₂d⟩ := exists_small_sq_mul K v d hε₂
  have hρ₂n : 0 < ‖ρ₂‖ := norm_pos_iff.2 hρ₂0
  set r : ℝ := min ‖ρ₁‖ ‖ρ₂‖ with hr
  have hrpos : 0 < r := lt_min hρ₁n hρ₂n

  set W : Set (GL (Fin 2) (v.adicCompletion K)) :=
    {γ | ‖(γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - c‖ < δ₀ * ‖(c : v.adicCompletion K)‖ ∧
      ‖(γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ < r * ‖(c : v.adicCompletion K)‖} with hW
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_norm.comp ((Units.continuous_val.matrix_elem 0 0).sub continuous_const))
        continuous_const
    · exact isOpen_lt (continuous_norm.comp (Units.continuous_val.matrix_elem 0 1)) continuous_const
  have hzW : z ∈ W := by
    refine ⟨?_, ?_⟩
    · show ‖(z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - c‖ < δ₀ * ‖(c : v.adicCompletion K)‖
      rw [hz, scalar_apply_00, sub_self, norm_zero]; exact mul_pos hδ₀ hcn
    · show ‖(z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ < r * ‖(c : v.adicCompletion K)‖
      rw [hz, scalar_apply_01, norm_zero]; exact mul_pos hrpos hcn
  refine ⟨W, hWopen.mem_nhds hzW, ?_⟩
  intro γ hγW hγT hreg τ hτ hmap I hI
  haveI := hτ
  beta_reduce

  set P : v.adicCompletion K := (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 with hP
  set R : v.adicCompletion K := (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 with hRdef
  have hcomm : γ * u = u * γ := Subgroup.mem_centralizer_singleton_iff.1 hγT
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![P, R; d * R, P] := coe_eq_of_commute hu hcomm
  have hR : R ≠ 0 := entry_ne_zero_of_isRegularSemisimple hγmat hreg
  have hCent : localCentralizer K v γ = localCentralizer K v u := centralizer_eq_of_coe_eq hu hγmat hR
  have hPc : ‖P - c‖ < δ₀ * ‖(c : v.adicCompletion K)‖ := hγW.1
  have hRr : ‖R‖ < r * ‖(c : v.adicCompletion K)‖ := hγW.2
  have hPc' : ‖P - c‖ < ‖(c : v.adicCompletion K)‖ := by
    calc ‖P - c‖ < δ₀ * ‖(c : v.adicCompletion K)‖ := hPc
      _ < 1 * ‖(c : v.adicCompletion K)‖ := mul_lt_mul_of_pos_right hδ₀1 hcn
      _ = ‖(c : v.adicCompletion K)‖ := one_mul _
  have hPn : ‖P‖ = ‖(c : v.adicCompletion K)‖ := by
    have : P = (P - c) + c := by ring
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hPc'.ne, max_eq_right hPc'.le]
  have hP0 : P ≠ 0 := fun h0 => by rw [h0, norm_zero] at hPn; exact hcn.ne hPn

  set pu : (v.adicCompletion K)ˣ := Units.mk0 P hP0 * c⁻¹ with hpu
  have hpucoe : (pu : v.adicCompletion K) = (c : v.adicCompletion K)⁻¹ * P := by
    rw [hpu, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, mul_comm]
  have hpU : Matrix.GeneralLinearGroup.scalar (Fin 2) pu ∈ U := by
    refine scalar_mem_of_norm_sub_one_le U hUδ pu ?_
    rw [hpucoe]
    have : (c : v.adicCompletion K)⁻¹ * P - 1 = (c : v.adicCompletion K)⁻¹ * (P - c) := by
      field_simp
    rw [this, norm_mul, norm_inv, inv_mul_le_iff₀ hcn, mul_comm]
    exact hPc.le

  set ρ : v.adicCompletion K := R / P with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hR hP0
  have hρn : ‖ρ‖ < r := by
    rw [hρ, norm_div, hPn, div_lt_iff₀ hcn]; exact hRr
  have hρ₁le : ‖ρ‖ ≤ ‖ρ₁‖ := (hρn.trans_le (min_le_left _ _)).le
  have hρ₂le : ‖ρ‖ ≤ ‖ρ₂‖ := (hρn.trans_le (min_le_right _ _)).le
  set lam : v.adicCompletion K := ρ ^ 2 * d with hlam
  have hlamn : ‖lam‖ < ε₂ := by
    refine lt_of_le_of_lt ?_ hρ₂d
    rw [hlam, norm_mul, norm_mul, norm_pow, norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hρ₂le 2) (norm_nonneg _)
  have hlamns : ¬ IsSquare lam := not_isSquare_sq_mul hd hρ0

  have hαlam : α lam = ((‖ρ‖ / ‖ρ₁‖ : ℝ) : ℂ) * α (ρ₁ ^ 2 * d) := by
    have hs0 : ρ / ρ₁ ≠ 0 := div_ne_zero hρ0 hρ₁0
    have hs1 : ‖ρ / ρ₁‖ ≤ 1 := by rw [norm_div, div_le_one hρ₁n]; exact hρ₁le
    have := hhom (ρ₁ ^ 2 * d) (ρ / ρ₁) (hρ₁d.trans_le (min_le_left _ _)) hns₁ hs0 hs1
    have heq : (ρ / ρ₁) ^ 2 * (ρ₁ ^ 2 * d) = lam := by
      rw [hlam]
      calc (ρ / ρ₁) ^ 2 * (ρ₁ ^ 2 * d) = (ρ / ρ₁ * ρ₁) ^ 2 * d := by ring
        _ = ρ ^ 2 * d := by rw [div_mul_cancel₀ ρ hρ₁0]
    rw [heq] at this
    rw [this, norm_div]

  have hT : ∀ Hf : GL (Fin 2) (v.adicCompletion K) → ℝ≥0∞, Measurable Hf →
      ∫⁻ t : localCentralizer K v γ, Hf (t : GL (Fin 2) (v.adicCompletion K)) ∂τ =
        cT * ∫⁻ q : v.adicCompletion K × v.adicCompletion K,
          (if h : (!![q.1, q.2; d * q.2, q.1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 then
              Hf (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) *
            ENNReal.ofReal ‖q.1 ^ 2 - d * q.2 ^ 2‖⁻¹ ∂(μ.prod μ) := by
    intro Hf hHf
    rw [← hT₀ Hf hHf]
    exact (lintegral_comap_eq_of_map_eq K v hCent (isClosed_subgroup_centralizer K v γ) τ νT hmap Hf).symm
  have hfm : Measurable f := hf.1.continuous.measurable
  have hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := hf.1.continuous.bounded_above_of_compact_support hf.2
  obtain ⟨-, hIeq⟩ :=
    AutomorphicForm.eq_div_mul_integral_norm_inv_smul_conj_affineChart_of_isOrbitalIntegral_of_not_isSquare K v μ
      cG hcG hcG' hG d hd P R hR γ hγmat τ hτ cT hcT hcT' hT f hfm hf.2 hfb I hI

  have hIeq' : I = (κ : ℂ) * ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      f ((sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1) ∂(νx.prod μ) := by
    rw [hIeq, ← hκ]
    congr 1
    refine (integral_congr_ae (ae_of_all _ (chart_integrand_eq K v γ f))).trans ?_
    rw [← integral_units_prod_eq_swap K v μ (chartFn K v γ f)]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    exact chartFn_units K v γ f q.2 q.1

  set Fm := liftFn f z with hFm
  have habs : ∀ N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
      liftFn f z ((pu : v.adicCompletion K) • N) = liftFn f z N := by
    intro N
    rw [liftFn_smul]
    congr 1
    funext g'
    have := hbi g' _ hpU 1 U.one_mem
    rwa [mul_one] at this
  have hint : ∀ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      f ((sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1) = Fm (1 + ρ • Ymat d q.2 q.1) := by
    intro q
    have h1 : (sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1 = z * (z⁻¹ * ((sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1)) := by group
    have h2 : ((z⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        (c : v.adicCompletion K)⁻¹ • (1 : Matrix _ _ _) := by
      rw [hz, ← map_inv, coe_scalar, Units.val_inv_eq_inv_val]
    rw [h1, ← liftFn_coe f z, Units.val_mul, coe_conj_torus hγmat, h2, Matrix.smul_mul, Matrix.one_mul,
      inv_smul_torus_eq hP0, ← hpucoe, habs]
  have hchartJ : ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      f ((sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1) ∂(νx.prod μ) =
      ((‖ρ‖⁻¹ : ℝ) : ℂ) * ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, Fm (1 + Ymat lam q.2 q.1) ∂(νx.prod μ) := by
    simp_rw [hint]
    rw [chart_change K v μ νx hρ0 Fm d, hlam, mul_comm d]

  have hsuppC : ∀ N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Fm N ≠ 0 →
      ∃ g₁ : GL (Fin 2) (v.adicCompletion K), (g₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = N ∧
        z * g₁ ∈ tsupport f := by
    intro N hN
    obtain ⟨g₁, hg₁, hmem⟩ := exists_of_liftFn_ne_zero f z hN
    exact ⟨g₁, hg₁, subset_tsupport _ hmem⟩
  have hinv : ∀ N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Fm N ≠ 0 → N.det ≠ 0 ∧ ∀ i j, ‖N⁻¹ i j‖ ≤ Bd := by
    intro N hN
    obtain ⟨g₁, hg₁, hmem⟩ := hsuppC N hN
    refine ⟨?_, fun i j => ?_⟩
    · rw [← hg₁, ← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g₁).ne_zero
    · rw [← hg₁, ← Matrix.coe_units_inv]
      exact (hBnd g₁ hmem i j).2
  have hFB : ∀ N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), Fm N ≠ 0 → ∀ i j, ‖N i j‖ ≤ Bd := by
    intro N hN i j
    obtain ⟨g₁, hg₁, hmem⟩ := hsuppC N hN
    rw [← hg₁]
    exact (hBnd g₁ hmem i j).1
  have hFδ : ∀ N E : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, ‖E i j‖ ≤ δ₀ / Bd) → Fm (N + E) = Fm N :=
    fun N E hE => liftFn_add f c U hbi hUδ hBpos hinv N E hE
  set J : v.adicCompletion K → ℂ := fun s =>
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, Fm (1 + Ymat s q.2 q.1) ∂(νx.prod μ) with hJ
  obtain ⟨-, hgermJ⟩ := hgerm₂ lam hlamn hlamns
  have hJeq : J lam = J 0 + α lam * Fm 1 := hgermJ Fm hFδ hFB J (fun s => rfl)
  have hF1 : Fm 1 = f z := by
    have := liftFn_coe f z 1
    rwa [Units.val_one, mul_one] at this

  have htest' : IsLocalTestFn K v (fun x => f (z * x)) :=
    ⟨hf.1.comp_continuous (continuous_const.mul continuous_id), hf.2.comp_homeomorph (Homeomorph.mulLeft z)⟩
  have hΦ := hunip _ htest'
  have hunipJ : ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      f (z * ((sGL q.2 q.1)⁻¹ * unipotentGL2 1 * sGL q.2 q.1)) ∂(νx.prod μ) = J 0 := by
    rw [hJ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only
    rw [hFm, ← liftFn_coe f z, coe_conj_unipotent]
  rw [hunipJ] at hΦ

  rw [hIeq', hchartJ]
  change (κ : ℂ) * ((((‖ρ‖⁻¹ : ℝ) : ℂ)) * J lam) = _
  rw [hJeq, hF1, hΦ, hαlam, hL]
  have hc₀c : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀.ne'
  have hρc : ((‖ρ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hρ0).ne'
  have hρ₁c : ((‖ρ₁‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ₁n.ne'
  push_cast
  field_simp
  ring

theorem main (c : (v.adicCompletion K)ˣ)
    (d : v.adicCompletion K) (hd : ¬ IsSquare d)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; d, 0])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (νT : Measure (GL (Fin 2) (v.adicCompletion K))) :
    ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), IsLocalTestFn K v f →
        ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          ∀ γ ∈ W, γ ∈ localCentralizer K v u → IsRegularSemisimple γ →
          ∀ (τ : Measure (localCentralizer K v γ)), τ.IsHaarMeasure →
            Measure.map Subtype.val τ = νT →
            ∀ I : ℂ, IsOrbitalIntegral K v γ τ f I →
              I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) +
                B γ * (∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                  (∫ x, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                    (k⁻¹ * unipotentGL2 x * k)) ∂ν) ∂(localHaar K v))) ∧
      ((Measure.comap Subtype.val νT : Measure (localCentralizer K v u)).IsHaarMeasure → A ≠ 0) :=
  main' K v c d hd u hu ν νT

end Main

end KcEllTorusGerm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare.KcEllTorusGerm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare.KcEllTorusGerm"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (d : v.adicCompletion K) (hd : ¬ IsSquare d)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; d, 0])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v)) :
    ∃ (A : ℂ) (B : GL (Fin 2) (v.adicCompletion K) → ℂ),
      (∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ), AutomorphicForm.IsLocalTestFn K v f →
        letI := AutomorphicForm.localGLBorel K v
        ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v u → AutomorphicForm.IsRegularSemisimple γ →
          ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)),
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
            @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
                Subtype.val τ = νT →
            ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ f I →
              I = A * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) +
                B γ * (∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
                  (∫ x, f (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                    (k⁻¹ * AutomorphicForm.unipotentGL2 x * k)) ∂ν) ∂(AutomorphicForm.localHaar K v))) ∧
      ((@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v u)
          (@Measure.comap _ _ (AutomorphicForm.localCentralizerBorel K v u) (AutomorphicForm.localGLBorel K v)
            Subtype.val νT)) → A ≠ 0) :=
  KcEllTorusGerm.main K v c d hd u hu ν νT

end S_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_nhds_scalar_forall_isOrbitalIntegral_eq_add_mul_of_mem_localCentralizer_of_not_isSquare (solution)
