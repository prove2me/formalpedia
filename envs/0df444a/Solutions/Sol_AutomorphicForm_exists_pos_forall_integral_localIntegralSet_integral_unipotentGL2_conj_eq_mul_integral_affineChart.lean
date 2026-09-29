-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/61f3ea15-0979-5f16-9d9f-806d97e438ba

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace P2mUnipotentChart

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem mem_coe_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ↔ ‖y‖ ≤ 1 := by
  rw [SetLike.mem_coe, mem_integers_iff_norm]

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

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM 0 0) (norm_nonneg _) (hM 1 1)
  · rw [norm_neg, norm_mul]; exact mul_le_one₀ (hM 0 1) (norm_nonneg _) (hM 1 0)

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hprod : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det *
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hn : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ *
      ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  by_contra hne
  have hlt : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ *
      ‖((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2
  exact this.ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) (v.adicCompletion K)}
    (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1)
    (h2 : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_one {M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) : ‖(M * N) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM i 0) (norm_nonneg _) (hN 0 j)
  · rw [norm_mul]; exact mul_le_one₀ (hM i 1) (norm_nonneg _) (hN 1 j)

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_one K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) (v.adicCompletion K)} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v hgh (inv_mem_localIntegralSet K v hh)
  rwa [mul_inv_cancel_right] at this

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem unipotentGL2_mem_iff (t : v.adicCompletion K) : unipotentGL2 t ∈ localIntegralSet K v ↔ ‖t‖ ≤ 1 := by
  rw [mem_localIntegralSet_iff_norm, unipotentGL2_coe, Matrix.det_fin_two_of]
  constructor
  · intro h; simpa using h.1 0 1
  · intro h
    refine ⟨fun i j => ?_, by simp⟩
    fin_cases i <;> fin_cases j <;> simp [h]

def lowerGL (q : v.adicCompletion K) : GL (Fin 2) (v.adicCompletion K) where
  val := !![1, 0; q, 1]
  inv := !![1, 0; -q, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerGL_mem {q : v.adicCompletion K} (hq : ‖q‖ ≤ 1) : lowerGL K v q ∈ localIntegralSet K v := by
  refine mem_localIntegralSet_of_norm K v (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [lowerGL, hq]
  · simp [lowerGL, Matrix.det_fin_two_of]

def weylGL : GL (Fin 2) (v.adicCompletion K) where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weylGL_mem : weylGL K v ∈ localIntegralSet K v := by
  refine mem_localIntegralSet_of_norm K v (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [weylGL]
  · simp [weylGL, Matrix.det_fin_two_of]

theorem weylGL_mul_weylGL : weylGL K v * weylGL K v = 1 := by
  refine Units.ext ?_
  simp only [Units.val_mul, weylGL, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weylGL_coe : ((weylGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
    !![0, 1; 1, 0] := rfl

theorem lowerGL_coe (q : v.adicCompletion K) :
    ((lowerGL K v q : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![1, 0; q, 1] := rfl

end Local

section Chart

variable {F : Type*} [Field F]

open AutomorphicForm

def sGL (a : F) (b : Fˣ) : GL (Fin 2) F where
  val := !![1, 0; a, b]
  inv := !![1, 0; -a * (b⁻¹ : Fˣ), (b⁻¹ : Fˣ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul, add_neg_cancel]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    try rw [mul_comm ((b : F)⁻¹) a, neg_add_cancel]

@[scoped simp] theorem sGL_coe (a : F) (b : Fˣ) : ((sGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; a, b] :=
  rfl

theorem sGL_inv_coe (a : F) (b : Fˣ) :
    (((sGL a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -a * (b⁻¹ : Fˣ), (b⁻¹ : Fˣ)] := rfl

def chartGL (q : Fˣ × F) : GL (Fin 2) F := (sGL q.2 q.1)⁻¹ * unipotentGL2 (1 : F) * sGL q.2 q.1

theorem chartGL_coe (b : Fˣ) (a : F) :
    ((chartGL (b, a) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1 + a, (b : F); -a ^ 2 / b, 1 - a] := by
  rw [chartGL, Units.val_mul, Units.val_mul, unipotentGL2_coe, sGL_inv_coe, sGL_coe]
  have hb : (b : F) ≠ 0 := b.ne_zero
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;> field_simp <;> ring

def conjGL (p : GL (Fin 2) F × F) : GL (Fin 2) F := p.1⁻¹ * unipotentGL2 p.2 * p.1

theorem coe_inv_eq (k : GL (Fin 2) F) :
    ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((k : Matrix (Fin 2) (Fin 2) F).det)⁻¹ •
        !![(k : Matrix (Fin 2) (Fin 2) F) 1 1, -(k : Matrix (Fin 2) (Fin 2) F) 0 1;
          -(k : Matrix (Fin 2) (Fin 2) F) 1 0, (k : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']

theorem det_coe_ne_zero (k : GL (Fin 2) F) : (k : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det k).ne_zero

theorem conjGL_coe (k : GL (Fin 2) F) (x : F) :
    ((conjGL (k, x) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 + (x / (k : Matrix (Fin 2) (Fin 2) F).det) •
        !![(k : Matrix (Fin 2) (Fin 2) F) 1 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0,
            (k : Matrix (Fin 2) (Fin 2) F) 1 1 ^ 2;
          -(k : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2,
            -((k : Matrix (Fin 2) (Fin 2) F) 1 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0)] := by
  have hΔ := det_coe_ne_zero k
  rw [conjGL, Units.val_mul, Units.val_mul, unipotentGL2_coe, coe_inv_eq]
  simp only
  set M := (k : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> (try rw [hdet]) <;> ring

theorem conjGL_eq_chartGL (k : GL (Fin 2) F) {x : F} (hx : x ≠ 0)
    (hδ : (k : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    conjGL (k, x) =
      chartGL (Units.mk0 (x * (k : Matrix (Fin 2) (Fin 2) F) 1 1 ^ 2 / (k : Matrix (Fin 2) (Fin 2) F).det)
          (div_ne_zero (mul_ne_zero hx (pow_ne_zero _ hδ)) (det_coe_ne_zero k)),
        x * (k : Matrix (Fin 2) (Fin 2) F) 1 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0 /
          (k : Matrix (Fin 2) (Fin 2) F).det) := by
  have hΔ := det_coe_ne_zero k
  apply Units.ext
  rw [conjGL_coe, chartGL_coe, Units.val_mk0]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end Chart

section Sets

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

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar

theorem isMulRightInvariant_localHaar : (localHaar K v).IsMulRightInvariant :=
  (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two (localHaar K v)).1

attribute [local instance] isMulRightInvariant_localHaar

def eγ (g : GL (Fin 2) (v.adicCompletion K)) : v.adicCompletion K := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0

def eδ (g : GL (Fin 2) (v.adicCompletion K)) : v.adicCompletion K := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1

def ratio (g : GL (Fin 2) (v.adicCompletion K)) : v.adicCompletion K := eγ K v g / eδ K v g

theorem continuous_eγ : Continuous (eγ K v) := Units.continuous_val.matrix_elem 1 0

theorem continuous_eδ : Continuous (eδ K v) := Units.continuous_val.matrix_elem 1 1

theorem continuous_det : Continuous fun g : GL (Fin 2) (v.adicCompletion K) =>
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det :=
  Units.continuous_val.matrix_det

theorem norm_eγ_eq_one_of_lt {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ localIntegralSet K v)
    (hδ : ‖eδ K v k‖ < 1) : ‖eγ K v k‖ = 1 := by
  obtain ⟨hent, hdet⟩ := (mem_localIntegralSet_iff_norm K v k).1 hk
  by_contra hne
  have hγ : ‖eγ K v k‖ < 1 := lt_of_le_of_ne (hent 1 0) hne
  have : ‖(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ < 1 := by
    rw [Matrix.det_fin_two, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hent 0 0) (norm_nonneg _) hδ
    · rw [norm_neg, norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hent 0 1) (norm_nonneg _) hγ
  exact this.ne hdet

def Dset : Set (GL (Fin 2) (v.adicCompletion K)) :=
  {g | ‖eδ K v g‖ = 1 ∧ ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ ≤ 1 ∧
    ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1}

def K1 : Set (GL (Fin 2) (v.adicCompletion K)) := {g | g ∈ localIntegralSet K v ∧ ‖eδ K v g‖ = 1}

def K2 : Set (GL (Fin 2) (v.adicCompletion K)) := {g | g ∈ localIntegralSet K v ∧ ‖eδ K v g‖ < 1}

def N0 : Set (GL (Fin 2) (v.adicCompletion K)) := {g | g ∈ localIntegralSet K v ∧ eδ K v g = 0}

theorem mem_K1_iff (g : GL (Fin 2) (v.adicCompletion K)) : g ∈ K1 K v ↔ g ∈ Dset K v ∧ ‖ratio K v g‖ ≤ 1 := by
  constructor
  · rintro ⟨hk, hδ⟩
    obtain ⟨hent, hdet⟩ := (mem_localIntegralSet_iff_norm K v g).1 hk
    refine ⟨⟨hδ, hent 0 1, hdet⟩, ?_⟩
    rw [ratio, norm_div, hδ, div_one]; exact hent 1 0
  · rintro ⟨⟨hδ, hβ, hdet⟩, hr⟩
    have hδ0 : eδ K v g ≠ 0 := fun h => by rw [h, norm_zero] at hδ; exact zero_ne_one hδ
    have hγ : ‖eγ K v g‖ ≤ 1 := by rwa [ratio, norm_div, hδ, div_one] at hr
    refine ⟨mem_localIntegralSet_of_norm K v (fun i j => ?_) hdet, hδ⟩
    fin_cases i <;> fin_cases j
    ·
      have hδ0' : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := hδ0
      have hα : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
          ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det +
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 * eγ K v g) / eδ K v g := by
        rw [Matrix.det_fin_two, eγ, eδ]; field_simp; ring
      change ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ≤ 1
      rw [hα, norm_div, hδ, div_one]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (le_of_eq hdet) ?_)
      rw [norm_mul]; exact mul_le_one₀ hβ (norm_nonneg _) hγ
    · exact hβ
    · exact hγ
    · exact le_of_eq hδ

theorem mul_lowerGL_apply (g : GL (Fin 2) (v.adicCompletion K)) (t : v.adicCompletion K) :
    eδ K v (g * lowerGL K v t) = eδ K v g ∧ eγ K v (g * lowerGL K v t) = eγ K v g + eδ K v g * t ∧
      ((g * lowerGL K v t : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 ∧
      ((g * lowerGL K v t : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := by
  simp only [eδ, eγ, Units.val_mul, lowerGL_coe, Matrix.det_mul, Matrix.det_fin_two_of]
  refine ⟨?_, ?_, ?_, by ring⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_lowerGL_mem_Dset_iff (g : GL (Fin 2) (v.adicCompletion K)) (t : v.adicCompletion K) :
    g * lowerGL K v t ∈ Dset K v ↔ g ∈ Dset K v := by
  obtain ⟨h1, -, h3, h4⟩ := mul_lowerGL_apply K v g t
  simp only [Dset, Set.mem_setOf_eq, h1, h3, h4]

theorem ratio_mul_lowerGL {g : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ Dset K v) (t : v.adicCompletion K) :
    ratio K v (g * lowerGL K v t) = ratio K v g + t := by
  obtain ⟨h1, h2, -, -⟩ := mul_lowerGL_apply K v g t
  have hδ0 : eδ K v g ≠ 0 := fun h => by
    have := hg.1; rw [h, norm_zero] at this; exact zero_ne_one this
  rw [ratio, ratio, h1, h2]; field_simp

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

theorem measurable_inv' : Measurable fun x : v.adicCompletion K => x⁻¹ :=
  measurable_of_continuousOn_compl_singleton 0 continuousOn_inv₀

theorem measurable_ratio : Measurable (ratio K v) := by
  unfold ratio
  simp_rw [div_eq_mul_inv]
  exact (continuous_eγ K v).measurable.mul ((measurable_inv' K v).comp (continuous_eδ K v).measurable)

def rhoD : Measure (v.adicCompletion K) := ((localHaar K v).restrict (Dset K v)).map (ratio K v)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem isClosed_Dset : IsClosed (Dset K v) :=
  (isClosed_eq (continuous_norm.comp (continuous_eδ K v)) continuous_const).inter
    ((isClosed_le (continuous_norm.comp (Units.continuous_val.matrix_elem 0 1)) continuous_const).inter
      (isClosed_eq (continuous_norm.comp (continuous_det K v)) continuous_const))

theorem measurableSet_Dset : MeasurableSet (Dset K v) := (isClosed_Dset K v).measurableSet

theorem rhoD_apply {A : Set (v.adicCompletion K)} (hA : MeasurableSet A) :
    rhoD K v A = localHaar K v (ratio K v ⁻¹' A ∩ Dset K v) := by
  rw [rhoD, Measure.map_apply (measurable_ratio K v) hA, Measure.restrict_apply ((measurable_ratio K v) hA)]

scoped instance isAddLeftInvariant_rhoD : (rhoD K v).IsAddLeftInvariant := by
  refine ⟨fun t => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_add t) hA, rhoD_apply K v hA,
    rhoD_apply K v ((measurable_const_add t) hA)]
  have hset : ratio K v ⁻¹' ((fun x => t + x) ⁻¹' A) ∩ Dset K v =
      (fun g => g * lowerGL K v t) ⁻¹' (ratio K v ⁻¹' A ∩ Dset K v) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (mul_lowerGL_mem_Dset_iff K v g t).2 h2⟩
      rw [ratio_mul_lowerGL K v h2, add_comm]; exact h1
    · rintro ⟨h1, h2⟩
      have hg : g ∈ Dset K v := (mul_lowerGL_mem_Dset_iff K v g t).1 h2
      refine ⟨?_, hg⟩
      rw [ratio_mul_lowerGL K v hg, add_comm] at h1; exact h1
  rw [hset, measure_preimage_mul_right]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in

theorem Dset_subset_integralUnitsSet {R : ℝ} (hR : 1 ≤ R) :
    ratio K v ⁻¹' Metric.closedBall (0 : v.adicCompletion K) R ∩ Dset K v ⊆
      integralUnitsSet (Metric.closedBall (0 : v.adicCompletion K) R) := by
  rintro g ⟨hr, hδ, hβ, hdet⟩
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hr
  have hδ0 : eδ K v g ≠ 0 := fun h => by rw [h, norm_zero] at hδ; exact zero_ne_one hδ
  have hγ : ‖eγ K v g‖ ≤ R := by rwa [ratio, norm_div, hδ, div_one] at hr
  have hα : ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ≤ R := by
    have hδ0' : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := hδ0
    have : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
        ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det +
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 * eγ K v g) / eδ K v g := by
      rw [Matrix.det_fin_two, eγ, eδ]; field_simp; ring
    rw [this, norm_div, hδ, div_one]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hdet.le.trans hR) ?_)
    rw [norm_mul]
    calc ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ * ‖eγ K v g‖ ≤ 1 * R :=
          mul_le_mul hβ hγ (norm_nonneg _) zero_le_one
      _ = R := one_mul R
  have hent : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ R := by
    intro i j; fin_cases i <;> fin_cases j
    · exact hα
    · exact hβ.trans hR
    · exact hγ
    · exact hδ.le.trans hR
  refine (mem_integralUnitsSet).2 ⟨fun i j => by simpa using hent i j, fun i j => ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  rw [coe_inv_eq, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hdet, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact hent 1 1
  · simpa using hent 0 1
  · simpa using hent 1 0
  · exact hent 0 0

scoped instance isFiniteMeasureOnCompacts_rhoD : IsFiniteMeasureOnCompacts (rhoD K v) := by
  refine ⟨fun C hC => ?_⟩
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : v.adicCompletion K)
  set R' : ℝ := max R 1 with hR'
  have hsub : C ⊆ Metric.closedBall (0 : v.adicCompletion K) R' :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  refine (measure_mono hsub).trans_lt ?_
  rw [rhoD_apply K v measurableSet_closedBall]
  refine (measure_mono (Dset_subset_integralUnitsSet K v (le_max_right R 1))).trans_lt ?_
  exact (isCompact_integralUnitsSet (isCompact_closedBall _ _)).measure_lt_top

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem isOpen_K1 : IsOpen (K1 K v) := by
  have : K1 K v = localIntegralSet K v ∩ (fun g => ‖eδ K v g‖) ⁻¹' {1} := rfl
  rw [this]
  refine (isOpen_localIntegralSet K v).inter ?_
  have h1 : (fun g : GL (Fin 2) (v.adicCompletion K) => ‖eδ K v g‖) ⁻¹' {1} =
      eδ K v ⁻¹' Metric.sphere (0 : v.adicCompletion K) 1 := by
    ext g; simp
  rw [h1]
  exact (IsUltrametricDist.isOpen_sphere (0 : v.adicCompletion K) one_ne_zero).preimage (continuous_eδ K v)

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem one_mem_K1 : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ K1 K v :=
  ⟨one_mem_localIntegralSet K v, by simp [eδ]⟩

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem exists_rhoD_eq_smul : ∃ c : ℝ≥0, 0 < c ∧ rhoD K v = c • μ := by
  have heq : rhoD K v = (rhoD K v).addHaarScalarFactor μ • μ := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(rhoD K v).addHaarScalarFactor μ, ?_, heq⟩
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0, zero_smul] at heq
  have hK1 : 0 < localHaar K v (K1 K v) := (isOpen_K1 K v).measure_pos _ ⟨1, one_mem_K1 K v⟩
  have hle : localHaar K v (K1 K v) ≤ rhoD K v Set.univ := by
    rw [rhoD_apply K v MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
    exact measure_mono fun g hg => ((mem_K1_iff K v g).1 hg).1
  rw [heq, Measure.coe_zero, Pi.zero_apply] at hle
  exact (hK1.trans_le hle).ne rfl

end Sets

section MeasureFacts

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm LanglandsTunnell.TateLocal

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  isMulRightInvariant_localHaar

def Mset (t : v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K)) :=
  {g | g ∈ localIntegralSet K v ∧ eδ K v g = t * eγ K v g}

theorem preimage_N0 {t : v.adicCompletion K} (ht : ‖t‖ ≤ 1) :
    (fun g => g * unipotentGL2 t) ⁻¹' N0 K v = Mset K v (-t) := by
  ext g
  simp only [Set.mem_preimage, N0, Mset, Set.mem_setOf_eq,
    mul_mem_localIntegralSet_iff_left K v ((unipotentGL2_mem_iff K v t).2 ht)]
  refine and_congr_right fun _ => ?_
  have : eδ K v (g * unipotentGL2 t) = eγ K v g * t + eδ K v g := by
    simp [eδ, eγ, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

theorem Mset_disjoint {t s : v.adicCompletion K} (hts : t ≠ s) : Disjoint (Mset K v t) (Mset K v s) := by
  rw [Set.disjoint_left]
  rintro g ⟨-, ht⟩ ⟨-, hs⟩
  have hγ : eγ K v g = 0 := by
    have : (t - s) * eγ K v g = 0 := by rw [sub_mul, ← ht, ← hs, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hts)
  have hδ : eδ K v g = 0 := by rw [ht, hγ, mul_zero]
  have hdet : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 0 := by
    rw [Matrix.det_fin_two]
    change _ * eδ K v g - _ * eγ K v g = 0
    rw [hγ, hδ, mul_zero, mul_zero, sub_zero]
  exact det_coe_ne_zero g hdet

theorem isClosed_localIntegralSet' : IsClosed (localIntegralSet K v) := (isCompact_localIntegralSet K v).isClosed

theorem measurableSet_Mset (t : v.adicCompletion K) : MeasurableSet (Mset K v t) :=
  ((isClosed_localIntegralSet' K v).inter (isClosed_eq (continuous_eδ K v)
    (continuous_const.mul (continuous_eγ K v)))).measurableSet

theorem measurableSet_N0 : MeasurableSet (N0 K v) :=
  ((isClosed_localIntegralSet' K v).inter (isClosed_eq (continuous_eδ K v) continuous_const)).measurableSet

theorem measure_N0 : localHaar K v (N0 K v) = 0 := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_pos_lt_one K v
  set t : ℕ → v.adicCompletion K := fun n => π ^ (n + 1) with ht
  have htn : ∀ n, ‖t n‖ ≤ 1 := fun n => by
    rw [ht]; simp only [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ1.le
  have htinj : Function.Injective t := by
    intro a b hab
    have h := congrArg (fun x => ‖x‖) hab
    simp only [ht, norm_pow] at h
    have := (pow_right_strictAnti₀ (norm_pos_iff.2 hπ0) hπ1).injective h
    omega
  have hmeas : ∀ n, localHaar K v (Mset K v (-t n)) = localHaar K v (N0 K v) := by
    intro n; rw [← preimage_N0 K v (htn n), measure_preimage_mul_right]
  have hdisj : Pairwise (Function.onFun Disjoint fun n => Mset K v (-t n)) := by
    intro a b hab
    exact Mset_disjoint K v (fun h => hab (htinj (neg_injective h)))
  have hsub : (⋃ n, Mset K v (-t n)) ⊆ localIntegralSet K v := Set.iUnion_subset fun n g hg => hg.1
  have hfin : localHaar K v (⋃ n, Mset K v (-t n)) < ⊤ :=
    (measure_mono hsub).trans_lt (isCompact_localIntegralSet K v).measure_lt_top
  rw [measure_iUnion hdisj (fun n => measurableSet_Mset K v _)] at hfin
  simp_rw [hmeas] at hfin
  by_contra hne
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hne] at hfin
  exact lt_irrefl _ hfin

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem measure_image_mul (u : (v.adicCompletion K)ˣ) (S : Set (v.adicCompletion K)) :
    μ ((fun x => (u : v.adicCompletion K) * x) '' S) = ‖(u : v.adicCompletion K)‖ₑ * μ S := by
  have h := distribHaarChar_mul μ u S
  have hu : distribHaarChar (v.adicCompletion K) u = ‖(u : v.adicCompletion K)‖₊ := by
    rw [← modulus_coe_units, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v]
  rw [hu] at h
  rw [enorm_eq_nnnorm, h]
  rfl

theorem measure_preimage_mul' (u : (v.adicCompletion K)ˣ) (S : Set (v.adicCompletion K)) :
    μ ((fun x => (u : v.adicCompletion K) * x) ⁻¹' S) = ‖(u : v.adicCompletion K)‖ₑ⁻¹ * μ S := by
  have himg : (fun x => (u : v.adicCompletion K) * x) ⁻¹' S =
      (fun x => ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) * x) '' S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hx; exact ⟨_, hx, by rw [← mul_assoc, Units.inv_mul, one_mul]⟩
    · rintro ⟨y, hy, rfl⟩; rwa [← mul_assoc, Units.mul_inv, one_mul]
  rw [himg, measure_image_mul, Units.val_inv_eq_inv_val, enorm_inv (Units.ne_zero u)]

variable [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]

theorem range_units_val : Set.range (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem measurableEmbedding_units_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion K)ˣ → v.adicCompletion K) := by
  refine Units.isEmbedding_val₀.measurableEmbedding ?_
  rw [range_units_val]
  exact (measurableSet_singleton 0).compl

theorem exists_lintegral_units_eq :
    ∃ c₁ : ℝ≥0, 0 < c₁ ∧ ∀ G : v.adicCompletion K → ℝ≥0∞, Measurable G →
      ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * G b ∂ν = (c₁ : ℝ≥0∞)⁻¹ * ∫⁻ x in {0}ᶜ, G x ∂μ := by
  set mm : Measure (v.adicCompletion K) := mulMeasure μ with hmm
  set ν' : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val mm with hν'
  haveI : ν'.IsHaarMeasure := LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure K v μ
  have hνeq : ν' = ν'.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul ν' ν
  set c₁ := ν'.haarScalarFactor ν with hc₁
  have hc₁pos : 0 < c₁ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν' ν
  refine ⟨c₁, hc₁pos, fun G hG => ?_⟩
  have hc₁0 : (c₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc₁pos.ne'

  have hmod : (fun x : v.adicCompletion K => ((modulus x : ℝ≥0∞))⁻¹) = fun x => ‖x‖ₑ⁻¹ := by
    funext x; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v x, enorm_eq_nnnorm]
  have hmm' : mm = (μ.restrict {0}ᶜ).withDensity fun x => ‖x‖ₑ⁻¹ := by rw [hmm, mulMeasure, hmod]

  set h : v.adicCompletion K → ℝ≥0∞ := fun x => ‖x‖ₑ * G x with hh
  have hemb := measurableEmbedding_units_val K v
  have step1 : ∫⁻ b, h b ∂ν' = ∫⁻ x, h x ∂mm := by
    rw [← hemb.lintegral_map, hν', hemb.map_comap, range_units_val]
    congr 1
    rw [hmm', ← restrict_withDensity (measurableSet_singleton 0).compl, Measure.restrict_restrict
      (measurableSet_singleton 0).compl, Set.inter_self]
  have step2 : ∫⁻ x, h x ∂mm = ∫⁻ x in {0}ᶜ, G x ∂μ := by
    rw [hmm', lintegral_withDensity_eq_lintegral_mul _ (measurable_enorm.fun_inv) (measurable_enorm.fun_mul hG)]
    refine setLIntegral_congr_fun (measurableSet_singleton 0).compl (fun x hx => ?_)
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by simpa using hx) enorm_ne_top, one_mul]
  have step3 : ∫⁻ b, h b ∂ν' = (c₁ : ℝ≥0∞) * ∫⁻ b, h b ∂ν := by
    rw [hνeq, lintegral_smul_measure]; rfl
  calc ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * G b ∂ν = (c₁ : ℝ≥0∞)⁻¹ * ((c₁ : ℝ≥0∞) * ∫⁻ b, h b ∂ν) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc₁0 ENNReal.coe_ne_top, one_mul]
    _ = (c₁ : ℝ≥0∞)⁻¹ * ∫⁻ x in {0}ᶜ, G x ∂μ := by rw [← step3, step1, step2]

include ν in

theorem lintegral_inv_sq_comp_inv (m : v.adicCompletion K → ℝ≥0∞) (hm : Measurable m) :
    ∫⁻ y in {y | y ≠ 0 ∧ ‖y‖ < 1}, ‖y‖ₑ⁻¹ ^ 2 * m y⁻¹ ∂μ = ∫⁻ z in {z | 1 < ‖z‖}, m z ∂μ := by
  obtain ⟨c₁, hc₁, hB⟩ := exists_lintegral_units_eq K v μ ν
  have hc₁0 : (c₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc₁.ne'

  set G : v.adicCompletion K → ℝ≥0∞ := fun x => {x | ‖x‖ < 1}.indicator (fun x => ‖x‖ₑ⁻¹ ^ 2 * m x⁻¹) x with hG
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ (isOpen_lt continuous_norm continuous_const).measurableSet
    exact ((measurable_enorm.inv).pow_const 2).mul (hm.comp (measurable_inv' K v))
  have hmeas1 : MeasurableSet {x : v.adicCompletion K | ‖x‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hmeas2 : MeasurableSet {x : v.adicCompletion K | 1 < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hL : ∫⁻ y in {y | y ≠ 0 ∧ ‖y‖ < 1}, ‖y‖ₑ⁻¹ ^ 2 * m y⁻¹ ∂μ = ∫⁻ x in {0}ᶜ, G x ∂μ := by
    have hset : {y : v.adicCompletion K | y ≠ 0 ∧ ‖y‖ < 1} = {x | ‖x‖ < 1} ∩ {0}ᶜ := by
      ext y; simp [and_comm]
    rw [hset, hG, lintegral_indicator hmeas1, Measure.restrict_restrict hmeas1]

  set G' : v.adicCompletion K → ℝ≥0∞ := fun x => {x | 1 < ‖x‖}.indicator m x with hG'
  have hG'm : Measurable G' := hm.indicator hmeas2
  have hR : ∫⁻ z in {z | 1 < ‖z‖}, m z ∂μ = ∫⁻ x in {0}ᶜ, G' x ∂μ := by
    have hset : {z : v.adicCompletion K | 1 < ‖z‖} = {x | 1 < ‖x‖} ∩ {0}ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, iff_self_and]
      intro hy h0; rw [h0, norm_zero] at hy; exact (not_lt.2 zero_le_one) hy
    rw [hset, hG', lintegral_indicator hmeas2, Measure.restrict_restrict hmeas2]
  rw [hL, hR]

  have hL' := hB G hGm
  have hR' := hB G' hG'm

  have hkey : ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * G b ∂ν = ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * G' b ∂ν := by
    have hinv : ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * G b ∂ν =
        ∫⁻ b, ‖(((b⁻¹ : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ₑ * G ((b⁻¹ : (v.adicCompletion K)ˣ)) ∂ν := by
      rw [← (Measure.measurePreserving_inv ν).lintegral_comp_emb (MeasurableEquiv.inv (v.adicCompletion K)ˣ).measurableEmbedding]
    rw [hinv]
    refine lintegral_congr fun b => ?_
    have hb0 : ((b : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := b.ne_zero
    have hbn : ‖((b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ₑ ≠ 0 := by simp
    simp only [hG, hG', Units.val_inv_eq_inv_val, Set.indicator, Set.mem_setOf_eq, norm_inv]
    by_cases h : 1 < ‖((b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖
    · rw [if_pos (inv_lt_one_of_one_lt₀ h), if_pos h, enorm_inv hb0, inv_inv, inv_inv, sq,
        ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hbn enorm_ne_top, one_mul]
    · have h' : ¬ ‖((b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖⁻¹ < 1 := fun hlt =>
        h ((inv_lt_one₀ (norm_pos_iff.2 hb0)).1 hlt)
      rw [if_neg h', if_neg h, mul_zero, mul_zero]
  rw [hkey, hR'] at hL'
  exact (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) (ENNReal.inv_ne_top.2 hc₁0)).1 hL'.symm

end MeasureFacts

section Pushforward

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  isMulRightInvariant_localHaar

theorem measurableSet_K1 : MeasurableSet (K1 K v) := (isOpen_K1 K v).measurableSet

theorem measurableSet_K2 : MeasurableSet (K2 K v) :=
  ((isClosed_localIntegralSet' K v).measurableSet).inter
    ((isOpen_lt (continuous_norm.comp (continuous_eδ K v)) continuous_const).measurableSet)

theorem K1_union_K2 : K1 K v ∪ K2 K v = localIntegralSet K v := by
  ext g
  simp only [K1, K2, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases (norm_entry_le_one_of_mem K v h 1 1).lt_or_eq with hlt | heq
    · exact Or.inr ⟨h, hlt⟩
    · exact Or.inl ⟨h, heq⟩

theorem disjoint_K1_K2 : Disjoint (K1 K v) (K2 K v) := by
  rw [Set.disjoint_left]
  rintro g ⟨-, h1⟩ ⟨-, h2⟩
  rw [h1] at h2; exact lt_irrefl _ h2

theorem K1_eq_inter : K1 K v = ratio K v ⁻¹' Metric.closedBall 0 1 ∩ Dset K v := by
  ext g; rw [mem_K1_iff]; simp [and_comm]

theorem mul_weylGL_apply (g : GL (Fin 2) (v.adicCompletion K)) :
    eδ K v (g * weylGL K v) = eγ K v g ∧ eγ K v (g * weylGL K v) = eδ K v g := by
  simp [eδ, eγ, Units.val_mul, weylGL_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_weylGL_mem_K2_iff (g : GL (Fin 2) (v.adicCompletion K)) :
    g * weylGL K v ∈ K2 K v ↔ g ∈ K1 K v ∧ ‖ratio K v g‖ < 1 := by
  obtain ⟨h1, h2⟩ := mul_weylGL_apply K v g
  simp only [K2, K1, Set.mem_setOf_eq, mul_mem_localIntegralSet_iff_left K v (weylGL_mem K v), h1]
  constructor
  · rintro ⟨hk, hγ⟩
    have hδ : ‖eδ K v g‖ = 1 := by
      have := norm_eγ_eq_one_of_lt K v (k := g * weylGL K v)
        ((mul_mem_localIntegralSet_iff_left K v (weylGL_mem K v)).2 hk) (by rw [h1]; exact hγ)
      rwa [h2] at this
    exact ⟨⟨hk, hδ⟩, by rw [ratio, norm_div, hδ, div_one]; exact hγ⟩
  · rintro ⟨⟨hk, hδ⟩, hr⟩
    rw [ratio, norm_div, hδ, div_one] at hr
    exact ⟨hk, hr⟩

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]

theorem setLIntegral_Dset_comp_ratio {c : ℝ≥0} (hc : rhoD K v = c • μ) (F : v.adicCompletion K → ℝ≥0∞)
    (hF : Measurable F) (B : Set (v.adicCompletion K)) (hB : MeasurableSet B) :
    ∫⁻ k in ratio K v ⁻¹' B ∩ Dset K v, F (ratio K v k) ∂(localHaar K v) = c * ∫⁻ y in B, F y ∂μ := by
  have h1 : ∫⁻ y, B.indicator F y ∂(rhoD K v) = ∫⁻ k in Dset K v, B.indicator F (ratio K v k) ∂(localHaar K v) := by
    rw [rhoD, lintegral_map (hF.indicator hB) (measurable_ratio K v)]
  rw [hc, lintegral_smul_measure, lintegral_indicator hB] at h1
  rw [← lintegral_indicator hB] at h1
  have h2 : ∫⁻ k in Dset K v, B.indicator F (ratio K v k) ∂(localHaar K v) =
      ∫⁻ k in ratio K v ⁻¹' B ∩ Dset K v, F (ratio K v k) ∂(localHaar K v) := by
    simp_rw [← Set.indicator_comp_right (ratio K v)]
    rw [lintegral_indicator ((measurable_ratio K v) hB), Measure.restrict_restrict ((measurable_ratio K v) hB)]
    rfl
  rw [← h2, ← h1, lintegral_indicator hB]
  rfl

include ν in
open scoped Valued in

theorem setLIntegral_localIntegralSet_ratio {c : ℝ≥0} (hc : rhoD K v = c • μ)
    (m : v.adicCompletion K → ℝ≥0∞) (hm : Measurable m) :
    ∫⁻ k in localIntegralSet K v, ‖eδ K v k‖ₑ⁻¹ ^ 2 * m (ratio K v k) ∂(localHaar K v) = c * ∫⁻ y, m y ∂μ := by
  haveI : NullSingletonClass μ := Measure.IsAddHaarMeasure.nullSingletonClass (μ := μ)
  set f : GL (Fin 2) (v.adicCompletion K) → ℝ≥0∞ := fun k => ‖eδ K v k‖ₑ⁻¹ ^ 2 * m (ratio K v k) with hf
  have hB₁ : MeasurableSet (Metric.closedBall (0 : v.adicCompletion K) 1) := measurableSet_closedBall
  have hB₂ : MeasurableSet {y : v.adicCompletion K | ‖y‖ < 1} := (isOpen_lt continuous_norm continuous_const).measurableSet

  have hK1 : ∫⁻ k in K1 K v, f k ∂(localHaar K v) = c * ∫⁻ y in Metric.closedBall 0 1, m y ∂μ := by
    have h1 : ∫⁻ k in K1 K v, f k ∂(localHaar K v) = ∫⁻ k in K1 K v, m (ratio K v k) ∂(localHaar K v) := by
      refine setLIntegral_congr_fun (measurableSet_K1 K v) (fun k hk => ?_)
      have : ‖eδ K v k‖ₑ = 1 := by
        rw [← ofReal_norm_eq_enorm, hk.2, ENNReal.ofReal_one]
      simp only [hf, this, inv_one, one_pow, one_mul]
    rw [h1, K1_eq_inter, setLIntegral_Dset_comp_ratio K v μ hc m hm _ hB₁]

  set G : v.adicCompletion K → ℝ≥0∞ := fun y => ‖y‖ₑ⁻¹ ^ 2 * m y⁻¹ with hG
  have hGm : Measurable G := ((measurable_enorm.inv).pow_const 2).mul (hm.comp (measurable_inv' K v))
  have hK2 : ∫⁻ k in K2 K v, f k ∂(localHaar K v) = c * ∫⁻ z in {z | 1 < ‖z‖}, m z ∂μ := by
    have h1 : ∫⁻ k in K2 K v, f k ∂(localHaar K v) =
        ∫⁻ k, (K2 K v).indicator f (k * weylGL K v) ∂(localHaar K v) := by
      rw [lintegral_mul_right_eq_self, lintegral_indicator (measurableSet_K2 K v)]
    have h2 : (fun k => (K2 K v).indicator f (k * weylGL K v)) =
        (ratio K v ⁻¹' {y | ‖y‖ < 1} ∩ Dset K v).indicator (fun k => G (ratio K v k)) := by
      funext k
      by_cases hk : k * weylGL K v ∈ K2 K v
      · obtain ⟨hk1, hr⟩ := (mul_weylGL_mem_K2_iff K v k).1 hk
        have hk' : k ∈ ratio K v ⁻¹' {y | ‖y‖ < 1} ∩ Dset K v := ⟨hr, ((mem_K1_iff K v k).1 hk1).1⟩
        rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk']
        obtain ⟨e1, e2⟩ := mul_weylGL_apply K v k
        have hδ1 : ‖eδ K v k‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, hk1.2, ENNReal.ofReal_one]
        simp only [hf, hG, ratio, e1, e2, inv_div]
        rw [show ‖eγ K v k / eδ K v k‖ₑ = ‖eγ K v k‖ₑ by
          rw [← ofReal_norm_eq_enorm, norm_div, hk1.2, div_one, ofReal_norm_eq_enorm]]
      · have hk' : k ∉ ratio K v ⁻¹' {y | ‖y‖ < 1} ∩ Dset K v := fun h =>
          hk ((mul_weylGL_mem_K2_iff K v k).2 ⟨(mem_K1_iff K v k).2 ⟨h.2, le_of_lt h.1⟩, h.1⟩)
        rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk']
    rw [h1, h2, lintegral_indicator (((measurable_ratio K v) hB₂).inter (measurableSet_Dset K v)),
      setLIntegral_Dset_comp_ratio K v μ hc G hGm _ hB₂, ← lintegral_inv_sq_comp_inv K v μ ν m hm]
    congr 1

    have hset : {y : v.adicCompletion K | y ≠ 0 ∧ ‖y‖ < 1} = {y | ‖y‖ < 1} \ {0} := by
      ext y; simp [and_comm]
    rw [hset, hG]
    exact (setLIntegral_congr (diff_null_ae_eq_self (measure_singleton (0 : v.adicCompletion K)))).symm

  rw [← K1_union_K2, lintegral_union (measurableSet_K2 K v) (disjoint_K1_K2 K v), hK1, hK2, ← mul_add]
  congr 1
  have hcompl : {z : v.adicCompletion K | 1 < ‖z‖} = (Metric.closedBall (0 : v.adicCompletion K) 1)ᶜ := by
    ext z; simp
  rw [hcompl, lintegral_add_compl _ hB₁]

end Pushforward

section Identity

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  isMulRightInvariant_localHaar

theorem continuous_unipotentGL2' :
    Continuous (fun y : v.adicCompletion K => (unipotentGL2 y : GL (Fin 2) (v.adicCompletion K))) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun y : v.adicCompletion K => ((unipotentGL2 y : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun y : v.adicCompletion K => (((unipotentGL2 y)⁻¹ : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = fun y => !![1, -y; 0, 1] := rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_conjGL :
    Continuous (conjGL : GL (Fin 2) (v.adicCompletion K) × v.adicCompletion K → GL (Fin 2) (v.adicCompletion K)) := by
  unfold conjGL
  exact (continuous_fst.inv.mul ((continuous_unipotentGL2' K v).comp continuous_snd)).mul continuous_fst

theorem continuous_sGL' :
    Continuous (fun q : (v.adicCompletion K)ˣ × v.adicCompletion K => (sGL q.2 q.1 : GL (Fin 2) (v.adicCompletion K))) := by
  have hb : Continuous fun q : (v.adicCompletion K)ˣ × v.adicCompletion K => ((q.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
    Units.continuous_val.comp continuous_fst
  have hbi : Continuous fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      (((q.1⁻¹ : (v.adicCompletion K)ˣ) : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
    Units.continuous_val.comp continuous_fst.inv
  have ha : Continuous fun q : (v.adicCompletion K)ˣ × v.adicCompletion K => q.2 := continuous_snd
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
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

theorem continuous_chartGL :
    Continuous (chartGL : (v.adicCompletion K)ˣ × v.adicCompletion K → GL (Fin 2) (v.adicCompletion K)) := by
  unfold chartGL
  exact ((continuous_sGL' K v).inv.mul continuous_const).mul (continuous_sGL' K v)

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]

open scoped Valued in
omit [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] in
theorem noAtoms_haar : NullSingletonClass μ := Measure.IsAddHaarMeasure.nullSingletonClass (μ := μ)

def Wset (A : Set (GL (Fin 2) (v.adicCompletion K))) : Set (v.adicCompletion K × (v.adicCompletion K)ˣ) :=
  {q | chartGL (q.2, (q.2 : v.adicCompletion K) * q.1) ∈ A}

def Tset (A : Set (GL (Fin 2) (v.adicCompletion K))) : Set (v.adicCompletion K × v.adicCompletion K) :=
  Prod.map id Units.val '' Wset K v A

def mA (A : Set (GL (Fin 2) (v.adicCompletion K))) (y : v.adicCompletion K) : ℝ≥0∞ := μ (Prod.mk y ⁻¹' Tset K v A)

omit [BorelSpace (v.adicCompletion K)] [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] in
theorem mem_Tset_iff (A : Set (GL (Fin 2) (v.adicCompletion K))) (y x : v.adicCompletion K) :
    (y, x) ∈ Tset K v A ↔ ∃ h : x ≠ 0, chartGL (Units.mk0 x h, x * y) ∈ A := by
  simp only [Tset, Wset, Set.mem_image, Set.mem_setOf_eq, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨y', b, hb, rfl, rfl⟩
    exact ⟨b.ne_zero, by rw [Units.mk0_val]; exact hb⟩
  · rintro ⟨h, hA⟩
    exact ⟨y, Units.mk0 x h, hA, rfl, rfl⟩

omit [BorelSpace (v.adicCompletion K)] [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] in
theorem units_mem_Tset_iff (A : Set (GL (Fin 2) (v.adicCompletion K))) (y : v.adicCompletion K)
    (b : (v.adicCompletion K)ˣ) :
    (y, (b : v.adicCompletion K)) ∈ Tset K v A ↔ chartGL (b, (b : v.adicCompletion K) * y) ∈ A := by
  rw [mem_Tset_iff]
  constructor
  · rintro ⟨h, hA⟩; rwa [Units.mk0_val] at hA
  · intro hA; exact ⟨b.ne_zero, by rwa [Units.mk0_val]⟩

theorem measurableSet_Wset {A : Set (GL (Fin 2) (v.adicCompletion K))} (hA : MeasurableSet A) :
    MeasurableSet (Wset K v A) := by
  have hc : Continuous fun q : v.adicCompletion K × (v.adicCompletion K)ˣ =>
      chartGL (q.2, (q.2 : v.adicCompletion K) * q.1) :=
    (continuous_chartGL K v).comp (continuous_snd.prodMk ((Units.continuous_val.comp continuous_snd).mul continuous_fst))
  exact hc.measurable hA

theorem measurableSet_Tset {A : Set (GL (Fin 2) (v.adicCompletion K))} (hA : MeasurableSet A) :
    MeasurableSet (Tset K v A) :=
  (MeasurableEmbedding.prodMap MeasurableEmbedding.id (measurableEmbedding_units_val K v)).measurableSet_image'
    (measurableSet_Wset K v hA)

theorem measurable_mA {A : Set (GL (Fin 2) (v.adicCompletion K))} (hA : MeasurableSet A) : Measurable (mA K v μ A) :=
  measurable_measure_prodMk_left (measurableSet_Tset K v hA)

theorem measure_fibre_conjGL (A : Set (GL (Fin 2) (v.adicCompletion K)))
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ localIntegralSet K v) (hδ : eδ K v k ≠ 0) :
    μ (Prod.mk k ⁻¹' (conjGL ⁻¹' A)) = ‖eδ K v k‖ₑ⁻¹ ^ 2 * mA K v μ A (ratio K v k) := by
  haveI : NullSingletonClass μ := noAtoms_haar K v μ
  have hΔ := det_coe_ne_zero k
  have hdet1 : ‖(k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = 1 := norm_det_eq_one_of_mem K v hk
  have hδ' : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := hδ
  obtain ⟨cδ, hcδ⟩ : ∃ cδ : v.adicCompletion K,
      cδ = eδ K v k ^ 2 / (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := ⟨_, rfl⟩
  have hcδ0 : cδ ≠ 0 := by rw [hcδ]; exact div_ne_zero (pow_ne_zero _ hδ) hΔ

  have hpair : ∀ (x : v.adicCompletion K) (hx : x ≠ 0),
      (Units.mk0 (x * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ^ 2 /
          (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det)
          (div_ne_zero (mul_ne_zero hx (pow_ne_zero _ hδ)) (det_coe_ne_zero k)),
        x * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 /
          (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) =
        (Units.mk0 (cδ * x) (mul_ne_zero hcδ0 hx), cδ * x * ratio K v k) := by
    intro x hx
    refine Prod.ext (Units.ext ?_) ?_
    · simp only [Units.val_mk0, hcδ, eδ]; ring
    · simp only [hcδ, eδ, eγ, ratio]; field_simp

  have hagree : ∀ x : v.adicCompletion K, x ≠ 0 →
      (x ∈ Prod.mk k ⁻¹' (conjGL ⁻¹' A) ↔ x ∈ (fun x => cδ * x) ⁻¹' (Prod.mk (ratio K v k) ⁻¹' Tset K v A)) := by
    intro x hx
    have e1 : x ∈ Prod.mk k ⁻¹' (conjGL ⁻¹' A) ↔ conjGL (k, x) ∈ A := Iff.rfl
    have e2 : x ∈ (fun x => cδ * x) ⁻¹' (Prod.mk (ratio K v k) ⁻¹' Tset K v A) ↔
        (ratio K v k, cδ * x) ∈ Tset K v A := Iff.rfl
    rw [e1, e2, mem_Tset_iff, conjGL_eq_chartGL k hx hδ', hpair x hx]
    exact ⟨fun h => ⟨mul_ne_zero hcδ0 hx, h⟩, fun ⟨_, h⟩ => h⟩
  have hae : (Prod.mk k ⁻¹' (conjGL ⁻¹' A) : Set (v.adicCompletion K)) =ᵐ[μ]
      ((fun x => cδ * x) ⁻¹' (Prod.mk (ratio K v k) ⁻¹' Tset K v A) : Set (v.adicCompletion K)) := by
    have h1 : (Prod.mk k ⁻¹' (conjGL ⁻¹' A) \ {0} : Set (v.adicCompletion K)) =ᵐ[μ]
        (Prod.mk k ⁻¹' (conjGL ⁻¹' A) : Set (v.adicCompletion K)) := diff_null_ae_eq_self (measure_singleton 0)
    have h2 : ((fun x => cδ * x) ⁻¹' (Prod.mk (ratio K v k) ⁻¹' Tset K v A) \ {0} : Set (v.adicCompletion K)) =ᵐ[μ]
        ((fun x => cδ * x) ⁻¹' (Prod.mk (ratio K v k) ⁻¹' Tset K v A) : Set (v.adicCompletion K)) :=
      diff_null_ae_eq_self (measure_singleton 0)
    have h12 : (Prod.mk k ⁻¹' (conjGL ⁻¹' A) \ {0} : Set (v.adicCompletion K)) =
        (fun x => cδ * x) ⁻¹' (Prod.mk (ratio K v k) ⁻¹' Tset K v A) \ {0} := by
      ext x
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, hx⟩; exact ⟨(hagree x hx).1 h, hx⟩
      · rintro ⟨h, hx⟩; exact ⟨(hagree x hx).2 h, hx⟩
    rw [h12] at h1
    exact h1.symm.trans h2
  rw [measure_congr hae]
  have hscale := measure_preimage_mul' K v μ (Units.mk0 cδ hcδ0) (Prod.mk (ratio K v k) ⁻¹' Tset K v A)
  rw [Units.val_mk0] at hscale
  rw [hscale, mA]
  congr 1
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hcδ, norm_div, hdet1, div_one, norm_pow,
    ENNReal.ofReal_pow (norm_nonneg _), ENNReal.inv_pow]

def Pmeas : Measure (GL (Fin 2) (v.adicCompletion K)) :=
  (((localHaar K v).restrict (localIntegralSet K v)).prod μ).map conjGL

def Qmeas : Measure (GL (Fin 2) (v.adicCompletion K)) := (ν.prod μ).map chartGL

theorem measurableSet_localIntegralSet : MeasurableSet (localIntegralSet K v) :=
  (isClosed_localIntegralSet' K v).measurableSet

include ν in
theorem Pmeas_apply {c : ℝ≥0} (hc : rhoD K v = c • μ) {A : Set (GL (Fin 2) (v.adicCompletion K))}
    (hA : MeasurableSet A) : Pmeas K v μ A = c * ∫⁻ y, mA K v μ A y ∂μ := by
  rw [Pmeas, Measure.map_apply (continuous_conjGL K v).measurable hA,
    Measure.prod_apply ((continuous_conjGL K v).measurable hA),
    ← setLIntegral_localIntegralSet_ratio K v μ ν hc (mA K v μ A) (measurable_mA K v μ hA)]
  refine setLIntegral_congr_fun_ae (measurableSet_localIntegralSet K v) ?_
  have hN : ∀ᵐ k ∂(localHaar K v), k ∉ N0 K v := (measure_eq_zero_iff_ae_notMem).1 (measure_N0 K v)
  filter_upwards [hN] with k hk hk0
  have hδ : eδ K v k ≠ 0 := fun h => hk ⟨hk0, h⟩
  exact measure_fibre_conjGL K v μ A hk0 hδ

theorem Qmeas_apply {c₁ : ℝ≥0}
    (hB : ∀ G : v.adicCompletion K → ℝ≥0∞, Measurable G →
      ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * G b ∂ν = (c₁ : ℝ≥0∞)⁻¹ * ∫⁻ x in {0}ᶜ, G x ∂μ)
    {A : Set (GL (Fin 2) (v.adicCompletion K))} (hA : MeasurableSet A) :
    Qmeas K v μ ν A = (c₁ : ℝ≥0∞)⁻¹ * ∫⁻ y, mA K v μ A y ∂μ := by
  have hW := measurableSet_Wset K v hA
  rw [Qmeas, Measure.map_apply (continuous_chartGL K v).measurable hA,
    Measure.prod_apply ((continuous_chartGL K v).measurable hA)]

  have hfib : ∀ b : (v.adicCompletion K)ˣ, μ (Prod.mk b ⁻¹' (chartGL ⁻¹' A)) =
      ‖(b : v.adicCompletion K)‖ₑ * ∫⁻ y, (Wset K v A).indicator 1 (y, b) ∂μ := by
    intro b
    have hset : Prod.mk b ⁻¹' (chartGL ⁻¹' A) =
        (fun y => (b : v.adicCompletion K) * y) '' {y | chartGL (b, (b : v.adicCompletion K) * y) ∈ A} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro ha
        refine ⟨(b : v.adicCompletion K)⁻¹ * a, ?_, ?_⟩
        · rwa [← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul]
        · rw [← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul]
      · rintro ⟨y, hy, rfl⟩; exact hy
    rw [hset, measure_image_mul]
    congr 1
    have hmeas : MeasurableSet {y : v.adicCompletion K | chartGL (b, (b : v.adicCompletion K) * y) ∈ A} :=
      (measurable_prodMk_right (m := inferInstance)) hW
    rw [← lintegral_indicator_one hmeas]
    rfl
  simp_rw [hfib]

  have hmeasF : Measurable fun q : (v.adicCompletion K)ˣ × v.adicCompletion K =>
      ‖(q.1 : v.adicCompletion K)‖ₑ * (Wset K v A).indicator 1 (q.2, q.1) :=
    ((Units.continuous_val.measurable.comp measurable_fst).enorm).mul
      ((measurable_one.indicator hW).comp measurable_swap)
  have hswap : ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * ∫⁻ y, (Wset K v A).indicator 1 (y, b) ∂μ ∂ν =
      ∫⁻ y, ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * (Wset K v A).indicator 1 (y, b) ∂ν ∂μ := by
    have : ∀ b : (v.adicCompletion K)ˣ, ‖(b : v.adicCompletion K)‖ₑ * ∫⁻ y, (Wset K v A).indicator 1 (y, b) ∂μ =
        ∫⁻ y, ‖(b : v.adicCompletion K)‖ₑ * (Wset K v A).indicator 1 (y, b) ∂μ := fun b => by
      have hmb : Measurable (fun y : v.adicCompletion K =>
          (Wset K v A).indicator (1 : v.adicCompletion K × (v.adicCompletion K)ˣ → ℝ≥0∞) (y, b)) :=
        (measurable_one.indicator hW).comp measurable_prodMk_right
      exact (lintegral_const_mul _ hmb).symm
    simp_rw [this]
    exact lintegral_lintegral_swap hmeasF.aemeasurable
  rw [hswap]

  have hinner : ∀ y : v.adicCompletion K,
      ∫⁻ b, ‖(b : v.adicCompletion K)‖ₑ * (Wset K v A).indicator 1 (y, b) ∂ν = (c₁ : ℝ≥0∞)⁻¹ * mA K v μ A y := by
    intro y
    have hT : MeasurableSet (Prod.mk y ⁻¹' Tset K v A) := measurable_prodMk_left (measurableSet_Tset K v hA)
    have h1 := hB ((Prod.mk y ⁻¹' Tset K v A).indicator 1) (measurable_one.indicator hT)
    have hG : ∀ b : (v.adicCompletion K)ˣ, (Prod.mk y ⁻¹' Tset K v A).indicator (1 : v.adicCompletion K → ℝ≥0∞) b =
        (Wset K v A).indicator 1 (y, b) := by
      intro b
      by_cases hb : chartGL (b, (b : v.adicCompletion K) * y) ∈ A
      · rw [Set.indicator_of_mem (show (b : v.adicCompletion K) ∈ Prod.mk y ⁻¹' Tset K v A from
          (units_mem_Tset_iff K v A y b).2 hb), Set.indicator_of_mem (show (y, b) ∈ Wset K v A from hb)]
        rfl
      · rw [Set.indicator_of_notMem (show (b : v.adicCompletion K) ∉ Prod.mk y ⁻¹' Tset K v A from
          fun h => hb ((units_mem_Tset_iff K v A y b).1 h)),
          Set.indicator_of_notMem (show (y, b) ∉ Wset K v A from hb)]
    simp_rw [hG] at h1
    rw [h1, lintegral_indicator_one hT, Measure.restrict_apply hT, mA]
    congr 2
    refine Set.inter_eq_self_of_subset_left fun x hx => ?_
    exact ((mem_Tset_iff K v A y x).1 hx).1
  simp_rw [hinner]
  rw [lintegral_const_mul _ (measurable_mA K v μ hA)]

theorem exists_Pmeas_eq_smul_Qmeas : ∃ c₀ : ℝ≥0, 0 < c₀ ∧ Pmeas K v μ = (c₀ : ℝ≥0∞) • Qmeas K v μ ν := by
  obtain ⟨c, hc, hcE⟩ := exists_rhoD_eq_smul K v μ
  obtain ⟨c₁, hc₁, hB⟩ := exists_lintegral_units_eq K v μ ν
  refine ⟨c * c₁, mul_pos hc hc₁, Measure.ext fun A hA => ?_⟩
  rw [Pmeas_apply K v μ ν hcE hA, Measure.smul_apply, Qmeas_apply K v μ ν hB hA, smul_eq_mul, ← mul_assoc,
    ENNReal.coe_mul, mul_assoc (c : ℝ≥0∞), ENNReal.mul_inv_cancel (by exact_mod_cast hc₁.ne') ENNReal.coe_ne_top,
    mul_one]

end Identity

section Final

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  isMulRightInvariant_localHaar

theorem exists_bound_unipotent (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : HasCompactSupport fv) :
    ∃ R : ℝ, ∀ k ∈ localIntegralSet K v, ∀ x : v.adicCompletion K, fv (conjGL (k, x)) ≠ 0 → ‖x‖ ≤ R := by
  set S : Set (GL (Fin 2) (v.adicCompletion K)) :=
    (fun t : GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) × GL (Fin 2) (v.adicCompletion K) =>
      t.1 * t.2.1 * t.2.2) '' (localIntegralSet K v ×ˢ (tsupport fv ×ˢ localIntegralSet K v)) with hS
  have hSc : IsCompact S :=
    ((isCompact_localIntegralSet K v).prod (hfv.isCompact.prod (isCompact_localIntegralSet K v))).image
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul (continuous_snd.comp continuous_snd))
  obtain ⟨R, hR⟩ := hSc.exists_bound_of_continuousOn
    ((Units.continuous_val.matrix_elem 0 1).continuousOn (s := S))
  refine ⟨R, fun k hk x hx => ?_⟩
  have hmem : unipotentGL2 x ∈ S := by
    refine ⟨(k, conjGL (k, x), k⁻¹), ⟨hk, subset_tsupport _ (Function.mem_support.2 hx), inv_mem_localIntegralSet K v hk⟩, ?_⟩
    simp only [conjGL]; group
  have := hR _ hmem
  simpa [unipotentGL2_coe] using this

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]

theorem integrable_conj (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : IsLocalTestFn K v fv) :
    Integrable (fun p : GL (Fin 2) (v.adicCompletion K) × v.adicCompletion K => fv (conjGL p))
      (((localHaar K v).restrict (localIntegralSet K v)).prod μ) := by
  obtain ⟨B, hB⟩ := hfv.1.continuous.bounded_above_of_compact_support hfv.2
  obtain ⟨R, hR⟩ := exists_bound_unipotent K v fv hfv.2
  have hcont : Continuous fun p : GL (Fin 2) (v.adicCompletion K) × v.adicCompletion K => fv (conjGL p) :=
    hfv.1.continuous.comp (continuous_conjGL K v)
  have hprod : ((localHaar K v).restrict (localIntegralSet K v)).prod μ =
      ((localHaar K v).prod μ).restrict (localIntegralSet K v ×ˢ Set.univ) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ)]
    exact Measure.prod_restrict _ _
  rw [hprod]
  change IntegrableOn _ _ _
  set s : Set (GL (Fin 2) (v.adicCompletion K) × v.adicCompletion K) :=
    localIntegralSet K v ×ˢ Metric.closedBall (0 : v.adicCompletion K) R with hs
  have hsfin : ((localHaar K v).prod μ) s ≠ ⊤ := by
    rw [hs, Measure.prod_prod]
    exact ENNReal.mul_ne_top (isCompact_localIntegralSet K v).measure_lt_top.ne
      (isCompact_closedBall (0 : v.adicCompletion K) R).measure_lt_top.ne
  have hint : IntegrableOn (fun p : GL (Fin 2) (v.adicCompletion K) × v.adicCompletion K => fv (conjGL p)) s
      ((localHaar K v).prod μ) := by
    haveI : IsFiniteMeasure (((localHaar K v).prod μ).restrict s) := isFiniteMeasure_restrict.2 hsfin
    exact (integrable_const B).mono' hcont.aestronglyMeasurable (ae_of_all _ fun p => hB _)
  refine hint.of_forall_diff_eq_zero ((measurableSet_localIntegralSet K v).prod MeasurableSet.univ) ?_
  rintro ⟨k, x⟩ ⟨⟨hk, -⟩, hns⟩
  by_contra hne
  apply hns
  refine ⟨hk, ?_⟩
  simpa using hR k hk x hne

theorem final
    (σ : v.adicCompletion K → (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K))
    (hσ : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ),
      (σ a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; a, (b : v.adicCompletion K)]) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv →
        (∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
            (∫ x, fv (k⁻¹ * unipotentGL2 x * k) ∂μ) ∂(localHaar K v)) =
        (c₀ : ℂ) * ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
            fv ((σ q.2 q.1)⁻¹ * unipotentGL2 1 * σ q.2 q.1) ∂(ν.prod μ) := by
  obtain ⟨c₀, hc₀, hPQ⟩ := exists_Pmeas_eq_smul_Qmeas K v μ ν
  refine ⟨c₀, by exact_mod_cast hc₀, fun fv hfv => ?_⟩
  have hσS : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ), σ a b = sGL a b := fun a b => Units.ext (hσ a b)
  have hmeas : MeasurableSet (localIntegralSet K v) := (isClosed_localIntegralSet' K v).measurableSet

  have hA : (∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
      (∫ x, fv (k⁻¹ * unipotentGL2 x * k) ∂μ) ∂(localHaar K v)) =
      ∫ k in localIntegralSet K v, (∫ x, fv (conjGL (k, x)) ∂μ) ∂(localHaar K v) := by
    rw [← integral_indicator hmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    by_cases hk : k ∈ localIntegralSet K v
    · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, one_mul]; rfl
    · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]

  have hB : ∫ k in localIntegralSet K v, (∫ x, fv (conjGL (k, x)) ∂μ) ∂(localHaar K v) = ∫ g, fv g ∂(Pmeas K v μ) := by
    rw [Pmeas, integral_map (continuous_conjGL K v).measurable.aemeasurable hfv.1.continuous.aestronglyMeasurable,
      integral_prod _ (integrable_conj K v μ fv hfv)]

  have hC : ∫ g, fv g ∂(Qmeas K v μ ν) =
      ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, fv ((σ q.2 q.1)⁻¹ * unipotentGL2 1 * σ q.2 q.1) ∂(ν.prod μ) := by
    rw [Qmeas, integral_map (continuous_chartGL K v).measurable.aemeasurable hfv.1.continuous.aestronglyMeasurable]
    simp_rw [hσS]
    rfl
  rw [hA, hB, hPQ, integral_smul_measure, hC, ENNReal.coe_toReal, Complex.real_smul]

end Final

end P2mUnipotentChart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart.P2mUnipotentChart"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (σ : v.adicCompletion K → (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K))
    (hσ : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ),
      (σ a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; a, (b : v.adicCompletion K)])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure] :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv →
        (letI := AutomorphicForm.localGLBorel K v
          ∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
            (∫ x, fv (k⁻¹ * AutomorphicForm.unipotentGL2 x * k) ∂μ) ∂(AutomorphicForm.localHaar K v)) =
        (c₀ : ℂ) * ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
            fv ((σ q.2 q.1)⁻¹ * AutomorphicForm.unipotentGL2 1 * σ q.2 q.1) ∂(ν.prod μ) :=
  P2mUnipotentChart.final K v μ ν σ hσ

end
end S_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_integral_localIntegralSet_integral_unipotentGL2_conj_eq_mul_integral_affineChart (solution)
