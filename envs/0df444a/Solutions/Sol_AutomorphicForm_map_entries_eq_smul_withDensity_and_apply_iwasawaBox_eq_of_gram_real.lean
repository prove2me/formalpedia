-- Prove2me | solution 1 for AutomorphicForm.map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f496fbce-5132-51ee-a459-24ec0a1eeed6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Set AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal

noncomputable section

namespace P2mGramBox

abbrev Ecx : Type := ℂ ⊗[ℝ] ℝ

abbrev Mcx : Type := Matrix (Fin 2) (Fin 2) Ecx

abbrev MR : Type := Matrix (Fin 2) (Fin 2) ℝ

abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

def ridE : Ecx ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ridE_tmul (l : ℂ) (a : ℝ) : ridE (l ⊗ₜ[ℝ] a) = a • l := rfl

theorem ridE_comm_symm (w : ℝ ⊗[ℝ] ℂ) :
    ridE ((TensorProduct.comm ℝ ℂ ℝ).symm w) = TensorProduct.lid ℝ ℂ w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul r z => rw [TensorProduct.comm_symm_tmul, ridE_tmul, TensorProduct.lid_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem ridE_smul (r : ℝ) (x : Ecx) : ridE (r • x) = r • ridE x := by
  rw [TensorProduct.RightActions.smul_def, ridE_comm_symm, LinearEquiv.map_smul, ← ridE_comm_symm,
    LinearEquiv.symm_apply_apply]

def ridL : Ecx ≃ₗ[ℝ] ℂ :=
  { ridE.toAddEquiv with map_smul' := fun r x => ridE_smul r x }

theorem finrank_Ecx : Module.finrank ℝ Ecx = 2 := by
  rw [ridL.finrank_eq, Complex.finrank_real_complex]

def iotaE (a : ℝ) : Ecx := (1 : ℂ) ⊗ₜ[ℝ] a

theorem iotaE_eq_algebraMap (a : ℝ) : iotaE a = algebraMap ℝ Ecx a := rfl

theorem ridE_iotaE (a : ℝ) : ridE (iotaE a) = (a : ℂ) := by
  rw [iotaE, ridE_tmul, Complex.real_smul, mul_one]

theorem iotaE_injective : Function.Injective iotaE := by
  intro a b h
  have := congrArg ridE h
  rw [ridE_iotaE, ridE_iotaE] at this
  exact_mod_cast this

theorem trace_iotaE (a : ℝ) : Algebra.trace ℝ Ecx (iotaE a) = 2 * a := by
  rw [iotaE_eq_algebraMap, Algebra.trace_algebraMap, finrank_Ecx, nsmul_eq_mul, Nat.cast_ofNat]

theorem norm_iotaE (a : ℝ) : Algebra.norm ℝ (iotaE a) = a ^ 2 := by
  rw [iotaE_eq_algebraMap, Algebra.norm_algebraMap, finrank_Ecx]

theorem real_smul_eq (r : ℝ) (e : Ecx) : r • e = iotaE r * e := Algebra.smul_def r e

def iotaM (Y : MR) : Mcx := Y.map fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ)

theorem iotaM_apply (Y : MR) (i j : Fin 2) : iotaM Y i j = iotaE (Y i j) := rfl

theorem iotaM_eq_mapMatrix (Y : MR) : iotaM Y = (algebraMap ℝ Ecx).mapMatrix Y := rfl

theorem iotaM_mul (X Y : MR) : iotaM (X * Y) = iotaM X * iotaM Y := by
  rw [iotaM_eq_mapMatrix, iotaM_eq_mapMatrix, iotaM_eq_mapMatrix, map_mul]

theorem iotaM_add (X Y : MR) : iotaM (X + Y) = iotaM X + iotaM Y := by
  rw [iotaM_eq_mapMatrix, iotaM_eq_mapMatrix, iotaM_eq_mapMatrix, map_add]

theorem iotaM_smul (r : ℝ) (Y : MR) : iotaM (r • Y) = r • iotaM Y := by
  ext i j
  rw [iotaM_apply, Matrix.smul_apply, Matrix.smul_apply, iotaM_apply, smul_eq_mul, real_smul_eq,
    iotaE_eq_algebraMap, iotaE_eq_algebraMap, iotaE_eq_algebraMap, map_mul]

theorem det_iotaM (Y : MR) : (iotaM Y).det = iotaE Y.det := by
  rw [iotaM_eq_mapMatrix, ← RingHom.map_det]; rfl

theorem trace_iotaM (Y : MR) : (iotaM Y).trace = iotaE Y.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, iotaM_apply, iotaM_apply, iotaE_eq_algebraMap,
    iotaE_eq_algebraMap, iotaE_eq_algebraMap, map_add]

theorem iotaM_injective : Function.Injective iotaM := by
  intro X Y h
  ext i j
  exact iotaE_injective (by rw [← iotaM_apply, ← iotaM_apply, h])

def iotaML : MR →ₗ[ℝ] Mcx where
  toFun := iotaM
  map_add' := iotaM_add
  map_smul' := iotaM_smul

theorem iotaML_apply (Y : MR) : iotaML Y = iotaM Y := rfl

scoped instance instIsTopologicalRingEcx : IsTopologicalRing Ecx := isTopologicalRing_tensor ℝ ℂ ℝ
scoped instance instT2Ecx : T2Space Ecx := t2Space_tensor ℝ ℂ ℝ
scoped instance instT2Mcx : T2Space Mcx := inferInstanceAs (T2Space (Fin 2 → Fin 2 → Ecx))
scoped instance instTAGMcx : IsTopologicalAddGroup Mcx := inferInstance
scoped instance instCSMMcx : ContinuousSMul ℝ Mcx := inferInstance
scoped instance instMeasMcx : MeasurableSpace Mcx := borel _
scoped instance instBorelMcx : BorelSpace Mcx := ⟨rfl⟩
scoped instance instMeasGR : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
scoped instance instBorelGR : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
scoped instance instMeasCent (γ : GL (Fin 2) ℝ) :
    MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := centralizerBorel ℝ γ
scoped instance instBorelCent (γ : GL (Fin 2) ℝ) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩

theorem polishSpace_GR : PolishSpace (GL (Fin 2) ℝ) := by
  haveI : PolishSpace (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℝ))
  haveI : PolishSpace (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.polishSpace
  exact Units.isClosedEmbedding_embedProduct.polishSpace

theorem polishSpace_Cent (γ : GL (Fin 2) ℝ) : PolishSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := by
  haveI := polishSpace_GR
  have hcl : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) : Set (GL (Fin 2) ℝ)) := by
    change IsClosed (({γ} : Set (GL (Fin 2) ℝ)).centralizer)
    exact Set.isClosed_centralizer _
  exact hcl.polishSpace

theorem continuous_iotaE : Continuous iotaE := by
  have : (iotaE : ℝ → Ecx) = algebraMap ℝ Ecx := rfl
  rw [this]
  exact continuous_algebraMap ℝ Ecx

theorem continuous_iotaM : Continuous iotaM := continuous_id.matrix_map continuous_iotaE

theorem continuous_algebraNorm : Continuous (Algebra.norm ℝ : Ecx → ℝ) := by
  classical
  set b := Module.finBasis ℝ Ecx
  have h : (Algebra.norm ℝ : Ecx → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous fun x : Ecx => Algebra.leftMulMatrix b x :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  exact hc.matrix_det

section Gram

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [MeasurableSpace V] [BorelSpace V]

def coordMap {n : ℕ} (e : Fin n → V) : (Fin n → ℝ) → V := fun c => ∑ i, c i • e i

theorem continuous_coordMap {n : ℕ} (e : Fin n → V) : Continuous (coordMap e) := by
  unfold coordMap
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_apply i).smul continuous_const

theorem measurable_coordMap {n : ℕ} (e : Fin n → V) : Measurable (coordMap e) :=
  (continuous_coordMap e).measurable

def gramDet (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : ℝ :=
  (Matrix.of fun i j : Fin n => B (e i) (e j)).det

def gramMeasure (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : Measure V :=
  ENNReal.ofReal (Real.sqrt |gramDet B e|) • Measure.map (coordMap e) volume

theorem coordMap_eq_comp {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    coordMap e' = coordMap e ∘ (Matrix.toLin' P) := by
  funext c
  simp only [coordMap, Function.comp_apply, Matrix.toLin'_apply]
  calc ∑ j, c j • e' j = ∑ j, ∑ i, (c j * P i j) • e i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hP j, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
    _ = ∑ i, ∑ j, (c j * P i j) • e i := Finset.sum_comm
    _ = ∑ i, (P.mulVec c) i • e i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        change ∑ j, c j * P i j = ∑ j, P i j * c j
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gramDet_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) :
    gramDet B e' = P.det ^ 2 * gramDet B e := by
  have hG : (Matrix.of fun i j : Fin n => B (e' i) (e' j)) =
      P.transpose * (Matrix.of fun i j : Fin n => B (e i) (e j)) * P := by
    ext j k
    have hjk : B (e' j) (e' k) = ∑ i, ∑ l, P i j * P l k * B (e i) (e l) := by
      have h1 : B (e' j) = ∑ i, P i j • B (e i) := by rw [hP j, map_sum]; simp only [map_smul]
      rw [h1, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, hP k, map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hjk, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [gramDet, gramDet, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gramMeasure_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ j, e' j = ∑ i, P i j • e i) (hdet : P.det ≠ 0) :
    gramMeasure B e' = gramMeasure B e := by
  rw [gramMeasure, gramMeasure, coordMap_eq_comp e e' P hP, gramDet_eq_of_comp B e e' P hP,
    ← Measure.map_map (measurable_coordMap e) (Matrix.toLin' P).continuous_of_finiteDimensional.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), abs_mul, abs_pow, Real.sqrt_mul' _ (abs_nonneg _),
    Real.sqrt_sq (abs_nonneg _), abs_inv]
  congr 1
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_mul]

theorem exists_matrix_of_span_eq {n : ℕ} (e e' : Fin n → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') ≤ Submodule.span ℝ (Set.range e)) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, (∀ j, e' j = ∑ i, P i j • e i) ∧ P.det ≠ 0 := by
  have hmem : ∀ j, e' j ∈ Submodule.span ℝ (Set.range e) := fun j =>
    hspan (Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hmem j)
  refine ⟨Matrix.of fun i j => c j i, fun j => ?_, ?_⟩
  · simp only [Matrix.of_apply]; exact (hc j).symm
  · intro hdet
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hP : ∀ j, e' j = ∑ i, (Matrix.of fun i j => c j i) i j • e i := fun j => by
      simp only [Matrix.of_apply]; exact (hc j).symm
    have h0 : coordMap e' v = 0 := by
      rw [coordMap_eq_comp e e' _ hP, Function.comp_apply, Matrix.toLin'_apply, hPv]
      simp [coordMap]
    apply hv
    funext j
    exact Fintype.linearIndependent_iff.mp he' v h0 j

theorem card_eq_of_span_eq {n n' : ℕ} (e : Fin n → V) (e' : Fin n' → V) (he : LinearIndependent ℝ e)
    (he' : LinearIndependent ℝ e')
    (hspan : Submodule.span ℝ (Set.range e') = Submodule.span ℝ (Set.range e)) : n' = n := by
  have h1 := finrank_span_eq_card he
  have h2 := finrank_span_eq_card he'
  rw [hspan, h1, Fintype.card_fin, Fintype.card_fin] at h2
  exact h2.symm

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (μ : Measure α) {ρ : β → ℝ≥0∞} (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = (Measure.map f μ).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hρ hf]
  rfl

theorem map_injective_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) {μ ν : Measure α}
    (h : Measure.map f μ = Measure.map f ν) : μ = ν := by
  ext s hs
  have h1 : μ s = Measure.map f μ (f '' s) := by
    rw [hf.map_apply, hf.injective.preimage_image]
  have h2 : ν s = Measure.map f ν (f '' s) := by
    rw [hf.map_apply, hf.injective.preimage_image]
  rw [h1, h2, h]

end Gram

theorem smul_mul_M (r : ℝ) (X Y : Mcx) : (r • X) * Y = r • (X * Y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, real_smul_eq, Finset.mul_sum, mul_assoc]

theorem mul_smul_M (r : ℝ) (X Y : Mcx) : X * (r • Y) = r • (X * Y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, real_smul_eq, Finset.mul_sum, mul_left_comm]

theorem trace_smul_M (r : ℝ) (X : Mcx) : Matrix.trace (r • X) = r • Matrix.trace X := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, real_smul_eq, Finset.mul_sum]

def Bcx : Mcx →ₗ[ℝ] Mcx →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y : Mcx => Algebra.trace ℝ Ecx (Matrix.trace (X * Y)))
    (fun X₁ X₂ Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by
      show Algebra.trace ℝ Ecx (Matrix.trace (r • X * Y)) = r • Algebra.trace ℝ Ecx (Matrix.trace (X * Y))
      rw [smul_mul_M, trace_smul_M, map_smul])
    (fun X Y₁ Y₂ => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by
      show Algebra.trace ℝ Ecx (Matrix.trace (X * (r • Y))) = r • Algebra.trace ℝ Ecx (Matrix.trace (X * Y))
      rw [mul_smul_M, trace_smul_M, map_smul])

theorem Bcx_apply (X Y : Mcx) : Bcx X Y = Algebra.trace ℝ Ecx (Matrix.trace (X * Y)) := rfl

theorem Bcx_iotaM (X Y : MR) : Bcx (iotaM X) (iotaM Y) = 2 * Matrix.trace (X * Y) := by
  rw [Bcx_apply, ← iotaM_mul, trace_iotaM, trace_iotaE]

def rho (X : Mcx) : ℝ≥0∞ := (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹

theorem measurable_rho : Measurable rho := by
  have hc : Continuous fun X : Mcx => |Algebra.norm ℝ (Matrix.det X)| :=
    continuous_abs.comp (continuous_algebraNorm.comp (continuous_id.matrix_det))
  exact (ENNReal.continuous_ofReal.comp hc).measurable.inv

theorem rho_iotaM (Y : MR) : rho (iotaM Y) = (ENNReal.ofReal (Y.det ^ 2))⁻¹ := by
  rw [rho, det_iotaM, norm_iotaE, abs_of_nonneg (sq_nonneg _)]

def rowIdx : Fin 4 → Fin 2 := ![0, 0, 1, 1]

def colIdx : Fin 4 → Fin 2 := ![0, 1, 0, 1]

def stdE (k : Fin 4) : MR := Matrix.single (rowIdx k) (colIdx k) 1

def mk (a : Fin 4 → ℝ) : Ent := ![![a 0, a 1], ![a 2, a 3]]

theorem sum_stdE (a : Fin 4 → ℝ) : ∑ k, a k • stdE k = Matrix.of (mk a) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, stdE, rowIdx, colIdx, mk, Fin.sum_univ_four,
    Matrix.of_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single]

def estd (k : Fin 4) : Mcx := iotaM (stdE k)

theorem coordMap_estd (a : Fin 4 → ℝ) : coordMap estd a = iotaM (Matrix.of (mk a)) := by
  unfold coordMap estd
  rw [← sum_stdE]
  have : ∑ k, a k • iotaM (stdE k) = iotaML (∑ k, a k • stdE k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, iotaML_apply]
  rw [this, iotaML_apply]

theorem linearIndependent_estd : LinearIndependent ℝ estd := by
  rw [Fintype.linearIndependent_iff]
  intro a ha k
  have h1 : coordMap estd a = 0 := ha
  rw [coordMap_estd] at h1
  have h2 : Matrix.of (mk a) = 0 := by
    apply iotaM_injective
    rw [h1]
    ext i j
    simp [iotaM_apply, iotaE]
  have e : ∀ i j, mk a i j = 0 := fun i j => by
    have := congrFun (congrFun h2 i) j
    simpa using this
  fin_cases k
  · exact e 0 0
  · exact e 0 1
  · exact e 1 0
  · exact e 1 1

theorem span_estd :
    (Submodule.span ℝ (Set.range estd) : Set Mcx) = Set.range iotaM := by
  apply Set.Subset.antisymm
  ·
    have h : Submodule.span ℝ (Set.range estd) ≤ LinearMap.range iotaML := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨stdE k, rfl⟩
    intro X hX
    obtain ⟨Y, hY⟩ := h hX
    exact ⟨Y, hY⟩
  · rintro _ ⟨Y, rfl⟩
    have hY : Y = Matrix.of (mk (![Y 0 0, Y 0 1, Y 1 0, Y 1 1])) := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have : iotaM Y = coordMap estd ![Y 0 0, Y 0 1, Y 1 0, Y 1 1] := by
      rw [coordMap_estd, ← hY]
    rw [this]
    unfold coordMap
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem gramDet_estd : gramDet Bcx estd = -16 := by
  have hG : (Matrix.of fun i j : Fin 4 => Bcx (estd i) (estd j)) =
      !![(2 : ℝ), 0, 0, 0; 0, 0, 2, 0; 0, 2, 0, 0; 0, 0, 0, 2] := by
    ext i j
    simp only [Matrix.of_apply, estd, Bcx_iotaM, stdE, rowIdx, colIdx, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  rw [gramDet, hG]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num

theorem sqrt_abs_gramDet_estd : Real.sqrt |gramDet Bcx estd| = 4 := by
  rw [gramDet_estd, abs_neg, show |(16 : ℝ)| = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

def mkEquiv : (Fin 4 → ℝ) ≃ᵐ Ent :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (finSumFinEquiv (m := 2) (n := 2))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
    (MeasurableEquiv.piFinTwo fun _ : Fin 2 => Fin 2 → ℝ).symm

theorem mkEquiv_apply (a : Fin 4 → ℝ) : mkEquiv a = mk a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem measurePreserving_mkEquiv :
    MeasurePreserving mkEquiv (volume : Measure (Fin 4 → ℝ)) (volume : Measure Ent) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (finSumFinEquiv (m := 2) (n := 2))).symm
      (volume : Measure (Fin 4 → ℝ)) (volume : Measure (Fin 2 ⊕ Fin 2 → ℝ)) :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) (finSumFinEquiv (m := 2) (n := 2))).symm
  have h2 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin 2 ⊕ Fin 2 => ℝ)
      (volume : Measure (Fin 2 ⊕ Fin 2 → ℝ)) (volume : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ))) :=
    volume_measurePreserving_sumPiEquivProdPi fun _ : Fin 2 ⊕ Fin 2 => ℝ
  have h3 : MeasurePreserving (MeasurableEquiv.piFinTwo fun _ : Fin 2 => Fin 2 → ℝ).symm
      (volume : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ))) (volume : Measure Ent) :=
    (volume_preserving_piFinTwo fun _ : Fin 2 => Fin 2 → ℝ).symm
  exact (h1.trans h2).trans h3

theorem map_mk_volume : Measure.map mk (volume : Measure (Fin 4 → ℝ)) = (volume : Measure Ent) := by
  have h : (mk : (Fin 4 → ℝ) → Ent) = mkEquiv := funext fun a => (mkEquiv_apply a).symm
  rw [h]
  exact measurePreserving_mkEquiv.map_eq

def iotaMof (q : Ent) : Mcx := iotaM (Matrix.of q)

theorem continuous_iotaMof : Continuous iotaMof := continuous_iotaM

theorem measurable_iotaMof : Measurable iotaMof := continuous_iotaMof.measurable

theorem iotaMof_injective : Function.Injective iotaMof := fun q q' h => by
  have := iotaM_injective h
  exact this

theorem measurableEmbedding_iotaMof : MeasurableEmbedding iotaMof :=
  continuous_iotaMof.measurableEmbedding iotaMof_injective

theorem coordMap_estd_eq : coordMap estd = iotaMof ∘ mk := funext coordMap_estd

theorem gramMeasure_estd : gramMeasure Bcx estd = (4 : ℝ≥0∞) • Measure.map iotaMof (volume : Measure Ent) := by
  rw [gramMeasure, sqrt_abs_gramDet_estd, coordMap_estd_eq, ← Measure.map_map measurable_iotaMof, map_mk_volume]
  · congr 1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  · exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => by
      fin_cases i <;> fin_cases j <;> simp [mk] <;> exact measurable_pi_apply _

theorem gramMeasure_eq_of_span {n : ℕ} (e : Fin n → Mcx) (hli : LinearIndependent ℝ e)
    (hspan : (Submodule.span ℝ (Set.range e) : Set Mcx) = Set.range iotaM) :
    gramMeasure Bcx e = (4 : ℝ≥0∞) • Measure.map iotaMof (volume : Measure Ent) := by
  have hsp : Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range estd) := by
    apply SetLike.coe_injective
    rw [hspan, span_estd]
  have hn := card_eq_of_span_eq estd e linearIndependent_estd hli hsp
  subst hn
  obtain ⟨P, hP, hdet⟩ := exists_matrix_of_span_eq estd e linearIndependent_estd hli hsp.le
  rw [gramMeasure_eq_of_comp Bcx estd e P hP hdet, gramMeasure_estd]

def densE (q : Ent) : ℝ≥0∞ := (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹

theorem rho_comp_iotaMof : rho ∘ iotaMof = densE := by
  funext q
  exact rho_iotaM (Matrix.of q)

theorem measurable_densE : Measurable densE := by
  rw [← rho_comp_iotaMof]; exact measurable_rho.comp measurable_iotaMof

def entC (c : ℝˣ) (t : Subgroup.centralizer
    ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) : Ent :=
  fun i j : Fin 2 => ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j

theorem continuous_entC (c : ℝˣ) : Continuous (entC c) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)))).comp continuous_subtype_val

theorem entC_injective (c : ℝˣ) : Function.Injective (entC c) := by
  intro t t' h
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact congrFun (congrFun h i) j

theorem measurableEmbedding_entC (c : ℝˣ) : MeasurableEmbedding (entC c) := by
  haveI := polishSpace_Cent (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  exact (continuous_entC c).measurableEmbedding (entC_injective c)

theorem main
    (c : ℝˣ)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (n₁ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hli : LinearIndependent ℝ e₁)
    (hspan : (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
      Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
        Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))))
    (hτ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       Measure.map (fun t : ↥(Subgroup.centralizer
             ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
           ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
             (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
         s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                 Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
               Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
             (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
               (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    (letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
     Measure.map (fun t : ↥(Subgroup.centralizer
           ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
         fun i j : Fin 2 => ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) τ =
       (4 * s) • (volume : Measure (Fin 2 → Fin 2 → ℝ)).withDensity
         (fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹)) ∧
    τ {t | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      s * ENNReal.ofReal (8 * Real.pi) := by

  change Measure.map (iotaMof ∘ entC c) τ = s • (gramMeasure Bcx e₁).withDensity rho at hτ
  rw [gramMeasure_eq_of_span e₁ hli hspan, withDensity_smul_measure, ← map_withDensity_comp measurable_iotaMof _
    measurable_rho, rho_comp_iotaMof, smul_smul, ← Measure.map_smul,
    ← Measure.map_map measurable_iotaMof (continuous_entC c).measurable] at hτ

  have h1 : Measure.map (entC c) τ = (s * 4) • (volume : Measure Ent).withDensity densE :=
    map_injective_of_measurableEmbedding measurableEmbedding_iotaMof hτ
  refine ⟨?_, ?_⟩
  · change Measure.map (entC c) τ = (4 * s) • (volume : Measure Ent).withDensity densE
    rw [h1, mul_comm]
  ·
    set boxE : Set Ent := {q | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        Matrix.of q = !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} with hboxE
    have hpre : {t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) |
        ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} = entC c ⁻¹' boxE := by
      ext t
      rfl
    have hbox : ((volume : Measure Ent).withDensity densE) boxE = ENNReal.ofReal (2 * Real.pi) :=
      AutomorphicForm.GL2Real.withDensity_volume_iwasawaBox_eq_two_mul_pi
    rw [hpre, ← (measurableEmbedding_entC c).map_apply τ boxE, h1, Measure.smul_apply, hbox, smul_eq_mul,
      mul_assoc]
    congr 1
    rw [show (8 : ℝ) * Real.pi = 4 * (2 * Real.pi) by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num

end P2mGramBox
p2m_reactivate "P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real.P2mGramBox"

open P2mGramBox in
theorem solution
    (c : ℝˣ)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (n₁ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hli : LinearIndependent ℝ e₁)
    (hspan : (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
      Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
        Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))))
    (hτ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       Measure.map (fun t : ↥(Subgroup.centralizer
             ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
           ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
             (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
         s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                 Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
               Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
             (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
               (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    (letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
     Measure.map (fun t : ↥(Subgroup.centralizer
           ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
         fun i j : Fin 2 => ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) τ =
       (4 * s) • (volume : Measure (Fin 2 → Fin 2 → ℝ)).withDensity
         (fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹)) ∧
    τ {t | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
        ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      s * ENNReal.ofReal (8 * Real.pi) :=
  main c τ n₁ e₁ s hli hspan hτ

end
end S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real
end P2MW
export P2MW.S_AutomorphicForm_map_entries_eq_smul_withDensity_and_apply_iwasawaBox_eq_of_gram_real (solution)
