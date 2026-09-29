-- Prove2me | solution 1 for AutomorphicForm.exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2f7fc586-0535-578f-a8aa-dae7eb174c07

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Set AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions ENNReal

noncomputable section

namespace P2mGramH

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

end P2mGramH
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

namespace ProperUnifCore

open Matrix Topology Filter Set

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

def ι : GL (Fin 2) ℝ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map Complex.ofRealHom

def cjGL : GL (Fin 2) ℂ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map (starRingEnd ℂ : ℂ →+* ℂ)

theorem ι_val (m : GL (Fin 2) ℝ) : ((ι m : GL (Fin 2) ℂ) : M2) = (m : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofRealHom := rfl

theorem cjGL_val (y : GL (Fin 2) ℂ) : ((cjGL y : GL (Fin 2) ℂ) : M2) = (y : M2).map (starRingEnd ℂ) := rfl

theorem cjGL_ι (m : GL (Fin 2) ℝ) : cjGL (ι m) = ι m := by
  refine Units.ext ?_
  rw [cjGL_val, ι_val, Matrix.map_map]
  congr 1
  funext r
  simp

theorem cjGL_cjGL (y : GL (Fin 2) ℂ) : cjGL (cjGL y) = y := by
  refine Units.ext ?_
  rw [cjGL_val, cjGL_val, Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id (y : M2)]
  congr 1
  funext z
  simp

theorem continuous_GL_map {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (f : R →+* S) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hf).congr fun _ => rfl
  · exact (Units.continuous_coe_inv.matrix_map hf).congr fun x => by
      show ((x⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f = _
      rfl

theorem continuous_ι : Continuous ι := continuous_GL_map _ Complex.continuous_ofReal

theorem continuous_cjGL : Continuous cjGL := continuous_GL_map _ Complex.continuous_conj

theorem ι_scalar_comm (d : ℝˣ) (y : GL (Fin 2) ℂ) :
    ι (Matrix.GeneralLinearGroup.scalar (Fin 2) d) * y = y * ι (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have e : (Matrix.diagonal fun _ : Fin 2 => (d : ℝ)).map Complex.ofRealHom = ((d : ℝ) : ℂ) • (1 : M2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem trace_ι (t : GL (Fin 2) ℝ) :
    Matrix.trace ((ι t : GL (Fin 2) ℂ) : M2) = ((Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) : ℝ) : ℂ) := by
  rw [ι_val, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp

theorem exists_ι_eq_of_map_star_eq (m : GL (Fin 2) ℂ) (hm : (m : M2).map (starRingEnd ℂ) = m) :
    ∃ m₀ : GL (Fin 2) ℝ, ι m₀ = m := by
  set mr : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ((m : M2) i j).re with hmr
  have hre : mr.map Complex.ofRealHom = (m : M2) := by
    ext i j
    have h := congrFun (congrFun hm i) j
    simp only [Matrix.map_apply, starRingEnd_apply] at h
    simp only [Matrix.map_apply, hmr, Complex.ofRealHom_eq_coe]
    exact (Complex.conj_eq_iff_re.1 h)
  have hdet : Matrix.det mr ≠ 0 := by
    intro h0
    have h1 : Matrix.det (m : M2) = 0 := by
      have hmd := RingHom.map_det Complex.ofRealHom mr
      rw [RingHom.mapMatrix_apply, hre] at hmd
      rw [← hmd, h0, map_zero]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero h1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero mr hdet, Units.ext ?_⟩
  rw [ι_val]
  exact hre

end ProperUnifCore
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

namespace QuatCore

open Matrix Topology Filter Set ProperUnifCore

def D0 (c : ℝ) (hc : c ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, (c : ℂ); 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp [hc])

theorem D0_val (c : ℝ) (hc : c ≠ 0) : ((D0 c hc : GL (Fin 2) ℂ) : M2) = !![0, (c : ℂ); 1, 0] := rfl

def rs (e : ℝ) (he : e ≠ 0) : GL (Fin 2) ℂ := ι (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 e he))

theorem rs_val (e : ℝ) (he : e ≠ 0) : ((rs e he : GL (Fin 2) ℂ) : M2) = ((e : ℝ) : ℂ) • (1 : M2) := by
  rw [rs, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def TwRel (D t : GL (Fin 2) ℂ) : Prop := t * D * (cjGL t)⁻¹ = D

theorem twRel_iff (D t : GL (Fin 2) ℂ) : TwRel D t ↔ t * D = D * cjGL t := by
  unfold TwRel
  rw [mul_inv_eq_iff_eq_mul]

theorem cjGL_apply (t : GL (Fin 2) ℂ) (i j : Fin 2) :
    ((cjGL t : GL (Fin 2) ℂ) : M2) i j = (starRingEnd ℂ) (((t : GL (Fin 2) ℂ) : M2) i j) := rfl

theorem entries_of_twRel_D0 (c : ℝ) (hc : c ≠ 0) (t : GL (Fin 2) ℂ) (ht : TwRel (D0 c hc) t) :
    ((t : GL (Fin 2) ℂ) : M2) 0 1 = (c : ℂ) * (starRingEnd ℂ) (((t : GL (Fin 2) ℂ) : M2) 1 0) ∧
      ((t : GL (Fin 2) ℂ) : M2) 1 1 = (starRingEnd ℂ) (((t : GL (Fin 2) ℂ) : M2) 0 0) := by
  rw [twRel_iff] at ht
  have hm := congrArg (fun u : GL (Fin 2) ℂ => (u : M2)) ht
  simp only [Units.val_mul, D0_val] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cjGL_apply] at h00 h10
  simp [Matrix.of_apply] at h00 h10
  exact ⟨by rw [h00], by rw [h10]⟩

theorem det_of_twRel_D0 (c : ℝ) (hc : c ≠ 0) (t : GL (Fin 2) ℂ) (ht : TwRel (D0 c hc) t) :
    Matrix.det ((t : GL (Fin 2) ℂ) : M2) =
      ((‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h01, h11⟩ := entries_of_twRel_D0 c hc t ht
  rw [Matrix.det_fin_two, h01, h11, Complex.sq_norm, Complex.sq_norm]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  ring

theorem det_pos_of_twRel_D0 (c : ℝ) (hc : c < 0) (t : GL (Fin 2) ℂ) (ht : TwRel (D0 c hc.ne) t) :
    0 < ‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 := by
  have hdet : Matrix.det ((t : GL (Fin 2) ℂ) : M2) ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 t.isUnit).ne_zero
  rw [det_of_twRel_D0 c hc.ne t ht, Complex.ofReal_ne_zero] at hdet
  have h1 : 0 ≤ ‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 := by positivity
  have h2 : 0 ≤ -c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 := by
    have : 0 ≤ -c := by linarith
    positivity
  rcases (show 0 ≤ ‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 by linarith).lt_or_eq with h | h
  · exact h
  · exact absurd h.symm hdet

def S (c : ℝ) : Set (ℂ × ℂ) := {p | ‖p.1‖ ^ 2 - c * ‖p.2‖ ^ 2 = 1}

theorem isCompact_S (c : ℝ) (hc : c < 0) : IsCompact (S c) := by
  haveI : ProperSpace (ℂ × ℂ) := inferInstance
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := max 1 (Real.sqrt (1 / -c)))).subset ?_
    intro p hp
    simp only [S, Set.mem_setOf_eq] at hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    have hc' : 0 < -c := by linarith
    have ha : ‖p.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p.2, sq_nonneg ‖p.2‖]
    have he : ‖p.2‖ ^ 2 ≤ 1 / -c := by
      rw [div_eq_mul_inv, le_mul_inv_iff₀ hc']
      nlinarith [sq_nonneg ‖p.1‖]
    constructor
    · exact le_trans (by nlinarith [norm_nonneg p.1]) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [← Real.sqrt_sq (norm_nonneg p.2)]
      exact Real.sqrt_le_sqrt he

def qM (c : ℝ) (p : ℂ × ℂ) : M2 := !![p.1, (c : ℂ) * (starRingEnd ℂ) p.2; p.2, (starRingEnd ℂ) p.1]

theorem continuous_qM (c : ℝ) : Continuous (qM c) := by
  unfold qM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem det_qM (c : ℝ) (p : ℂ × ℂ) :
    Matrix.det (qM c p) = ((‖p.1‖ ^ 2 - c * ‖p.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [qM, Matrix.det_fin_two_of, Complex.sq_norm, Complex.sq_norm]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  ring

def qU (c : ℝ) (p : S c) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (qM c p.1) (by
    rw [det_qM]
    have hp : ‖(p.1).1‖ ^ 2 - c * ‖(p.1).2‖ ^ 2 = 1 := p.2
    rw [hp]; simp)

theorem qU_val (c : ℝ) (p : S c) : ((qU c p : GL (Fin 2) ℂ) : M2) = qM c p.1 := rfl

theorem det_qU (c : ℝ) (p : S c) : Matrix.det ((qU c p : GL (Fin 2) ℂ) : M2) = 1 := by
  rw [qU_val, det_qM]
  have hp : ‖(p.1).1‖ ^ 2 - c * ‖(p.1).2‖ ^ 2 = 1 := p.2
  rw [hp]; simp

theorem continuous_qU (c : ℝ) : Continuous (qU c) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_qM c).comp continuous_subtype_val).congr fun p => rfl
  · have e : (fun p : S c => (((qU c p)⁻¹ : GL (Fin 2) ℂ) : M2)) = fun p => (qM c p.1).adjugate := by
      funext p
      rw [Matrix.coe_units_inv, qU_val, Matrix.inv_def, ← qU_val, det_qU]
      simp
    rw [e]
    exact (continuous_qM c).matrix_adjugate.comp continuous_subtype_val

theorem twRel_qU (c : ℝ) (hc : c ≠ 0) (p : S c) : TwRel (D0 c hc) (qU c p) := by
  rw [twRel_iff]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, qU_val, D0_val, cjGL_val, qU_val, qM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

section NormalForm

variable (c : ℝ) (hc : c < 0) (D : GL (Fin 2) ℂ)
  (hD : ((D * cjGL D : GL (Fin 2) ℂ) : M2) = (c : ℂ) • (1 : M2))

include hD in
theorem normEq (i j : Fin 2) :
    ∑ k : Fin 2, ((D : GL (Fin 2) ℂ) : M2) i k * (starRingEnd ℂ) (((D : GL (Fin 2) ℂ) : M2) k j) =
      if i = j then (c : ℂ) else 0 := by
  have h := congrFun (congrFun hD i) j
  rw [Units.val_mul, Matrix.mul_apply, cjGL_val] at h
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  exact h

include hc hD in
theorem D10_ne : ((D : GL (Fin 2) ℂ) : M2) 1 0 ≠ 0 := by
  intro h0
  have h := normEq c D hD 0 0
  rw [Fin.sum_univ_two, h0, map_zero, mul_zero, add_zero, if_pos rfl] at h

  have hre := congrArg Complex.re h
  rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] at hre
  have : 0 ≤ Complex.normSq (((D : GL (Fin 2) ℂ) : M2) 0 0) := Complex.normSq_nonneg _
  simp at hre
  linarith

def xD : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, ((D : GL (Fin 2) ℂ) : M2) 0 0; 0, ((D : GL (Fin 2) ℂ) : M2) 1 0]
    (by rw [Matrix.det_fin_two_of]; simpa using D10_ne c hc D hD)

theorem xD_val : ((xD c hc D hD : GL (Fin 2) ℂ) : M2) =
    !![1, ((D : GL (Fin 2) ℂ) : M2) 0 0; 0, ((D : GL (Fin 2) ℂ) : M2) 1 0] := rfl

include hc hD in

theorem conj_eq : D * cjGL (xD c hc D hD) = xD c hc D hD * D0 c hc.ne := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, cjGL_val, xD_val, D0_val]
  have h00 := normEq c D hD 0 0
  have h10 := normEq c D hD 1 0
  rw [Fin.sum_univ_two] at h00 h10
  simp only [if_pos, if_neg, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true, reduceIte] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  · exact h00
  · exact h10

include hc hD in
theorem twRel_iff_conj (t : GL (Fin 2) ℂ) :
    TwRel D t ↔ TwRel (D0 c hc.ne) ((xD c hc D hD)⁻¹ * t * xD c hc D hD) := by
  have key := conj_eq c hc D hD

  have hDeq : D = xD c hc D hD * D0 c hc.ne * (cjGL (xD c hc D hD))⁻¹ := by
    rw [← key]; group
  rw [twRel_iff, twRel_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h

    have := congrArg (fun u => (xD c hc D hD)⁻¹ * u * cjGL (xD c hc D hD)) h
    beta_reduce at this
    rw [show (xD c hc D hD)⁻¹ * (t * D) * cjGL (xD c hc D hD) =
        (xD c hc D hD)⁻¹ * t * xD c hc D hD * ((xD c hc D hD)⁻¹ * (D * cjGL (xD c hc D hD))) by group, key,
      show (xD c hc D hD)⁻¹ * (D * cjGL t) * cjGL (xD c hc D hD) =
        ((xD c hc D hD)⁻¹ * (D * cjGL (xD c hc D hD))) * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD)) by group,
      key] at this
    rw [show (xD c hc D hD)⁻¹ * t * xD c hc D hD * ((xD c hc D hD)⁻¹ * (xD c hc D hD * D0 c hc.ne)) =
        (xD c hc D hD)⁻¹ * t * xD c hc D hD * D0 c hc.ne by group,
      show (xD c hc D hD)⁻¹ * (xD c hc D hD * D0 c hc.ne) * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD)) =
        D0 c hc.ne * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD)) by group] at this
    exact this
  · intro h
    rw [hDeq]
    have := congrArg (fun u => xD c hc D hD * u * (cjGL (xD c hc D hD))⁻¹) h
    beta_reduce at this
    calc t * (xD c hc D hD * D0 c hc.ne * (cjGL (xD c hc D hD))⁻¹)
        = xD c hc D hD * ((xD c hc D hD)⁻¹ * t * xD c hc D hD * D0 c hc.ne) * (cjGL (xD c hc D hD))⁻¹ := by group
      _ = xD c hc D hD * (D0 c hc.ne * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD))) *
            (cjGL (xD c hc D hD))⁻¹ := by rw [h]
      _ = xD c hc D hD * D0 c hc.ne * (cjGL (xD c hc D hD))⁻¹ * cjGL t := by group

end NormalForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

theorem core (c : ℝ) (hc : c < 0) (D : GL (Fin 2) ℂ)
    (hD : ((D * cjGL D : GL (Fin 2) ℂ) : M2) = (c : ℂ) • (1 : M2)) :
    ∃ C : Set (GL (Fin 2) ℂ), IsCompact C ∧ (∀ k ∈ C, TwRel D k) ∧
      ∀ t : GL (Fin 2) ℂ, TwRel D t → ∃ (e : ℝ) (he : e ≠ 0), ∃ k ∈ C, t = rs e he * k := by
  set x := xD c hc D hD with hx
  set F : S c → GL (Fin 2) ℂ := fun p => x * qU c p * x⁻¹ with hF
  have hSc : IsCompact (S c) := isCompact_S c hc
  haveI : CompactSpace (S c) := isCompact_iff_compactSpace.1 hSc
  have hFc : Continuous F := (continuous_const.mul (continuous_qU c)).mul continuous_const
  refine ⟨Set.range F, isCompact_range hFc, ?_, ?_⟩
  · rintro k ⟨p, rfl⟩
    rw [twRel_iff_conj c hc D hD]
    have : (xD c hc D hD)⁻¹ * (x * qU c p * x⁻¹) * xD c hc D hD = qU c p := by rw [hx]; group
    rw [this]
    exact twRel_qU c hc.ne p
  · intro t ht
    set s := x⁻¹ * t * x with hs
    have hs' : TwRel (D0 c hc.ne) s := (twRel_iff_conj c hc D hD t).1 ht
    obtain ⟨h01, h11⟩ := entries_of_twRel_D0 c hc.ne s hs'
    set r : ℝ := ‖((s : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((s : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 with hr
    have hrpos : 0 < r := det_pos_of_twRel_D0 c hc s hs'
    set e : ℝ := Real.sqrt r with he
    have hepos : 0 < e := Real.sqrt_pos.2 hrpos
    have hesq : e ^ 2 = r := Real.sq_sqrt hrpos.le

    set a : ℂ := (e : ℂ)⁻¹ * ((s : GL (Fin 2) ℂ) : M2) 0 0 with ha
    set f : ℂ := (e : ℂ)⁻¹ * ((s : GL (Fin 2) ℂ) : M2) 1 0 with hf
    have hp : ‖a‖ ^ 2 - c * ‖f‖ ^ 2 = 1 := by
      rw [ha, hf, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hepos]
      field_simp
      rw [hesq, hr]
    refine ⟨e, hepos.ne', F ⟨(a, f), hp⟩, ⟨_, rfl⟩, ?_⟩

    have hsval : ((s : GL (Fin 2) ℂ) : M2) = (e : ℂ) • qM c (a, f) := by
      rw [Matrix.eta_fin_two ((s : GL (Fin 2) ℂ) : M2), h01, h11, qM]
      have hene : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hepos.ne'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hf, Matrix.smul_apply] <;> field_simp
    have hsu : s = rs e hepos.ne' * qU c ⟨(a, f), hp⟩ := by
      refine Units.ext ?_
      show ((s : GL (Fin 2) ℂ) : M2) = _
      rw [hsval, Units.val_mul, rs_val, qU_val, Matrix.smul_mul, Matrix.one_mul]
    have hrs : ∀ z : GL (Fin 2) ℂ, rs e hepos.ne' * z = z * rs e hepos.ne' := fun z =>
      ι_scalar_comm (Units.mk0 e hepos.ne') z
    calc t = x * s * x⁻¹ := by rw [hs]; group
      _ = x * (rs e hepos.ne' * qU c ⟨(a, f), hp⟩) * x⁻¹ := by rw [hsu]
      _ = rs e hepos.ne' * (x * qU c ⟨(a, f), hp⟩ * x⁻¹) := by rw [← mul_assoc, ← hrs x]; group

end QuatCore
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

namespace ProperUnifBridge

open scoped TensorProduct TensorProduct.RightActions
open ProperUnifCore

abbrev TT : Type := ℂ ⊗[ℝ] ℝ

def ρr : TT ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ρr_tmul (z : ℂ) (s : ℝ) : ρr (z ⊗ₜ s) = (s : ℂ) * z := by
  simp [ρr, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem ρr_symm_apply (z : ℂ) : ρr.symm z = z ⊗ₜ 1 := by
  simp [ρr]

def ρrLin : TT →ₗ[ℝ] ℂ where
  toFun := ρr
  map_add' := map_add ρr
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z s =>
        rw [TensorProduct.RightActions.smul_def]
        simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_symm_tmul,
          ρr_tmul, RingHom.id_apply, Complex.real_smul]
        push_cast
        ring
    | add x y hx hy =>
        rw [TensorProduct.RightActions.smul_def, map_add, smul_add, map_add, map_add,
          ← TensorProduct.RightActions.smul_def, ← TensorProduct.RightActions.smul_def, hx, hy, map_add, smul_add]

def ρrSymmLin : ℂ →ₗ[ℝ] TT where
  toFun := ρr.symm
  map_add' := map_add ρr.symm
  map_smul' := by
    intro r z
    rw [ρr_symm_apply, ρr_symm_apply, RingHom.id_apply, TensorProduct.RightActions.smul_def]
    simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.comm_symm_tmul]
    rw [TensorProduct.smul_tmul, smul_eq_mul, mul_one]

theorem continuous_ρr : Continuous ρr := by
  haveI := AutomorphicForm.t2Space_tensor ℝ ℂ ℝ
  exact LinearMap.continuous_of_finiteDimensional ρrLin

theorem continuous_ρr_symm : Continuous ρr.symm :=
  LinearMap.continuous_of_finiteDimensional ρrSymmLin

def ρ : GL (Fin 2) TT →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map ρr.toRingHom

def ρi : GL (Fin 2) ℂ →* GL (Fin 2) TT := Matrix.GeneralLinearGroup.map ρr.symm.toRingHom

theorem ρ_val (x : GL (Fin 2) TT) : ((ρ x : GL (Fin 2) ℂ) : M2) = (x : Matrix (Fin 2) (Fin 2) TT).map ρr := rfl

theorem ρi_val (y : GL (Fin 2) ℂ) :
    ((ρi y : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT) = (y : M2).map ρr.symm := rfl

theorem ρi_ρ (x : GL (Fin 2) TT) : ρi (ρ x) = x := by
  refine Units.ext ?_
  rw [ρi_val, ρ_val, Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id (x : Matrix (Fin 2) (Fin 2) TT)]
  congr 1
  funext e
  simp

theorem ρ_ρi (y : GL (Fin 2) ℂ) : ρ (ρi y) = y := by
  refine Units.ext ?_
  rw [ρ_val, ρi_val, Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id (y : M2)]
  congr 1
  funext e
  simp

theorem continuous_ρi : Continuous ρi := by
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map continuous_ρr_symm

theorem toTensorGL_apply (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL ℝ ℂ ℝ m : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT) i j =
      (1 : ℂ) ⊗ₜ (((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := rfl

theorem ρ_toTensorGL (m : GL (Fin 2) ℝ) : ρ (AutomorphicForm.toTensorGL ℝ ℂ ℝ m) = ι m := by
  refine Units.ext ?_
  ext i j
  rw [ρ_val, ι_val, Matrix.map_apply, Matrix.map_apply, toTensorGL_apply, ρr_tmul, mul_one]
  rfl

theorem toTensorGL_eq_ρi_ι (m : GL (Fin 2) ℝ) : AutomorphicForm.toTensorGL ℝ ℂ ℝ m = ρi (ι m) := by
  rw [← ρ_toTensorGL, ρi_ρ]

theorem ρr_sigma (e : TT) :
    ρr (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe e) = (starRingEnd ℂ) (ρr e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul z s =>
      rw [AutomorphicForm.sigmaTensor]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        ρr_tmul]
      simp [Complex.conj_ofReal]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ρ_sigmaGL (x : GL (Fin 2) TT) : ρ (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe x) = cjGL (ρ x) := by
  refine Units.ext ?_
  rw [ρ_val, cjGL_val, ρ_val]
  show (((x : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT).map (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe)).map ρr = _
  rw [Matrix.map_map, Matrix.map_map]
  congr 1
  funext e
  exact ρr_sigma e

end ProperUnifBridge
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

namespace QuatChart

open Matrix ProperUnifCore QuatCore ProperUnifBridge

abbrev Mcx : Type := Matrix (Fin 2) (Fin 2) TT

def ρM : Mcx ≃+* M2 := ρr.mapMatrix

theorem ρM_apply (X : Mcx) : ρM X = X.map ρr := rfl

theorem ρM_symm_apply (Y : M2) : ρM.symm Y = Y.map ρr.symm := rfl

theorem ρM_val (g : GL (Fin 2) TT) : ρM ((g : GL (Fin 2) TT) : Mcx) = ((ρ g : GL (Fin 2) ℂ) : M2) := rfl

theorem ρM_smul (r : ℝ) (X : Mcx) : ρM (r • X) = (r : ℂ) • ρM X := by
  ext i j
  simp only [ρM_apply, Matrix.map_apply, Matrix.smul_apply]
  have := ρrLin.map_smul r (X i j)
  simpa [ρrLin, Complex.real_smul] using this

theorem ρM_symm_smul (r : ℝ) (Y : M2) : ρM.symm ((r : ℂ) • Y) = r • ρM.symm Y := by
  apply ρM.injective
  rw [RingEquiv.apply_symm_apply, ρM_smul, RingEquiv.apply_symm_apply]

def cjM (Y : M2) : M2 := Y.map (starRingEnd ℂ)

theorem ρM_sigma (X : Mcx) : ρM (X.map (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe)) = cjM (ρM X) := by
  ext i j
  simp only [ρM_apply, cjM, Matrix.map_apply]
  exact ρr_sigma _

theorem cjM_mul (A B : M2) : cjM (A * B) = cjM A * cjM B := Matrix.map_mul

theorem cjM_val (g : GL (Fin 2) ℂ) : cjM ((g : GL (Fin 2) ℂ) : M2) = ((cjGL g : GL (Fin 2) ℂ) : M2) := rfl

def bp : Fin 4 → ℂ × ℂ := ![(1, 0), (Complex.I, 0), (0, 1), (0, Complex.I)]

theorem qM_coord (c : ℝ) (a : Fin 4 → ℝ) :
    qM c ((a 0 : ℂ) + (a 1 : ℂ) * Complex.I, (a 2 : ℂ) + (a 3 : ℂ) * Complex.I) =
      ∑ k, (a k : ℂ) • qM c (bp k) := by
  simp only [qM, bp, Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I] <;> ring

theorem qM_entries (c : ℝ) (p : ℂ × ℂ) : (qM c p) 0 0 = p.1 ∧ (qM c p) 1 0 = p.2 := by
  simp [qM]

section Chart

theorem hD (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : (((ρ δ) * cjGL (ρ δ) : GL (Fin 2) ℂ) : M2) = ((c : ℝ) : ℂ) • (1 : M2) := by
  have hN : AutomorphicForm.normString ℝ ℂ ℝ Complex.conjAe δ = δ * AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
    rw [AutomorphicForm.normString, Complex.finrank_real_complex]
    simp [List.range_succ, Function.iterate_zero]
  have hδ' : δ * AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe δ =
      y * AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y⁻¹ := by
    have h := hδ
    rw [AutomorphicForm.IsNormConjugator, hN] at h
    rw [h]; group
  have hcomm := ι_scalar_comm c (ρ y)
  have e1 : ρ δ * cjGL (ρ δ) = ι (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [← ρ_sigmaGL, ← map_mul, hδ', map_mul, map_mul, map_inv, ρ_toTensorGL, ← hcomm]
    group
  rw [e1, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def xq (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : GL (Fin 2) ℂ := xD (c : ℝ) hc (ρ δ) (hD c hc δ y hδ)

def qb (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (k : Fin 4) : Mcx :=
  ρM.symm ((((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * qM (c : ℝ) (bp k) * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2))

def chart (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : (Fin 4 → ℝ) →ₗ[ℝ] Mcx := Fintype.linearCombination ℝ (qb c hc δ y hδ)

theorem chart_eq_sum (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (a : Fin 4 → ℝ) : chart c hc δ y hδ a = ∑ k, a k • qb c hc δ y hδ k := by
  simp [chart, Fintype.linearCombination_apply]

theorem chart_eq (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (a : Fin 4 → ℝ) :
    chart c hc δ y hδ a = ρM.symm ((((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) *
      qM (c : ℝ) ((a 0 : ℂ) + (a 1 : ℂ) * Complex.I, (a 2 : ℂ) + (a 3 : ℂ) * Complex.I) *
      (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2)) := by
  rw [chart_eq_sum c hc δ y hδ, qM_coord, Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qb, ← ρM_symm_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem ρM_chart (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (a : Fin 4 → ℝ) :
    ρM (chart c hc δ y hδ a) = (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) *
      qM (c : ℝ) ((a 0 : ℂ) + (a 1 : ℂ) * Complex.I, (a 2 : ℂ) + (a 3 : ℂ) * Complex.I) *
      (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) := by
  rw [chart_eq c hc δ y hδ, RingEquiv.apply_symm_apply]

theorem xq_mul_inv (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem xq_inv_mul (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem det_chart (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (a : Fin 4 → ℝ) :
    Matrix.det (chart c hc δ y hδ a) = ((1 : ℂ) ⊗ₜ[ℝ] (a 0 ^ 2 + a 1 ^ 2 - (c : ℝ) * (a 2 ^ 2 + a 3 ^ 2)) : ℂ ⊗[ℝ] ℝ) := by
  apply ρr.injective
  have h1 : ρr (Matrix.det (chart c hc δ y hδ a)) = Matrix.det (ρM (chart c hc δ y hδ a)) :=
    RingHom.map_det ρr.toRingHom _
  rw [h1, ρM_chart c hc δ y hδ, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, xq_inv_mul c hc δ y hδ,
    Matrix.det_one, one_mul, det_qM, ρr_tmul, mul_one]
  congr 1
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

theorem chart_injective (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : Function.Injective (chart c hc δ y hδ) := by
  intro a b hab
  have h := congrArg ρM hab
  rw [ρM_chart c hc δ y hδ, ρM_chart c hc δ y hδ] at h
  have h2 : qM (c : ℝ) ((a 0 : ℂ) + (a 1 : ℂ) * Complex.I, (a 2 : ℂ) + (a 3 : ℂ) * Complex.I) =
      qM (c : ℝ) ((b 0 : ℂ) + (b 1 : ℂ) * Complex.I, (b 2 : ℂ) + (b 3 : ℂ) * Complex.I) := by
    have := congrArg (fun Z => (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * Z * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2)) h
    beta_reduce at this
    have key : ∀ Z : M2, (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * ((((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * Z *
        (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2)) * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) = Z := fun Z => by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, xq_inv_mul c hc δ y hδ, Matrix.mul_one, ← Matrix.mul_assoc,
        xq_inv_mul c hc δ y hδ, Matrix.one_mul]
    rw [key, key] at this
    exact this
  obtain ⟨e0, e1⟩ := qM_entries (c : ℝ) ((a 0 : ℂ) + (a 1 : ℂ) * Complex.I, (a 2 : ℂ) + (a 3 : ℂ) * Complex.I)
  obtain ⟨f0, f1⟩ := qM_entries (c : ℝ) ((b 0 : ℂ) + (b 1 : ℂ) * Complex.I, (b 2 : ℂ) + (b 3 : ℂ) * Complex.I)
  rw [h2] at e0 e1
  rw [f0] at e0; rw [f1] at e1
  have ha0 := congrArg Complex.re e0; have ha1 := congrArg Complex.im e0
  have ha2 := congrArg Complex.re e1; have ha3 := congrArg Complex.im e1
  simp at ha0 ha1 ha2 ha3
  funext k
  fin_cases k
  · exact ha0.symm
  · exact ha1.symm
  · exact ha2.symm
  · exact ha3.symm

end Chart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

theorem D0_val' (c : ℝ) (hc : c ≠ 0) : ((D0 c hc : GL (Fin 2) ℂ) : M2) = !![0, (c : ℂ); 1, 0] := rfl

theorem qM_rel (c : ℝ) (hc : c ≠ 0) (p : ℂ × ℂ) :
    qM c p * ((D0 c hc : GL (Fin 2) ℂ) : M2) = ((D0 c hc : GL (Fin 2) ℂ) : M2) * cjM (qM c p) := by
  rw [D0_val', qM, cjM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem entries_of_rel (c : ℝ) (hc : c ≠ 0) (Z : M2)
    (h : Z * ((D0 c hc : GL (Fin 2) ℂ) : M2) = ((D0 c hc : GL (Fin 2) ℂ) : M2) * cjM Z) :
    Z 0 1 = (c : ℂ) * (starRingEnd ℂ) (Z 1 0) ∧ Z 1 1 = (starRingEnd ℂ) (Z 0 0) := by
  rw [D0_val'] at h
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cjM, Matrix.map_apply] at h00 h10
  simp [Matrix.of_apply] at h00 h10
  exact ⟨by rw [h00], by rw [h10]⟩

theorem cjM_one : cjM (1 : M2) = 1 := by
  ext i j; simp [cjM, Matrix.one_apply]

theorem rel_iff (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (X : Mcx) :
    X * ((δ : GL (Fin 2) TT) : Mcx) = ((δ : GL (Fin 2) TT) : Mcx) * X.map (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe) ↔
      ρM X * (((ρ δ) : GL (Fin 2) ℂ) : M2) = (((ρ δ) : GL (Fin 2) ℂ) : M2) * cjM (ρM X) := by
  constructor
  · intro h
    have := congrArg ρM h
    rwa [map_mul, map_mul, ρM_val, ρM_sigma] at this
  · intro h
    apply ρM.injective
    rw [map_mul, map_mul, ρM_val, ρM_sigma]
    exact h

theorem rel_iff_conj (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) (Y : M2) :
    Y * (((ρ δ) : GL (Fin 2) ℂ) : M2) = (((ρ δ) : GL (Fin 2) ℂ) : M2) * cjM Y ↔
      ((((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * Y * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2)) *
          ((D0 (c : ℝ) hc.ne : GL (Fin 2) ℂ) : M2) =
        ((D0 (c : ℝ) hc.ne : GL (Fin 2) ℂ) : M2) *
          cjM ((((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * Y * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2)) := by

  set x : M2 := (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) with hx
  set xi : M2 := (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) with hxi
  set Dv : M2 := (((ρ δ) : GL (Fin 2) ℂ) : M2) with hDv
  set E : M2 := ((D0 (c : ℝ) hc.ne : GL (Fin 2) ℂ) : M2) with hE
  have hxxi : x * xi = 1 := xq_mul_inv c hc δ y hδ
  have hxix : xi * x = 1 := xq_inv_mul c hc δ y hδ
  have hcxxi : cjM x * cjM xi = 1 := by rw [← cjM_mul, hxxi, cjM_one]
  have hcxix : cjM xi * cjM x = 1 := by rw [← cjM_mul, hxix, cjM_one]

  have key : Dv * cjM x = x * E := by
    have := congrArg (fun u : GL (Fin 2) ℂ => (u : M2)) (conj_eq (c : ℝ) hc (ρ δ) (hD c hc δ y hδ))
    simp only [Units.val_mul] at this
    exact this

  have hD1 : xi * Dv = E * cjM xi := by
    calc xi * Dv = xi * Dv * (cjM x * cjM xi) := by rw [hcxxi, Matrix.mul_one]
      _ = xi * (Dv * cjM x) * cjM xi := by simp only [Matrix.mul_assoc]
      _ = xi * (x * E) * cjM xi := by rw [key]
      _ = (xi * x) * E * cjM xi := by simp only [Matrix.mul_assoc]
      _ = E * cjM xi := by rw [hxix, Matrix.one_mul]
  constructor
  · intro h
    calc xi * Y * x * E = xi * Y * (x * E) := by simp only [Matrix.mul_assoc]
      _ = xi * Y * (Dv * cjM x) := by rw [key]
      _ = xi * (Y * Dv) * cjM x := by simp only [Matrix.mul_assoc]
      _ = xi * (Dv * cjM Y) * cjM x := by rw [h]
      _ = (xi * Dv) * cjM Y * cjM x := by simp only [Matrix.mul_assoc]
      _ = E * cjM xi * cjM Y * cjM x := by rw [hD1]
      _ = E * cjM (xi * Y * x) := by rw [cjM_mul, cjM_mul]; simp only [Matrix.mul_assoc]
  · intro h

    have hY : Y = x * (xi * Y * x) * xi := by
      calc Y = (x * xi) * Y * (x * xi) := by rw [hxxi, Matrix.one_mul, Matrix.mul_one]
        _ = x * (xi * Y * x) * xi := by simp only [Matrix.mul_assoc]
    have hDv : Dv = x * E * cjM xi := by
      calc Dv = Dv * (cjM x * cjM xi) := by rw [hcxxi, Matrix.mul_one]
        _ = (Dv * cjM x) * cjM xi := by simp only [Matrix.mul_assoc]
        _ = x * E * cjM xi := by rw [key]
    set Z := xi * Y * x with hZ
    have e1 : Y * Dv = x * E * (cjM Z * cjM xi) := by
      calc Y * Dv = x * Z * xi * (x * E * cjM xi) := by rw [← hY, ← hDv]
        _ = x * Z * (xi * x) * E * cjM xi := by simp only [Matrix.mul_assoc]
        _ = x * (Z * E) * cjM xi := by rw [hxix]; simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = x * (E * cjM Z) * cjM xi := by rw [h]
        _ = x * E * (cjM Z * cjM xi) := by simp only [Matrix.mul_assoc]
    have e2 : Dv * cjM Y = x * E * (cjM Z * cjM xi) := by
      calc Dv * cjM Y = x * E * cjM xi * cjM (x * Z * xi) := by rw [← hY, ← hDv]
        _ = x * E * cjM xi * (cjM x * cjM Z * cjM xi) := by rw [cjM_mul, cjM_mul]
        _ = x * E * ((cjM xi * cjM x) * cjM Z * cjM xi) := by simp only [Matrix.mul_assoc]
        _ = x * E * (cjM Z * cjM xi) := by rw [hcxix, Matrix.one_mul]
    rw [e1, e2]

theorem range_chart (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    Set.range (chart c hc δ y hδ) =
      {X : Mcx | X * ((δ : GL (Fin 2) TT) : Mcx) =
        ((δ : GL (Fin 2) TT) : Mcx) * X.map (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe)} := by
  ext X
  constructor
  · rintro ⟨a, rfl⟩
    rw [Set.mem_setOf_eq, rel_iff c hc δ y hδ, rel_iff_conj c hc δ y hδ, ρM_chart c hc δ y hδ]
    have key : ∀ Z : M2, (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * ((((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * Z *
        (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2)) * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) = Z := fun Z => by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, xq_inv_mul c hc δ y hδ, Matrix.mul_one, ← Matrix.mul_assoc,
        xq_inv_mul c hc δ y hδ, Matrix.one_mul]
    rw [key]
    exact qM_rel _ _ _
  · intro hX
    rw [Set.mem_setOf_eq, rel_iff c hc δ y hδ, rel_iff_conj c hc δ y hδ] at hX
    set Z : M2 := (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * ρM X * (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) with hZ
    obtain ⟨h01, h11⟩ := entries_of_rel (c : ℝ) hc.ne Z hX
    refine ⟨![(Z 0 0).re, (Z 0 0).im, (Z 1 0).re, (Z 1 0).im], ?_⟩
    apply ρM.injective
    rw [ρM_chart c hc δ y hδ]
    have hp : qM (c : ℝ) ((((![(Z 0 0).re, (Z 0 0).im, (Z 1 0).re, (Z 1 0).im] : Fin 4 → ℝ) 0 : ℝ) : ℂ) +
          (((![(Z 0 0).re, (Z 0 0).im, (Z 1 0).re, (Z 1 0).im] : Fin 4 → ℝ) 1 : ℝ) : ℂ) * Complex.I,
        (((![(Z 0 0).re, (Z 0 0).im, (Z 1 0).re, (Z 1 0).im] : Fin 4 → ℝ) 2 : ℝ) : ℂ) +
          (((![(Z 0 0).re, (Z 0 0).im, (Z 1 0).re, (Z 1 0).im] : Fin 4 → ℝ) 3 : ℝ) : ℂ) * Complex.I) = Z := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [show ((Z 0 0).re : ℂ) + ((Z 0 0).im : ℂ) * Complex.I = Z 0 0 from Complex.re_add_im _,
        show ((Z 1 0).re : ℂ) + ((Z 1 0).im : ℂ) * Complex.I = Z 1 0 from Complex.re_add_im _, qM]
      conv_rhs => rw [Matrix.eta_fin_two Z, h01, h11]
    rw [hp, hZ]
    rw [show ∀ W : M2, (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * ((((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) * W *
        (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2)) * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) = W from fun W => by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, xq_mul_inv c hc δ y hδ, Matrix.mul_one, ← Matrix.mul_assoc,
        xq_mul_inv c hc δ y hδ, Matrix.one_mul]]

def ρA : TT ≃ₐ[ℝ] ℂ :=
  AlgEquiv.ofRingEquiv (f := ρr) (fun r => by
    show ρr ((1 : ℂ) ⊗ₜ[ℝ] r) = (r : ℂ)
    rw [ρr_tmul, mul_one])

theorem ρA_apply (e : TT) : ρA e = ρr e := rfl

theorem trace_TT (e : TT) : Algebra.trace ℝ TT e = 2 * (ρr e).re := by
  rw [← Algebra.trace_eq_of_algEquiv ρA e, ρA_apply, Algebra.trace_complex_apply]

theorem trace_ρM (X : Mcx) : Matrix.trace (ρM X) = ρr (Matrix.trace X) := by
  rw [ρM_apply, Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]; rfl

theorem coord_single (i : Fin 4) :
    ((((Pi.single i 1 : Fin 4 → ℝ) 0 : ℝ) : ℂ) + (((Pi.single i 1 : Fin 4 → ℝ) 1 : ℝ) : ℂ) * Complex.I,
      (((Pi.single i 1 : Fin 4 → ℝ) 2 : ℝ) : ℂ) + (((Pi.single i 1 : Fin 4 → ℝ) 3 : ℝ) : ℂ) * Complex.I) = bp i := by
  fin_cases i <;> simp [bp, Pi.single_apply]

theorem two_mul_re_trace_qM (c : ℝ) (i j : Fin 4) :
    2 * (Matrix.trace (qM c (bp i) * qM c (bp j))).re = Matrix.diagonal ![4, -4, 4 * c, 4 * c] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [qM, bp, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Complex.conj_I] <;> ring

theorem gram_chart (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    (Matrix.of fun i j : Fin 4 =>
        Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (chart c hc δ y hδ (Pi.single i 1) * chart c hc δ y hδ (Pi.single j 1)))) =
      Matrix.diagonal ![4, -4, 4 * (c : ℝ), 4 * (c : ℝ)] := by
  ext i j
  rw [Matrix.of_apply, trace_TT, ← two_mul_re_trace_qM]
  congr 2
  rw [← trace_ρM, map_mul, ρM_chart c hc δ y hδ, ρM_chart c hc δ y hδ, coord_single, coord_single]

  rw [show ∀ A B : M2, (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * A * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) *
      ((((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * B * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2)) =
      (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * (A * B) * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) from fun A B => by
    calc _ = (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2) * A * ((((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) *
          (((xq c hc δ y hδ) : GL (Fin 2) ℂ) : M2)) * B * (((xq c hc δ y hδ)⁻¹ : GL (Fin 2) ℂ) : M2) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [xq_inv_mul c hc δ y hδ, Matrix.mul_one]; simp only [Matrix.mul_assoc],
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc, xq_inv_mul c hc δ y hδ, Matrix.one_mul]

theorem sqrt_abs_det_gram_chart (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    Real.sqrt |(Matrix.of fun i j : Fin 4 =>
        Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (chart c hc δ y hδ (Pi.single i 1) * chart c hc δ y hδ (Pi.single j 1)))).det| =
      16 * |(c : ℝ)| := by
  rw [gram_chart c hc δ y hδ, Matrix.det_diagonal]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [show (4 : ℝ) * -4 * (4 * (c : ℝ)) * (4 * (c : ℝ)) = -(16 * |(c : ℝ)|) ^ 2 by rw [mul_pow, sq_abs]; ring,
    abs_neg, abs_pow, Real.sqrt_sq (abs_nonneg _), abs_mul, abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 16)]

def qbF (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : AutomorphicForm.IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) : Fin 4 → Mcx := fun k => chart c hc δ y hδ (Pi.single k 1)

end QuatChart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

namespace P2mGramH

section HChart

variable (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
  (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)

def qe (k : Fin 4) : Mcx := QuatChart.chart c hc δ y hδ (Pi.single k 1)

theorem sum_smul_single (a : Fin 4 → ℝ) : (∑ k, a k • (Pi.single k 1 : Fin 4 → ℝ)) = a := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem coordMap_qe : coordMap (qe c hc δ y hδ) = QuatChart.chart c hc δ y hδ := by
  funext a
  unfold coordMap qe
  rw [← sum_smul_single a, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, sum_smul_single]

theorem linearIndependent_qe : LinearIndependent ℝ (qe c hc δ y hδ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : QuatChart.chart c hc δ y hδ g = 0 := by
    rw [← coordMap_qe]; exact hg
  have : g = 0 := QuatChart.chart_injective c hc δ y hδ (by rw [h0, map_zero])
  exact fun i => congrFun this i

theorem span_qe_eq_range :
    (Submodule.span ℝ (Set.range (qe c hc δ y hδ)) : Set Mcx) = Set.range (QuatChart.chart c hc δ y hδ) := by
  apply le_antisymm
  · change Submodule.span ℝ (Set.range (qe c hc δ y hδ)) ≤ LinearMap.range (QuatChart.chart c hc δ y hδ)
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨Pi.single k 1, rfl⟩
  · rintro _ ⟨a, rfl⟩
    rw [← coordMap_qe]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem gramMeasure_qe :
    gramMeasure Bcx (qe c hc δ y hδ) =
      ENNReal.ofReal (16 * |(c : ℝ)|) • Measure.map (QuatChart.chart c hc δ y hδ) (volume : Measure (Fin 4 → ℝ)) := by
  rw [gramMeasure, coordMap_qe]
  congr 2
  exact QuatChart.sqrt_abs_det_gram_chart c hc δ y hδ

end HChart
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

end P2mGramH
p2m_reactivate "P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.P2mGramH"

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions
open P2mGramH in
theorem solution
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hgram₂ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
         Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
             ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
    letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
    ∃ φ : (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ),
      Function.Injective φ ∧
      (∀ a : Fin 4 → ℝ, Matrix.det (φ a) = ((1 : ℂ) ⊗ₜ[ℝ] (a 0 ^ 2 + a 1 ^ 2 - (c : ℝ) * (a 2 ^ 2 + a 3 ^ 2)) : ℂ ⊗[ℝ] ℝ)) ∧
      Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
          ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
        (ENNReal.ofReal (16 * |(c : ℝ)|) * s) •
          (Measure.map φ (volume : Measure (Fin 4 → ℝ))).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by
  letI iT : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  obtain ⟨hli, hspan, hτ⟩ := hgram₂

  change Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
      ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Mcx)) τ' = s • (gramMeasure Bcx e₂).withDensity rho at hτ

  have hsp : Submodule.span ℝ (Set.range e₂) = Submodule.span ℝ (Set.range (qe c hc δ y hδ)) := by
    apply SetLike.coe_injective
    rw [hspan, span_qe_eq_range, QuatChart.range_chart]
  have hn := card_eq_of_span_eq (qe c hc δ y hδ) e₂ (linearIndependent_qe c hc δ y hδ) hli hsp
  subst hn
  obtain ⟨P, hP, hdet⟩ := exists_matrix_of_span_eq (qe c hc δ y hδ) e₂ (linearIndependent_qe c hc δ y hδ) hli hsp.le
  rw [gramMeasure_eq_of_comp Bcx (qe c hc δ y hδ) e₂ P hP hdet, gramMeasure_qe, withDensity_smul_measure,
    smul_smul] at hτ
  refine ⟨QuatChart.chart c hc δ y hδ, QuatChart.chart_injective c hc δ y hδ, QuatChart.det_chart c hc δ y hδ, ?_⟩
  rw [mul_comm] at hτ
  exact hτ

end
end S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg
end P2MW
export P2MW.S_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg (solution)
