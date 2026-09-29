-- Prove2me | solution 1 for AutomorphicForm.isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6bc2b946-79f6-5cb6-a0fe-fbcacc43bcc6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set
open TensorProduct Matrix
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL toTensorGL sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel mem_sigmaCentralizer_iff"
namespace InvTCPlace
p2m_open "AutomorphicForm"

section Structures

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]

abbrev E : Type := L ⊗[K] F

abbrev ME : Type := Matrix (Fin 2) (Fin 2) (E K L F)

abbrev algRE : Algebra ℝ (E K L F) :=
  ((Algebra.TensorProduct.includeRight : F →ₐ[K] E K L F).toRingHom.comp (algebraMap ℝ F)).toAlgebra

attribute [local instance] algRE

theorem algebraMap_FE_apply (a : F) : algebraMap F (E K L F) a = (1 : L) ⊗ₜ a := rfl

scoped instance isScalarTower_RFE : IsScalarTower ℝ F (E K L F) :=
  IsScalarTower.of_algebraMap_eq (R := ℝ) (S := F) (A := E K L F) fun _ => rfl

scoped instance moduleFree_FE : Module.Free F (E K L F) := inferInstance
scoped instance moduleFinite_FE : Module.Finite F (E K L F) := inferInstance

scoped instance moduleFinite_RE : Module.Finite ℝ (E K L F) := Module.Finite.trans F (E K L F)

scoped instance instIsTopologicalRingE : IsTopologicalRing (E K L F) := isTopologicalRing_tensor K L _
scoped instance instT2E : T2Space (E K L F) := t2Space_tensor K L _
scoped instance instLCE : LocallyCompactSpace (E K L F) := locallyCompactSpace_tensor K L _

theorem continuous_algebraMap_FE : Continuous (algebraMap F (E K L F)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F (E K L F))

theorem continuous_algebraMap_RE : Continuous (algebraMap ℝ (E K L F)) :=
  (continuous_algebraMap_FE K L F).comp (continuous_algebraMap ℝ F)

scoped instance continuousSMul_RE : ContinuousSMul ℝ (E K L F) :=
  ⟨((continuous_algebraMap_RE K L F).comp continuous_fst).mul continuous_snd⟩

scoped instance instT2ME : T2Space (ME K L F) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → E K L F))
scoped instance instTAG_ME : IsTopologicalAddGroup (ME K L F) := inferInstance
scoped instance instCSM_ME : ContinuousSMul ℝ (ME K L F) := inferInstance
scoped instance instTR_ME : IsTopologicalRing (ME K L F) := inferInstance
scoped instance instFD_ME : FiniteDimensional ℝ (ME K L F) := Module.Finite.matrix

scoped instance instMeasurableSpaceME : MeasurableSpace (ME K L F) := borel _
scoped instance instBorelSpaceME : BorelSpace (ME K L F) := ⟨rfl⟩

scoped instance instSecondCountableE : SecondCountableTopology (E K L F) := by
  let b := Module.Free.chooseBasis F (E K L F)
  let e : E K L F ≃L[F] (Module.Free.ChooseBasisIndex F (E K L F) → F) :=
    IsModuleTopology.continuousLinearEquiv b.equivFun
  exact e.toHomeomorph.secondCountableTopology

scoped instance instSecondCountableME : SecondCountableTopology (ME K L F) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E K L F))

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X]
    [SecondCountableTopology X] : SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance instSecondCountableGL : SecondCountableTopology (GL (Fin 2) (E K L F)) :=
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instTG_GL : IsTopologicalGroup (GL (Fin 2) (E K L F)) := isTopologicalGroup_tensorGL K L _
scoped instance instT2_GL : T2Space (GL (Fin 2) (E K L F)) := t2Space_tensorGL K L _
scoped instance instLC_GL : LocallyCompactSpace (GL (Fin 2) (E K L F)) := locallyCompactSpace_tensorGL K L _

end Structures

section TraceForm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F] [Module.Finite ℝ F]

attribute [local instance] algRE

theorem nondegenerate_traceForm_F : (Algebra.traceForm ℝ F).Nondegenerate :=
  traceForm_nondegenerate ℝ F

theorem lmul_one_tmul (l : L) :
    (Algebra.lmul F (F ⊗[K] L) ((1 : F) ⊗ₜ[K] l) : F ⊗[K] L →ₗ[F] F ⊗[K] L) =
      (Algebra.lmul K L l : L →ₗ[K] L).baseChange F := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [LinearMap.baseChange_tmul]
      show ((1 : F) ⊗ₜ[K] l) * (a ⊗ₜ[K] m) = a ⊗ₜ[K] (Algebra.lmul K L l) m
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem trace_one_tmul (l : L) :
    Algebra.trace F (F ⊗[K] L) ((1 : F) ⊗ₜ[K] l) = algebraMap K F (Algebra.trace K L l) := by
  rw [Algebra.trace_apply, lmul_one_tmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

def commEF : F ⊗[K] L ≃ₐ[F] E K L F :=
  TensorProduct.RightActions.Algebra.TensorProduct.comm K F L

theorem commEF_tmul (a : F) (l : L) : commEF K L F (a ⊗ₜ l) = l ⊗ₜ a := rfl

theorem trace_EF_tmul_one (l : L) :
    Algebra.trace F (E K L F) (l ⊗ₜ[K] (1 : F)) = algebraMap K F (Algebra.trace K L l) := by
  rw [← commEF_tmul K L F 1 l, Algebra.trace_eq_of_algEquiv (commEF K L F), trace_one_tmul]

def bE {ι : Type*} (b : Module.Basis ι K L) : Module.Basis ι F (E K L F) :=
  TensorProduct.RightActions.Algebra.TensorProduct.basis F b

theorem bE_apply {ι : Type*} (b : Module.Basis ι K L) (i : ι) : bE K L F b i = b i ⊗ₜ (1 : F) := by
  rw [bE, TensorProduct.RightActions.Algebra.TensorProduct.basis, Module.Basis.map_apply,
    Algebra.TensorProduct.basis_apply]
  rfl

theorem traceForm_bE {ι : Type*} (b : Module.Basis ι K L) (i j : ι) :
    Algebra.traceForm F (E K L F) (bE K L F b i) (bE K L F b j) =
      algebraMap K F (Algebra.traceForm K L (b i) (b j)) := by
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply, bE_apply, bE_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, trace_EF_tmul_one]

theorem separatingLeft_traceForm_EF : (Algebra.traceForm F (E K L F)).SeparatingLeft := by
  classical
  intro x hx
  set b := Module.finBasis K L with hb
  set n := Module.finrank K L
  set B := bE K L F b with hB
  set G : Matrix (Fin n) (Fin n) K := (Algebra.traceForm K L).toMatrix b with hG
  set G' : Matrix (Fin n) (Fin n) F := G.map (algebraMap K F) with hG'
  have hGdet : G.det ≠ 0 := det_traceForm_ne_zero b
  have hG'det : IsUnit G'.det := by
    rw [hG', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hGdet).map _
  set a : Fin n → F := ⇑(B.repr x) with ha
  have hxsum : x = ∑ i, a i • B i := (B.sum_repr x).symm
  have hvec : a ᵥ* G' = 0 := by
    funext j
    have h := hx (B j)
    rw [hxsum, _root_.map_sum, LinearMap.sum_apply] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [Matrix.vecMul, dotProduct, Pi.zero_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG', Matrix.map_apply, hG, LinearMap.BilinForm.toMatrix_apply, ← traceForm_bE K L F b i j]
  have ha0 : a = 0 := by
    have : a ᵥ* G' ᵥ* G'⁻¹ = a := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG'det, Matrix.vecMul_one]
    rw [← this, hvec, Matrix.zero_vecMul]
  rw [hxsum]
  simp [ha0]

theorem nondegenerate_traceForm_E : (Algebra.traceForm ℝ (E K L F)).Nondegenerate := by
  have hsep : (Algebra.traceForm ℝ (E K L F)).SeparatingLeft := by
    intro x hx
    refine separatingLeft_traceForm_EF K L F x fun y => ?_
    refine (nondegenerate_traceForm_F F).1 (Algebra.traceForm F (E K L F) x y) fun a => ?_
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    have key : a * Algebra.trace F (E K L F) (x * y) =
        Algebra.trace F (E K L F) (algebraMap F (E K L F) a * (x * y)) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
    have h := hx (algebraMap F (E K L F) a * y)
    rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := F), mul_left_comm, ← key] at h
    rw [mul_comm]
    exact h
  have hs : (Algebra.traceForm ℝ (E K L F)).IsSymm := @Algebra.traceForm_isSymm ℝ (E K L F) _ _ _
  exact hs.isRefl.nondegenerate_iff_separatingLeft.2 hsep

end TraceForm

section Twist

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F] (σ : L ≃ₐ[K] L)

attribute [local instance] algRE

abbrev sE : E K L F →+* E K L F := sigmaTensor K L F σ

theorem sE_tmul (l : L) (a : F) : sE K L F σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sE, sigmaTensor]

theorem sE_algebraMap (a : F) : sE K L F σ (algebraMap F (E K L F) a) = algebraMap F (E K L F) a := by
  rw [algebraMap_FE_apply, sE_tmul, map_one]

theorem sE_algebraMap_real (r : ℝ) : sE K L F σ (algebraMap ℝ (E K L F) r) = algebraMap ℝ (E K L F) r :=
  sE_algebraMap K L F σ _

def sEa : E K L F →ₐ[ℝ] E K L F :=
  { sE K L F σ with commutes' := sE_algebraMap_real K L F σ }

theorem sEa_apply (z : E K L F) : sEa K L F σ z = sE K L F σ z := rfl

theorem continuous_sE : Continuous (sE K L F σ) :=
  IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L F σ.toAlgHom).toLinearMap

theorem sE_iterate_tmul (k : ℕ) (l : L) (a : F) : (sE K L F σ)^[k] (l ⊗ₜ a) = ((⇑σ)^[k] l) ⊗ₜ a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, sE_tmul, Function.iterate_succ_apply']

theorem sigma_pow_finrank : σ ^ Module.finrank K L = 1 := by
  have h1 : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L =
      Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    IntermediateField.finrank_fixedField_eq_card ⊤
  have h2 := Module.finrank_mul_finrank K
    (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
  rw [h1, Subgroup.card_top, Nat.card_eq_fintype_card] at h2
  have hdvd : Fintype.card (L ≃ₐ[K] L) ∣ Module.finrank K L := Dvd.intro_left _ h2
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_card (G := L ≃ₐ[K] L)).trans hdvd)

theorem sE_iterate_finrank (z : E K L F) : (sE K L F σ)^[Module.finrank K L] z = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [Function.iterate_fixed (map_zero _)]
  | tmul l a =>
      rw [sE_iterate_tmul, ← AlgEquiv.coe_pow, sigma_pow_finrank K L σ, AlgEquiv.one_apply]
  | add x y hx hy =>
      rw [← RingHom.coe_pow] at hx hy ⊢
      rw [map_add, hx, hy]

theorem bijective_sE : Function.Bijective (sE K L F σ) := by
  have hn : Module.finrank K L = (Module.finrank K L - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm
  constructor
  · intro x y hxy
    have hx := sE_iterate_finrank K L F σ x
    have hy := sE_iterate_finrank K L F σ y
    rw [hn, Function.iterate_succ_apply] at hx hy
    rw [← hx, ← hy, hxy]
  · intro z
    refine ⟨(sE K L F σ)^[Module.finrank K L - 1] z, ?_⟩
    have hz := sE_iterate_finrank K L F σ z
    rw [hn, Function.iterate_succ_apply'] at hz
    exact hz

def sEe : E K L F ≃ₐ[ℝ] E K L F := AlgEquiv.ofBijective (sEa K L F σ) (bijective_sE K L F σ)

theorem sEe_apply (z : E K L F) : sEe K L F σ z = sE K L F σ z := rfl

theorem trace_sE (z : E K L F) : Algebra.trace ℝ (E K L F) (sE K L F σ z) = Algebra.trace ℝ (E K L F) z := by
  rw [← sEe_apply]; exact Algebra.trace_eq_of_algEquiv (sEe K L F σ) z

abbrev sR : ME K L F →+* ME K L F := (sE K L F σ).mapMatrix

theorem sR_apply (X : ME K L F) : sR K L F σ X = X.map (sE K L F σ) := rfl

theorem trace_sR (X : ME K L F) : (sR K L F σ X).trace = sE K L F σ X.trace := by
  rw [RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]

theorem sR_smul_real (r : ℝ) (X : ME K L F) : sR K L F σ (r • X) = r • sR K L F σ X := by
  ext i j
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.map_apply, Algebra.smul_def, Algebra.smul_def, map_mul, sE_algebraMap_real]

theorem coe_sigmaGL (t : GL (Fin 2) (E K L F)) :
    ((sigmaGL K L F σ t : GL (Fin 2) (E K L F)) : ME K L F) = sR K L F σ (t : ME K L F) := rfl

theorem coe_sigmaGL_iterate (k : ℕ) (t : GL (Fin 2) (E K L F)) :
    (((sigmaGL K L F σ)^[k] t : GL (Fin 2) (E K L F)) : ME K L F) = (sR K L F σ)^[k] (t : ME K L F) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_sigmaGL, ih]

theorem sR_iterate_finrank (X : ME K L F) : (sR K L F σ)^[Module.finrank K L] X = X := by
  have key : ∀ k : ℕ, ∀ Y : ME K L F, (sR K L F σ)^[k] Y = Y.map ((sE K L F σ)^[k]) := by
    intro k
    induction k with
    | zero => intro Y; ext i j; rfl
    | succ k ih =>
        intro Y
        rw [Function.iterate_succ_apply', ih]
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Function.iterate_succ_apply']
  rw [key]
  ext i j
  simp only [Matrix.map_apply]
  exact sE_iterate_finrank K L F σ _

theorem continuous_sR : Continuous (sR K L F σ) := continuous_id.matrix_map (continuous_sE K L F σ)

theorem continuous_sigmaGL : Continuous (sigmaGL K L F σ) :=
  Continuous.units_map _ (continuous_sR K L F σ)

variable (δ : GL (Fin 2) (E K L F))

def Adelta : Subalgebra ℝ (ME K L F) where
  carrier := {X | X * (δ : ME K L F) = (δ : ME K L F) * sR K L F σ X}
  mul_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [map_mul, mul_assoc, hY, ← mul_assoc, hX, mul_assoc]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_one, one_mul, mul_one]
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [map_add, add_mul, mul_add, hX, hY]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, zero_mul, mul_zero]
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    have h1 : sR K L F σ (algebraMap ℝ (ME K L F) r) = algebraMap ℝ (ME K L F) r := by
      rw [Algebra.algebraMap_eq_smul_one, sR_smul_real, map_one]
    rw [h1]
    exact Algebra.commutes r _

theorem mem_Adelta {X : ME K L F} : X ∈ Adelta K L F σ δ ↔ X * (δ : ME K L F) = (δ : ME K L F) * sR K L F σ X := Iff.rfl

theorem mem_twistedCentralizer_iff (g : GL (Fin 2) (E K L F)) :
    g ∈ twistedCentralizer K L F σ δ ↔ (g : ME K L F) ∈ Adelta K L F σ δ := by
  rw [mem_sigmaCentralizer_iff, mem_Adelta, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    have := congrArg (fun x : GL (Fin 2) (E K L F) => (x : ME K L F)) h
    simpa [coe_sigmaGL] using this
  · intro h
    apply Units.ext
    simpa [coe_sigmaGL] using h

theorem isClosed_twistedCentralizer :
    IsClosed ((twistedCentralizer K L F σ δ : Subgroup (GL (Fin 2) (E K L F))) : Set (GL (Fin 2) (E K L F))) := by
  have h : ((twistedCentralizer K L F σ δ : Subgroup (GL (Fin 2) (E K L F))) : Set (GL (Fin 2) (E K L F))) =
      (fun t : GL (Fin 2) (E K L F) => t * δ * (sigmaGL K L F σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_sigmaCentralizer_iff
  rw [h]
  refine IsClosed.preimage ?_ isClosed_singleton
  exact (continuous_id.mul continuous_const).mul ((continuous_sigmaGL K L F σ).inv)

end Twist

section Theta

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F] (σ : L ≃ₐ[K] L)
  (δ : GL (Fin 2) (E K L F))

attribute [local instance] algRE

scoped instance instSMulCommClassME : SMulCommClass ℝ (ME K L F) (ME K L F) := ⟨fun r X Y => (Matrix.mul_smul X r Y).symm⟩
scoped instance instIsScalarTowerME : IsScalarTower ℝ (ME K L F) (ME K L F) := ⟨fun r X Y => Matrix.smul_mul r X Y⟩
scoped instance instSMulCommClassEME : SMulCommClass (E K L F) (ME K L F) (ME K L F) :=
  ⟨fun r X Y => (Matrix.mul_smul X r Y).symm⟩
scoped instance instIsScalarTowerEME : IsScalarTower (E K L F) (ME K L F) (ME K L F) := ⟨fun r X Y => Matrix.smul_mul r X Y⟩

def Θ : ME K L F →ₗ[ℝ] ME K L F where
  toFun X := (δ : ME K L F) * sR K L F σ X * ((δ⁻¹ : GL (Fin 2) (E K L F)) : ME K L F)
  map_add' X Y := by rw [map_add, mul_add, add_mul]
  map_smul' r X := by
    rw [sR_smul_real, RingHom.id_apply, mul_smul_comm, smul_mul_assoc]

theorem Θ_apply (X : ME K L F) :
    Θ K L F σ δ X = (δ : ME K L F) * sR K L F σ X * ((δ⁻¹ : GL (Fin 2) (E K L F)) : ME K L F) := rfl

theorem D_mul_Dinv : (δ : ME K L F) * ((δ⁻¹ : GL (Fin 2) (E K L F)) : ME K L F) = 1 := Units.mul_inv δ
theorem Dinv_mul_D : ((δ⁻¹ : GL (Fin 2) (E K L F)) : ME K L F) * (δ : ME K L F) = 1 := Units.inv_mul δ

theorem mem_Adelta_iff_Θ (X : ME K L F) : X ∈ Adelta K L F σ δ ↔ Θ K L F σ δ X = X := by
  rw [mem_Adelta, Θ_apply]
  constructor
  · intro h
    rw [← h, mul_assoc, D_mul_Dinv, mul_one]
  · intro h
    conv_lhs => rw [← h]
    rw [mul_assoc, Dinv_mul_D, mul_one]

theorem Θ_mul (X Y : ME K L F) : Θ K L F σ δ (X * Y) = Θ K L F σ δ X * Θ K L F σ δ Y := by
  simp only [Θ_apply, map_mul, mul_assoc]
  rw [← mul_assoc ((δ⁻¹ : GL (Fin 2) (E K L F)) : ME K L F) (δ : ME K L F), Dinv_mul_D, one_mul]

def NG (k : ℕ) : GL (Fin 2) (E K L F) := ((List.range k).map fun i => (sigmaGL K L F σ)^[i] δ).prod

theorem NG_zero : NG K L F σ δ 0 = 1 := rfl

theorem NG_succ (k : ℕ) : NG K L F σ δ (k + 1) = NG K L F σ δ k * (sigmaGL K L F σ)^[k] δ := by
  unfold NG
  exact List.prod_range_succ (fun i => (sigmaGL K L F σ)^[i] δ) k

theorem NG_finrank : NG K L F σ δ (Module.finrank K L) = normString K L F σ δ := rfl

theorem sR_iterate_mul (k : ℕ) (X Y : ME K L F) :
    (sR K L F σ)^[k] (X * Y) = (sR K L F σ)^[k] X * (sR K L F σ)^[k] Y := by
  rw [← RingHom.coe_pow, map_mul]

theorem sR_iterate_coe_inv (k : ℕ) (g : GL (Fin 2) (E K L F)) :
    (sR K L F σ)^[k] ((g⁻¹ : GL (Fin 2) (E K L F)) : ME K L F) =
      ((((sigmaGL K L F σ)^[k] g)⁻¹ : GL (Fin 2) (E K L F)) : ME K L F) := by
  rw [← coe_sigmaGL_iterate]
  have h : ∀ (k : ℕ) (g : GL (Fin 2) (E K L F)), ((sigmaGL K L F σ)^[k] g)⁻¹ = (sigmaGL K L F σ)^[k] g⁻¹ := by
    intro k
    induction k with
    | zero => intro g; rfl
    | succ k ih => intro g; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, ← map_inv]
  rw [h]

theorem Θ_iterate (k : ℕ) (X : ME K L F) :
    (Θ K L F σ δ)^[k] X = (NG K L F σ δ k : ME K L F) * (sR K L F σ)^[k] X * ((NG K L F σ δ k)⁻¹ : GL (Fin 2) (E K L F)) := by
  induction k generalizing X with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, NG_zero, inv_one, Units.val_one, one_mul,
        mul_one]
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, Θ_apply, sR_iterate_mul, sR_iterate_mul, sR_iterate_coe_inv,
        ← Function.iterate_succ_apply (sR K L F σ) k X, NG_succ, _root_.mul_inv_rev, Units.val_mul, Units.val_mul,
        coe_sigmaGL_iterate]
      simp only [mul_assoc]

variable (cδ : (E K L F)ˣ) (hN : (normString K L F σ δ : ME K L F) = (cδ : E K L F) • (1 : ME K L F))

include hN in

theorem Θ_iterate_finrank (X : ME K L F) : (Θ K L F σ δ)^[Module.finrank K L] X = X := by
  rw [Θ_iterate, sR_iterate_finrank, NG_finrank]
  have h1 : (normString K L F σ δ : ME K L F) * X = X * (normString K L F σ δ : ME K L F) := by
    rw [hN, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  rw [h1, mul_assoc, Units.mul_inv, mul_one]

theorem sum_range_shift {G : Type*} [AddCommGroup G] (f : ℕ → G) (n : ℕ) (h : f n = f 0) :
    ∑ k ∈ Finset.range n, f (k + 1) = ∑ k ∈ Finset.range n, f k := by
  have h1 := Finset.sum_range_succ' f n
  have h2 := Finset.sum_range_succ f n
  rw [h] at h2
  exact add_right_cancel (h1.symm.trans h2)

end Theta

section Gram

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]

attribute [local instance] algRE

def β : LinearMap.BilinForm ℝ (ME K L F) :=
  LinearMap.mk₂ ℝ (fun X Y => Algebra.trace ℝ (E K L F) (X * Y).trace)
    (fun X₁ X₂ Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by rw [smul_mul_assoc, Matrix.trace_smul r (X * Y), map_smul, smul_eq_mul])
    (fun X Y₁ Y₂ => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by rw [mul_smul_comm, Matrix.trace_smul r (X * Y), map_smul, smul_eq_mul])

theorem β_apply (X Y : ME K L F) : β K L F X Y = Algebra.trace ℝ (E K L F) (X * Y).trace := rfl

theorem β_comm (X Y : ME K L F) : β K L F X Y = β K L F Y X := by
  rw [β_apply, β_apply, Matrix.trace_mul_comm]

theorem eq_zero_of_forall_β_eq_zero (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate) {X : ME K L F}
    (h : ∀ Y, β K L F X Y = 0) : X = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  refine hE.1 (X i j) fun z => ?_
  rw [Algebra.traceForm_apply]
  have := h (Matrix.single j i z)
  rwa [β_apply, Matrix.trace_mul_single, op_smul_eq_mul] at this

variable (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (E K L F))

theorem β_Θ (X Y : ME K L F) : β K L F (Θ K L F σ δ X) (Θ K L F σ δ Y) = β K L F X Y := by
  rw [β_apply, ← Θ_mul, Θ_apply, Matrix.trace_mul_cycle, Dinv_mul_D, one_mul, trace_sR, trace_sE, β_apply]

theorem β_Θ_iterate (k : ℕ) (X Y : ME K L F) :
    β K L F ((Θ K L F σ δ)^[k] X) ((Θ K L F σ δ)^[k] Y) = β K L F X Y := by
  induction k generalizing X Y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, β_Θ]

variable (cδ : (E K L F)ˣ) (hN : (normString K L F σ δ : ME K L F) = (cδ : E K L F) • (1 : ME K L F))

def Sop (X : ME K L F) : ME K L F := ∑ k ∈ Finset.range (Module.finrank K L), (Θ K L F σ δ)^[k] X

theorem Sop_apply (X : ME K L F) : Sop K L F σ δ X = ∑ k ∈ Finset.range (Module.finrank K L), (Θ K L F σ δ)^[k] X := rfl

theorem Sop_of_mem {X : ME K L F} (hX : X ∈ Adelta K L F σ δ) : Sop K L F σ δ X = (Module.finrank K L : ℝ) • X := by
  have hfix : ∀ k, (Θ K L F σ δ)^[k] X = X := fun k =>
    Function.iterate_fixed ((mem_Adelta_iff_Θ K L F σ δ X).1 hX) k
  rw [Sop_apply, Finset.sum_congr rfl fun k _ => hfix k, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]

include hN in

theorem Sop_mem (X : ME K L F) : Sop K L F σ δ X ∈ Adelta K L F σ δ := by
  rw [mem_Adelta_iff_Θ, Sop_apply, _root_.map_sum]
  have h : ∀ k, Θ K L F σ δ ((Θ K L F σ δ)^[k] X) = (Θ K L F σ δ)^[k + 1] X := fun k =>
    (Function.iterate_succ_apply' _ _ _).symm
  simp_rw [h]
  exact sum_range_shift (fun k => (Θ K L F σ δ)^[k] X) _ (Θ_iterate_finrank K L F σ δ cδ hN X)

include hN in

theorem β_Sop (X Y : ME K L F) : β K L F (Sop K L F σ δ X) Y = β K L F X (Sop K L F σ δ Y) := by
  set n := Module.finrank K L with hn
  rw [Sop_apply, Sop_apply, LinearMap.map_sum₂, _root_.map_sum]
  have h1 : ∀ k ∈ Finset.range n, β K L F ((Θ K L F σ δ)^[k] X) Y = β K L F X ((Θ K L F σ δ)^[n - 1 - k + 1] Y) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.1 hk
    have hY : (Θ K L F σ δ)^[k] ((Θ K L F σ δ)^[n - 1 - k + 1] Y) = Y := by
      rw [← Function.iterate_add_apply]
      have : k + (n - 1 - k + 1) = n := by omega
      rw [this]
      exact Θ_iterate_finrank K L F σ δ cδ hN Y
    conv_lhs => rw [← hY]
    exact β_Θ_iterate K L F σ δ k X _
  rw [Finset.sum_congr rfl h1, Finset.sum_range_reflect (fun k => β K L F X ((Θ K L F σ δ)^[k + 1] Y)) n]
  exact sum_range_shift (fun k => β K L F X ((Θ K L F σ δ)^[k] Y)) n
    (by simp only [hn]; rw [Θ_iterate_finrank K L F σ δ cδ hN Y, Function.iterate_zero_apply])

include hN in

theorem eq_zero_of_mem_Adelta (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate)
    {m : ME K L F} (hm : m ∈ Adelta K L F σ δ) (h : ∀ Y ∈ Adelta K L F σ δ, β K L F m Y = 0) : m = 0 := by
  refine eq_zero_of_forall_β_eq_zero K L F hE fun Y => ?_
  have hn : (Module.finrank K L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have key : (Module.finrank K L : ℝ) * β K L F m Y = 0 := by
    rw [← smul_eq_mul, ← LinearMap.map_smul₂, ← Sop_of_mem K L F σ δ hm, β_Sop K L F σ δ cδ hN]
    exact h _ (Sop_mem K L F σ δ cδ hN Y)
  exact (mul_eq_zero.1 key).resolve_left hn

end Gram

section Frobenius

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F] (σ : L ≃ₐ[K] L)
  (δ : GL (Fin 2) (E K L F))

attribute [local instance] algRE

abbrev W : Submodule ℝ (ME K L F) := Subalgebra.toSubmodule (Adelta K L F σ δ)

scoped instance instCSM_W : ContinuousSMul ℝ (W K L F σ δ) := inferInstance
scoped instance instTAG_W : IsTopologicalAddGroup (W K L F σ δ) := inferInstance

def lam (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) : W K L F σ δ →ₗ[ℝ] W K L F σ δ where
  toFun x := ⟨a * (x : ME K L F), (Adelta K L F σ δ).mul_mem ha x.2⟩
  map_add' x y := by apply Subtype.ext; simp [mul_add]
  map_smul' r x := by apply Subtype.ext; simp

def rho (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) : W K L F σ δ →ₗ[ℝ] W K L F σ δ where
  toFun x := ⟨(x : ME K L F) * a, (Adelta K L F σ δ).mul_mem x.2 ha⟩
  map_add' x y := by apply Subtype.ext; simp [add_mul]
  map_smul' r x := by apply Subtype.ext; simp

theorem coe_lam (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) (x : W K L F σ δ) :
    ((lam K L F σ δ a ha x : W K L F σ δ) : ME K L F) = a * (x : ME K L F) := rfl

theorem coe_rho (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) (x : W K L F σ δ) :
    ((rho K L F σ δ a ha x : W K L F σ δ) : ME K L F) = (x : ME K L F) * a := rfl

theorem lam_one : lam K L F σ δ 1 (Adelta K L F σ δ).one_mem = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_lam, one_mul, LinearMap.id_apply]

theorem lam_mul (a b : ME K L F) (ha : a ∈ Adelta K L F σ δ) (hb : b ∈ Adelta K L F σ δ) :
    lam K L F σ δ (a * b) ((Adelta K L F σ δ).mul_mem ha hb) = lam K L F σ δ a ha ∘ₗ lam K L F σ δ b hb := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [LinearMap.comp_apply, coe_lam, coe_lam, coe_lam, mul_assoc]

def bW : Module.Basis (Fin (Module.finrank ℝ (W K L F σ δ))) ℝ (W K L F σ δ) := Module.finBasis ℝ (W K L F σ δ)

def βW : LinearMap.BilinForm ℝ (W K L F σ δ) := (β K L F).comp (W K L F σ δ).subtype (W K L F σ δ).subtype

theorem βW_apply (x y : W K L F σ δ) : βW K L F σ δ x y = β K L F (x : ME K L F) (y : ME K L F) := rfl

variable (cδ : (E K L F)ˣ) (hN : (normString K L F σ δ : ME K L F) = (cδ : E K L F) • (1 : ME K L F))

include hN in
theorem nondegenerate_βW (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate) : (βW K L F σ δ).Nondegenerate := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · apply Subtype.ext
    refine eq_zero_of_mem_Adelta K L F σ δ cδ hN hE m.2 fun Y hY => ?_
    exact hm ⟨Y, hY⟩
  · apply Subtype.ext
    refine eq_zero_of_mem_Adelta K L F σ δ cδ hN hE m.2 fun Y hY => ?_
    have := hm ⟨Y, hY⟩
    rw [βW_apply, β_comm] at this
    exact this

theorem βW_comp_lam_eq_comp_rho (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) :
    (βW K L F σ δ).comp (lam K L F σ δ a ha) LinearMap.id = (βW K L F σ δ).comp LinearMap.id (rho K L F σ δ a ha) := by
  refine LinearMap.ext₂ fun x y => ?_
  simp only [LinearMap.BilinForm.comp_apply, LinearMap.id_apply]
  rw [βW_apply, βW_apply, coe_lam, coe_rho, β_apply, β_apply]
  conv_rhs => rw [← mul_assoc, Matrix.trace_mul_cycle]

include hN in

theorem det_lam_eq_det_rho (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate) (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) :
    (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ a ha)).det =
      (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (rho K L F σ δ a ha)).det := by
  have hJ0 : (LinearMap.BilinForm.toMatrix (bW K L F σ δ) (βW K L F σ δ)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bW K L F σ δ)).1 (nondegenerate_βW K L F σ δ cδ hN hE)
  have h1 := LinearMap.BilinForm.toMatrix_comp (bW K L F σ δ) (bW K L F σ δ) (βW K L F σ δ) (lam K L F σ δ a ha) LinearMap.id
  have h2 := LinearMap.BilinForm.toMatrix_comp (bW K L F σ δ) (bW K L F σ δ) (βW K L F σ δ) LinearMap.id (rho K L F σ δ a ha)
  rw [βW_comp_lam_eq_comp_rho, h2, LinearMap.toMatrix_id, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one] at h1

  have h3 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h3
  have h4 : (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (rho K L F σ δ a ha)).det *
      (LinearMap.BilinForm.toMatrix (bW K L F σ δ) (βW K L F σ δ)).det =
      (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ a ha)).det *
      (LinearMap.BilinForm.toMatrix (bW K L F σ δ) (βW K L F σ δ)).det := by
    rw [mul_comm]; exact h3
  exact (mul_right_cancel₀ hJ0 h4).symm

theorem lam_bW_eq_sum (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) (j : Fin (Module.finrank ℝ (W K L F σ δ))) :
    lam K L F σ δ a ha (bW K L F σ δ j) =
      ∑ i, LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ a ha) i j • bW K L F σ δ i := by
  have h := Matrix.toLin_self (v₁ := bW K L F σ δ) (v₂ := bW K L F σ δ)
    (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ a ha)) j
  rw [Matrix.toLin_toMatrix] at h
  exact h

theorem rho_bW_eq_sum (a : ME K L F) (ha : a ∈ Adelta K L F σ δ) (j : Fin (Module.finrank ℝ (W K L F σ δ))) :
    rho K L F σ δ a ha (bW K L F σ δ j) =
      ∑ i, LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (rho K L F σ δ a ha) i j • bW K L F σ δ i := by
  have h := Matrix.toLin_self (v₁ := bW K L F σ δ) (v₂ := bW K L F σ δ)
    (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (rho K L F σ δ a ha)) j
  rw [Matrix.toLin_toMatrix] at h
  exact h

abbrev Aδ : Type := ↥(Adelta K L F σ δ)

scoped instance instTR_Aδ : IsTopologicalRing (Aδ K L F σ δ) :=
  inferInstanceAs (IsTopologicalRing (Adelta K L F σ δ).toSubring)

scoped instance instMS_Aδ : MeasurableSpace (Aδ K L F σ δ) := borel _
scoped instance instBS_Aδ : BorelSpace (Aδ K L F σ δ) := ⟨rfl⟩
scoped instance instFD_Aδ : FiniteDimensional ℝ (Aδ K L F σ δ) :=
  FiniteDimensional.of_injective (Adelta K L F σ δ).val.toLinearMap Subtype.val_injective

def WtoA : W K L F σ δ ≃ₗ[ℝ] Aδ K L F σ δ where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem coe_WtoA (x : W K L F σ δ) : ((WtoA K L F σ δ x : Aδ K L F σ δ) : ME K L F) = (x : ME K L F) := rfl

def bA : Module.Basis (Fin (Module.finrank ℝ (W K L F σ δ))) ℝ (Aδ K L F σ δ) := (bW K L F σ δ).map (WtoA K L F σ δ)

def eA : Fin (Module.finrank ℝ (W K L F σ δ)) → Aδ K L F σ δ := fun i => WtoA K L F σ δ (bW K L F σ δ i)

theorem bA_apply (i : Fin (Module.finrank ℝ (W K L F σ δ))) : bA K L F σ δ i = eA K L F σ δ i :=
  Module.Basis.map_apply _ _ _

theorem coe_bA : ⇑(bA K L F σ δ) = eA K L F σ δ := funext (bA_apply K L F σ δ)

theorem linearIndependent_eA : LinearIndependent ℝ (eA K L F σ δ) := by
  rw [← coe_bA]; exact (bA K L F σ δ).linearIndependent

theorem span_eA : Submodule.span ℝ (Set.range (eA K L F σ δ)) = Subalgebra.toSubmodule (⊤ : Subalgebra ℝ (Aδ K L F σ δ)) := by
  rw [Algebra.top_toSubmodule, ← coe_bA, (bA K L F σ δ).span_eq]

def χ : Aδ K L F σ δ →* ℝ where
  toFun g := (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ (g : ME K L F) g.2)).det
  map_one' := by
    have h : lam K L F σ δ ((1 : Aδ K L F σ δ) : ME K L F) (1 : Aδ K L F σ δ).2 = LinearMap.id := lam_one K L F σ δ
    rw [h, LinearMap.toMatrix_id, Matrix.det_one]
  map_mul' g h := by
    have hm : lam K L F σ δ ((g * h : Aδ K L F σ δ) : ME K L F) (g * h).2 =
        lam K L F σ δ (g : ME K L F) g.2 ∘ₗ lam K L F σ δ (h : ME K L F) h.2 := lam_mul K L F σ δ _ _ g.2 h.2
    rw [hm, LinearMap.toMatrix_comp (bW K L F σ δ) (bW K L F σ δ) (bW K L F σ δ), Matrix.det_mul]

theorem χ_apply (g : Aδ K L F σ δ) :
    χ K L F σ δ g = (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ (g : ME K L F) g.2)).det := rfl

theorem continuous_χ : Continuous (χ K L F σ δ) := by
  have hrepr : Continuous ((bW K L F σ δ).equivFun : W K L F σ δ → (Fin (Module.finrank ℝ (W K L F σ δ)) → ℝ)) :=
    (bW K L F σ δ).equivFun.toLinearMap.continuous_of_finiteDimensional
  have hmat : Continuous fun g : Aδ K L F σ δ =>
      LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ (g : ME K L F) g.2) := by
    refine continuous_matrix fun i j => ?_
    have h : (fun g : Aδ K L F σ δ => LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ (g : ME K L F) g.2) i j) =
        fun g : Aδ K L F σ δ => (bW K L F σ δ).equivFun (lam K L F σ δ (g : ME K L F) g.2 (bW K L F σ δ j)) i := by
      funext g
      rw [LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]
    rw [h]
    refine (continuous_apply i).comp (hrepr.comp ?_)
    exact (continuous_subtype_val.mul continuous_const).subtype_mk _
  show Continuous fun g : Aδ K L F σ δ =>
    (LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ (g : ME K L F) g.2)).det
  exact hmat.matrix_det

theorem mul_eA_eq_sum (g : Aδ K L F σ δ) (j : Fin (Module.finrank ℝ (W K L F σ δ))) :
    g * eA K L F σ δ j =
      ∑ i, LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ (g : ME K L F) g.2) i j • eA K L F σ δ i := by
  have h := congrArg (WtoA K L F σ δ) (lam_bW_eq_sum K L F σ δ (g : ME K L F) g.2 j)
  rw [_root_.map_sum] at h
  simp only [map_smul] at h
  refine Eq.trans ?_ h
  apply Subtype.ext
  rfl

theorem eA_mul_eq_sum (g : Aδ K L F σ δ) (j : Fin (Module.finrank ℝ (W K L F σ δ))) :
    eA K L F σ δ j * g =
      ∑ i, LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (rho K L F σ δ (g : ME K L F) g.2) i j • eA K L F σ δ i := by
  have h := congrArg (WtoA K L F σ δ) (rho_bW_eq_sum K L F σ δ (g : ME K L F) g.2 j)
  rw [_root_.map_sum] at h
  simp only [map_smul] at h
  refine Eq.trans ?_ h
  apply Subtype.ext
  rfl

include hN in

theorem exists_haar_units (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate) :
    letI : MeasurableSpace (⊤ : Subgroup (Aδ K L F σ δ)ˣ) := borel _
    ∃ τ : Measure (⊤ : Subgroup (Aδ K L F σ δ)ˣ), τ.IsHaarMeasure ∧ τ.IsMulRightInvariant := by
  obtain ⟨τ, hH, hR, -⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
      (⊤ : Subalgebra ℝ (Aδ K L F σ δ)) (⊤ : Subgroup (Aδ K L F σ δ)ˣ) (fun g => by simp)
      _ (eA K L F σ δ) (linearIndependent_eA K L F σ δ) (span_eA K L F σ δ)
      (χ K L F σ δ) (continuous_χ K L F σ δ)
      (fun g _ => ⟨LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (lam K L F σ δ ((g : Aδ K L F σ δ) : ME K L F) (g : Aδ K L F σ δ).2),
        mul_eA_eq_sum K L F σ δ (g : Aδ K L F σ δ), rfl⟩)
      (fun g _ => ⟨LinearMap.toMatrix (bW K L F σ δ) (bW K L F σ δ) (rho K L F σ δ ((g : Aδ K L F σ δ) : ME K L F) (g : Aδ K L F σ δ).2),
        eA_mul_eq_sum K L F σ δ (g : Aδ K L F σ δ), by
          rw [χ_apply, det_lam_eq_det_rho K L F σ δ cδ hN hE]⟩)
  exact ⟨τ, hH, hR⟩

end Frobenius

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F] (σ : L ≃ₐ[K] L)
  (δ : GL (Fin 2) (E K L F))

attribute [local instance] algRE

abbrev Tδ : Type := ↥(twistedCentralizer K L F σ δ)

scoped instance instMS_Tδ : MeasurableSpace (Tδ K L F σ δ) := twistedCentralizerBorel K L F σ δ
scoped instance instBS_Tδ : BorelSpace (Tδ K L F σ δ) := ⟨rfl⟩
scoped instance instLC_Tδ : LocallyCompactSpace (Tδ K L F σ δ) := (isClosed_twistedCentralizer K L F σ δ).locallyCompactSpace
scoped instance instSC_Tδ : SecondCountableTopology (Tδ K L F σ δ) := TopologicalSpace.Subtype.secondCountableTopology _
scoped instance instTG_Tδ : IsTopologicalGroup (Tδ K L F σ δ) := inferInstance

def toUnit (t : Tδ K L F σ δ) : (Aδ K L F σ δ)ˣ where
  val := ⟨((t : GL (Fin 2) (E K L F)) : ME K L F), (mem_twistedCentralizer_iff K L F σ δ _).1 t.2⟩
  inv := ⟨(((t : GL (Fin 2) (E K L F))⁻¹ : GL (Fin 2) (E K L F)) : ME K L F),
    (mem_twistedCentralizer_iff K L F σ δ _).1 (Subgroup.inv_mem _ t.2)⟩
  val_inv := Subtype.ext (Units.mul_inv _)
  inv_val := Subtype.ext (Units.inv_mul _)

def ofUnit (u : (Aδ K L F σ δ)ˣ) : Tδ K L F σ δ :=
  ⟨⟨((u : Aδ K L F σ δ) : ME K L F), ((u⁻¹ : (Aδ K L F σ δ)ˣ) : Aδ K L F σ δ),
      congrArg Subtype.val u.mul_inv, congrArg Subtype.val u.inv_mul⟩,
    (mem_twistedCentralizer_iff K L F σ δ _).2 (u : Aδ K L F σ δ).2⟩

def unitEquiv : Tδ K L F σ δ ≃* (Aδ K L F σ δ)ˣ where
  toFun := toUnit K L F σ δ
  invFun := ofUnit K L F σ δ
  left_inv t := by
    apply Subtype.ext; apply Units.ext; rfl
  right_inv u := by
    apply Units.ext; apply Subtype.ext; rfl
  map_mul' s t := by
    apply Units.ext; apply Subtype.ext; rfl

theorem continuous_unitEquiv : Continuous (unitEquiv K L F σ δ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).subtype_mk _

theorem continuous_unitEquiv_symm : Continuous (unitEquiv K L F σ δ).symm := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_subtype_val.comp Units.continuous_val
  · exact continuous_subtype_val.comp Units.continuous_coe_inv

def unitEquivTop : Tδ K L F σ δ ≃ₜ* (⊤ : Subgroup (Aδ K L F σ δ)ˣ) where
  toMulEquiv := (unitEquiv K L F σ δ).trans Subgroup.topEquiv.symm
  continuous_toFun := (continuous_unitEquiv K L F σ δ).subtype_mk _
  continuous_invFun := (continuous_unitEquiv_symm K L F σ δ).comp continuous_subtype_val

variable (cδ : (E K L F)ˣ) (hN : (normString K L F σ δ : ME K L F) = (cδ : E K L F) • (1 : ME K L F))

include hN in

theorem exists_haar_twoSided (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate) :
    ∃ τ : Measure (Tδ K L F σ δ), τ.IsHaarMeasure ∧ τ.IsMulRightInvariant := by
  letI : MeasurableSpace (⊤ : Subgroup (Aδ K L F σ δ)ˣ) := borel _
  haveI : BorelSpace (⊤ : Subgroup (Aδ K L F σ δ)ˣ) := ⟨rfl⟩
  obtain ⟨τ₀, hH, hR⟩ := exists_haar_units K L F σ δ cδ hN hE
  set e := (unitEquivTop K L F σ δ).symm with he
  refine ⟨Measure.map e τ₀, ContinuousMulEquiv.isHaarMeasure_map τ₀ e, ⟨fun g => ?_⟩⟩
  have hme : Measurable e := e.continuous.measurable
  rw [Measure.map_map (measurable_mul_const g) hme]
  have hfun : ((fun x => x * g) ∘ e) = e ∘ fun x => x * e.symm g := by
    funext x
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
  rw [hfun, ← Measure.map_map hme (measurable_mul_const _), MeasureTheory.map_mul_right_eq_self]

include hN in

theorem isMulRightInvariant_of_isHaarMeasure (hE : (Algebra.traceForm ℝ (E K L F)).Nondegenerate)
    (τ' : Measure (Tδ K L F σ δ)) [τ'.IsHaarMeasure] : τ'.IsMulRightInvariant := by
  obtain ⟨τ, hH, hR⟩ := exists_haar_twoSided K L F σ δ cδ hN hE
  haveI := hH; haveI := hR
  have h := Measure.isMulLeftInvariant_eq_smul τ' τ
  rw [h]
  infer_instance

end Transport

section Central

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F] (σ : L ≃ₐ[K] L)

attribute [local instance] algRE

abbrev sc {R : Type*} [CommRing R] (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem coe_sc {R : Type*} [CommRing R] (c : Rˣ) : ((sc c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (c : R) • 1 := by
  show Matrix.scalar (Fin 2) (c : R) = _
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem map_sc {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : R →* S) c) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) R) i j) = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all [sc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem exists_hN (c : Fˣ) (δ y : GL (Fin 2) (E K L F)) (hδ : IsNormConjugator K L F σ (sc c) δ y) :
    ∃ cδ : (E K L F)ˣ, (normString K L F σ δ : ME K L F) = (cδ : E K L F) • (1 : ME K L F) := by
  set c' : (E K L F)ˣ := Units.map ((Algebra.TensorProduct.includeRight : F →ₐ[K] E K L F).toRingHom : F →* E K L F) c
  have hT : toTensorGL K L F (sc c) = sc c' := map_sc _ c
  have hNs : normString K L F σ δ = sc c' := by
    have h := hδ
    rw [IsNormConjugator, hT] at h
    calc normString K L F σ δ = y * (y⁻¹ * normString K L F σ δ * y) * y⁻¹ := by group
      _ = sc c' := by rw [← h, ← scalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨c', by rw [hNs, coe_sc]⟩

end Central

section Engine

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (F : Type) [Field F] [Algebra K F] [Algebra ℝ F]
  [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [ContinuousSMul ℝ F] [Module.Finite ℝ F] (σ : L ≃ₐ[K] L)

attribute [local instance] algRE

theorem isInvInvariant_of_isHaarMeasure (c : Fˣ) (δ y : GL (Fin 2) (E K L F))
    (hδ : IsNormConjugator K L F σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : Measure (Tδ K L F σ δ)) [τ'.IsHaarMeasure] : τ'.IsMulRightInvariant ∧ τ'.IsInvInvariant := by
  have hE := nondegenerate_traceForm_E K L F
  obtain ⟨cδ, hN⟩ := exists_hN K L F σ c δ y hδ
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure K L F σ δ cδ hN hE τ'
  exact ⟨this, MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant τ'⟩

end Engine

section Place

variable (K : Type) [Field K] [NumberField K] (v : InfinitePlace K)

abbrev algRinf : Algebra ℝ (InfiniteAdeleRing K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

abbrev algRF : Algebra ℝ v.Completion :=
  ((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K)))).toAlgebra

attribute [local instance] algRinf algRF

def mixedAlgEquiv : InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) fun r => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
    exact RingEquiv.apply_symm_apply _ _

theorem moduleFinite_inf : Module.Finite ℝ (InfiniteAdeleRing K) :=
  Module.Finite.equiv (mixedAlgEquiv K).symm.toLinearEquiv

def evalLin : InfiniteAdeleRing K →ₗ[ℝ] v.Completion where
  toFun x := x v
  map_add' x y := rfl
  map_smul' r x := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
    rfl

theorem moduleFinite_completion : Module.Finite ℝ v.Completion :=
  haveI := moduleFinite_inf K
  Module.Finite.of_surjective (evalLin K v) (Function.surjective_eval v)

theorem continuous_ringEquiv_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro w
  by_cases hw : InfinitePlace.IsReal w
  · have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y w)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm (y.1 ⟨w, hw⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨w, hw⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex w := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y w)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨w, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨w, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_algebraMap_RF : Continuous (algebraMap ℝ v.Completion) :=
  (continuous_apply v).comp ((continuous_ringEquiv_mixedSpace_symm K).comp
    (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K)))

theorem continuousSMul_completion : ContinuousSMul ℝ v.Completion :=
  ⟨((continuous_algebraMap_RF K v).comp continuous_fst).mul continuous_snd⟩

theorem secondCountableTopology_completion : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

end Place

end AutomorphicForm.InvTCPlace
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.AutomorphicForm.InvTCPlace"
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.AutomorphicForm.InvTCPlace"

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (c : (v.Completion)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : AutomorphicForm.IsNormConjugator K L v.Completion σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L v.Completion σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ) τ') :
    @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ) _ τ' := by
  open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.AutomorphicForm AutomorphicForm.InvTCPlace in
  · letI : Algebra ℝ v.Completion := algRF K v
    haveI : Module.Finite ℝ v.Completion := moduleFinite_completion K v
    haveI : ContinuousSMul ℝ v.Completion := continuousSMul_completion K v
    haveI : SecondCountableTopology v.Completion := secondCountableTopology_completion K v
    haveI := hτ'
    exact (isInvInvariant_of_isHaarMeasure K L v.Completion σ c δ y hδ τ').2

end S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
end P2MW
export P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar (solution)
