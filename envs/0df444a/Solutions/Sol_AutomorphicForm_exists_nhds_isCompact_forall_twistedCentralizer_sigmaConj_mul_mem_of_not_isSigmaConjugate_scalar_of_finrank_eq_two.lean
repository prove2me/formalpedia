-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/39f63c23-5b26-5bd1-b177-13b7ec50d23b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain TopologicalSpace Topology Filter Set
open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedCompactT

section Algebra

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_algebraMap (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (algebraMap A (L ⊗[K] A) a) = algebraMap A (L ⊗[K] A) a := by
  change AutomorphicForm.sigmaTensor K L A σ ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (b : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A σ (AutomorphicForm.sigmaTensor K L A σ b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigma_facts (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∀ l : L, ∃ k : K, l + σ l = algebraMap K L k := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, fun l => ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · set m := l + σ l with hm
    have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have hσσ : σ (σ l) = l := by
      have := AlgEquiv.congr_fun hpow l
      rwa [pow_two, AlgEquiv.mul_apply] at this
    have hσm : σ m = m := by rw [hm, map_add, hσσ, add_comm]
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) m :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, hσm])
    have hfix : ∀ τ : L ≃ₐ[K] L, τ m = m := fun τ => by
      have := hle (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have hmem : m ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr fun τ _ => hfix τ
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk.symm⟩

theorem exists_add_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    ∃ r : A, e + AutomorphicForm.sigmaTensor K L A σ e = algebraMap A (L ⊗[K] A) r := by
  obtain ⟨-, htr⟩ := sigma_facts K L σ h2 hgen
  induction e using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := htr l
      refine ⟨k • a, ?_⟩
      rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, hk, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      change (1 : L) ⊗ₜ[K] (k • a) = (k • a) • ((1 : L) ⊗ₜ[K] (1 : A))
      rw [TensorProduct.RightActions.smul_def]
      simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
      obtain ⟨r₁, h₁⟩ := hx
      obtain ⟨r₂, h₂⟩ := hy
      refine ⟨r₁ + r₂, ?_⟩
      rw [map_add, map_add, ← h₁, ← h₂]
      abel

theorem exists_eq_algebraMap_of_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A}
    (he : AutomorphicForm.sigmaTensor K L A σ e = e) :
    ∃ r : A, e = algebraMap A (L ⊗[K] A) r := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  obtain ⟨r, hr⟩ := exists_add_sigmaTensor_eq K L A σ h2 hgen e
  rw [he] at hr
  refine ⟨2⁻¹ * r, ?_⟩
  rw [map_mul, ← hr]
  have h2A : algebraMap A (L ⊗[K] A) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap A (L ⊗[K] A)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc e = (algebraMap A (L ⊗[K] A) 2⁻¹ * 2) * e := by rw [h2A, one_mul]
    _ = algebraMap A (L ⊗[K] A) 2⁻¹ * (e + e) := by rw [mul_assoc, two_mul]

theorem exists_leftInverse :
    ∃ pr : (L ⊗[K] A) →ₗ[A] A, ∀ a : A, pr (algebraMap A (L ⊗[K] A) a) = a := by
  have hinj : Function.Injective (algebraMap A (L ⊗[K] A)) := (algebraMap A (L ⊗[K] A)).injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap A (L ⊗[K] A))
    (LinearMap.ker_eq_bot.mpr hinj)
  exact ⟨g, fun a => by simpa using LinearMap.congr_fun hg a⟩

def pr : (L ⊗[K] A) →ₗ[A] A := Classical.choose (exists_leftInverse K L A)

theorem pr_algebraMap (a : A) : pr K L A (algebraMap A (L ⊗[K] A) a) = a :=
  Classical.choose_spec (exists_leftInverse K L A) a

def nrm (e : L ⊗[K] A) : A := pr K L A (e * AutomorphicForm.sigmaTensor K L A σ e)

theorem mul_sigmaTensor_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    e * AutomorphicForm.sigmaTensor K L A σ e = algebraMap A (L ⊗[K] A) (nrm K L A σ e) := by
  obtain ⟨hσσ, -⟩ := sigma_facts K L σ h2 hgen
  have hfix : AutomorphicForm.sigmaTensor K L A σ (e * AutomorphicForm.sigmaTensor K L A σ e) =
      e * AutomorphicForm.sigmaTensor K L A σ e := by
    rw [map_mul, sigmaTensor_sigmaTensor K L A σ hσσ, mul_comm]
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_sigmaTensor_eq K L A σ h2 hgen hfix
  rw [nrm, hr, pr_algebraMap]

theorem isUnit_iff_nrm_ne_zero (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (e : L ⊗[K] A) :
    IsUnit e ↔ nrm K L A σ e ≠ 0 := by
  have key := mul_sigmaTensor_eq K L A σ h2 hgen e
  constructor
  · intro he h0
    rw [h0, map_zero] at key
    have hu : IsUnit (e * AutomorphicForm.sigmaTensor K L A σ e) :=
      he.mul (he.map (AutomorphicForm.sigmaTensor K L A σ))
    rw [key] at hu
    exact not_isUnit_zero hu
  · intro hn
    refine IsUnit.of_mul_eq_one
      (AutomorphicForm.sigmaTensor K L A σ e * algebraMap A (L ⊗[K] A) (nrm K L A σ e)⁻¹) ?_
    rw [← mul_assoc, key, ← map_mul, mul_inv_cancel₀ hn, map_one]

theorem inverse_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A} (he : IsUnit e) :
    Ring.inverse e =
      AutomorphicForm.sigmaTensor K L A σ e * algebraMap A (L ⊗[K] A) (nrm K L A σ e)⁻¹ := by
  have key := mul_sigmaTensor_eq K L A σ h2 hgen e
  have hn : nrm K L A σ e ≠ 0 := (isUnit_iff_nrm_ne_zero K L A σ h2 hgen e).mp he
  obtain ⟨u, rfl⟩ := he
  rw [Ring.inverse_unit]
  apply Units.inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, key, ← map_mul, mul_inv_cancel₀ hn, map_one]

end Algebra

section Scalars

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((AutomorphicForm.sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j
      = AutomorphicForm.sigmaTensor K L A σ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j
      = (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A γ)
      = AutomorphicForm.toTensorGL K L A γ := by
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply]
  simp [AutomorphicForm.sigmaTensor]

def Z (a : Aˣ) : GL (Fin 2) (L ⊗[K] A) :=
  AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) a)

theorem Z_eq_scalar (a : Aˣ) :
    Z K L A a = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) : A →* L ⊗[K] A) a) := by
  ext i j
  rw [Z, toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem Z_mul_comm (a : Aˣ) (g : GL (Fin 2) (L ⊗[K] A)) : Z K L A a * g = g * Z K L A a := by
  rw [Z_eq_scalar]
  apply Units.ext
  push_cast
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem sigmaGL_Z (a : Aˣ) : AutomorphicForm.sigmaGL K L A σ (Z K L A a) = Z K L A a :=
  sigmaGL_toTensorGL K L A σ _

theorem Z_inv_mul (a : Aˣ) : Z K L A a⁻¹ * Z K L A a = 1 := by
  unfold Z
  rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]

end Scalars

section Place

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem continuous_sigmaTensor :
    Continuous (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L (v.adicCompletion K) σ.toAlgHom).toLinearMap
  exact h

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ((AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
      = (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map
          (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem continuous_pr : Continuous (pr K L (v.adicCompletion K)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_nrm : Continuous (nrm K L (v.adicCompletion K) σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (continuous_pr K L v).comp (continuous_id.mul (continuous_sigmaTensor K L v σ))

theorem isOpen_isUnit (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    IsOpen {e : L ⊗[K] v.adicCompletion K | IsUnit e} := by
  have : {e : L ⊗[K] v.adicCompletion K | IsUnit e} =
      nrm K L (v.adicCompletion K) σ ⁻¹' {0}ᶜ := by
    ext e
    simp [isUnit_iff_nrm_ne_zero K L (v.adicCompletion K) σ h2 hgen]
  rw [this]
  exact isOpen_compl_singleton.preimage (continuous_nrm K L v σ)

theorem continuousOn_inverse (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ContinuousOn Ring.inverse {e : L ⊗[K] v.adicCompletion K | IsUnit e} := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have heq : EqOn Ring.inverse (fun e => AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e *
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        (nrm K L (v.adicCompletion K) σ e)⁻¹) {e | IsUnit e} :=
    fun e he => inverse_eq K L (v.adicCompletion K) σ h2 hgen he
  refine ContinuousOn.congr ?_ heq
  refine (continuous_sigmaTensor K L v σ).continuousOn.mul ?_
  refine (continuous_algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)).comp_continuousOn ?_
  exact (continuous_nrm K L v σ).continuousOn.inv₀ fun e he =>
    (isUnit_iff_nrm_ne_zero K L (v.adicCompletion K) σ h2 hgen e).mp he

theorem isOpen_isUnit_matrix (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    IsOpen {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | IsUnit Y} := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have : {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | IsUnit Y} =
      Matrix.det ⁻¹' {e : L ⊗[K] v.adicCompletion K | IsUnit e} := by
    ext Y
    simp [Matrix.isUnit_iff_isUnit_det]
  rw [this]
  exact (isOpen_isUnit K L v σ h2 hgen).preimage (continuous_id.matrix_det)

theorem isEmbedding_units_val (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    IsEmbedding (Units.val : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  refine Units.isEmbedding_val_mk'
    (f := fun Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      Ring.inverse Y.det • Y.adjugate) ?_ (fun u => ?_)
  · have h1 : ContinuousOn (fun Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        Ring.inverse Y.det) {Y | IsUnit Y} :=
      (continuousOn_inverse K L v σ h2 hgen).comp continuous_id.matrix_det.continuousOn
        fun Y hY => (Matrix.isUnit_iff_isUnit_det Y).mp hY
    exact h1.smul continuous_id.matrix_adjugate.continuousOn
  · rw [Matrix.coe_units_inv, Matrix.inv_def]

def crd : (L ⊗[K] v.adicCompletion K) ≃ₗ[v.adicCompletion K]
    (Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) → v.adicCompletion K) :=
  (Module.finBasis (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)).equivFun

theorem continuous_crd [FiniteDimensional K L] : Continuous (crd K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact IsModuleTopology.continuous_of_linearMap (crd K L v).toLinearMap

theorem continuous_crd_symm [FiniteDimensional K L] : Continuous (crd K L v).symm := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact IsModuleTopology.continuous_of_linearMap (crd K L v).symm.toLinearMap

def Xi (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Fin 2 → Fin 2 → Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) →
      v.adicCompletion K :=
  fun i j => crd K L v (Y i j)

def XiInv (Z : Fin 2 → Fin 2 →
    Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) → v.adicCompletion K) :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Matrix.of fun i j => (crd K L v).symm (Z i j)

theorem XiInv_Xi (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) : XiInv K L v (Xi K L v Y) = Y := by
  ext i j
  simp [XiInv, Xi]

theorem Xi_XiInv (Z : Fin 2 → Fin 2 →
    Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) → v.adicCompletion K) :
    Xi K L v (XiInv K L v Z) = Z := by
  funext i j
  simp [XiInv, Xi]

theorem continuous_Xi [FiniteDimensional K L] : Continuous (Xi K L v) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_crd K L v).comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_XiInv [FiniteDimensional K L] : Continuous (XiInv K L v) :=
  continuous_matrix fun i j =>
    (continuous_crd_symm K L v).comp ((continuous_apply j).comp (continuous_apply i))

def gauge (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) : ℝ := ‖Xi K L v Y‖

theorem gauge_smul (a : v.adicCompletion K) (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    gauge K L v ((algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a) • Y) = ‖a‖ * gauge K L v Y := by
  unfold gauge
  have : Xi K L v ((algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a) • Y) = a • Xi K L v Y := by
    funext i j
    simp only [Xi, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
    rw [← Algebra.smul_def, map_smul]
  rw [this, norm_smul]

theorem gauge_eq_zero_iff (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    gauge K L v Y = 0 ↔ Y = 0 := by
  unfold gauge
  rw [norm_eq_zero]
  constructor
  · intro h
    rw [← XiInv_Xi K L v Y, h]
    ext i j
    simp [XiInv]
  · rintro rfl
    funext i j
    simp [Xi]

theorem gauge_nonneg (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) : 0 ≤ gauge K L v Y :=
  norm_nonneg _

theorem continuous_gauge [FiniteDimensional K L] : Continuous (gauge K L v) :=
  continuous_norm.comp (continuous_Xi K L v)

theorem isCompact_gauge_le [FiniteDimensional K L] (R : ℝ) :
    IsCompact {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | gauge K L v Y ≤ R} := by
  have : {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | gauge K L v Y ≤ R} =
      XiInv K L v '' Metric.closedBall 0 R := by
    ext Y
    constructor
    · intro h
      exact ⟨Xi K L v Y, by simpa [gauge] using h, XiInv_Xi K L v Y⟩
    · rintro ⟨Z, hZ, rfl⟩
      simpa [gauge, Xi_XiInv] using hZ
  rw [this]
  exact (isCompact_closedBall _ R).image (continuous_XiInv K L v)

theorem exists_norm_lt_one : ∃ π : v.adicCompletion K, 0 < ‖π‖ ∧ ‖π‖ < 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨FinitePlace.embedding v (algebraMap (𝓞 K) K x), ?_, ?_⟩
  · rw [norm_pos_iff]
    intro h
    apply hx0
    have h1 : algebraMap (𝓞 K) K x = 0 := (map_eq_zero _).mp h
    exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h1
  · exact (FinitePlace.norm_lt_one_iff_mem K v x).mpr hx

theorem exists_smul_mem_shell [FiniteDimensional K L] {π : v.adicCompletion K} (hπ0 : 0 < ‖π‖)
    (hπ1 : ‖π‖ < 1) {Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)} (hY : Y ≠ 0) :
    ∃ m : ℤ, ‖π‖ < gauge K L v ((algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (π ^ m)) • Y) ∧
      gauge K L v ((algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (π ^ m)) • Y) ≤ 1 := by
  have hg : 0 < gauge K L v Y :=
    lt_of_le_of_ne (gauge_nonneg K L v Y) (fun h => hY ((gauge_eq_zero_iff K L v Y).mp h.symm))
  have hπne : ‖π‖ ≠ 0 := hπ0.ne'
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hg ((one_lt_inv₀ hπ0).mpr hπ1)
  refine ⟨n + 1, ?_, ?_⟩ <;> rw [gauge_smul, norm_zpow]
  · calc ‖π‖ = ‖π‖ ^ (n + 1) * ‖π‖⁻¹ ^ n := by
          rw [inv_zpow', ← zpow_add₀ hπne]
          simp
      _ < ‖π‖ ^ (n + 1) * gauge K L v Y := by gcongr
  · calc ‖π‖ ^ (n + 1) * gauge K L v Y ≤ ‖π‖ ^ (n + 1) * ‖π‖⁻¹ ^ (n + 1) := by
          gcongr
      _ = 1 := by rw [inv_zpow', ← zpow_add₀ hπne]; simp

theorem algebraMap_eq_tmul (a : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a = (1 : L) ⊗ₜ[K] a := rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in
theorem main
    (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hω : IsCompact ω) :
    ∃ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
        ∀ h ∈ V, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          x⁻¹ * h * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ ω →
            ∃ a : (v.adicCompletion K)ˣ, ∃ g ∈ Ω,
              x = AutomorphicForm.toTensorGL K L (v.adicCompletion K)
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) a) * g := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] v.adicCompletion K))

  obtain ⟨π, hπ0, hπ1⟩ := exists_norm_lt_one K v
  set Y₀ : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    {Y | ‖π‖ ≤ gauge K L v Y ∧ gauge K L v Y ≤ 1} with hY₀
  have hY₀c : IsCompact Y₀ := by
    refine (isCompact_gauge_le K L v 1).of_isClosed_subset ?_ (fun Y hY => hY.2)
    exact (isClosed_le continuous_const (continuous_gauge K L v)).inter
      (isClosed_le (continuous_gauge K L v) continuous_const)
  have hY₀0 : ∀ Y ∈ Y₀, Y ≠ 0 := by
    rintro Y ⟨hY1, -⟩ rfl
    rw [(gauge_eq_zero_iff K L v 0).mpr rfl] at hY1
    exact absurd hY1 (not_le.mpr hπ0)

  obtain ⟨C₁, hC₁c, hC₁⟩ := exists_compact_mem_nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K))

  set Rel : GL (Fin 2) (L ⊗[K] v.adicCompletion K) × Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) ×
      GL (Fin 2) (L ⊗[K] v.adicCompletion K) → Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) :=
    fun p => (p.1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        (p.2.1).map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) -
      p.2.1 * (p.2.2 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) with hRel
  have hRelc : Continuous Rel := by
    refine Continuous.sub ?_ ?_
    · refine ((Units.continuous_val.comp continuous_fst).mul continuous_const).mul ?_
      exact (continuous_fst.comp continuous_snd).matrix_map (continuous_sigmaTensor K L v σ)
    · exact (continuous_fst.comp continuous_snd).mul
        (Units.continuous_val.comp (continuous_snd.comp continuous_snd))

  have hZc : ∀ C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact C →
      IsCompact {p : GL (Fin 2) (L ⊗[K] v.adicCompletion K) ×
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) × GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          p.1 ∈ C ∧ p.2.1 ∈ Y₀ ∧ p.2.2 ∈ ω ∧ Rel p = 0} := by
    intro C hC
    have h1 : IsCompact (C ×ˢ (Y₀ ×ˢ ω)) := hC.prod (hY₀c.prod hω)
    have h2' : IsClosed (Rel ⁻¹' {0}) := isClosed_singleton.preimage hRelc
    convert h1.inter_right h2' using 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]

  set Zbad := {p : GL (Fin 2) (L ⊗[K] v.adicCompletion K) ×
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) × GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        p.1 ∈ C₁ ∧ p.2.1 ∈ Y₀ ∧ p.2.2 ∈ ω ∧ Rel p = 0} ∩ {p | ¬ IsUnit p.2.1} with hZbad
  have hZbadc : IsCompact Zbad := by
    refine (hZc C₁ hC₁c).inter_right ?_
    have : {p : GL (Fin 2) (L ⊗[K] v.adicCompletion K) ×
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) × GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          ¬ IsUnit p.2.1} = (fun p => p.2.1) ⁻¹' {Y | IsUnit Y}ᶜ := by
      ext p; simp
    rw [this]
    exact (isOpen_isUnit_matrix K L v σ h2 hgen).isClosed_compl.preimage
      (continuous_fst.comp continuous_snd)
  set P : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := Prod.fst '' Zbad with hP
  have hPc : IsClosed P := (hZbadc.image continuous_fst).isClosed
  have h1P : (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∉ P := by
    rintro ⟨p, ⟨⟨-, hpY, -, hpR⟩, hpu⟩, hp1⟩
    apply hpu
    have hrel : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        (p.2.1).map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) =
          p.2.1 * (p.2.2 : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
      have := hpR
      rw [hRel] at this
      simp only [hp1, Units.val_one, one_mul, sub_eq_zero] at this
      exact this
    exact AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen (v.adicCompletion K) c δ hδ hδq p.2.1 (hY₀0 _ hpY) _ hrel

  obtain ⟨C₂, hC₂c, h1C₂, hC₂sub⟩ := exists_compact_subset (isOpen_interior.inter hPc.isOpen_compl)
    (⟨mem_interior_iff_mem_nhds.mpr hC₁, h1P⟩ : (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ interior C₁ ∩ Pᶜ)
  set Z₂ := {p : GL (Fin 2) (L ⊗[K] v.adicCompletion K) ×
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) × GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        p.1 ∈ C₂ ∧ p.2.1 ∈ Y₀ ∧ p.2.2 ∈ ω ∧ Rel p = 0} with hZ₂
  have hZ₂c : IsCompact Z₂ := hZc C₂ hC₂c
  have hunit : ∀ p ∈ Z₂, IsUnit p.2.1 := by
    intro p hp
    by_contra hu
    have hpC₁ : p.1 ∈ C₁ := interior_subset (hC₂sub hp.1).1
    have hpP : p.1 ∈ P := ⟨p, ⟨⟨hpC₁, hp.2.1, hp.2.2.1, hp.2.2.2⟩, hu⟩, rfl⟩
    exact (hC₂sub hp.1).2 hpP
  set Y₁ : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := (fun p => p.2.1) '' Z₂ with hY₁
  have hY₁c : IsCompact Y₁ := hZ₂c.image (continuous_fst.comp continuous_snd)
  set Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    {g | (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Y₁} with hΩ
  have hΩimg : Units.val '' Ω = Y₁ := by
    ext Y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hY
      obtain ⟨p, hp, hpY⟩ := hY
      obtain ⟨u, hu⟩ := hunit p hp
      have hpY' : p.2.1 = Y := hpY
      refine ⟨u, ?_, ?_⟩
      · show (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Y₁
        rw [hu]
        exact ⟨p, hp, rfl⟩
      · rw [hu, hpY']
  have hΩc : IsCompact Ω := by
    rw [(isEmbedding_units_val K L v σ h2 hgen).isInducing.isCompact_iff, hΩimg]
    exact hY₁c
  refine ⟨interior C₂, isOpen_interior.mem_nhds h1C₂, Ω, hΩc, ?_⟩
  intro h hh x hx
  set k₀ := x⁻¹ * h * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x with hk₀

  have hxM : (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ≠ 0 := x.ne_zero
  obtain ⟨m, hm1, hm2⟩ := exists_smul_mem_shell K L v hπ0 hπ1 hxM
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  have ha0 : π ^ m ≠ 0 := zpow_ne_zero m hπne
  set aU : (v.adicCompletion K)ˣ := Units.mk0 (π ^ m) ha0 with haU

  set g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) := Z K L (v.adicCompletion K) aU * x with hgdef
  have hcoe : (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (π ^ m)) •
        (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
    ext i j
    rw [hgdef, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      algebraMap_eq_tmul]
    simp only [Z, toTensorGL_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      haU, Units.val_mk0]
    fin_cases i <;> simp
  have hYY₀ : (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Y₀ := by
    rw [hcoe]
    exact ⟨hm1.le, hm2⟩
  have hrel : Rel (h, (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)), k₀) = 0 := by
    have hG : h * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x = x * k₀ := by
      rw [hk₀]; group
    have hG' : h * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ g = g * k₀ := by
      rw [hgdef, map_mul, sigmaGL_Z, mul_assoc _ x k₀, ← hG]
      have e1 : δ * Z K L (v.adicCompletion K) aU = Z K L (v.adicCompletion K) aU * δ :=
        (Z_mul_comm K L (v.adicCompletion K) aU δ).symm
      have e2 : h * Z K L (v.adicCompletion K) aU = Z K L (v.adicCompletion K) aU * h :=
        (Z_mul_comm K L (v.adicCompletion K) aU h).symm
      calc h * δ * (Z K L (v.adicCompletion K) aU * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)
          = h * (δ * Z K L (v.adicCompletion K) aU) * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x := by
            group
        _ = (h * Z K L (v.adicCompletion K) aU) * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x := by
            rw [e1]; group
        _ = Z K L (v.adicCompletion K) aU * (h * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) := by
            rw [e2]; group
    have hM' := congrArg (fun q : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (q : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) hG'
    simp only [Units.val_mul, coe_sigmaGL] at hM'
    rw [hRel]
    simp only [sub_eq_zero]
    exact hM'
  have hp : (h, (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)), k₀) ∈ Z₂ :=
    ⟨interior_subset hh, hYY₀, hx, hrel⟩
  refine ⟨aU⁻¹, g, ⟨_, hp, rfl⟩, ?_⟩
  show x = Z K L (v.adicCompletion K) aU⁻¹ * g
  rw [hgdef, ← mul_assoc, Z_inv_mul, one_mul]

theorem Z_mem_twistedCentralizer (a : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Z K L (v.adicCompletion K) a ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, sigmaGL_Z, Z_mul_comm, mul_inv_cancel_right]

theorem main_twistedCentralizer
    (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hω : IsCompact ω) :
    ∃ U₁ ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
      ∀ h ∈ U₁, h ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ →
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          x⁻¹ * (h * δ) * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ ω →
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ d ∈ Ω, x = t * d := by
  obtain ⟨V, hV, Ω, hΩ, hmain⟩ := main K L v σ h2 hgen c δ hδ hδq ω hω
  refine ⟨V, hV, Ω, hΩ, fun h hh _ x hx => ?_⟩
  have hx' : x⁻¹ * h * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ ω := by
    simpa only [mul_assoc] using hx
  obtain ⟨a, g, hg, hxg⟩ := hmain h hh x hx'
  exact ⟨Z K L (v.adicCompletion K) a, Z_mem_twistedCentralizer K L v σ a δ, g, hg, hxg⟩

end Place

end P2mTwistedCompactT

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hω : IsCompact ω) :
    ∃ U₁ ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
      ∀ h ∈ U₁, h ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ →
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          x⁻¹ * (h * δ) * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ ω →
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ d ∈ Ω, x = t * d :=
  P2mTwistedCompactT.main_twistedCentralizer K L v σ h2 hgen c δ hδ hδq ω hω

end S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
