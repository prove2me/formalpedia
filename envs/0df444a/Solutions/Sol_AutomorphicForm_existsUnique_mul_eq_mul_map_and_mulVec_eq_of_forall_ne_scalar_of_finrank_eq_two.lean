-- Prove2me | solution 1 for AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6cf18375-7ac7-575f-a2d9-b872bce14aa0

import Theorems.Thm_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf"
namespace TwistedColumnSol
p2m_open "AutomorphicForm"

section Galois

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]

theorem sigma_involutive_and_ne_one (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∃ ℓ : L, σ ℓ ≠ ℓ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · by_contra h
    push Not at h
    have hσ1 : σ = 1 := AlgEquiv.ext h
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [← hk, hσ1, one_zpow]
    have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

theorem exists_algebraMap_eq_of_sigma_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {m : L} (hm : σ m = m) :
    ∃ k : K, algebraMap K L k = m := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) m :=
    Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, hm])
  have hfix : ∀ τ : L ≃ₐ[K] L, τ m = m := fun τ => by
    have := hle (hgen τ)
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  have hmem : m ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun τ _ => hfix τ
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
  exact hmem

end Galois

section Space

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (d : Matrix (Fin 2) (Fin 2) L)

theorem map_sigma_add (x y : Matrix (Fin 2) (Fin 2) L) : (x + y).map σ = x.map σ + y.map σ := by
  ext i j
  simp [Matrix.map_apply]

theorem map_sigma_smul (a : L) (x : Matrix (Fin 2) (Fin 2) L) : (a • x).map σ = σ a • x.map σ := by
  ext i j
  simp [Matrix.map_apply, smul_eq_mul]

theorem map_sigma_smulK (k : K) (x : Matrix (Fin 2) (Fin 2) L) : (k • x).map σ = k • x.map σ := by
  ext i j
  simp [Matrix.map_apply]

theorem map_sigma_mul (x y : Matrix (Fin 2) (Fin 2) L) : (x * y).map σ = x.map σ * y.map σ :=
  Matrix.map_mul

def Dsub : Submodule K (Matrix (Fin 2) (Fin 2) L) where
  carrier := {x | x * d = d * x.map σ}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [add_mul, map_sigma_add, mul_add, hx, hy]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_mul]
    rw [show (0 : Matrix (Fin 2) (Fin 2) L).map σ = 0 from by ext i j; simp, mul_zero]
  smul_mem' := by
    intro k x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [smul_mul_assoc, map_sigma_smulK, mul_smul_comm, hx]

theorem mem_Dsub {x : Matrix (Fin 2) (Fin 2) L} : x ∈ Dsub K L σ d ↔ x * d = d * x.map σ := Iff.rfl

def colMap (v : Fin 2 → L) : Dsub K L σ d →ₗ[K] (Fin 2 → L) where
  toFun x := (x : Matrix (Fin 2) (Fin 2) L).mulVec v
  map_add' x y := by
    simp only [Submodule.coe_add, Matrix.add_mulVec]
  map_smul' k x := by
    simp only [Submodule.coe_smul, RingHom.id_apply, Matrix.smul_mulVec]

theorem colMap_apply (v : Fin 2 → L) (x : Dsub K L σ d) :
    colMap K L σ d v x = (x : Matrix (Fin 2) (Fin 2) L).mulVec v := rfl

end Space

section Descent

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (δ₀ : GL (Fin 2) L)

local notation "dd" => ((δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
local notation "di" => ((δ₀⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)

theorem dd_mul_di : dd * di = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; rfl

theorem di_mul_dd : di * dd = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; rfl

def theta (y : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 2) (Fin 2) L := dd * y.map σ * di

theorem sigma_data (hσσ : ∀ l : L, σ (σ l) = l) (z : Lˣ)
    (hz : dd * (dd).map σ = Matrix.scalar (Fin 2) (z : L)) :
    (dd).map σ = (z : L) • di ∧ σ (z : L) = z ∧ (di).map σ = ((z : L)⁻¹) • dd := by
  have hsc : Matrix.scalar (Fin 2) (z : L) = (z : L) • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have h1 : (dd).map σ = (z : L) • di := by
    calc (dd).map σ = di * (dd * (dd).map σ) := by rw [← mul_assoc, di_mul_dd, one_mul]
      _ = (z : L) • di := by rw [hz, hsc, mul_smul_comm, mul_one]
  have h2 : σ (z : L) = z := by

    have hA : (dd).map σ * dd = (z : L) • (1 : Matrix (Fin 2) (Fin 2) L) := by
      rw [h1, smul_mul_assoc, di_mul_dd]
    have hB : (dd).map σ * dd = σ (z : L) • (1 : Matrix (Fin 2) (Fin 2) L) := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) L => M.map σ) hz
      rw [map_sigma_mul, hsc, map_sigma_smul] at this
      rw [show ((dd).map σ).map σ = dd from by
        rw [Matrix.map_map]; ext i j; simp [Matrix.map_apply, hσσ]] at this
      rw [this, show (1 : Matrix (Fin 2) (Fin 2) L).map σ = 1 from by
        ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite σ]]
    have h := hA.symm.trans hB
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00.symm
  refine ⟨h1, h2, ?_⟩

  have h3 : (di).map σ * ((z : L) • di) = 1 := by
    rw [← h1, ← map_sigma_mul, di_mul_dd]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite σ]
  have hz0 : (z : L) ≠ 0 := z.ne_zero
  calc (di).map σ = (di).map σ * ((z : L) • di) * (((z : L)⁻¹) • dd) := by
          rw [mul_assoc, smul_mul_smul_comm, mul_inv_cancel₀ hz0, one_smul, di_mul_dd, mul_one]
    _ = ((z : L)⁻¹) • dd := by rw [h3, one_mul]

theorem smul_add_smul_theta_mem (hσσ : ∀ l : L, σ (σ l) = l) (z : Lˣ)
    (hz : dd * (dd).map σ = Matrix.scalar (Fin 2) (z : L))
    (ℓ' : L) (y : Matrix (Fin 2) (Fin 2) L) :
    ℓ' • y + σ ℓ' • theta K L σ δ₀ y ∈ Dsub K L σ dd := by
  obtain ⟨h1, h2, h3⟩ := sigma_data K L σ δ₀ hσσ z hz
  have hz0 : (z : L) ≠ 0 := z.ne_zero
  rw [mem_Dsub]

  have hyσσ : (y.map σ).map σ = y := by
    rw [Matrix.map_map]; ext i j; simp [Matrix.map_apply, hσσ]
  have key : dd * (theta K L σ δ₀ y).map σ = y * dd := by
    unfold theta
    rw [map_sigma_mul, map_sigma_mul, h1, hyσσ, h3]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
    rw [dd_mul_di, one_mul, inv_mul_cancel₀ hz0, one_smul]
  have key2 : theta K L σ δ₀ y * dd = dd * y.map σ := by
    unfold theta
    rw [mul_assoc, di_mul_dd, mul_one]
  rw [add_mul, map_sigma_add, mul_add, map_sigma_smul, map_sigma_smul, hσσ, smul_mul_assoc,
    smul_mul_assoc, mul_smul_comm, mul_smul_comm, key, key2, add_comm]

theorem finrank_matrix_le_two_mul (hσσ : ∀ l : L, σ (σ l) = l) (hℓ : ∃ ℓ : L, σ ℓ ≠ ℓ) (z : Lˣ)
    (hz : dd * (dd).map σ = Matrix.scalar (Fin 2) (z : L)) [FiniteDimensional K L] :
    Module.finrank K (Matrix (Fin 2) (Fin 2) L) ≤ 2 * Module.finrank K (Dsub K L σ dd) := by
  obtain ⟨ℓ, hℓ⟩ := hℓ
  set c₁ : L := (σ ℓ - ℓ)⁻¹ * σ ℓ with hc₁
  set c₂ : L := -(σ ℓ - ℓ)⁻¹ with hc₂

  let Ψ : (Dsub K L σ dd × Dsub K L σ dd) →ₗ[K] Matrix (Fin 2) (Fin 2) L :=
    { toFun := fun p => c₁ • (p.1 : Matrix (Fin 2) (Fin 2) L) + c₂ • (p.2 : Matrix (Fin 2) (Fin 2) L)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro k p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm c₁ k, smul_comm c₂ k] }
  have hsurj : Function.Surjective Ψ := by
    intro y
    have ha := smul_add_smul_theta_mem K L σ δ₀ hσσ z hz 1 y
    have hb := smul_add_smul_theta_mem K L σ δ₀ hσσ z hz ℓ y
    rw [one_smul, map_one, one_smul] at ha
    refine ⟨(⟨_, ha⟩, ⟨_, hb⟩), ?_⟩
    show c₁ • (y + theta K L σ δ₀ y) + c₂ • (ℓ • y + σ ℓ • theta K L σ δ₀ y) = y
    have hne : σ ℓ - ℓ ≠ 0 := sub_ne_zero.mpr hℓ
    have e1 : c₁ + c₂ * σ ℓ = 0 := by rw [hc₁, hc₂]; ring
    have e2 : c₁ + c₂ * ℓ = 1 := by
      rw [hc₁, hc₂, neg_mul, ← sub_eq_add_neg, ← mul_sub, inv_mul_cancel₀ hne]
    calc c₁ • (y + theta K L σ δ₀ y) + c₂ • (ℓ • y + σ ℓ • theta K L σ δ₀ y)
        = (c₁ + c₂ * ℓ) • y + (c₁ + c₂ * σ ℓ) • theta K L σ δ₀ y := by
          rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, add_smul]; abel
      _ = y := by rw [e1, e2, one_smul, zero_smul, add_zero]
  haveI : Module.Finite K (Dsub K L σ dd) :=
    Module.Finite.of_injective (Dsub K L σ dd).subtype Subtype.val_injective
  have h1 : Module.finrank K (Matrix (Fin 2) (Fin 2) L)
      ≤ Module.finrank K (Dsub K L σ dd × Dsub K L σ dd) := by
    have hr : LinearMap.range Ψ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    calc Module.finrank K (Matrix (Fin 2) (Fin 2) L)
        = Module.finrank K (⊤ : Submodule K (Matrix (Fin 2) (Fin 2) L)) := (finrank_top K _).symm
      _ = Module.finrank K (LinearMap.range Ψ) := by rw [hr]
      _ ≤ Module.finrank K (Dsub K L σ dd × Dsub K L σ dd) := LinearMap.finrank_range_le Ψ
  rw [Module.finrank_prod] at h1
  omega

end Descent

section Division

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

def eqv : L ≃ₐ[K] L ⊗[K] K := (Algebra.TensorProduct.rid K K L).symm

theorem eqv_apply (l : L) : eqv K L l = l ⊗ₜ[K] (1 : K) := rfl

theorem sigmaTensor_eqv (l : L) :
    AutomorphicForm.sigmaTensor K L K σ (eqv K L l) = eqv K L (σ l) := by
  rw [eqv_apply, eqv_apply]
  simp [AutomorphicForm.sigmaTensor]

theorem eqv_symm_sigmaTensor (e : L ⊗[K] K) :
    (eqv K L).symm (AutomorphicForm.sigmaTensor K L K σ e) = σ ((eqv K L).symm e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul l k =>
      have : l ⊗ₜ[K] k = eqv K L (k • l) := by
        rw [eqv_apply, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
      rw [this, sigmaTensor_eqv, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_map_sigmaTensor (x : Matrix (Fin 2) (Fin 2) L) :
    (x.map (eqv K L)).map (AutomorphicForm.sigmaTensor K L K σ) = (x.map σ).map (eqv K L) := by
  ext i j
  simp only [Matrix.map_apply]
  exact sigmaTensor_eqv K L σ _

theorem map_symm_map_sigmaTensor (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) :
    (y.map (AutomorphicForm.sigmaTensor K L K σ)).map (eqv K L).symm = (y.map (eqv K L).symm).map σ := by
  ext i j
  simp only [Matrix.map_apply]
  exact eqv_symm_sigmaTensor K L σ _

theorem map_eqv_map_symm (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) :
    (y.map (eqv K L).symm).map (eqv K L) = y := by
  rw [Matrix.map_map]; ext i j; simp [Matrix.map_apply]

theorem map_symm_map_eqv (x : Matrix (Fin 2) (Fin 2) L) :
    (x.map (eqv K L)).map (eqv K L).symm = x := by
  rw [Matrix.map_map]; ext i j; simp [Matrix.map_apply]

def glE : GL (Fin 2) L →* GL (Fin 2) (L ⊗[K] K) :=
  Matrix.GeneralLinearGroup.map ((eqv K L : L ≃ₐ[K] L ⊗[K] K) : L →+* L ⊗[K] K)

def glL : GL (Fin 2) (L ⊗[K] K) →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (((eqv K L).symm : L ⊗[K] K ≃ₐ[K] L) : L ⊗[K] K →+* L)

theorem coe_glE (x : GL (Fin 2) L) :
    ((glE K L x : GL (Fin 2) (L ⊗[K] K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) =
      (x : Matrix (Fin 2) (Fin 2) L).map (eqv K L) := rfl

theorem coe_glL (y : GL (Fin 2) (L ⊗[K] K)) :
    ((glL K L y : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)).map (eqv K L).symm := rfl

theorem glL_glE (x : GL (Fin 2) L) : glL K L (glE K L x) = x := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((glL K L (glE K L x) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j = _
  rw [coe_glL, coe_glE, map_symm_map_eqv]

theorem coe_map_sigma (x : GL (Fin 2) L) :
    ((Matrix.GeneralLinearGroup.map (σ : L →+* L) x : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      (x : Matrix (Fin 2) (Fin 2) L).map σ := rfl

theorem coe_sigmaGL (y : GL (Fin 2) (L ⊗[K] K)) :
    ((AutomorphicForm.sigmaGL K L K σ y : GL (Fin 2) (L ⊗[K] K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) =
      (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)).map (AutomorphicForm.sigmaTensor K L K σ) := rfl

theorem glL_sigmaGL (y : GL (Fin 2) (L ⊗[K] K)) :
    glL K L (AutomorphicForm.sigmaGL K L K σ y) = Matrix.GeneralLinearGroup.map (σ : L →+* L) (glL K L y) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((glL K L (AutomorphicForm.sigmaGL K L K σ y) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
    ((Matrix.GeneralLinearGroup.map (σ : L →+* L) (glL K L y) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
  rw [coe_glL, coe_sigmaGL, coe_map_sigma, coe_glL, map_symm_map_sigmaTensor]

theorem glE_sigma (x : GL (Fin 2) L) :
    glE K L (Matrix.GeneralLinearGroup.map (σ : L →+* L) x) = AutomorphicForm.sigmaGL K L K σ (glE K L x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((glE K L (Matrix.GeneralLinearGroup.map (σ : L →+* L) x) : GL (Fin 2) (L ⊗[K] K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) i j =
    ((AutomorphicForm.sigmaGL K L K σ (glE K L x) : GL (Fin 2) (L ⊗[K] K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) i j
  rw [coe_glE, coe_sigmaGL, coe_map_sigma, coe_glE, map_map_sigmaTensor]

theorem coe_scalar {R : Type} [CommRing R] (u : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (u : R) := rfl

theorem glL_scalar (u : (L ⊗[K] K)ˣ) :
    glL K L (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((eqv K L).symm : L ⊗[K] K →* L) u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((glL K L (Matrix.GeneralLinearGroup.scalar (Fin 2) u) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
    = ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((eqv K L).symm : L ⊗[K] K →* L) u) :
        GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
  rw [coe_glL, coe_scalar, coe_scalar, Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem glE_scalar (u : Lˣ) :
    glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((eqv K L) : L →* L ⊗[K] K) u) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) u) : GL (Fin 2) (L ⊗[K] K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) i j
    = ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map ((eqv K L) : L →* L ⊗[K] K) u) :
        GL (Fin 2) (L ⊗[K] K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) i j
  rw [coe_glE, coe_scalar, coe_scalar, Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem normString_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] K)) :
    AutomorphicForm.normString K L K σ δ = δ * AutomorphicForm.sigmaGL K L K σ δ := by
  unfold AutomorphicForm.normString
  rw [h2]
  simp [List.range_succ, Function.iterate_zero]

theorem isUnit_of_mem (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    {x : Matrix (Fin 2) (Fin 2) L}
    (hx : x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ) (hx0 : x ≠ 0) :
    IsUnit x := by
  obtain ⟨hσσ, -⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  obtain ⟨z, hz⟩ := hN

  have hzmat : (δ₀ : Matrix (Fin 2) (Fin 2) L) * ((δ₀ : Matrix (Fin 2) (Fin 2) L)).map σ =
      Matrix.scalar (Fin 2) (z : L) := by
    have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) hz
    simp only [Matrix.GeneralLinearGroup.coe_mul] at this
    exact this
  obtain ⟨-, hσz, -⟩ := sigma_data K L σ δ₀ hσσ z hzmat
  obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_sigma_eq K L h2 σ hgen hσz
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact z.ne_zero hk.symm
  set c : Kˣ := Units.mk0 k hk0 with hc
  set δ : GL (Fin 2) (L ⊗[K] K) := glE K L δ₀ with hδ

  have hnorm : AutomorphicForm.IsNormOf K L K σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ := by
    refine ⟨1, ?_⟩
    unfold AutomorphicForm.IsNormConjugator
    rw [inv_one, one_mul, mul_one, normString_two K L σ h2, hδ, ← glE_sigma, ← map_mul, hz, glE_scalar]
    unfold AutomorphicForm.toTensorGL
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    change (Algebra.TensorProduct.includeRight : K →ₐ[K] L ⊗[K] K)
        (((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) = _
    rw [coe_scalar, coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.diagonal_apply]
    split_ifs with hij
    · rw [Units.coe_map, MonoidHom.coe_coe, hc, Units.val_mk0]
      change (1 : L) ⊗ₜ[K] k = eqv K L (z : L)
      rw [eqv_apply, ← hk, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    · rw [map_zero]

  have hnsq : ∀ z' : (L ⊗[K] K)ˣ, ¬ AutomorphicForm.IsSigmaConjugate K L K σ δ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z') := by
    rintro z' ⟨y, hy⟩
    have := congrArg (glL K L) hy
    rw [glL_scalar, map_mul, map_mul, map_inv, glL_sigmaGL, hδ, glL_glE] at this
    exact hns (glL K L y) _ this.symm

  set y : Matrix (Fin 2) (Fin 2) (L ⊗[K] K) := x.map (eqv K L) with hy
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    rw [← map_symm_map_eqv K L x, ← hy, h]
    ext i j; simp
  have hyk : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) * y.map (AutomorphicForm.sigmaTensor K L K σ) =
      y * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] K)) := by
    rw [hδ, coe_glE, hy, map_map_sigmaTensor, ← Matrix.map_mul, ← Matrix.map_mul, hx]
  have hunit : IsUnit y :=
    AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen K c δ hnorm hnsq y hy0 _ hyk
  have := hunit.map (RingHom.mapMatrix (((eqv K L).symm : L ⊗[K] K ≃ₐ[K] L) : L ⊗[K] K →+* L))
  rw [RingHom.mapMatrix_apply] at this
  change IsUnit (y.map (eqv K L).symm) at this
  rwa [hy, map_symm_map_eqv] at this

end Division

section Main

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]

theorem main (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (δ₀ : GL (Fin 2) L)
    (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0) :
    Function.Bijective (colMap K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L) v) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  obtain ⟨hσσ, hℓ⟩ := sigma_involutive_and_ne_one K L h2 σ hgen
  obtain ⟨z, hz⟩ := hN
  have hzmat : (δ₀ : Matrix (Fin 2) (Fin 2) L) * ((δ₀ : Matrix (Fin 2) (Fin 2) L)).map σ =
      Matrix.scalar (Fin 2) (z : L) := by
    have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) hz
    simp only [Matrix.GeneralLinearGroup.coe_mul] at this
    exact this

  have hinj : Function.Injective (colMap K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L) v) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hx0' : (x : Matrix (Fin 2) (Fin 2) L) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hu := isUnit_of_mem K L σ h2 hgen δ₀ ⟨z, hz⟩ hns x.2 hx0'
    rw [colMap_apply] at hx
    obtain ⟨u, hu⟩ := hu
    apply hv
    calc v = ((u⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) : Matrix (Fin 2) (Fin 2) L).mulVec
          ((x : Matrix (Fin 2) (Fin 2) L).mulVec v) := by
          rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
      _ = 0 := by rw [hx, Matrix.mulVec_zero]

  have hM : Module.finrank K (Matrix (Fin 2) (Fin 2) L) = 4 * Module.finrank K L := by
    rw [Module.finrank_matrix]; simp
  have hV : Module.finrank K (Fin 2 → L) = 2 * Module.finrank K L := by
    rw [Module.finrank_pi_fintype]; simp [Finset.sum_const, two_mul]
  have hle := finrank_matrix_le_two_mul K L σ δ₀ hσσ hℓ z hzmat
  have hge : Module.finrank K (Fin 2 → L) ≤ Module.finrank K (Dsub K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L)) := by
    rw [hV]; rw [hM] at hle; omega
  have hle' : Module.finrank K (Dsub K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L)) ≤ Module.finrank K (Fin 2 → L) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have heq : Module.finrank K (Dsub K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L)) = Module.finrank K (Fin 2 → L) :=
    le_antisymm hle' hge
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj⟩

end Main

end AutomorphicForm.TwistedColumnSol

end

open AutomorphicForm.TwistedColumnSol in
theorem solution
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0) (w : Fin 2 → L) :
    ∃! x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ∧
        Matrix.mulVec x v = w := by
  have hb := main K L h2 σ hgen δ₀ hN hns v hv
  obtain ⟨x, hx⟩ := hb.2 w
  refine ⟨(x : Matrix (Fin 2) (Fin 2) L), ⟨x.2, hx⟩, ?_⟩
  rintro y ⟨hy, hyv⟩
  have : (⟨y, hy⟩ : Dsub K L σ (δ₀ : Matrix (Fin 2) (Fin 2) L)) = x :=
    hb.1 (by rw [colMap_apply, colMap_apply] at *; exact hyv.trans hx.symm)
  exact congrArg Subtype.val this

end S_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two (solution)
