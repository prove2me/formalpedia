-- Prove2me | Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
-- name    : GroundTheory_Brauer_CrossedProductTensor
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:10.000217+00:00
-- url     : https://prove2.me/theorems/86e8d4fd-17e2-5560-a70b-db1fded4d679
-- title:
--   Crossed Product Tensor
-- statement:
--   Definitions and structural lemmas for Crossed Product Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mk_mem_relBrauer_iff
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_mk_mul_mk
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_one
import Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_one
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_finrank_baseChange_eq
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_of_algEquiv_matrix
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.BrauerGroup.baseChange_mk
attribute [local simp] GroundTheory.Brauer.CrossedProduct.basis_apply
attribute [local simp] GroundTheory.Brauer.CrossedProduct.toMatrix_incl
attribute [local simp] GroundTheory.Brauer.CrossedProduct.toMatrix_u
attribute [local simp] GroundTheory.Brauer.H2mul.mulEquivH2_mk
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauer_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open groupCohomology TensorProduct
universe u
namespace CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [DecidableEq (L ≃ₐ[K] L)]
section Right
variable {f g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
def rightCoeff (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (ρ τ : L ≃ₐ[K] L) : L :=
  (ρ * τ⁻¹)⁻¹ ((f (ρ * τ⁻¹, τ) : L)⁻¹)
omit [FiniteDimensional K L] [DecidableEq (L ≃ₐ[K] L)] in

theorem rightCoeff_mul (hf : IsMulCocycle₂ f) (k σ τ : L ≃ₐ[K] L) :
    rightCoeff f (k * τ⁻¹) σ * σ (rightCoeff f k τ) * ((f (σ, τ) : L) * (g (σ, τ) : L)) =
      (g (σ, τ) : L) * rightCoeff f k (σ * τ) := by
  obtain ⟨π, rfl⟩ : ∃ π, k = π * σ * τ := ⟨k * τ⁻¹ * σ⁻¹, by group⟩
  have e1 : π * σ * τ * τ⁻¹ * σ⁻¹ = π := by group
  have e2 : π * σ * τ * τ⁻¹ = π * σ := by group
  have e3 : π * σ * τ * (σ * τ)⁻¹ = π := by group
  have e4 : σ * (π * σ)⁻¹ = π⁻¹ := by group
  rw [rightCoeff, rightCoeff, rightCoeff, e1, e2, e3, ← AlgEquiv.mul_apply σ, e4]
  have h := cocycle_apply hf π⁻¹ π σ τ
  rw [← AlgEquiv.mul_apply π⁻¹ π, inv_mul_cancel, AlgEquiv.one_apply] at h
  simp only [map_inv₀]
  have n1 : π⁻¹ (f (π, σ) : L) ≠ 0 := by simp
  have n2 : π⁻¹ (f (π * σ, τ) : L) ≠ 0 := by simp
  have n3 : π⁻¹ (f (π, σ * τ) : L) ≠ 0 := by simp
  field_simp
  linear_combination h
omit [FiniteDimensional K L] [DecidableEq (L ≃ₐ[K] L)] in

theorem rightCoeff_one (hf : IsMulCocycle₂ f) (k : L ≃ₐ[K] L) :
    rightCoeff f k 1 * ((f (1, 1) : L) * (g (1, 1) : L)) = (g (1, 1) : L) := by
  rw [rightCoeff, inv_one, mul_one, map_one_snd_of_isMulCocycle₂ hf, val_smul_units, map_inv₀,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have n : (f (1, 1) : L) ≠ 0 := by simp
  field_simp
omit [FiniteDimensional K L] [DecidableEq (L ≃ₐ[K] L)] in

theorem rightCoeff_comm (hf : IsMulCocycle₂ f) (k σ τ : L ≃ₐ[K] L) :
    (σ * (k * τ⁻¹))⁻¹ (f (σ, k * τ⁻¹) : L) * rightCoeff f k τ =
      rightCoeff f (σ * k) τ * τ ((σ * k)⁻¹ (f (σ, k) : L)) := by
  obtain ⟨μ, rfl⟩ : ∃ μ, k = μ * τ := ⟨k * τ⁻¹, by group⟩
  have e1 : σ * (μ * τ) * τ⁻¹ = σ * μ := by group
  have e2 : μ * τ * τ⁻¹ = μ := by group
  have e3 : τ * (σ * (μ * τ))⁻¹ = (σ * μ)⁻¹ := by group
  have e4 : μ⁻¹ = (σ * μ)⁻¹ * σ := by group
  rw [rightCoeff, rightCoeff, e1, e2, ← AlgEquiv.mul_apply τ, e3, e4, AlgEquiv.mul_apply]
  have h := cocycle_apply hf (σ * μ)⁻¹ σ μ τ
  simp only [map_inv₀]
  have n1 : (σ * μ)⁻¹ (σ (f (μ, τ) : L)) ≠ 0 := by simp
  have n2 : (σ * μ)⁻¹ (f (σ * μ, τ) : L) ≠ 0 := by simp
  field_simp
  linear_combination -h
variable (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) (hfg : IsMulCocycle₂ (f * g))
def rightU (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (hfg : IsMulCocycle₂ (f * g)) (τ : L ≃ₐ[K] L) :
    Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct hfg) :=
  monomial (Equiv.mulRight τ⁻¹) fun ρ => incl (rightCoeff f ρ τ) * u τ
def toMatrixRight : CrossedProduct hg →ₐ[K] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct hfg) :=
  lift (diagHom fun _ => incl) (rightU f hfg)
    (fun τ b => by
      rw [diagHom_apply, diagHom_apply, rightU, monomial_mul_monomial, monomial_mul_monomial]
      refine monomial_congr (by rw [mul_one, one_mul]) fun ρ => ?_
      simp only [Equiv.Perm.one_apply]
      rw [mul_assoc, u_mul_incl, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul]
      congr 2
      ring)
    (fun σ τ => by
      rw [diagHom_apply, rightU, rightU, rightU, monomial_mul_monomial, monomial_mul_monomial]
      refine monomial_congr (by ext ρ; simp [mul_assoc]) fun ρ => ?_
      simp only [Equiv.coe_mulRight]
      rw [mul_assoc, ← mul_assoc (u σ), u_mul_incl, mul_assoc, u_mul_u, ← mul_assoc,
        ← mul_assoc, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul]
      congr 2
      rw [Pi.mul_apply, Units.val_mul]
      exact rightCoeff_mul hf ρ σ τ)
    (by
      rw [diagHom_apply, rightU, inv_one, Equiv.mulRight_one]
      refine monomial_congr rfl fun ρ => ?_
      rw [u_one, ← map_mul, Pi.mul_apply, Units.val_mul, rightCoeff_one hf])
@[simp] theorem toMatrixRight_incl (b : L) :
    toMatrixRight hf hg hfg (incl b) = diagHom (fun _ => incl) b :=
  lift_incl _ _ _ _ _ b
@[simp] theorem toMatrixRight_u (τ : L ≃ₐ[K] L) : toMatrixRight hf hg hfg (u τ) = rightU f hfg τ :=
  lift_u _ _ _ _ _ τ
theorem commute_toMatrix_toMatrixRight (x : CrossedProduct hf) (y : CrossedProduct hg) :
    Commute (toMatrix incl hf x) (toMatrixRight hf hg hfg y) := by
  have dd : ∀ a b : L, Commute (diagHom (fun ρ => (incl : L →ₐ[K] CrossedProduct hfg).comp
      (ρ⁻¹ : L ≃ₐ[K] L).toAlgHom) a) (diagHom (fun _ => incl) b) := fun a b => by
    rw [Commute, SemiconjBy, diagHom_apply, diagHom_apply, monomial_mul_monomial,
      monomial_mul_monomial]
    refine monomial_congr rfl fun ρ => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Equiv.Perm.one_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  have dr : ∀ (a : L) (τ : L ≃ₐ[K] L), Commute (diagHom (fun ρ =>
      (incl : L →ₐ[K] CrossedProduct hfg).comp (ρ⁻¹ : L ≃ₐ[K] L).toAlgHom) a)
      (rightU f hfg τ) := fun a τ => by
    rw [Commute, SemiconjBy, diagHom_apply, rightU, monomial_mul_monomial, monomial_mul_monomial]
    refine monomial_congr (by rw [mul_one, one_mul]) fun ρ => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Equiv.coe_mulRight, Equiv.Perm.one_apply]
    rw [mul_assoc, u_mul_incl, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 2
    rw [mul_inv_rev, inv_inv, AlgEquiv.mul_apply]
    ring
  have rd : ∀ (σ : L ≃ₐ[K] L) (b : L), Commute (regularU (incl : L →ₐ[K] CrossedProduct hfg) f σ)
      (diagHom (fun _ => incl) b) := fun σ b => by
    rw [Commute, SemiconjBy, diagHom_apply, regularU, monomial_mul_monomial, monomial_mul_monomial]
    refine monomial_congr (by rw [mul_one, one_mul]) fun ρ => ?_
    simp only [Equiv.Perm.one_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  have rr : ∀ σ τ : L ≃ₐ[K] L, Commute (regularU (incl : L →ₐ[K] CrossedProduct hfg) f σ)
      (rightU f hfg τ) := fun σ τ => by
    rw [Commute, SemiconjBy, regularU, rightU, monomial_mul_monomial, monomial_mul_monomial]
    refine monomial_congr (by ext ρ; simp [mul_assoc]) fun ρ => ?_
    simp only [Equiv.coe_mulRight, Equiv.coe_mulLeft]
    simp only [mul_assoc, u_mul_incl]
    simp only [← mul_assoc, ← map_mul]
    congr 2
    have h := rightCoeff_comm hf ρ σ τ
    simp only [mul_assoc] at h ⊢
    exact h
  induction x using induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add x x' hx hx' => rw [map_add]; exact hx.add_left hx'
  | single σ a =>
  induction y using induction_on with
  | zero => rw [map_zero]; exact Commute.zero_right _
  | add y y' hy hy' => rw [map_add]; exact hy.add_right hy'
  | single τ b =>
  rw [← incl_mul_u, ← incl_mul_u, map_mul, map_mul, toMatrix_incl, toMatrix_u, toMatrixRight_incl,
    toMatrixRight_u]
  exact ((dd a b).mul_right (dr a τ)).mul_left ((rd σ b).mul_right (rr σ τ))
end Right
omit [DecidableEq (L ≃ₐ[K] L)] in

theorem card_aut [IsGalois K L] : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
section Tensor
variable {f g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
  (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g) (hfg : IsMulCocycle₂ (f * g))
def tensorToMatrix :
    CrossedProduct hf ⊗[K] CrossedProduct hg →ₐ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct hfg) :=
  Algebra.TensorProduct.lift (toMatrix incl hf) (toMatrixRight hf hg hfg)
    (commute_toMatrix_toMatrixRight hf hg hfg)
variable [IsGalois K L]
theorem tensorToMatrix_bijective : Function.Bijective (tensorToMatrix hf hg hfg) := by
  have hinj : Function.Injective (tensorToMatrix hf hg hfg) :=
    RingHom.injective (tensorToMatrix hf hg hfg).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (CrossedProduct hf ⊗[K] CrossedProduct hg) =
      Module.finrank K (Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct hfg)) := by
    rw [Module.finrank_tensorProduct, finrank_eq_sq, finrank_eq_sq, Module.finrank_matrix,
      finrank_eq_sq, card_aut]
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (tensorToMatrix hf hg hfg).toLinearMap)).1 hinj
def tensorAlgEquivMatrix :
    CrossedProduct hf ⊗[K] CrossedProduct hg ≃ₐ[K]
      Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) (CrossedProduct hfg) :=
  AlgEquiv.ofBijective _ (tensorToMatrix_bijective hf hg hfg)
omit [DecidableEq (L ≃ₐ[K] L)] in

theorem isBrauerEquivalent_tensor :
    IsBrauerEquivalent (tensorCSA (csaOf K (CrossedProduct hf)) (csaOf K (CrossedProduct hg)))
      (csaOf K (CrossedProduct hfg)) := by
  classical
  exact isBrauerEquivalent_of_algEquiv_matrix (C := CrossedProduct hfg)
    (tensorAlgEquivMatrix hf hg hfg) (matrixFinOneAlgEquiv (CrossedProduct hfg)).symm
end Tensor
section BaseChange
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)
def baseChangeToMatrix : L ⊗[K] CrossedProduct hf →ₐ[L] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (toMatrix (AlgHom.id K L) hf)
    (fun l _ => Algebra.commute_algebraMap_left l _)
variable [IsGalois K L]
theorem baseChangeToMatrix_bijective : Function.Bijective (baseChangeToMatrix hf) := by
  have hinj : Function.Injective (baseChangeToMatrix hf) :=
    RingHom.injective (baseChangeToMatrix hf).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank L (L ⊗[K] CrossedProduct hf) =
      Module.finrank L (Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) := by
    rw [finrank_baseChange_eq, finrank_eq_sq, Module.finrank_matrix, Module.finrank_self,
      card_aut]
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (baseChangeToMatrix hf).toLinearMap)).1 hinj
def baseChangeAlgEquivMatrix :
    L ⊗[K] CrossedProduct hf ≃ₐ[L] Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  AlgEquiv.ofBijective _ (baseChangeToMatrix_bijective hf)
end BaseChange
end CrossedProduct
section Classes
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
theorem CrossedProduct.mk_mem_relBrauer {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) :
    (⟦csaOf K (CrossedProduct hf)⟧ : BrauerGroup.{u, u} K) ∈ BrauerGroup.relBrauer K L := by
  classical
  rw [BrauerGroup.mk_mem_relBrauer_iff]
  exact ⟨_, ⟨(CrossedProduct.baseChangeAlgEquivMatrix hf).trans
    (Matrix.reindexAlgEquiv L L (Fintype.equivFin _))⟩⟩
namespace H2mul
theorem toBrauer_mul (x y : H2mul (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L (x * y) = toBrauer K L x * toBrauer K L y := by
  induction x using H2mul.induction_on with
  | h c =>
  induction y using H2mul.induction_on with
  | h c' =>
  rw [← map_mul, toBrauer_mk, toBrauer_mk, toBrauer_mk, BrauerGroup.mk_mul_mk]
  exact Quotient.sound (CrossedProduct.isBrauerEquivalent_tensor (isMulCocycle₂_of_mem c)
    (isMulCocycle₂_of_mem c') (isMulCocycle₂_of_mem (c * c'))).symm
variable (K L) in

def toBrauerHom : H2mul (L ≃ₐ[K] L) Lˣ →* BrauerGroup.{u, u} K where
  toFun := toBrauer K L
  map_one' := toBrauer_one
  map_mul' := toBrauer_mul
theorem toBrauer_mem_relBrauer (x : H2mul (L ≃ₐ[K] L) Lˣ) : toBrauer K L x ∈ BrauerGroup.relBrauer K L := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [toBrauer_mk]
  exact CrossedProduct.mk_mem_relBrauer _
variable (K L) in

def toRelBrauer : H2mul (L ≃ₐ[K] L) Lˣ →* BrauerGroup.relBrauer K L :=
  (toBrauerHom K L).codRestrict _ toBrauer_mem_relBrauer
end H2mul
end Classes
end GroundTheory.Brauer
end


