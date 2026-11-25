-- Prove2me | Definitions.Def_GroundTheory_Brauer_Inflation
-- name    : GroundTheory_Brauer_Inflation
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:34.263796+00:00
-- url     : https://prove2.me/theorems/ebaee9b9-9777-5535-b679-efe755e7f0ef
-- title:
--   Inflation
-- statement:
--   Definitions and structural lemmas for Inflation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_one
import Theorems.Thm_GroundTheory_Brauer_H2mul_coe_toRelBrauer
import Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauerHom_apply
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
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
attribute [local simp] GroundTheory.Brauer.H2mul.coe_toRelBrauer
attribute [local simp] GroundTheory.Brauer.H2mul.mulEquivH2_mk
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauerHom_apply
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauer_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open groupCohomology
universe u
namespace CrossedProduct
section Inflate
variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]
theorem algebraMap_restrictNormalHom (σ : L' ≃ₐ[K] L') (x : L) :
    algebraMap L L' (AlgEquiv.restrictNormalHom L σ x) = σ (algebraMap L L' x) :=
  AlgEquiv.restrictNormal_commutes σ L x
theorem map_smul_restrictNormalHom (σ : L' ≃ₐ[K] L') (c : L) (y : L') :
    σ (c • y) = AlgEquiv.restrictNormalHom L σ c • σ y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_restrictNormalHom]
theorem unitsMap_smul (σ : L' ≃ₐ[K] L') (m : Lˣ) :
    Units.map (algebraMap L L' : L →* L') (AlgEquiv.restrictNormalHom L σ • m) =
      σ • Units.map (algebraMap L L' : L →* L') m := by
  ext
  exact algebraMap_restrictNormalHom σ (m : L)
variable (L') in

def inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L') → L'ˣ :=
  fun p => Units.map (algebraMap L L' : L →* L')
    (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))
theorem val_inflate (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L' ≃ₐ[K] L') × (L' ≃ₐ[K] L')) :
    ((inflate L' f p : L'ˣ) : L') =
      algebraMap L L' (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2)) :=
  rfl
variable (L') in

theorem isMulCocycle₂_inflate {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (inflate L' f) :=
  (H2mul.mapCocycles₂ (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    unitsMap_smul ⟨f, hf⟩).2
section Basis
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')
def galMatrix (σ : L' ≃ₐ[K] L') : Matrix ι ι L :=
  fun i j => b.repr (σ (b j)) i
omit [DecidableEq ι] in

theorem repr_apply_algEquiv (σ : L' ≃ₐ[K] L') (x : L') (i : ι) :
    b.repr (σ x) i = ∑ j, galMatrix b σ i j * AlgEquiv.restrictNormalHom L σ (b.repr x j) := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul_restrictNormalHom, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, galMatrix]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
omit [DecidableEq ι] in

theorem galMatrix_mul (σ τ : L' ≃ₐ[K] L') :
    galMatrix b (σ * τ) = galMatrix b σ * (galMatrix b τ).map (AlgEquiv.restrictNormalHom L σ) := by
  ext i k
  change b.repr ((σ * τ) (b k)) i = _
  rw [AlgEquiv.mul_apply, repr_apply_algEquiv, Matrix.mul_apply]
  rfl
omit [Algebra K L] [IsScalarTower K L L'] [Normal K L] [Fintype ι] in

theorem galMatrix_one : galMatrix b (1 : L' ≃ₐ[K] L') = 1 := by
  ext i j
  simp only [galMatrix, AlgEquiv.one_apply, Module.Basis.repr_self, Finsupp.single_apply,
    Matrix.one_apply]
  exact if_congr eq_comm rfl rfl
theorem galMatrix_mul_leftMulMatrix (σ : L' ≃ₐ[K] L') (a : L') :
    galMatrix b σ * (Algebra.leftMulMatrix b a).map (AlgEquiv.restrictNormalHom L σ) =
      Algebra.leftMulMatrix b (σ a) * galMatrix b σ := by
  ext i k
  have h : b.repr (σ (a * b k)) i =
      ∑ j, galMatrix b σ i j * AlgEquiv.restrictNormalHom L σ (Algebra.leftMulMatrix b a j k) := by
    rw [repr_apply_algEquiv]
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [← h, map_mul, ← Algebra.leftMulMatrix_mulVec_repr]
  rfl
end Basis
section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L L')
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)
def inflateIncl : L' →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  (incl : L →ₐ[K] CrossedProduct hf).mapMatrix.comp ((Algebra.leftMulMatrix b).restrictScalars K)
def inflateU (σ : L' ≃ₐ[K] L') : Matrix ι ι (CrossedProduct hf) :=
  (galMatrix b σ).map incl * Matrix.diagonal fun _ => u (AlgEquiv.restrictNormalHom L σ)
omit [Normal K L] in
theorem inflateIncl_apply (a : L') :
    inflateIncl b hf a = (Algebra.leftMulMatrix b a).map incl :=
  rfl
omit [IsScalarTower K L L'] [Normal K L] in

theorem diagonal_u_mul_map_incl (τ : L ≃ₐ[K] L) (M : Matrix ι ι L) :
    (Matrix.diagonal fun _ => (u τ : CrossedProduct hf)) * M.map incl =
      (M.map τ).map incl * Matrix.diagonal fun _ => (u τ : CrossedProduct hf) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, u_mul_incl]
omit [IsScalarTower K L L'] [Normal K L] in

theorem diagonal_u_mul_diagonal_u (σ τ : L ≃ₐ[K] L) :
    (Matrix.diagonal fun _ => (u σ : CrossedProduct hf)) * Matrix.diagonal (fun _ => u τ) =
      (algebraMap L (Matrix ι ι L) (f (σ, τ) : L)).map incl *
        Matrix.diagonal fun _ => (u (σ * τ) : CrossedProduct hf) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext _
  simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact u_mul_u σ τ
theorem inflateU_mul_inflateIncl (σ : L' ≃ₐ[K] L') (a : L') :
    inflateU b hf σ * inflateIncl b hf a = inflateIncl b hf (σ a) * inflateU b hf σ := by
  rw [inflateU, inflateIncl_apply, inflateIncl_apply, mul_assoc, diagonal_u_mul_map_incl,
    ← mul_assoc, ← Matrix.map_mul, galMatrix_mul_leftMulMatrix, Matrix.map_mul, mul_assoc]
theorem inflateU_mul_inflateU (σ τ : L' ≃ₐ[K] L') :
    inflateU b hf σ * inflateU b hf τ =
      inflateIncl b hf (inflate L' f (σ, τ) : L') * inflateU b hf (σ * τ) := by
  rw [inflateU, inflateU, inflateU, inflateIncl_apply, val_inflate, mul_assoc,
    ← mul_assoc (Matrix.diagonal _), diagonal_u_mul_map_incl, mul_assoc,
    diagonal_u_mul_diagonal_u, ← mul_assoc, ← mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul,
    ← galMatrix_mul, ← map_mul, AlgHom.commutes, ← mul_assoc, ← Matrix.map_mul,
    Algebra.commutes]
theorem inflateU_one :
    inflateU b hf 1 = inflateIncl b hf (inflate L' f (1, 1) : L') := by
  rw [inflateU, inflateIncl_apply, val_inflate, map_one, galMatrix_one, AlgHom.commutes,
    Matrix.map_one _ (map_zero _) (map_one _), one_mul, u_one, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_map (map_zero _)]
  rfl
def inflateHom :
    CrossedProduct (isMulCocycle₂_inflate L' hf) →ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  lift (inflateIncl b hf) (inflateU b hf) (inflateU_mul_inflateIncl b hf)
    (inflateU_mul_inflateU b hf) (inflateU_one b hf)
variable [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K L'] [IsGalois K L']
  [Nonempty ι]
theorem inflateHom_bijective : Function.Bijective (inflateHom b hf) := by
  have hinj : Function.Injective (inflateHom b hf) :=
    RingHom.injective (inflateHom b hf).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (CrossedProduct (isMulCocycle₂_inflate L' hf)) =
      Module.finrank K (Matrix ι ι (CrossedProduct hf)) := by
    rw [finrank_eq_sq, Module.finrank_matrix, finrank_eq_sq, ← Module.finrank_eq_card_basis b,
      ← Module.finrank_mul_finrank K L L']
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (inflateHom b hf).toLinearMap)).1 hinj
def inflateAlgEquiv :
    CrossedProduct (isMulCocycle₂_inflate L' hf) ≃ₐ[K] Matrix ι ι (CrossedProduct hf) :=
  AlgEquiv.ofBijective _ (inflateHom_bijective b hf)
end Matrix
end Inflate
section Brauer
variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']
end Brauer
end CrossedProduct
namespace BrauerGroup
variable (K L L' : Type u) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L']
end BrauerGroup
namespace H2mul
section Inflation
variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]
def inflation : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L' ≃ₐ[K] L') L'ˣ :=
  mapPair (AlgEquiv.restrictNormalHom L) (Units.map (algebraMap L L' : L →* L'))
    CrossedProduct.unitsMap_smul
variable {K L L'}
end Inflation
section Brauer
variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']
end Brauer
end H2mul
end GroundTheory.Brauer
end


