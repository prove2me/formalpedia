-- Prove2me | Definitions.Def_GroundTheory_Brauer_BaseChangeCentralizer
-- name    : GroundTheory_Brauer_BaseChangeCentralizer
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:01.324459+00:00
-- url     : https://prove2.me/theorems/029759fb-163e-5b8f-a9bd-c8bdf6995965
-- title:
--   Base Change Centralizer
-- statement:
--   Definitions and structural lemmas for Base Change Centralizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChangeCentralizer.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProductIso
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_one
import Theorems.Thm_GroundTheory_Brauer_H2mul_coe_relBrauerEquiv
import Theorems.Thm_GroundTheory_Brauer_H2mul_coe_toRelBrauer
import Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauerHom_apply
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_degree_baseChangeCSA
import Theorems.Thm_GroundTheory_Brauer_degree_matrixCSA
import Theorems.Thm_GroundTheory_Brauer_degree_tensorCSA
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
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
attribute [local simp] GroundTheory.Brauer.H2mul.coe_relBrauerEquiv
attribute [local simp] GroundTheory.Brauer.H2mul.coe_toRelBrauer
attribute [local simp] GroundTheory.Brauer.H2mul.mulEquivH2_mk
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauerHom_apply
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauer_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.degree_baseChangeCSA
attribute [local simp] GroundTheory.Brauer.degree_matrixCSA
attribute [local simp] GroundTheory.Brauer.degree_tensorCSA
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier
attribute [local simp] GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open Module groupCohomology
open scoped TensorProduct
universe u
namespace CrossedProduct
section Restrict
variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]
variable (K E) in

def resCocycle (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : (L ≃ₐ[E] L) × (L ≃ₐ[E] L) → Lˣ :=
  fun p => f (p.1.restrictScalars K, p.2.restrictScalars K)
@[simp]
theorem resCocycle_apply (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) (p : (L ≃ₐ[E] L) × (L ≃ₐ[E] L)) :
    resCocycle K E f p = f (p.1.restrictScalars K, p.2.restrictScalars K) :=
  rfl
theorem isMulCocycle₂_resCocycle {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (resCocycle K E f) := by
  intro g h j
  exact hf (g.restrictScalars K) (h.restrictScalars K) (j.restrictScalars K)
end Restrict
section Action
variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)
variable (E) in

def inclBase : E →ₐ[K] CrossedProduct hf :=
  (incl (hf := hf)).comp (IsScalarTower.toAlgHom K E L)
theorem inclBase_apply (e : E) : inclBase E hf e = incl (algebraMap E L e) :=
  rfl
theorem incl_mul_inclBase (a : L) (e : E) :
    incl a * inclBase E hf e = inclBase E hf e * (incl a : CrossedProduct hf) := by
  rw [inclBase_apply, ← map_mul, mul_comm, map_mul]
theorem u_mul_inclBase (τ : L ≃ₐ[E] L) (e : E) :
    u (τ.restrictScalars K) * inclBase E hf e = inclBase E hf e * (u (τ.restrictScalars K) : CrossedProduct hf) := by
  rw [inclBase_apply, u_mul_incl, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
def rightMulEnd (c : CrossedProduct hf) (hc : ∀ e : E, c * inclBase E hf e = inclBase E hf e * c) :
    Module.End E (RightMul (inclBase E hf)) where
  toFun x := RightMul.of _ (x.val * c)
  map_add' x y := add_mul x.val y.val c
  map_smul' e x := by
    change x.val * inclBase E hf e * c = x.val * c * inclBase E hf e
    rw [mul_assoc, ← hc, mul_assoc]
def rightInclHom : L →ₐ[E] (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ where
  toFun a := MulOpposite.op (rightMulEnd hf (incl a) (incl_mul_inclBase hf a))
  map_one' := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl 1) = x
    rw [map_one, mul_one]
    rfl
  map_mul' a b := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (a * b)) = RightMul.of _ ((x.val * incl a) * incl b)
    rw [map_mul, mul_assoc]
  map_zero' := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl 0) = 0
    rw [map_zero, mul_zero]
    rfl
  map_add' a b := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (a + b)) = RightMul.of _ (x.val * incl a + x.val * incl b)
    rw [map_add, mul_add]
  commutes' e := by
    apply MulOpposite.unop_injective
    refine LinearMap.ext fun x => ?_
    change RightMul.of _ (x.val * incl (algebraMap E L e)) = e • x
    rfl
def rightSymbol (τ : L ≃ₐ[E] L) : (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ :=
  MulOpposite.op (rightMulEnd hf (u (τ.restrictScalars K)) (u_mul_inclBase hf τ))
def rightAction :
    CrossedProduct (isMulCocycle₂_resCocycle (E := E) hf) →ₐ[E]
      (Module.End E (RightMul (inclBase E hf)))ᵐᵒᵖ :=
  lift (rightInclHom hf) (rightSymbol hf)
    (fun σ a => by
      apply MulOpposite.unop_injective
      refine LinearMap.ext fun x => ?_
      change RightMul.of _ ((x.val * u (σ.restrictScalars K)) * incl a) =
        RightMul.of _ ((x.val * incl (σ a)) * u (σ.restrictScalars K))
      rw [mul_assoc, u_mul_incl, mul_assoc]
      rfl)
    (fun σ τ => by
      apply MulOpposite.unop_injective
      refine LinearMap.ext fun x => ?_
      change RightMul.of _ ((x.val * u (σ.restrictScalars K)) * u (τ.restrictScalars K)) =
        RightMul.of _ ((x.val * incl (f (σ.restrictScalars K, τ.restrictScalars K) : L)) *
          u ((σ * τ).restrictScalars K))
      rw [mul_assoc, u_mul_u, mul_assoc]
      rfl)
    (by
      apply MulOpposite.unop_injective
      refine LinearMap.ext fun x => ?_
      change RightMul.of _ (x.val * u ((1 : L ≃ₐ[E] L).restrictScalars K)) =
        RightMul.of _ (x.val * incl (f ((1 : L ≃ₐ[E] L).restrictScalars K,
          (1 : L ≃ₐ[E] L).restrictScalars K) : L))
      exact congrArg (fun y => RightMul.of _ (x.val * y)) (u_one (hf := hf)))
end Action
section Main
variable {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f)
def rightActionOp :
    (CrossedProduct (isMulCocycle₂_resCocycle (E := E) hf))ᵐᵒᵖ →ₐ[E]
      Module.End E (RightMul (inclBase E hf)) :=
  (AlgEquiv.opOp E (Module.End E (RightMul (inclBase E hf)))).symm.toAlgHom.comp
    (AlgHom.op (rightAction hf))
end Main
end CrossedProduct
namespace H2mul
section Res
variable (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L]
def resBase : H2mul (L ≃ₐ[K] L) Lˣ →* H2mul (L ≃ₐ[E] L) Lˣ :=
  mapPair (AlgEquiv.restrictScalarsHom K) (MonoidHom.id Lˣ) (fun _ _ => rfl)
variable {K E L}
end Res
section Brauer
variable {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L]
end Brauer
end H2mul
end GroundTheory.Brauer


