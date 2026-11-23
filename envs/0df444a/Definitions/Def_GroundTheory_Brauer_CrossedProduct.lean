-- Prove2me | Definitions.Def_GroundTheory_Brauer_CrossedProduct
-- name    : GroundTheory_Brauer_CrossedProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:19.851063+00:00
-- url     : https://prove2.me/theorems/e2ee3159-ee8c-443e-954c-b5d18c566a6c
-- title:
--   Crossed Product
-- statement:
--   Definitions and structural lemmas for Crossed Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Brauer
open groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
@[ext]
structure CrossedProduct {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) where

  ofCoeff ::

  coeff : (L ≃ₐ[K] L) →₀ L
namespace CrossedProduct
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
theorem val_smul_units (σ : L ≃ₐ[K] L) (x : Lˣ) : ((σ • x : Lˣ) : L) = σ x := rfl
def mulCoeff (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :
    ((L ≃ₐ[K] L) →₀ L) →+ ((L ≃ₐ[K] L) →₀ L) →+ ((L ≃ₐ[K] L) →₀ L) :=
  Finsupp.liftAddHom fun σ =>
    { toFun := fun a => Finsupp.liftAddHom fun τ =>
        (Finsupp.singleAddHom (σ * τ)).comp
          ((AddMonoidHom.mulRight ((f (σ, τ) : Lˣ) : L)).comp
            ((AddMonoidHom.mulLeft a).comp (σ : L →+ L)))
      map_zero' := by
        ext τ b
        simp
      map_add' := fun a b => by
        ext τ c
        simp [add_mul] }
theorem mulCoeff_single_single (σ τ : L ≃ₐ[K] L) (a b : L) :
    mulCoeff f (Finsupp.single σ a) (Finsupp.single τ b) =
      Finsupp.single (σ * τ) (a * σ b * f (σ, τ)) := by
  simp [mulCoeff]
theorem mulCoeff_assoc (hf : IsMulCocycle₂ f) (x y z : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f (mulCoeff f x y) z = mulCoeff f x (mulCoeff f y z) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, AddMonoidHom.add_apply, hy, hy']
  | single τ b =>
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | single ρ c =>
  simp only [mulCoeff_single_single, mul_assoc, AlgEquiv.mul_apply, map_mul]
  congr 1
  have h := congrArg (fun x : Lˣ => (x : L)) (hf σ τ ρ)
  simp only [Units.val_mul, val_smul_units] at h
  linear_combination (a * σ b * σ (τ c)) * h
theorem mulCoeff_smul_left (c : L) (x y : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f (c • x) y = c • mulCoeff f x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
  | single τ b =>
  simp only [Finsupp.smul_single, smul_eq_mul, mulCoeff_single_single, mul_assoc]
theorem mulCoeff_smul_right (c : K) (x y : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f x (c • y) = c • mulCoeff f x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
  | single τ b =>
  simp only [Finsupp.smul_single, mulCoeff_single_single, Algebra.smul_def, map_mul,
    AlgEquiv.commutes]
  congr 1
  ring
theorem one_mulCoeff (hf : IsMulCocycle₂ f) (x : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f (Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L)) x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single τ b =>
  simp only [mulCoeff_single_single, map_one_fst_of_isMulCocycle₂ hf, one_mul,
    AlgEquiv.one_apply]
  rw [mul_right_comm, Units.inv_mul, one_mul]
theorem mulCoeff_one (hf : IsMulCocycle₂ f) (x : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f x (Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L)) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  rw [mulCoeff_single_single, map_one_snd_of_isMulCocycle₂ hf σ, mul_one, val_smul_units, mul_assoc,
    ← map_mul, Units.inv_mul, map_one, mul_one]
variable {hf : IsMulCocycle₂ f}
instance : Zero (CrossedProduct hf) := ⟨⟨0⟩⟩
instance : Add (CrossedProduct hf) := ⟨fun x y => ⟨x.coeff + y.coeff⟩⟩
instance : Neg (CrossedProduct hf) := ⟨fun x => ⟨-x.coeff⟩⟩
instance : Sub (CrossedProduct hf) := ⟨fun x y => ⟨x.coeff - y.coeff⟩⟩
instance {R : Type*} [SMulZeroClass R L] : SMul R (CrossedProduct hf) :=
  ⟨fun r x => ⟨r • x.coeff⟩⟩
@[simp] theorem coeff_zero : (0 : CrossedProduct hf).coeff = 0 := rfl
@[simp] theorem coeff_add (x y : CrossedProduct hf) : (x + y).coeff = x.coeff + y.coeff := rfl
@[simp] theorem coeff_neg (x : CrossedProduct hf) : (-x).coeff = -x.coeff := rfl
@[simp] theorem coeff_sub (x y : CrossedProduct hf) : (x - y).coeff = x.coeff - y.coeff := rfl
@[simp] theorem coeff_smul {R : Type*} [SMulZeroClass R L] (r : R) (x : CrossedProduct hf) :
    (r • x).coeff = r • x.coeff := rfl
@[simp] theorem coeff_ofCoeff (a : (L ≃ₐ[K] L) →₀ L) : (ofCoeff a : CrossedProduct hf).coeff = a :=
  rfl
theorem coeff_injective : Function.Injective (coeff : CrossedProduct hf → _) :=
  fun _ _ => CrossedProduct.ext
instance : AddCommGroup (CrossedProduct hf) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
def coeffAddHom : CrossedProduct hf →+ ((L ≃ₐ[K] L) →₀ L) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl
instance {R : Type*} [Semiring R] [Module R L] : Module R (CrossedProduct hf) :=
  Function.Injective.module R coeffAddHom coeff_injective fun _ _ => rfl
instance : IsScalarTower K L (CrossedProduct hf) :=
  ⟨fun c a x => CrossedProduct.ext (smul_assoc c a x.coeff)⟩
def coeffEquiv (R : Type*) [Semiring R] [Module R L] :
    CrossedProduct hf ≃ₗ[R] ((L ≃ₐ[K] L) →₀ L) where
  toFun := coeff
  invFun := ofCoeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] theorem coeffEquiv_apply (R : Type*) [Semiring R] [Module R L] (x : CrossedProduct hf) :
    coeffEquiv R x = x.coeff := rfl
@[simp] theorem coeffEquiv_symm_apply (R : Type*) [Semiring R] [Module R L]
    (a : (L ≃ₐ[K] L) →₀ L) : (coeffEquiv R).symm a = (ofCoeff a : CrossedProduct hf) := rfl
instance : Mul (CrossedProduct hf) := ⟨fun x y => ⟨mulCoeff f x.coeff y.coeff⟩⟩
instance : One (CrossedProduct hf) := ⟨⟨Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L)⟩⟩
theorem coeff_mul (x y : CrossedProduct hf) : (x * y).coeff = mulCoeff f x.coeff y.coeff := rfl
instance instRing : Ring (CrossedProduct hf) where
  __ := (inferInstance : AddCommGroup (CrossedProduct hf))
  mul := (· * ·)
  one := 1
  mul_assoc x y z := CrossedProduct.ext (mulCoeff_assoc hf _ _ _)
  one_mul x := CrossedProduct.ext (one_mulCoeff hf _)
  mul_one x := CrossedProduct.ext (mulCoeff_one hf _)
  left_distrib x y z := CrossedProduct.ext (map_add (mulCoeff f x.coeff) _ _)
  right_distrib x y z := CrossedProduct.ext (by
    simp only [coeff_mul, coeff_add, map_add, AddMonoidHom.add_apply])
  zero_mul x := CrossedProduct.ext (by simp only [coeff_mul, coeff_zero, map_zero,
    AddMonoidHom.zero_apply])
  mul_zero x := CrossedProduct.ext (by simp only [coeff_mul, coeff_zero, map_zero])
instance : IsScalarTower L (CrossedProduct hf) (CrossedProduct hf) :=
  ⟨fun a x y => CrossedProduct.ext (mulCoeff_smul_left a x.coeff y.coeff)⟩
instance instAlgebra : Algebra K (CrossedProduct hf) :=
  Algebra.ofModule
    (fun c x y => CrossedProduct.ext (by
      change mulCoeff f (c • x.coeff) y.coeff = c • mulCoeff f x.coeff y.coeff
      rw [← algebraMap_smul L c x.coeff, mulCoeff_smul_left, algebraMap_smul]))
    (fun c x y => CrossedProduct.ext (mulCoeff_smul_right c x.coeff y.coeff))
theorem algebraMap_eq_smul_one' (c : K) :
    algebraMap K (CrossedProduct hf) c = c • 1 := Algebra.algebraMap_eq_smul_one c
def single (σ : L ≃ₐ[K] L) (a : L) : CrossedProduct hf := ⟨Finsupp.single σ a⟩
def u (σ : L ≃ₐ[K] L) : CrossedProduct hf := single σ 1
@[simp] theorem coeff_single (σ : L ≃ₐ[K] L) (a : L) :
    (single σ a : CrossedProduct hf).coeff = Finsupp.single σ a := rfl
@[simp] theorem coeff_u (σ : L ≃ₐ[K] L) : (u σ : CrossedProduct hf).coeff = Finsupp.single σ 1 :=
  rfl
@[simp] theorem single_zero (σ : L ≃ₐ[K] L) : (single σ 0 : CrossedProduct hf) = 0 := by
  ext1; simp
theorem single_add (σ : L ≃ₐ[K] L) (a b : L) :
    (single σ (a + b) : CrossedProduct hf) = single σ a + single σ b := by
  ext1; simp [Finsupp.single_add]
theorem smul_single (c : L) (σ : L ≃ₐ[K] L) (a : L) :
    c • (single σ a : CrossedProduct hf) = single σ (c * a) := by
  ext1; simp
theorem single_injective (σ : L ≃ₐ[K] L) :
    Function.Injective (single σ : L → CrossedProduct hf) := fun _ _ h =>
  Finsupp.single_injective σ (congrArg coeff h)
@[simp] theorem single_eq_zero {σ : L ≃ₐ[K] L} {a : L} :
    (single σ a : CrossedProduct hf) = 0 ↔ a = 0 := by
  rw [← single_zero σ, (single_injective σ).eq_iff]
theorem single_mul_single (σ τ : L ≃ₐ[K] L) (a b : L) :
    (single σ a : CrossedProduct hf) * single τ b = single (σ * τ) (a * σ b * f (σ, τ)) :=
  CrossedProduct.ext (mulCoeff_single_single σ τ a b)
theorem one_def : (1 : CrossedProduct hf) = single 1 (((f (1, 1))⁻¹ : Lˣ) : L) := rfl
@[elab_as_elim]
theorem induction_on {p : CrossedProduct hf → Prop} (x : CrossedProduct hf) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (single : ∀ σ a, p (single σ a)) : p x := by
  obtain ⟨c⟩ := x
  induction c using Finsupp.induction_linear with
  | zero => exact zero
  | add c d hc hd => exact add ⟨c⟩ ⟨d⟩ hc hd
  | single σ a => exact single σ a
def incl : L →ₐ[K] CrossedProduct hf where
  toFun a := single 1 (a * ((f (1, 1))⁻¹ : Lˣ))
  map_one' := by rw [one_mul]; rfl
  map_mul' a b := by
    rw [single_mul_single, one_mul, AlgEquiv.one_apply]
    congr 1
    have h := Units.inv_mul (f (1, 1))
    linear_combination (-(a * b * ((f (1, 1))⁻¹ : Lˣ))) * h
  map_zero' := by rw [zero_mul, single_zero]
  map_add' a b := by rw [add_mul, single_add]
  commutes' c := by
    rw [algebraMap_eq_smul_one', one_def]
    ext1
    rw [coeff_smul, coeff_single, coeff_single, Finsupp.smul_single, Algebra.smul_def]
theorem incl_apply (a : L) :
    (incl a : CrossedProduct hf) = single 1 (a * ((f (1, 1))⁻¹ : Lˣ)) := rfl
theorem incl_injective : Function.Injective (incl : L → CrossedProduct hf) := fun a b h => by
  rw [incl_apply, incl_apply] at h
  simpa using single_injective 1 h
instance : Nontrivial (CrossedProduct hf) := (incl_injective (hf := hf)).nontrivial
def basis : Module.Basis (L ≃ₐ[K] L) L (CrossedProduct hf) :=
  (Finsupp.basisSingleOne).map (coeffEquiv L).symm
instance : Module.Free L (CrossedProduct hf) := Module.Free.of_basis basis
instance [FiniteDimensional K L] : Module.Finite L (CrossedProduct hf) :=
  Module.Finite.of_basis basis
instance [FiniteDimensional K L] : FiniteDimensional K (CrossedProduct hf) :=
  Module.Finite.trans L _
end CrossedProduct
end GroundTheory.Brauer
end


