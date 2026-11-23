-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:44.403718+00:00
-- url     : https://prove2.me/theorems/b8162c31-61aa-479b-9016-d5e313124d01
-- title:
--   Mem Primitive Tensors Iff Is Primitive Elem
-- statement:
--   Definitions and structural lemmas for Mem Primitive Tensors Iff Is Primitive Elem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
namespace GlobalTheory
abbrev CartierDual (R H : Type*) [CommSemiring R] [AddCommMonoid H] [Module R H] :=
  WithConv (H →ₗ[R] R)
namespace CartierDual
section Modules
variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]
theorem ext_apply {φ ψ : CartierDual R M} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  WithConv.ext (LinearMap.ext h)
variable (R M) in

def toDual : CartierDual R M ≃ₗ[R] Module.Dual R M := WithConv.linearEquiv R _
@[simp] theorem toDual_apply (φ : CartierDual R M) : toDual R M φ = φ.ofConv := rfl
@[simp] theorem toDual_symm_apply (φ : Module.Dual R M) : (toDual R M).symm φ = toConv φ := rfl
instance instFinite [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R (CartierDual R M) :=
  Module.Finite.equiv (toDual R M).symm
instance instProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective R (CartierDual R M) :=
  Module.Projective.of_equiv (toDual R M).symm
instance instFree [Module.Finite R M] [Module.Free R M] : Module.Free R (CartierDual R M) :=
  Module.Free.of_equiv (toDual R M).symm
variable (R M) in

def evalAt : M →ₗ[R] CartierDual R M →ₗ[R] R :=
  (toDual R M).toLinearMap.flip
@[simp] theorem evalAt_apply (a : M) (φ : CartierDual R M) : evalAt R M a φ = φ a := rfl
variable (R M N) in

def pair : CartierDual R M ⊗[R] CartierDual R N →ₗ[R] M ⊗[R] N →ₗ[R] R :=
  dualDistrib R M N ∘ₗ TensorProduct.map (toDual R M).toLinearMap (toDual R N).toLinearMap
@[simp] theorem pair_tmul_tmul (φ : CartierDual R M) (ψ : CartierDual R N) (a : M) (b : N) :
    pair R M N (φ ⊗ₜ ψ) (a ⊗ₜ b) = φ a * ψ b := by
  simp [pair]
theorem pair_tmul (φ : CartierDual R M) (ψ : CartierDual R N) (t : M ⊗[R] N) :
    pair R M N (φ ⊗ₜ ψ) t = LinearMap.mul' R R (TensorProduct.map φ.ofConv ψ.ofConv t) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp
theorem pair_bijective [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] : Function.Bijective (pair R M N) := by
  have : pair R M N = ((TensorProduct.congr (toDual R M) (toDual R N)) ≪≫ₗ
      (homTensorHomEquiv R M N R R) ≪≫ₗ
      (LinearEquiv.congrRight (TensorProduct.lid R R))).toLinearMap := by
    ext φ ψ a b
    simp [LinearEquiv.congrRight]
  rw [this]
  exact LinearEquiv.bijective _
variable (R M N) in

def pairEquiv [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] :
    CartierDual R M ⊗[R] CartierDual R N ≃ₗ[R] (M ⊗[R] N →ₗ[R] R) :=
  LinearEquiv.ofBijective (pair R M N) pair_bijective
@[simp] theorem pairEquiv_apply [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] (x : CartierDual R M ⊗[R] CartierDual R N) :
    pairEquiv R M N x = pair R M N x := rfl
theorem tensor_ext [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] {x y : CartierDual R M ⊗[R] CartierDual R N}
    (h : ∀ a b, pair R M N x (a ⊗ₜ b) = pair R M N y (a ⊗ₜ b)) : x = y :=
  pair_bijective.1 (TensorProduct.ext' h)
theorem eq_of_forall_apply [Module.Projective R M] {a b : M}
    (h : ∀ φ : CartierDual R M, φ a = φ b) : a = b := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective R M›
  have hi : Function.Injective s := LinearMap.injective_of_comp_eq_id _ _ hs
  exact hi (Finsupp.ext fun i => h (toConv (Finsupp.lapply i ∘ₗ s)))
theorem tensor_eq_of_forall_pair [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] {s t : M ⊗[R] N}
    (h : ∀ φ ψ, pair R M N (φ ⊗ₜ ψ) s = pair R M N (φ ⊗ₜ ψ) t) : s = t := by
  refine eq_of_forall_apply (R := R) fun χ => ?_
  obtain ⟨x, hx⟩ := (pair_bijective (R := R) (M := M) (N := N)).2 χ.ofConv
  rw [← hx]
  clear hx
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul φ ψ => exact h φ ψ
def pair₃ : CartierDual R M ⊗[R] (CartierDual R N ⊗[R] CartierDual R P) →ₗ[R]
    M ⊗[R] (N ⊗[R] P) →ₗ[R] R :=
  pair R M (N ⊗[R] P) ∘ₗ LinearMap.lTensor _ ((toDual R _).symm.toLinearMap ∘ₗ pair R N P)
theorem pair₃_tmul (φ : CartierDual R M) (x : CartierDual R N ⊗[R] CartierDual R P)
    (a : M) (t : N ⊗[R] P) : pair₃ (φ ⊗ₜ x) (a ⊗ₜ t) = φ a * pair R N P x t := by
  simp [pair₃]
theorem pair₃_assoc (x : CartierDual R M ⊗[R] CartierDual R N) (χ : CartierDual R P)
    (a : M) (b : N) (c : P) :
    pair₃ (TensorProduct.assoc R _ _ _ (x ⊗ₜ χ)) (a ⊗ₜ (b ⊗ₜ c)) = pair R M N x (a ⊗ₜ b) * χ c := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, LinearMap.add_apply, hx, hy, add_mul]
  | tmul φ ψ => simp [pair₃_tmul, mul_assoc]
theorem pair₃_ext [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] [Module.Finite R P] [Module.Projective R P]
    {x y : CartierDual R M ⊗[R] (CartierDual R N ⊗[R] CartierDual R P)}
    (h : ∀ a b c, pair₃ x (a ⊗ₜ (b ⊗ₜ c)) = pair₃ y (a ⊗ₜ (b ⊗ₜ c))) : x = y := by
  have hinj : Function.Injective (pair₃ (R := R) (M := M) (N := N) (P := P)) := by
    have : pair₃ (R := R) (M := M) (N := N) (P := P) =
        ((LinearEquiv.lTensor _ (pairEquiv R N P ≪≫ₗ (toDual R _).symm)) ≪≫ₗ
          pairEquiv R M (N ⊗[R] P)).toLinearMap := by
      ext; simp [pair₃]
    rw [this]; exact LinearEquiv.injective _
  exact hinj (TensorProduct.ext_threefold' h)
end Modules
section Coalgebra
variable {R H : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Module.Finite R H]
  [Module.Projective R H]
instance instCoalgebraStruct : CoalgebraStruct R (CartierDual R H) where
  comul := (pairEquiv R H H).symm.toLinearMap ∘ₗ (LinearMap.mul' R H).dualMap ∘ₗ
    (toDual R H).toLinearMap
  counit := evalAt R H 1
@[simp] theorem counit_apply (φ : CartierDual R H) : counit (R := R) φ = φ 1 := rfl
theorem pair_comul (φ : CartierDual R H) :
    pair R H H (comul φ) = φ.ofConv ∘ₗ LinearMap.mul' R H :=
  (pairEquiv R H H).apply_symm_apply _
@[simp] theorem pair_comul_tmul (φ : CartierDual R H) (a b : H) :
    pair R H H (comul φ) (a ⊗ₜ b) = φ (a * b) := by
  simp [pair_comul]
instance instCoalgebra : Coalgebra R (CartierDual R H) where
  coassoc := by
    refine LinearMap.ext fun φ => pair₃_ext fun a b c => ?_
    have h1 (t : CartierDual R H ⊗[R] CartierDual R H) :
        pair₃ (TensorProduct.assoc R _ _ _ (LinearMap.rTensor _ comul t)) (a ⊗ₜ (b ⊗ₜ c)) =
          pair R H H t ((a * b) ⊗ₜ c) := by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
      | tmul φ ψ => simp [pair₃_assoc]
    have h2 (t : CartierDual R H ⊗[R] CartierDual R H) :
        pair₃ (LinearMap.lTensor _ comul t) (a ⊗ₜ (b ⊗ₜ c)) = pair R H H t (a ⊗ₜ (b * c)) := by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
      | tmul φ ψ => simp [pair₃_tmul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, pair_comul_tmul, mul_assoc]
  rTensor_counit_comp_comul := by
    refine LinearMap.ext fun φ => (TensorProduct.lid R _).injective (ext_apply fun a => ?_)
    have h (t : CartierDual R H ⊗[R] CartierDual R H) :
        (TensorProduct.lid R _ (LinearMap.rTensor _ counit t)) a = pair R H H t (1 ⊗ₜ a) := by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, ofConv_add, LinearMap.add_apply, hx, hy]
      | tmul φ ψ => simp
    simp only [LinearMap.comp_apply, h]
    simp
  lTensor_counit_comp_comul := by
    refine LinearMap.ext fun φ => (TensorProduct.rid R _).injective (ext_apply fun a => ?_)
    have h (t : CartierDual R H ⊗[R] CartierDual R H) :
        (TensorProduct.rid R _ (LinearMap.lTensor _ counit t)) a = pair R H H t (a ⊗ₜ 1) := by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, ofConv_add, LinearMap.add_apply, hx, hy]
      | tmul φ ψ => simp [mul_comm]
    simp only [LinearMap.comp_apply, h]
    simp
end Coalgebra
theorem pair_comm {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (x : CartierDual R M ⊗[R] CartierDual R N) (a : M) (b : N) :
    pair R N M (TensorProduct.comm R _ _ x) (b ⊗ₜ a) = pair R M N x (a ⊗ₜ b) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul φ ψ => simp [mul_comm]
instance instIsCocomm {R H : Type*} [CommSemiring R] [CommSemiring H] [Algebra R H]
    [Module.Finite R H] [Module.Projective R H] : IsCocomm R (CartierDual R H) where
  comm_comp_comul := LinearMap.ext fun φ => tensor_ext fun a b => by
    simp [pair_comm, mul_comm]
section Algebra
variable {R C C' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid C'] [Module R C'] [Coalgebra R C']
theorem mul_apply (φ ψ : CartierDual R C) (a : C) :
    (φ * ψ) a = pair R C C (φ ⊗ₜ ψ) (comul a) := by
  rw [pair_tmul]; rfl
theorem one_apply (a : C) : (1 : CartierDual R C) a = counit a := rfl
theorem mul'_apply (x : CartierDual R C ⊗[R] CartierDual R C) (a : C) :
    (LinearMap.mul' R _ x) a = pair R C C x (comul a) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, ofConv_add, LinearMap.add_apply, hx, hy]
  | tmul φ ψ => rw [LinearMap.mul'_apply, mul_apply]
theorem pair_mul (x y : CartierDual R C ⊗[R] CartierDual R C') :
    toConv (pair R C C' (x * y)) = toConv (pair R C C' x) * toConv (pair R C C' y) := by
  induction x with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, toConv_add, hx, hx']
  | tmul φ ψ =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, toConv_add, hy, hy']
    | tmul φ' ψ' =>
      refine WithConv.ext (TensorProduct.ext' fun a b => ?_)
      rw [LinearMap.convMul_apply, TensorProduct.comul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        ofConv_toConv, pair_tmul_tmul, LinearMap.convMul_apply, LinearMap.convMul_apply]
      generalize comul (R := R) a = s
      generalize comul (R := R) b = t
      induction s with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, add_mul, hx, hy]
      | tmul a a' =>
        induction t with
        | zero => simp
        | add x y hx hy => simp only [tmul_add, map_add, mul_add, hx, hy]
        | tmul b b' => simp [mul_mul_mul_comm]
end Algebra
section Bialgebra
variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H]
instance instBialgebra : Bialgebra R (CartierDual R H) :=
  Bialgebra.mk' R (CartierDual R H) (by simp)
    (fun {φ ψ} => by simp [Algebra.TensorProduct.one_def])
    (tensor_ext fun a b => by simp [Algebra.TensorProduct.one_def])
    (fun {φ ψ} => tensor_ext fun a b => by
      have h := congr($(pair_mul (comul φ) (comul ψ)).ofConv (a ⊗ₜ b))
      rw [ofConv_toConv] at h
      rw [h, pair_comul_tmul, ((ℛ R a).mul (ℛ R b)).convMul_apply,
        ((ℛ R a).tmul (ℛ R b)).convMul_apply]
      simp)
end Bialgebra
section Hopf
variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H] [Module.Finite R H]
  [Module.Projective R H]
instance instHopfAlgebraStruct : HopfAlgebraStruct R (CartierDual R H) where
  antipode := (toDual R H).symm.toLinearMap ∘ₗ (antipode R).dualMap ∘ₗ (toDual R H).toLinearMap
@[simp] theorem antipode_apply (φ : CartierDual R H) (a : H) :
    (antipode R φ : CartierDual R H) a = φ (antipode R a) := rfl
instance instHopfAlgebra : HopfAlgebra R (CartierDual R H) where
  mul_antipode_rTensor_comul := by
    refine LinearMap.ext fun φ => ext_apply fun a => ?_
    have h (x : CartierDual R H ⊗[R] CartierDual R H) (t : H ⊗[R] H) :
        pair R H H (LinearMap.rTensor _ (antipode R) x) t =
          pair R H H x (LinearMap.rTensor _ (antipode R) t) := by
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
      | tmul φ ψ =>
        induction t with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b => simp
    simp only [LinearMap.comp_apply, mul'_apply, h, pair_comul, mul_antipode_rTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  mul_antipode_lTensor_comul := by
    refine LinearMap.ext fun φ => ext_apply fun a => ?_
    have h (x : CartierDual R H ⊗[R] CartierDual R H) (t : H ⊗[R] H) :
        pair R H H (LinearMap.lTensor _ (antipode R) x) t =
          pair R H H x (LinearMap.lTensor _ (antipode R) t) := by
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
      | tmul φ ψ =>
        induction t with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b => simp
    simp only [LinearMap.comp_apply, mul'_apply, h, pair_comul, mul_antipode_lTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
end Hopf
section Transpose
variable {R M N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
def transpose (f : M →ₗ[R] N) : CartierDual R N →ₗ[R] CartierDual R M :=
  (toDual R M).symm.toLinearMap ∘ₗ f.dualMap ∘ₗ (toDual R N).toLinearMap
@[simp] theorem transpose_apply (f : M →ₗ[R] N) (φ : CartierDual R N) (a : M) :
    transpose f φ a = φ (f a) := rfl
theorem pair_map_transpose (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    (x : CartierDual R N ⊗[R] CartierDual R Q) (t : M ⊗[R] P) :
    pair R M P (TensorProduct.map (transpose f) (transpose g) x) t =
      pair R N Q x (TensorProduct.map f g t) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul φ ψ =>
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp
theorem transpose_injective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Injective (transpose f) := fun φ ψ h => ext_apply fun b => by
  obtain ⟨a, rfl⟩ := hf b
  exact congr($h a)
variable (R M) in

def cartierDualToBidual : M →ₗ[R] CartierDual R (CartierDual R M) :=
  (toDual R _).symm.toLinearMap ∘ₗ evalAt R M
@[simp] theorem toBidual_apply (a : M) (φ : CartierDual R M) : cartierDualToBidual R M a φ = φ a := rfl
theorem toBidual_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (cartierDualToBidual R M) := by
  have : cartierDualToBidual R M = (Module.evalEquiv R M ≪≫ₗ (toDual R M).dualMap ≪≫ₗ
      (toDual R _).symm).toLinearMap := by
    ext; rfl
  rw [this]; exact LinearEquiv.bijective _
theorem pair_map_toBidual (t : M ⊗[R] N) (x : CartierDual R M ⊗[R] CartierDual R N) :
    pair R _ _ (TensorProduct.map (cartierDualToBidual R M) (cartierDualToBidual R N) t) x = pair R M N x t := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul φ ψ =>
    induction t with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul a b => simp
theorem transpose_bijective {f : M →ₗ[R] N} (hf : Function.Bijective f) :
    Function.Bijective (transpose f) :=
  ⟨transpose_injective hf.2, fun φ =>
    ⟨transpose (LinearEquiv.ofBijective f hf).symm.toLinearMap φ, ext_apply fun a => by
      rw [transpose_apply, transpose_apply]
      exact congrArg φ.ofConv ((LinearEquiv.ofBijective f hf).symm_apply_apply a)⟩⟩
theorem transpose_bijective_iff [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N) :
    Function.Bijective (transpose f) ↔ Function.Bijective f := by
  refine ⟨fun h => ?_, transpose_bijective⟩
  have h2 := (transpose_bijective h).comp (toBidual_bijective (R := R) (M := M))
  have h3 : transpose (transpose f) ∘ cartierDualToBidual R M = cartierDualToBidual R N ∘ f := rfl
  rw [h3] at h2
  exact (Function.Bijective.of_comp_iff' toBidual_bijective f).1 h2
end Transpose
section MapAlg
variable {R C C' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid C'] [Module R C'] [Coalgebra R C']
def mapAlgHom (f : C →ₗc[R] C') : CartierDual R C' →ₐ[R] CartierDual R C :=
  AlgHom.ofLinearMap (transpose (f : C →ₗ[R] C')) (ext_apply fun a => by simp)
    (fun φ ψ => ext_apply fun a => by
      rw [transpose_apply, mul_apply, mul_apply, ← TensorProduct.map_tmul, pair_map_transpose,
        CoalgHomClass.map_comp_comul_apply]
      rfl)
@[simp] theorem mapAlgHom_apply (f : C →ₗc[R] C') (φ : CartierDual R C') (a : C) :
    mapAlgHom f φ a = φ (f a) := rfl
end MapAlg
section MapCoalg
variable {R H K : Type*} [CommSemiring R] [Semiring H] [Algebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Algebra R K] [Module.Finite R K] [Module.Projective R K]
def mapCoalgHom (f : H →ₐ[R] K) : CartierDual R K →ₗc[R] CartierDual R H where
  __ := transpose f.toLinearMap
  counit_comp := LinearMap.ext fun φ => by simp
  map_comp_comul := LinearMap.ext fun φ => tensor_ext fun a b => by
    simp [pair_map_transpose]
@[simp] theorem mapCoalgHom_apply (f : H →ₐ[R] K) (φ : CartierDual R K) (a : H) :
    mapCoalgHom f φ a = φ (f a) := rfl
end MapCoalg
section Map
variable {R H K L : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Bialgebra R K] [Module.Finite R K] [Module.Projective R K]
  [Semiring L] [Bialgebra R L] [Module.Finite R L] [Module.Projective R L]
def map (f : H →ₐc[R] K) : CartierDual R K →ₐc[R] CartierDual R H where
  __ := mapCoalgHom (f : H →ₐ[R] K)
  map_one' := map_one (mapAlgHom (f : H →ₗc[R] K))
  map_mul' := map_mul (mapAlgHom (f : H →ₗc[R] K))
@[simp] theorem map_apply (f : H →ₐc[R] K) (φ : CartierDual R K) (a : H) :
    map f φ a = φ (f a) := rfl
@[simp] theorem map_id : map (BialgHom.id R H) = BialgHom.id R _ := rfl
theorem map_comp (g : K →ₐc[R] L) (f : H →ₐc[R] K) : map (g.comp f) = (map f).comp (map g) := rfl
def congr (e : H ≃ₐc[R] K) : CartierDual R K ≃ₐc[R] CartierDual R H :=
  BialgEquiv.ofBialgHom (map (e : H →ₐc[R] K)) (map (e.symm : K →ₐc[R] H))
    (by rw [← map_comp, BialgEquiv.symm_comp, map_id])
    (by rw [← map_comp, BialgEquiv.comp_symm, map_id])
@[simp] theorem congr_apply (e : H ≃ₐc[R] K) (φ : CartierDual R K) (a : H) :
    congr e φ a = φ (e a) := rfl
@[simp] theorem congr_symm_apply (e : H ≃ₐc[R] K) (φ : CartierDual R H) (a : K) :
    (congr e).symm φ a = φ (e.symm a) := rfl
variable (R H) in

def bidualHom : H →ₐc[R] CartierDual R (CartierDual R H) where
  __ := cartierDualToBidual R H
  counit_comp := LinearMap.ext fun a => by simp
  map_comp_comul := LinearMap.ext fun a => tensor_ext fun φ ψ => by
    simp only [LinearMap.comp_apply, pair_map_toBidual, pair_comul_tmul, toBidual_apply, mul_apply]
  map_one' := ext_apply fun φ => by simp
  map_mul' a b := ext_apply fun φ => by
    change cartierDualToBidual R H (a * b) φ = (cartierDualToBidual R H a * cartierDualToBidual R H b) φ
    rw [mul_apply, ← TensorProduct.map_tmul, pair_map_toBidual, pair_comul_tmul, toBidual_apply]
variable (R H) in

def bidual : H ≃ₐc[R] CartierDual R (CartierDual R H) :=
  BialgEquiv.ofBijective (bidualHom R H) toBidual_bijective
@[simp] theorem bidualHom_apply (a : H) (φ : CartierDual R H) : bidualHom R H a φ = φ a := rfl
@[simp] theorem bidual_apply (a : H) (φ : CartierDual R H) : bidual R H a φ = φ a := rfl
@[simp] theorem apply_bidual_symm (x : CartierDual R (CartierDual R H)) (φ : CartierDual R H) :
    φ ((bidual R H).symm x) = x φ := by
  rw [← bidual_apply, BialgEquiv.apply_symm_apply]
end Map
section BaseChange
variable {R : Type*} (A : Type*) {M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
instance instIsScalarTower {X : Type*} [AddCommMonoid X] [Module A X] :
    IsScalarTower R A (CartierDual A X) :=
  ⟨fun r a φ => WithConv.ext (smul_assoc r a φ.ofConv)⟩
variable (R M) in

def baseChangeLinear : A ⊗[R] CartierDual R M →ₗ[A] CartierDual A (A ⊗[R] M) :=
  (toDual A _).symm.toLinearMap ∘ₗ
    LinearMap.liftBaseChange A (Module.Dual.baseChange A ∘ₗ (toDual R M).toLinearMap)
@[simp] theorem baseChangeLinear_tmul_tmul (a b : A) (φ : CartierDual R M) (m : M) :
    baseChangeLinear R A M (a ⊗ₜ φ) (b ⊗ₜ m) = φ m • (a * b) := by
  simp [baseChangeLinear]
theorem baseChangeLinear_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (baseChangeLinear R A M) := by
  let e : (M →ₗ[R] A) ≃ₗ[A] (A ⊗[R] M →ₗ[A] A) := LinearMap.liftBaseChangeEquiv A
  have : ⇑(baseChangeLinear R A M) = (toDual A _).symm ∘ e ∘ dualTensorHom R M A ∘
      TensorProduct.comm R _ _ ∘ LinearEquiv.lTensor A (toDual R M) := by
    funext x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
    | tmul a φ =>
      refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => ?_)
      simp [e, mul_comm]
  rw [this]
  exact (LinearEquiv.bijective _).comp <| (LinearEquiv.bijective _).comp <|
    dualTensorHom_bijective.comp <| (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)
theorem pair_baseChange (x : CartierDual R M ⊗[R] CartierDual R N) (t : M ⊗[R] N) :
    pair A (A ⊗[R] M) (A ⊗[R] N)
      (TensorProduct.map (baseChangeLinear R A M) (baseChangeLinear R A N)
        (AlgebraTensorModule.tensorTensorTensorComm R A R A A A _ _ ((1 ⊗ₜ[A] 1) ⊗ₜ[R] x)))
      (AlgebraTensorModule.tensorTensorTensorComm R A R A A A _ _ ((1 ⊗ₜ[A] 1) ⊗ₜ[R] t)) =
    algebraMap R A (pair R M N x t) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [tmul_add, map_add, LinearMap.add_apply, hx, hy]
  | tmul φ ψ =>
    induction t with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul a b => simp [Algebra.smul_def, mul_comm]
section Coalgebra
variable {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
theorem baseChangeLinear_one : baseChangeLinear R A C 1 = 1 :=
  WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => by
    simp [Algebra.TensorProduct.one_def])
theorem baseChangeLinear_mul (x y : A ⊗[R] CartierDual R C) :
    baseChangeLinear R A C (x * y) = baseChangeLinear R A C x * baseChangeLinear R A C y := by
  have key (φ ψ : CartierDual R C) : baseChangeLinear R A C (1 ⊗ₜ (φ * ψ)) =
      baseChangeLinear R A C (1 ⊗ₜ φ) * baseChangeLinear R A C (1 ⊗ₜ ψ) := by
    refine WithConv.ext ?_
    ext a
    have := pair_baseChange A (φ ⊗ₜ ψ) (comul a)
    rw [← mul_apply] at this
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars]
    rw [mul_apply, baseChangeLinear_tmul_tmul, mul_one, ← Algebra.algebraMap_eq_smul_one, ← this]
    simp
  induction x with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a φ =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | tmul b ψ =>
      have h (a : A) (φ : CartierDual R C) : a ⊗ₜ[R] φ = a • ((1 : A) ⊗ₜ[R] φ) := by
        simp [smul_tmul']
      rw [Algebra.TensorProduct.tmul_mul_tmul, h (a * b), h a, h b, map_smul, map_smul, map_smul,
        key, smul_mul_smul_comm]
end Coalgebra
variable (R) (H : Type*) [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H]
def baseChangeHom : A ⊗[R] CartierDual R H →ₐc[A] CartierDual A (A ⊗[R] H) where
  __ := baseChangeLinear R A H
  counit_comp := by
    ext φ
    simp [Algebra.TensorProduct.one_def]
  map_comp_comul := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext_ring (LinearMap.ext fun φ => pair_bijective.1 ?_)
    ext a b
    have := pair_baseChange A (comul φ) (a ⊗ₜ b)
    simpa [Algebra.algebraMap_eq_smul_one] using this
  map_one' := baseChangeLinear_one A
  map_mul' := baseChangeLinear_mul A
def baseChange : A ⊗[R] CartierDual R H ≃ₐc[A] CartierDual A (A ⊗[R] H) :=
  BialgEquiv.ofBijective (baseChangeHom R A H) (baseChangeLinear_bijective A)
variable {R H}
@[simp] theorem baseChange_tmul_tmul (a b : A) (φ : CartierDual R H) (h : H) :
    baseChange R A H (a ⊗ₜ φ) (b ⊗ₜ h) = φ h • (a * b) :=
  baseChangeLinear_tmul_tmul A a b φ h
end BaseChange
section Product
theorem pair_tensorTensorTensorComm {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (s : CartierDual R M ⊗[R] CartierDual R M)
    (t : CartierDual R N ⊗[R] CartierDual R N) (a : M) (b : N) (c : M) (d : N) :
    pair R _ _ (TensorProduct.map ((toDual R _).symm.toLinearMap ∘ₗ pair R M N)
      ((toDual R _).symm.toLinearMap ∘ₗ pair R M N)
      (AlgebraTensorModule.tensorTensorTensorComm R R R R _ _ _ _ (s ⊗ₜ t)))
      ((a ⊗ₜ b) ⊗ₜ (c ⊗ₜ d)) = pair R M M s (a ⊗ₜ c) * pair R N N t (b ⊗ₜ d) := by
  induction s with
  | zero => simp only [zero_tmul, LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply,
      zero_mul]
  | add x y hx hy =>
    simp only [add_tmul, LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply, add_mul,
      hx, hy]
  | tmul φ φ' =>
    induction t with
    | zero => simp only [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply,
        mul_zero]
    | add x y hx hy =>
      simp only [tmul_add, LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply, mul_add,
        hx, hy]
    | tmul ψ ψ' => simp [mul_mul_mul_comm]
variable (R H K : Type*) [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Bialgebra R K] [Module.Finite R K] [Module.Projective R K]
def tensorHom : CartierDual R H ⊗[R] CartierDual R K →ₐc[R] CartierDual R (H ⊗[R] K) where
  __ := (toDual R _).symm.toLinearMap ∘ₗ pair R H K
  counit_comp := TensorProduct.ext' fun φ ψ => by
    simp [Algebra.TensorProduct.one_def, mul_comm]
  map_comp_comul := TensorProduct.ext' fun φ ψ => pair_bijective.1 <| by
    refine TensorProduct.ext_fourfold' fun a b c d => ?_
    have := pair_tensorTensorTensorComm (comul φ) (comul ψ) a b c d
    simpa using this
  map_one' := WithConv.ext (TensorProduct.ext' fun a b => by
    simp [Algebra.TensorProduct.one_def, mul_comm])
  map_mul' := pair_mul
def tensorEquiv : CartierDual R H ⊗[R] CartierDual R K ≃ₐc[R] CartierDual R (H ⊗[R] K) :=
  BialgEquiv.ofBijective (tensorHom R H K) ((toDual R _).symm.bijective.comp pair_bijective)
variable {R H K} in

@[simp] theorem tensorEquiv_apply (x : CartierDual R H ⊗[R] CartierDual R K) (t : H ⊗[R] K) :
    tensorEquiv R H K x t = pair R H K x t := rfl
end Product
section Tensor
variable {R N M N' M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
variable (R N M) in

def tensorToHom : N ⊗[R] M →ₗ[R] CartierDual R M →ₗ[R] N :=
  dualTensorHom R (CartierDual R M) N ∘ₗ LinearMap.rTensor N (evalAt R M) ∘ₗ
    (TensorProduct.comm R N M).toLinearMap
@[simp] theorem tensorToHom_tmul (n : N) (m : M) (φ : CartierDual R M) :
    tensorToHom R N M (n ⊗ₜ m) φ = φ m • n := rfl
theorem tensorToHom_map (g : N →ₗ[R] N') (f : M →ₗ[R] M') (x : N ⊗[R] M) (φ : CartierDual R M') :
    tensorToHom R N' M' (TensorProduct.map g f x) φ = g (tensorToHom R N M x (transpose f φ)) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul n m => simp
theorem apply_tensorToHom (x : N ⊗[R] M) (ψ : CartierDual R N) (φ : CartierDual R M) :
    ψ (tensorToHom R N M x φ) = pair R N M (ψ ⊗ₜ φ) x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul n m => simp [mul_comm]
theorem apply_tensorToHom_comm (x : N ⊗[R] M) (ψ : CartierDual R N) (φ : CartierDual R M) :
    φ (tensorToHom R M N (TensorProduct.comm R N M x) ψ) = pair R N M (ψ ⊗ₜ φ) x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul n m => simp
theorem tensorToHom_bijective [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (tensorToHom R N M) := by
  have h : Function.Bijective (evalAt R M) := (toDual R _).bijective.comp toBidual_bijective
  exact dualTensorHom_bijective.comp <|
    (LinearEquiv.rTensor N (LinearEquiv.ofBijective _ h)).bijective.comp
      (TensorProduct.comm R N M).bijective
variable (R N M) in

def tensorEquivHom [Module.Finite R M] [Module.Projective R M] :
    N ⊗[R] M ≃ₗ[R] (CartierDual R M →ₗ[R] N) :=
  LinearEquiv.ofBijective (tensorToHom R N M) tensorToHom_bijective
@[simp] theorem tensorEquivHom_apply [Module.Finite R M] [Module.Projective R M] (x : N ⊗[R] M) :
    tensorEquivHom R N M x = tensorToHom R N M x := rfl
@[simp] theorem tensorToHom_tensorEquivHom_symm [Module.Finite R M] [Module.Projective R M]
    (f : CartierDual R M →ₗ[R] N) : tensorToHom R N M ((tensorEquivHom R N M).symm f) = f :=
  (tensorEquivHom R N M).apply_symm_apply f
theorem eq_of_forall_tensorToHom [Module.Finite R M] [Module.Projective R M] {x y : N ⊗[R] M}
    (h : ∀ φ, tensorToHom R N M x φ = tensorToHom R N M y φ) : x = y :=
  tensorToHom_bijective.1 (LinearMap.ext h)
theorem eq_of_forall_tensorToHom_pair [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R M'] [Module.Projective R M'] {x y : N ⊗[R] (M ⊗[R] M')}
    (h : ∀ φ ψ, tensorToHom R N _ x (toConv (pair R M M' (φ ⊗ₜ ψ))) =
      tensorToHom R N _ y (toConv (pair R M M' (φ ⊗ₜ ψ)))) : x = y := by
  refine eq_of_forall_tensorToHom fun χ => ?_
  obtain ⟨t, ht⟩ := (pair_bijective (R := R) (M := M) (N := M')).2 χ.ofConv
  rw [← toConv_ofConv χ, ← ht]
  clear ht
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, toConv_add, hs, ht]
  | tmul φ ψ => exact h φ ψ
theorem baseChangeLinear_tmul_apply {A : Type*} [CommSemiring A] [Algebra R A] (a : A)
    (φ : CartierDual R M) (x : A ⊗[R] M) :
    baseChangeLinear R A M (a ⊗ₜ φ) x = a * tensorToHom R A M x φ := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, mul_add, hx, hy]
  | tmul n m => simp
end Tensor
section Points
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Module.Finite R C] [Module.Projective R C]
theorem isGroupLikeElem_iff_mul (a : C) : IsGroupLikeElem R a ↔
    (1 : CartierDual R C) a = 1 ∧ ∀ φ ψ : CartierDual R C, (φ * ψ) a = φ a * ψ a := by
  rw [isGroupLikeElem_iff]
  refine and_congr Iff.rfl ⟨fun h φ ψ => ?_, fun h => tensor_eq_of_forall_pair fun φ ψ => ?_⟩
  · rw [mul_apply, h, pair_tmul_tmul]
  · rw [← mul_apply, h, pair_tmul_tmul]
variable {A : Type*} [CommSemiring A] [Algebra R A]
theorem isGroupLikeElem_tensor_iff_mul (x : A ⊗[R] C) : IsGroupLikeElem A x ↔
    tensorToHom R A C x 1 = 1 ∧
      ∀ φ ψ, tensorToHom R A C x (φ * ψ) = tensorToHom R A C x φ * tensorToHom R A C x ψ := by
  rw [isGroupLikeElem_iff_mul, ← baseChangeLinear_one, Algebra.TensorProduct.one_def,
    baseChangeLinear_tmul_apply, one_mul]
  refine and_congr Iff.rfl ⟨fun h φ ψ => ?_, fun h Φ Ψ => ?_⟩
  · have := h (baseChangeLinear R A C (1 ⊗ₜ φ)) (baseChangeLinear R A C (1 ⊗ₜ ψ))
    rw [← baseChangeLinear_mul, Algebra.TensorProduct.tmul_mul_tmul] at this
    simpa only [baseChangeLinear_tmul_apply, one_mul] using this
  · obtain ⟨s, rfl⟩ := (baseChangeLinear_bijective (R := R) (M := C) A).2 Φ
    obtain ⟨t, rfl⟩ := (baseChangeLinear_bijective (R := R) (M := C) A).2 Ψ
    rw [← baseChangeLinear_mul]
    induction s with
    | zero => simp
    | add s s' hs hs' => simp only [add_mul, map_add, ofConv_add, LinearMap.add_apply, hs, hs']
    | tmul a φ =>
      induction t with
      | zero => simp
      | add t t' ht ht' => simp only [mul_add, map_add, ofConv_add, LinearMap.add_apply, ht, ht']
      | tmul b ψ =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, baseChangeLinear_tmul_apply, h,
          mul_mul_mul_comm]
variable (R C A) in

def pointsEquiv : (CartierDual R C →ₐ[R] A) ≃ GroupLike A (A ⊗[R] C) where
  toFun f := ⟨(tensorEquivHom R A C).symm f.toLinearMap,
    (isGroupLikeElem_tensor_iff_mul _).2 (by simp)⟩
  invFun x := AlgHom.ofLinearMap (tensorToHom R A C x.val)
    ((isGroupLikeElem_tensor_iff_mul _).1 x.2).1 ((isGroupLikeElem_tensor_iff_mul _).1 x.2).2
  left_inv f := AlgHom.ext fun φ => by simp
  right_inv x := GroupLike.ext ((tensorEquivHom R A C).symm_apply_apply x.val)
@[simp] theorem pointsEquiv_symm_apply (x : GroupLike A (A ⊗[R] C)) (φ : CartierDual R C) :
    (pointsEquiv R C A).symm x φ = tensorToHom R A C x.val φ := rfl
@[simp] theorem tensorToHom_pointsEquiv (f : CartierDual R C →ₐ[R] A) (φ : CartierDual R C) :
    tensorToHom R A C (pointsEquiv R C A f).val φ = f φ := by
  simp [pointsEquiv]
end Points
theorem tensorToHom_mul {R H A : Type*} [CommSemiring R] [Semiring H] [Algebra R H]
    [Module.Finite R H] [Module.Projective R H] [Semiring A] [Algebra R A] (x y : A ⊗[R] H) :
    toConv (tensorToHom R A H (x * y)) =
      toConv (tensorToHom R A H x) * toConv (tensorToHom R A H y) := by
  induction x with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, toConv_add, hx, hx']
  | tmul a h =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, toConv_add, hy, hy']
    | tmul b k =>
      refine WithConv.ext (LinearMap.ext fun φ => ?_)
      rw [LinearMap.convMul_apply, Algebra.TensorProduct.tmul_mul_tmul, ofConv_toConv,
        tensorToHom_tmul, ← pair_comul_tmul]
      generalize comul (R := R) φ = t
      induction t with
      | zero => simp
      | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_smul, hs, ht]
      | tmul φ ψ => simp [smul_smul, mul_comm]
section PointsBialgebra
variable {R H A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [CommSemiring A] [Algebra R A]
variable (R H A) in

def pointsMulEquiv : WithConv (CartierDual R H →ₐ[R] A) ≃* GroupLike A (A ⊗[R] H) :=
  MulEquiv.symm
  { toEquiv := (pointsEquiv R H A).symm.trans (WithConv.equiv _).symm
    map_mul' := fun x y => WithConv.ext (AlgHom.toLinearMap_injective
      (toConv_injective (tensorToHom_mul x.val y.val))) }
@[simp] theorem pointsMulEquiv_apply (f : WithConv (CartierDual R H →ₐ[R] A)) :
    pointsMulEquiv R H A f = pointsEquiv R H A f.ofConv := rfl
@[simp] theorem pointsMulEquiv_symm_apply (x : GroupLike A (A ⊗[R] H)) :
    (pointsMulEquiv R H A).symm x = toConv ((pointsEquiv R H A).symm x) := rfl
variable (R H A) in

def dualPointsEquiv : (H →ₐ[R] A) ≃ GroupLike A (A ⊗[R] CartierDual R H) :=
  (AlgEquiv.arrowCongr (bidual R H).toAlgEquiv AlgEquiv.refl).trans
    (pointsEquiv R (CartierDual R H) A)
@[simp] theorem tensorToHom_dualPointsEquiv (f : H →ₐ[R] A) (a : H) :
    tensorToHom R A _ (dualPointsEquiv R H A f).val (bidual R H a) = f a :=
  (tensorToHom_pointsEquiv _ _).trans (congrArg f ((bidual R H).symm_apply_apply a))
end PointsBialgebra
end CartierDual
theorem tmul_tmul_one_eq {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (a : A) (m : M) (n : N) :
    (a ⊗ₜ[R] m) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] n) = ((1 : A) ⊗ₜ[R] m) ⊗ₜ[A] (a ⊗ₜ[R] n) := by
  rw [show a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) by simp [smul_tmul'], smul_tmul]
  simp [smul_tmul']
theorem distribBaseChange_lTensor_comul {R A C : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid C] [Module R C] [Coalgebra R C] (x : A ⊗[R] C) :
    AlgebraTensorModule.distribBaseChange R A C C (LinearMap.lTensor A comul x) =
      comul (R := A) x := by
  induction x with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  | tmul a h =>
    rw [LinearMap.lTensor_tmul, TensorProduct.comul_tmul]
    generalize comul (R := R) h = t
    induction t with
    | zero => simp only [tmul_zero, LinearEquiv.map_zero]
    | add s t hs ht => simp only [tmul_add, LinearEquiv.map_add, hs, ht]
    | tmul b c => simp [tmul_tmul_one_eq a]
section Primitive
variable (R : Type*) {H K : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring K]
  [Bialgebra R K]
def IsPrimitiveElem (a : H) : Prop := comul (R := R) a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a
variable (H) in

def primitiveComul : H →ₗ[R] H ⊗[R] H :=
  (TensorProduct.mk R H H).flip 1 + TensorProduct.mk R H H 1
@[simp] theorem primitiveComul_apply (a : H) : primitiveComul R H a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a := rfl
variable (H) in

def primitiveElems : Submodule R H := LinearMap.eqLocus comul (primitiveComul R H)
variable {R} in

@[simp] theorem mem_primitiveElems {a : H} : a ∈ primitiveElems R H ↔ IsPrimitiveElem R a :=
  Iff.rfl
variable {R} in

theorem IsPrimitiveElem.map {a : H} (ha : IsPrimitiveElem R a) (f : H →ₐc[R] K) :
    IsPrimitiveElem R (f a) := by
  rw [IsPrimitiveElem, ← CoalgHomClass.map_comp_comul_apply, ha]
  simp
def primitiveTensors (M H : Type*) [AddCommMonoid M] [Module R M] [Semiring H] [Bialgebra R H] :
    Submodule R (M ⊗[R] H) :=
  LinearMap.eqLocus (LinearMap.lTensor M comul) (LinearMap.lTensor M (primitiveComul R H))
variable {R} in

theorem mem_primitiveTensors {M : Type*} [AddCommMonoid M] [Module R M] {x : M ⊗[R] H} :
    x ∈ primitiveTensors R M H ↔
      LinearMap.lTensor M comul x = LinearMap.lTensor M (primitiveComul R H) x := Iff.rfl
variable {R} in

theorem mem_primitiveTensors_iff_isPrimitiveElem {A : Type*} [CommSemiring A] [Algebra R A]
    {x : A ⊗[R] H} : x ∈ primitiveTensors R A H ↔ IsPrimitiveElem A x := by
  have h2 : AlgebraTensorModule.distribBaseChange R A H H
      (LinearMap.lTensor A (primitiveComul R H) x) = primitiveComul A _ x := by
    induction x with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]
    | tmul a h =>
      simp [tmul_add, Algebra.TensorProduct.one_def, tmul_tmul_one_eq (R := R) a (1 : H) h]
  rw [mem_primitiveTensors, ← (AlgebraTensorModule.distribBaseChange R A H H).injective.eq_iff,
    distribBaseChange_lTensor_comul, h2]
  rfl
variable {R} in

theorem mem_primitiveTensors_self {x : R ⊗[R] H} :
    x ∈ primitiveTensors R R H ↔ IsPrimitiveElem R (TensorProduct.lid R H x) := by
  obtain ⟨a, rfl⟩ := (TensorProduct.lid R H).symm.surjective x
  rw [mem_primitiveTensors, ← (TensorProduct.lid R _).injective.eq_iff]
  simp [IsPrimitiveElem]
end Primitive
namespace CartierDual
section Lie
variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H]
theorem mem_primitiveTensors_iff {M : Type*} [AddCommMonoid M] [Module R M] (x : M ⊗[R] H) :
    x ∈ primitiveTensors R M H ↔ ∀ φ ψ : CartierDual R H, tensorToHom R M H x (φ * ψ) =
      φ 1 • tensorToHom R M H x ψ + ψ 1 • tensorToHom R M H x φ := by
  have h1 (φ ψ : CartierDual R H) : transpose comul (toConv (pair R H H (φ ⊗ₜ ψ))) = φ * ψ :=
    ext_apply fun a => (mul_apply φ ψ a).symm
  have h2 (φ ψ : CartierDual R H) :
      transpose (primitiveComul R H) (toConv (pair R H H (φ ⊗ₜ ψ))) = φ 1 • ψ + ψ 1 • φ :=
    ext_apply fun a => by simp [mul_comm, add_comm]
  have h3 (φ ψ : CartierDual R H) :
      tensorToHom R M _ (LinearMap.lTensor M comul x) (toConv (pair R H H (φ ⊗ₜ ψ))) =
        tensorToHom R M H x (φ * ψ) := by
    rw [LinearMap.lTensor, tensorToHom_map, h1]; rfl
  have h4 (φ ψ : CartierDual R H) :
      tensorToHom R M _ (LinearMap.lTensor M (primitiveComul R H) x)
        (toConv (pair R H H (φ ⊗ₜ ψ))) =
        φ 1 • tensorToHom R M H x ψ + ψ 1 • tensorToHom R M H x φ := by
    rw [LinearMap.lTensor, tensorToHom_map, h2, map_add, map_smul, map_smul]; rfl
  rw [mem_primitiveTensors]
  exact ⟨fun h φ ψ => by rw [← h3, h, h4],
    fun h => eq_of_forall_tensorToHom_pair fun φ ψ => by rw [h3, h4, h]⟩
end Lie
section LieRing
open TrivSqZeroExt
variable (R H A M : Type*) [CommRing R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
  [Module Aᵐᵒᵖ M] [IsCentralScalar A M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
def tangentEquiv :
    {f : CartierDual R H →ₐ[R] TrivSqZeroExt A M //
      ∀ φ, (f φ).fst = algebraMap R A (counit φ)} ≃ primitiveTensors R M H where
  toFun f := ⟨(tensorEquivHom R M H).symm ((sndHom A M).restrictScalars R ∘ₗ f.1.toLinearMap),
    (mem_primitiveTensors_iff _).2 fun φ ψ => by simp [f.2]⟩
  invFun x := ⟨AlgHom.ofLinearMap
      (Algebra.linearMap R (TrivSqZeroExt A M) ∘ₗ counit +
        (inrHom A M).restrictScalars R ∘ₗ tensorToHom R M H x.1)
      (by
        have h := (mem_primitiveTensors_iff _).1 x.2 1 1
        have h1 : tensorToHom R M H x.1 1 = 0 := by simpa using h
        simp [h1])
      (fun φ ψ => by
        have h := (mem_primitiveTensors_iff _).1 x.2 φ ψ
        ext
        · simp [algebraMap_eq_inl', Algebra.TensorProduct.one_def]
        · simp [algebraMap_eq_inl', h]),
    fun φ => by simp [algebraMap_eq_inl']⟩
  left_inv f := Subtype.ext (AlgHom.ext fun φ => by
    ext
    · simp [algebraMap_eq_inl', f.2]
    · simp [algebraMap_eq_inl'])
  right_inv x := Subtype.ext (eq_of_forall_tensorToHom fun φ => by
    simp [algebraMap_eq_inl'])
variable {R H A M}
@[simp] theorem tensorToHom_tangentEquiv (f : {f : CartierDual R H →ₐ[R] TrivSqZeroExt A M //
      ∀ φ, (f φ).fst = algebraMap R A (counit φ)}) (φ : CartierDual R H) :
    tensorToHom R M H (tangentEquiv R H A M f).1 φ = (f.1 φ).snd :=
  congr($(tensorToHom_tensorEquivHom_symm ((sndHom A M).restrictScalars R ∘ₗ f.1.toLinearMap)) φ)
@[simp] theorem snd_tangentEquiv_symm (x : primitiveTensors R M H) (φ : CartierDual R H) :
    (((tangentEquiv R H A M).symm x).1 φ).snd = tensorToHom R M H x.1 φ := by
  rw [← tensorToHom_tangentEquiv, Equiv.apply_symm_apply]
variable (R H A) in

def dualNumberEquiv :
    {f : CartierDual R H →ₐ[R] DualNumber A // ∀ φ, (f φ).fst = algebraMap R A (counit φ)} ≃
      primitiveElems A (A ⊗[R] H) :=
  (tangentEquiv R H A A).trans
    (Equiv.subtypeEquivRight fun _ => mem_primitiveTensors_iff_isPrimitiveElem)
@[simp] theorem tensorToHom_dualNumberEquiv (f : {f : CartierDual R H →ₐ[R] DualNumber A //
      ∀ φ, (f φ).fst = algebraMap R A (counit φ)}) (φ : CartierDual R H) :
    tensorToHom R A H (dualNumberEquiv R H A f).1 φ = (f.1 φ).snd :=
  tensorToHom_tangentEquiv f φ
variable (R H) in

def primitiveEquiv :
    {f : CartierDual R H →ₐ[R] DualNumber R // ∀ φ, (f φ).fst = counit φ} ≃ primitiveElems R H :=
  (tangentEquiv R H R R).trans
    ((TensorProduct.lid R H).toEquiv.subtypeEquiv fun _ => mem_primitiveTensors_self)
@[simp] theorem apply_primitiveEquiv (f : {f : CartierDual R H →ₐ[R] DualNumber R //
      ∀ φ, (f φ).fst = counit φ}) (φ : CartierDual R H) :
    φ (primitiveEquiv R H f).1 = (f.1 φ).snd := by
  rw [← tensorToHom_tangentEquiv (A := R) f φ]
  change φ (TensorProduct.lid R H (tangentEquiv R H R R f).1) = _
  generalize (tangentEquiv R H R R f).1 = x
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul r a => simp [mul_comm]
@[simp] theorem snd_primitiveEquiv_symm (a : primitiveElems R H) (φ : CartierDual R H) :
    (((primitiveEquiv R H).symm a).1 φ).snd = φ a.1 := by
  rw [← apply_primitiveEquiv, Equiv.apply_symm_apply]
end LieRing
section MonoidAlgebra
variable (R Γ : Type*) [CommSemiring R]
def monoidAlgebraEquiv : CartierDual R (MonoidAlgebra R Γ) ≃ₐ[R] (Γ → R) :=
  AlgEquiv.ofLinearEquiv (toDual R _ ≪≫ₗ ((MonoidAlgebra.basis Γ R).constr R).symm)
    (funext fun γ => by simp [MonoidAlgebra.basis_apply])
    (fun φ ψ => funext fun γ => by simp [MonoidAlgebra.basis_apply])
variable {R Γ}
@[simp] theorem monoidAlgebraEquiv_apply (φ : CartierDual R (MonoidAlgebra R Γ)) (γ : Γ) :
    monoidAlgebraEquiv R Γ φ γ = φ (MonoidAlgebra.single γ 1) := by
  simp [monoidAlgebraEquiv, MonoidAlgebra.basis_apply]
@[simp] theorem monoidAlgebraEquiv_symm_single (f : Γ → R) (γ : Γ) (r : R) :
    (monoidAlgebraEquiv R Γ).symm f (MonoidAlgebra.single γ r) = r * f γ := by
  have h := monoidAlgebraEquiv_apply ((monoidAlgebraEquiv R Γ).symm f) γ
  rw [AlgEquiv.apply_symm_apply] at h
  rw [h, ← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
end MonoidAlgebra
section AddMonoidAlgebra
variable (R Γ : Type*) [CommSemiring R]
def addMonoidAlgebraEquiv : CartierDual R (AddMonoidAlgebra R Γ) ≃ₐ[R] (Γ → R) :=
  AlgEquiv.ofLinearEquiv (toDual R _ ≪≫ₗ ((AddMonoidAlgebra.basis Γ R).constr R).symm)
    (funext fun γ => by simp [AddMonoidAlgebra.basis_apply])
    (fun φ ψ => funext fun γ => by simp [AddMonoidAlgebra.basis_apply])
variable {R Γ}
@[simp] theorem addMonoidAlgebraEquiv_apply (φ : CartierDual R (AddMonoidAlgebra R Γ)) (γ : Γ) :
    addMonoidAlgebraEquiv R Γ φ γ = φ (AddMonoidAlgebra.single γ 1) := by
  simp [addMonoidAlgebraEquiv, AddMonoidAlgebra.basis_apply]
@[simp] theorem addMonoidAlgebraEquiv_symm_single (f : Γ → R) (γ : Γ) (r : R) :
    (addMonoidAlgebraEquiv R Γ).symm f (AddMonoidAlgebra.single γ r) = r * f γ := by
  have h := addMonoidAlgebraEquiv_apply ((addMonoidAlgebraEquiv R Γ).symm f) γ
  rw [AlgEquiv.apply_symm_apply] at h
  rw [h, ← smul_eq_mul, ← map_smul, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
theorem antipode_addMonoidAlgebra [AddGroup Γ] [Finite Γ]
    (φ : CartierDual R (AddMonoidAlgebra R Γ)) (γ : Γ) :
    addMonoidAlgebraEquiv R Γ (antipode R φ) γ = addMonoidAlgebraEquiv R Γ φ (-γ) := by
  simp
end AddMonoidAlgebra
end CartierDual
section GroupLikeBase
open Algebra.TensorProduct (includeLeft includeRight productMap)
variable {R A K : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [CommSemiring K] [Bialgebra R K] {x : A ⊗[R] K} {B : Type*} [CommSemiring B] [Algebra R B]
end GroupLikeBase
section Bicharacter
open CartierDual
open Algebra.TensorProduct (productMap)
variable (R : Type*) {H K : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [CommSemiring K] [Bialgebra R K]
structure IsBicharacter (u : H ⊗[R] K) : Prop where

  left : IsGroupLikeElem K (TensorProduct.comm R H K u)

  right : IsGroupLikeElem H u
def pairingMap (u : H ⊗[R] K) : CartierDual R H →ₗ[R] K :=
  tensorToHom R K H (TensorProduct.comm R H K u)
structure IsPerfectBicharacter (u : H ⊗[R] K) : Prop extends IsBicharacter R u where

  bijective : Function.Bijective (pairingMap R u)
variable {R} {u v : H ⊗[R] K}
@[simp] theorem pairingMap_tmul (a : H) (b : K) (φ : CartierDual R H) :
    pairingMap R (a ⊗ₜ[R] b) φ = φ a • b := rfl
theorem apply_pairingMap (u : H ⊗[R] K) (φ : CartierDual R H) (ψ : CartierDual R K) :
    ψ (pairingMap R u φ) = pair R H K (φ ⊗ₜ ψ) u :=
  apply_tensorToHom_comm u φ ψ
theorem pairingMap_comm (u : H ⊗[R] K) :
    pairingMap R (TensorProduct.comm R H K u) = tensorToHom R H K u := by
  simp [pairingMap]
theorem apply_pairingMap_comm (u : H ⊗[R] K) (φ : CartierDual R H) (ψ : CartierDual R K) :
    φ (pairingMap R (TensorProduct.comm R H K u) ψ) = ψ (pairingMap R u φ) := by
  rw [pairingMap_comm, apply_tensorToHom, apply_pairingMap]
namespace IsBicharacter
theorem symm (hu : IsBicharacter R u) : IsBicharacter R (TensorProduct.comm R H K u) :=
  ⟨by simpa using hu.right, hu.left⟩
variable {A : Type*} [CommSemiring A] [Algebra R A]
end IsBicharacter
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]
theorem isGroupLikeElem_iff_pairingMap (u : H ⊗[R] K) : IsGroupLikeElem H u ↔
    counit ∘ₗ pairingMap R u = counit ∧
      TensorProduct.map (pairingMap R u) (pairingMap R u) ∘ₗ comul = comul ∘ₗ pairingMap R u := by
  have key (ψ ψ' : CartierDual R K) (φ : CartierDual R H) :
      pair R K K (ψ ⊗ₜ ψ') (TensorProduct.map (pairingMap R u) (pairingMap R u) (comul φ)) =
        φ (tensorToHom R H K u ψ * tensorToHom R H K u ψ') := by
    rw [← pair_comul_tmul]
    generalize comul (R := R) φ = t
    induction t with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
    | tmul φ φ' => simp [apply_pairingMap, apply_tensorToHom]
  have key' (ψ : CartierDual R K) (φ : CartierDual R H) :
      ψ (pairingMap R u φ) = φ (tensorToHom R H K u ψ) := by
    rw [apply_pairingMap, apply_tensorToHom]
  rw [isGroupLikeElem_tensor_iff_mul]
  refine and_congr ⟨fun h => LinearMap.ext fun φ => ?_, fun h => ?_⟩
    ⟨fun h => LinearMap.ext fun φ => tensor_eq_of_forall_pair fun ψ ψ' => ?_, fun h ψ ψ' => ?_⟩
  · rw [LinearMap.comp_apply, ← one_apply, key', h, counit_apply]
  · refine eq_of_forall_apply (R := R) fun φ => ?_
    rw [← key', one_apply, ← LinearMap.comp_apply, h, counit_apply]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, key, ← mul_apply, key', h]
  · refine eq_of_forall_apply (R := R) fun φ => ?_
    rw [← key, ← key', mul_apply, ← LinearMap.comp_apply comul, ← h, LinearMap.comp_apply]
def IsBicharacter.toBialgHom (hu : IsBicharacter R u) : CartierDual R H →ₐc[R] K where
  __ := pairingMap R u
  counit_comp := ((isGroupLikeElem_iff_pairingMap u).1 hu.right).1
  map_comp_comul := ((isGroupLikeElem_iff_pairingMap u).1 hu.right).2
  map_one' := ((isGroupLikeElem_tensor_iff_mul _).1 hu.left).1
  map_mul' := ((isGroupLikeElem_tensor_iff_mul _).1 hu.left).2
@[simp] theorem IsBicharacter.toBialgHom_apply (hu : IsBicharacter R u) (φ : CartierDual R H) :
    hu.toBialgHom φ = pairingMap R u φ := rfl
variable (R H K) in

def pairingMapEquiv : H ⊗[R] K ≃ₗ[R] (CartierDual R H →ₗ[R] K) :=
  TensorProduct.comm R H K ≪≫ₗ tensorEquivHom R K H
omit [Module.Finite R K] [Module.Projective R K] in

@[simp] theorem pairingMapEquiv_apply (u : H ⊗[R] K) : pairingMapEquiv R H K u = pairingMap R u :=
  rfl
omit [Module.Finite R K] [Module.Projective R K] in

@[simp] theorem pairingMap_pairingMapEquiv_symm (f : CartierDual R H →ₗ[R] K) :
    pairingMap R ((pairingMapEquiv R H K).symm f) = f :=
  (pairingMapEquiv R H K).apply_symm_apply f
theorem isBicharacter_iff_exists_bialgHom (u : H ⊗[R] K) : IsBicharacter R u ↔
    ∃ f : CartierDual R H →ₐc[R] K, ∀ φ, f φ = pairingMap R u φ := by
  refine ⟨fun hu => ⟨hu.toBialgHom, fun _ => rfl⟩, fun ⟨f, hf⟩ => ?_⟩
  have h : pairingMap R u = (f : CartierDual R H →ₗ[R] K) := LinearMap.ext fun φ => (hf φ).symm
  refine ⟨(isGroupLikeElem_tensor_iff_mul _).2 ⟨(hf 1).symm.trans (map_one f), fun φ ψ => ?_⟩,
    (isGroupLikeElem_iff_pairingMap u).2 ?_⟩
  · exact (hf _).symm.trans ((map_mul f φ ψ).trans (by rw [hf, hf]; rfl))
  · rw [h]; exact ⟨CoalgHomClass.counit_comp f, CoalgHomClass.map_comp_comul f⟩
variable (R H K) in

def bicharacterEquiv : {u : H ⊗[R] K // IsBicharacter R u} ≃ (CartierDual R H →ₐc[R] K) where
  toFun u := u.2.toBialgHom
  invFun f := ⟨(pairingMapEquiv R H K).symm (f : CartierDual R H →ₗ[R] K),
    (isBicharacter_iff_exists_bialgHom _).2 ⟨f, fun φ => by simp⟩⟩
  left_inv u := Subtype.ext ((pairingMapEquiv R H K).symm_apply_apply u.1)
  right_inv f := BialgHom.ext fun φ => by simp
@[simp] theorem bicharacterEquiv_apply (u : {u : H ⊗[R] K // IsBicharacter R u}) :
    bicharacterEquiv R H K u = u.2.toBialgHom := rfl
@[simp] theorem pairingMap_bicharacterEquiv_symm (f : CartierDual R H →ₐc[R] K)
    (φ : CartierDual R H) : pairingMap R ((bicharacterEquiv R H K).symm f).1 φ = f φ :=
  congr($((bicharacterEquiv R H K).apply_symm_apply f) φ)
theorem pairingMap_comm_bijective_iff (u : H ⊗[R] K) :
    Function.Bijective (pairingMap R (TensorProduct.comm R H K u)) ↔
      Function.Bijective (pairingMap R u) := by
  have h : cartierDualToBidual R H ∘ pairingMap R (TensorProduct.comm R H K u) =
      transpose (pairingMap R u) := funext fun ψ => ext_apply fun φ => apply_pairingMap_comm u φ ψ
  rw [← transpose_bijective_iff (pairingMap R u), ← h,
    Function.Bijective.of_comp_iff' toBidual_bijective]
theorem IsPerfectBicharacter.symm (hu : IsPerfectBicharacter R u) :
    IsPerfectBicharacter R (TensorProduct.comm R H K u) :=
  ⟨hu.toIsBicharacter.symm, (pairingMap_comm_bijective_iff u).2 hu.bijective⟩
def IsPerfectBicharacter.toBialgEquiv (hu : IsPerfectBicharacter R u) : CartierDual R H ≃ₐc[R] K :=
  BialgEquiv.ofBijective hu.toIsBicharacter.toBialgHom hu.bijective
@[simp] theorem IsPerfectBicharacter.toBialgEquiv_apply (hu : IsPerfectBicharacter R u)
    (φ : CartierDual R H) : hu.toBialgEquiv φ = pairingMap R u φ := rfl
theorem IsBicharacter.eq_one_of_isGroupLikeElem (hu : IsBicharacter R u)
    (h : IsGroupLikeElem R u) : u = 1 := by
  refine tensor_eq_of_forall_pair fun φ ψ => ?_
  have h1 := ((isGroupLikeElem_iff_mul u).1 h).2 (toConv (pair R H K (φ ⊗ₜ 1)))
    (toConv (pair R H K (1 ⊗ₜ ψ)))
  rw [← pair_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ofConv_toConv,
    ofConv_toConv, ofConv_toConv, ← apply_tensorToHom u φ 1, ← apply_tensorToHom_comm u 1 ψ,
    ((isGroupLikeElem_tensor_iff_mul _).1 hu.left).1,
    ((isGroupLikeElem_tensor_iff_mul _).1 hu.right).1] at h1
  rw [h1, Algebra.TensorProduct.one_def, pair_tmul_tmul]
end Bicharacter
namespace CartierDual
section Canonical
variable (R H : Type*) [CommSemiring R] [AddCommMonoid H] [Module R H] [Module.Finite R H]
  [Module.Projective R H]
def canonical : H ⊗[R] CartierDual R H :=
  TensorProduct.comm R _ _ ((tensorEquivHom R (CartierDual R H) H).symm LinearMap.id)
variable {R H}
theorem tensorToHom_comm_canonical :
    tensorToHom R _ H (TensorProduct.comm R _ _ (canonical R H)) = LinearMap.id := by
  simp [canonical]
end Canonical
section CanonicalPairing
variable {R H : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H] [IsCocomm R H]
  [Module.Finite R H] [Module.Projective R H]
@[simp] theorem pairingMap_canonical : pairingMap R (canonical R H) = LinearMap.id :=
  tensorToHom_comm_canonical
variable (R H) in

theorem isPerfectBicharacter_canonical : IsPerfectBicharacter R (canonical R H) :=
  ⟨(isBicharacter_iff_exists_bialgHom _).2 ⟨BialgHom.id R _, fun φ => by simp⟩,
    by rw [pairingMap_canonical]; exact Function.bijective_id⟩
end CanonicalPairing
end CartierDual
section PairingMap
open CartierDual
variable {R : Type*} [CommSemiring R]
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
variable (A : Type*) [CommSemiring A] [Algebra R A]
def pairingBaseChange (u : H ⊗[R] K) : (A ⊗[R] H) ⊗[A] (A ⊗[R] K) :=
  AlgebraTensorModule.distribBaseChange R A H K (1 ⊗ₜ u)
variable [Module.Finite R H] [Module.Projective R H] [Module.Finite R K] [Module.Projective R K]
end PairingMap
section Examples
open CartierDual
example (R H : Type) [CommRing R] [CommRing H] [HopfAlgebra R H] [IsCocomm R H]
    [Module.Finite R H] [Module.Projective R H] : CommHopfAlgCat R :=
  have : IsCocomm R (CartierDual R H) := inferInstance
  have : Module.Finite R (CartierDual R H) := inferInstance
  have : Module.Projective R (CartierDual R H) := inferInstance
  CommHopfAlgCat.of R (CartierDual R H)
example : addMonoidAlgebraEquiv ℤ (ZMod 3)
    (antipode ℤ ((addMonoidAlgebraEquiv ℤ (ZMod 3)).symm (Pi.single 1 1))) = Pi.single 2 1 := by
  funext γ
  rw [antipode_addMonoidAlgebra, AlgEquiv.apply_symm_apply]
  revert γ
  decide
theorem canonical_zmod_two_ne_one (R : Type*) [CommRing R] [Nontrivial R] :
    canonical R (AddMonoidAlgebra R (ZMod 2)) ≠ 1 := by
  intro h
  have h1 := pairingMap_canonical (R := R) (H := AddMonoidAlgebra R (ZMod 2))
  rw [h, Algebra.TensorProduct.one_def] at h1
  have h2 := congr(addMonoidAlgebraEquiv R (ZMod 2)
    ($h1 ((addMonoidAlgebraEquiv R (ZMod 2)).symm (Pi.single 0 1))) 1)
  rw [pairingMap_tmul, map_smul, LinearMap.id_apply, AlgEquiv.apply_symm_apply,
    map_one (addMonoidAlgebraEquiv R (ZMod 2)), AddMonoidAlgebra.one_def,
    addMonoidAlgebraEquiv_symm_single] at h2
  simp at h2
example (R : Type) [CommRing R] [Nontrivial R] :
    IsPerfectBicharacter R (canonical R (AddMonoidAlgebra R (ZMod 2))) ∧
      ¬ IsGroupLikeElem R (canonical R (AddMonoidAlgebra R (ZMod 2))) :=
  ⟨isPerfectBicharacter_canonical _ _, fun h => canonical_zmod_two_ne_one R
    ((isPerfectBicharacter_canonical _ _).toIsBicharacter.eq_one_of_isGroupLikeElem h)⟩
example : IsPrimitiveElem (ZMod 2) ((addMonoidAlgebraEquiv (ZMod 2) (ZMod 2)).symm id) := by
  refine tensor_ext fun a b => ?_
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | single g r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | single g' r' =>
      simp [AddMonoidAlgebra.single_mul_single]
      ring
end Examples
end GlobalTheory


