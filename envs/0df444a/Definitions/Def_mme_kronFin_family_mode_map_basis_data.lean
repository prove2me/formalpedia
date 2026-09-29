-- Prove2me | Definitions.Def_mme_kronFin_family_mode_map_basis_data
-- name    : mme_kronFin_family_mode_map_basis_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T07:51:51.650653+00:00
-- url     : https://prove2.me/theorems/136b8c92-1f29-4d04-8c91-a6bb23f55329
-- title:
--   Factorwise maps on finite Kronecker families with exact basis semantics
-- statement:
--   Given an ordered finite family of tensors and one mode map on each factor, this module tensors the maps in the same recursive order as the finite Kronecker product. It proves three coordinate-level properties: factorwise tensor preservation implies preservation of the whole product tensor; prescribed images of factor basis vectors give the exact image of every product-basis word; and killing one selected factor basis vector kills the entire product word. These are the finite-family assembly rules used to apply all fifteen DWZ component projections simultaneously.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6 and Table 2; multilinear factorwise projection infrastructure for the Prove2Me 2.3747 mission.

import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_kronFin_mode_pi_basis

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.TensorObj

set_option linter.unusedVariables false in
/-- Tensor a possibly noninvertible mode map over every factor of an ordered
finite Kronecker product. -/
noncomputable def kronFinFamilyModeMap
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d)
      (f : ∀ r i, (X r).V i →ₗ[K] (Y r).V i) (i : Fin d),
      (TensorObj.kronFin n X).V i →ₗ[K]
        (TensorObj.kronFin n Y).V i
  | 0, _, _, _, _ => LinearMap.id
  | n + 1, X, Y, f, i =>
      TensorProduct.map (f 0 i)
        (kronFinFamilyModeMap n
          (fun r : Fin n ↦ X r.succ)
          (fun r : Fin n ↦ Y r.succ)
          (fun r j ↦ f r.succ j) i)

/-- Factorwise tensor preservation implies preservation by the recursively
tensored family map. -/
theorem kronFinFamilyModeMap_preserves_tensor
    {K : Type u} [Field K] {d n : ℕ}
    (X Y : Fin n → TensorObj K d)
    (f : ∀ r i, (X r).V i →ₗ[K] (Y r).V i)
    (hf : ∀ r,
      PiTensorProduct.map (f r) (X r).t = (Y r).t) :
    PiTensorProduct.map (kronFinFamilyModeMap n X Y f)
        (TensorObj.kronFin n X).t =
      (TensorObj.kronFin n Y).t := by
  induction n with
  | zero =>
      change PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id)
          (TensorObj.oneObj (K := K) (d := d)).t = _
      rw [PiTensorProduct.map_id]
      rfl
  | succ n ih =>
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map (f 0 i)
            (kronFinFamilyModeMap n
              (fun r : Fin n ↦ X r.succ)
              (fun r : Fin n ↦ Y r.succ)
              (fun r j ↦ f r.succ j) i))
          (interchange (X 0).t
            (TensorObj.kronFin n (fun r : Fin n ↦ X r.succ)).t) = _
      rw [TensorObj.TypeGrading.kronMap_interchange, hf 0]
      rw [ih (fun r : Fin n ↦ X r.succ)
        (fun r : Fin n ↦ Y r.succ)
        (fun r j ↦ f r.succ j) (fun r ↦ hf r.succ)]
      rfl

private theorem kronFinModePiBasis_succ_apply_family_map
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 1) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, index r) :
    TensorObj.kronFinModePiBasis (n + 1) T i b w =
      (b 0 (w 0)) ⊗ₜ[K]
        (TensorObj.kronFinModePiBasis n
          (fun r : Fin n ↦ T r.succ) i
          (fun r ↦ b r.succ) (fun r ↦ w r.succ)) := by
  change (((b 0).tensorProduct
    (TensorObj.kronFinModePiBasis n
      (fun r : Fin n ↦ T r.succ) i
      (fun r ↦ b r.succ))).reindex (Fin.consEquiv index)) w = _
  rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
    Module.Basis.tensorProduct_apply]
  rfl

/-- If every factor map sends a chosen basis vector to its labelled target
basis vector, the family map has the corresponding exact product-basis
action. -/
theorem kronFinFamilyModeMap_basis
    {K : Type u} [Field K] {d n : ℕ}
    (X Y : Fin n → TensorObj K d) (i : Fin d)
    {indexX indexY : Fin n → Type u}
    (bX : ∀ r, Basis (indexX r) K ((X r).V i))
    (bY : ∀ r, Basis (indexY r) K ((Y r).V i))
    (f : ∀ r j, (X r).V j →ₗ[K] (Y r).V j)
    (label : ∀ r, indexX r → indexY r)
    (hf : ∀ r x, f r i (bX r x) = bY r (label r x))
    (w : ∀ r, indexX r) :
    kronFinFamilyModeMap n X Y f i
        (TensorObj.kronFinModePiBasis n X i bX w) =
      TensorObj.kronFinModePiBasis n Y i bY
        (fun r ↦ label r (w r)) := by
  induction n with
  | zero =>
      let _uX : Unique (∀ r : Fin 0, indexX r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by funext r; exact r.elim0 }
      let _uY : Unique (∀ r : Fin 0, indexY r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by funext r; exact r.elim0 }
      simp only [kronFinFamilyModeMap,
        TensorObj.kronFinModePiBasis]
      calc
        _ = (1 : K) := by
          exact Module.Basis.singleton_apply _ K w
        _ = _ := by
          symm
          exact Module.Basis.singleton_apply _ K _
  | succ n ih =>
      rw [kronFinModePiBasis_succ_apply_family_map,
        kronFinModePiBasis_succ_apply_family_map]
      change TensorProduct.map (f 0 i)
          (kronFinFamilyModeMap n
            (fun r : Fin n ↦ X r.succ)
            (fun r : Fin n ↦ Y r.succ)
            (fun r j ↦ f r.succ j) i)
          ((bX 0 (w 0)) ⊗ₜ[K]
            TensorObj.kronFinModePiBasis n
              (fun r : Fin n ↦ X r.succ) i
              (fun r ↦ bX r.succ) (fun r ↦ w r.succ)) = _
      rw [TensorProduct.map_tmul, hf 0]
      rw [ih (fun r : Fin n ↦ X r.succ)
        (fun r : Fin n ↦ Y r.succ)
        (fun r ↦ bX r.succ) (fun r ↦ bY r.succ)
        (fun r j ↦ f r.succ j) (fun r ↦ label r.succ)
        (fun r x ↦ hf r.succ x) (fun r ↦ w r.succ)]

/-- If one selected factor basis vector is killed, the entire product-basis
word is killed by the family map. -/
theorem kronFinFamilyModeMap_basis_eq_zero_of_exists
    {K : Type u} [Field K] {d n : ℕ}
    (X Y : Fin n → TensorObj K d) (i : Fin d)
    {indexX : Fin n → Type u}
    (bX : ∀ r, Basis (indexX r) K ((X r).V i))
    (f : ∀ r j, (X r).V j →ₗ[K] (Y r).V j)
    (w : ∀ r, indexX r)
    (hzero : ∃ r, f r i (bX r (w r)) = 0) :
    kronFinFamilyModeMap n X Y f i
        (TensorObj.kronFinModePiBasis n X i bX w) = 0 := by
  induction n with
  | zero =>
      rcases hzero with ⟨r, _⟩
      exact r.elim0
  | succ n ih =>
      rw [kronFinModePiBasis_succ_apply_family_map]
      change TensorProduct.map (f 0 i)
          (kronFinFamilyModeMap n
            (fun r : Fin n ↦ X r.succ)
            (fun r : Fin n ↦ Y r.succ)
            (fun r j ↦ f r.succ j) i)
          ((bX 0 (w 0)) ⊗ₜ[K]
            TensorObj.kronFinModePiBasis n
              (fun r : Fin n ↦ X r.succ) i
              (fun r ↦ bX r.succ) (fun r ↦ w r.succ)) = 0
      rw [TensorProduct.map_tmul]
      rcases hzero with ⟨r, hr⟩
      revert hr
      refine Fin.cases ?_ (fun q ↦ ?_) r
      · intro hr0
        rw [hr0, zero_tmul]
      · intro hrq
        have htail := ih
            (fun r : Fin n ↦ X r.succ)
            (fun r : Fin n ↦ Y r.succ)
            (fun r ↦ bX r.succ)
            (fun r j ↦ f r.succ j)
            (fun r ↦ w r.succ) ⟨q, hrq⟩
        rw [htail, tmul_zero]

end MME.TensorObj


