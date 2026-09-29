-- Prove2me | Definitions.Def_mme_coupled_Ctensor_packaging_data
-- name    : mme_coupled_Ctensor_packaging_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T07:57:26.557961+00:00
-- url     : https://prove2.me/theorems/2837bfe3-b98b-4eb8-804b-887055d92f2e
-- title:
--   Shared-Z C-tensor star packaging data
-- statement:
--   This module defines the concrete shared-third-mode packaging for a primary q=6 hash family. For each outer fiber it forms the graded-address component tensors, identifies their common Z space, includes every component into a star with disjoint X and Y modes and shared Z mode, and equips that star with the standard one-H-one basis grading. These definitions expose the actual objects and linear identifications used by the outer extraction, without asserting the later tensor-restriction or volume theorems.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, enhanced 112 construction in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.Dimension.Constructions

open MME PiTensorProduct BigOperators Module

universe u

set_option autoImplicit false

namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]

section SharedZStar

variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {N L G A H : ℕ}

def firstFiberIndex (family : CWQ6PrimaryHashFamily N L G A H) : Fin H :=
  ⟨0, family.hHpos⟩

/-- Use the X/Y words of entry `(a,h)` and the fixed Z word of its outer
fiber. This makes the shared third-mode space definitionally independent
of `h`. -/
def componentAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : CWQ6CoupledAddress N :=
  cwQ6CoupledMixedAddress
    (family.entry (a, h)).1
    (family.entry (a, h)).1
    (family.entry (a, firstFiberIndex family)).1

@[simp] theorem componentAddress_eq_entry
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    componentAddress family a h = (family.entry (a, h)).1 := by
  funext i j
  fin_cases i
  · rfl
  · rfl
  · exact congrFun
      (family.zSameFiber a (firstFiberIndex family) h) j

def componentExactAddress
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : CWQ6ExactCoupledAddress N L G :=
  ⟨componentAddress family a h, by
    rw [componentAddress_eq_entry]
    exact (family.entry (a, h)).2⟩

noncomputable def componentObj
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : TensorObj K 3 :=
  gradedAddressBlock grading (componentAddress family a h)

noncomputable def gradedAddressBlockModeEquiv
    {t : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t) :
    (R : ℕ) → (address address' : Fin 3 → Fin R → Fin t) →
      (i : Fin 3) → (address i = address' i) →
      (gradedAddressBlock G0 address).V i ≃ₗ[K]
        (gradedAddressBlock G0 address').V i
  | 0, _, _, _, _ => LinearEquiv.refl K K
  | R + 1, address, address', i, hi =>
      TensorProduct.congr
        (LinearEquiv.ofEq
          (G0.classOf i (address i 0))
          (G0.classOf i (address' i 0))
          (by rw [congrFun hi 0]))
        (gradedAddressBlockModeEquiv G0 R
          (fun i' j => address i' j.succ)
          (fun i' j => address' i' j.succ) i (by
            funext j
            exact congrFun hi j.succ))

noncomputable def componentZEquiv
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    (componentObj grading family a h).V 2 ≃ₗ[K]
      (componentObj grading family a (firstFiberIndex family)).V 2 := by
  exact gradedAddressBlockModeEquiv grading (2 * N)
    (componentAddress family a h)
    (componentAddress family a (firstFiberIndex family)) 2 (by rfl)

@[reducible] def starSpace
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : Fin 3 → Type u
  | 0 => ∀ h : Fin H, (componentObj grading family a h).V 0
  | 1 => ∀ h : Fin H, (componentObj grading family a h).V 1
  | 2 => (componentObj grading family a (firstFiberIndex family)).V 2

noncomputable instance starSpaceAddCommGroup
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    AddCommGroup (starSpace grading family a i) :=
  match i with
  | 0 => Pi.addCommGroup
  | 1 => Pi.addCommGroup
  | 2 =>
      (componentObj grading family a (firstFiberIndex family)).acg 2

noncomputable instance starSpaceModule
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Module K (starSpace grading family a i) :=
  match i with
  | 0 => Pi.module _ _ _
  | 1 => Pi.module _ _ _
  | 2 =>
      (componentObj grading family a (firstFiberIndex family)).mod 2

instance starSpaceFinite
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Module.Finite K (starSpace grading family a i) :=
  match i with
  | 0 => inferInstanceAs
      (Module.Finite K
        (∀ h : Fin H, (componentObj grading family a h).V 0))
  | 1 => inferInstanceAs
      (Module.Finite K
        (∀ h : Fin H, (componentObj grading family a h).V 1))
  | 2 =>
      (componentObj grading family a (firstFiberIndex family)).fin 2

/-- Include a graded address block back into its ambient tensor power. -/
noncomputable def gradedAddressEmbed
    {t : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t) :
    (R : ℕ) → (address : Fin 3 → Fin R → Fin t) → (i : Fin 3) →
      (gradedAddressBlock G0 address).V i →ₗ[K] (X.kronPow R).V i
  | 0, _, _ => LinearMap.id
  | R + 1, address, i =>
      TensorProduct.map
        (G0.classOf i (address i 0)).subtype
        (gradedAddressEmbed G0 R (fun i' j => address i' j.succ) i)

noncomputable def componentInclusion
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
    (componentObj grading family a h).V i →ₗ[K]
      starSpace grading family a i
  | 0 => LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h
  | 1 => LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h
  | 2 => (componentZEquiv grading family a h).toLinearMap

noncomputable def starObj
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : TensorObj K 3 where
  V := starSpace grading family a
  t := ∑ h : Fin H,
    PiTensorProduct.map (componentInclusion grading family a h)
      (componentObj grading family a h).t

@[reducible] def starBasisIndex
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : Fin 3 → Type
  | 0 => Σ h : Fin H,
      Fin (Module.finrank K ((componentObj grading family a h).V 0))
  | 1 => Σ h : Fin H,
      Fin (Module.finrank K ((componentObj grading family a h).V 1))
  | 2 => Fin (Module.finrank K
      ((componentObj grading family a (firstFiberIndex family)).V 2))

private instance starBasisIndexFinite
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Finite (starBasisIndex grading family a i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

private noncomputable instance starBasisIndexDecidableEq
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    DecidableEq (starBasisIndex grading family a i) := by
  exact match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

noncomputable def starBasis
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (i : Fin 3) :
    Basis (starBasisIndex grading family a i) K
      ((starObj grading family a).V i) := by
  exact match i with
  | 0 => Pi.basis (fun h =>
      Module.finBasis K ((componentObj grading family a h).V 0))
  | 1 => Pi.basis (fun h =>
      Module.finBasis K ((componentObj grading family a h).V 1))
  | 2 => Module.finBasis K
      ((componentObj grading family a (firstFiberIndex family)).V 2)

def starBasisGrade
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : ∀ i : Fin 3,
      starBasisIndex grading family a i → Fin (H + 1)
  | 0, j => Fin.castSucc j.1
  | 1, j => Fin.castSucc j.1
  | 2, _ => Fin.last H

noncomputable def starGrading
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) : (starObj grading family a).TypeGrading (H + 1) where
  decomp i := cwBasisGrade (starBasis grading family a i)
    (starBasisGrade grading family a i)
  is_internal i := cwBasisGrade_isInternal
    (starBasis grading family a i)
    (starBasisGrade grading family a i)

end SharedZStar

end CoupledCTensorPackaging


