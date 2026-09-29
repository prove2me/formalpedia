-- Prove2me | Definitions.Def_mme_kronFin_rec_groups_data
-- name    : mme_kronFin_rec_groups_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T06:56:51.975321+00:00
-- url     : https://prove2.me/theorems/48eb2036-f5a6-4de8-8c4b-705e6a2d8ef4
-- title:
--   Exact recursive data for grouping heterogeneous Kronecker factors
-- statement:
--   Given finitely many tensor types and a multiplicity for each type, list the corresponding factors in consecutive groups. This package defines the recursion-aligned total length, flat factor family, canonical modewise reassociation, split dependent words, and the matching dependent factor bases. It is the coordinate-level data needed to pass from retained source-position words to the fifteen grouped component powers of the DWZ Table-2 standard tensor.
--
--   The construction records exact basis coordinates; it does not replace the source tensor by an abstract isomorphism class.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and the Table-2 component regrouping in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_rec_append_data

open MME TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.TensorObj

def recGroupLength : (k : ℕ) → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, count =>
      recAppendLength (count 0)
        (recGroupLength k (fun s ↦ count s.succ))

def recGroupFamily {alpha : Type u} :
    ∀ (k : ℕ) (count : Fin k → ℕ),
      (Fin k → alpha) → Fin (recGroupLength k count) → alpha
  | 0, _, _ => fun r ↦ r.elim0
  | k + 1, count, X =>
      recAppendFamily (count 0)
        (recGroupLength k (fun s ↦ count s.succ))
        (fun _ ↦ X 0)
        (recGroupFamily k (fun s ↦ count s.succ)
          (fun s ↦ X s.succ))

noncomputable def kronFinRecGroupsModeEquiv
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (k : ℕ) (count : Fin k → ℕ)
      (X : Fin k → TensorObj K d) (i : Fin d),
      (TensorObj.kronFin (recGroupLength k count)
        (recGroupFamily k count X)).V i ≃ₗ[K]
      (TensorObj.kronFin k (fun s ↦
        TensorObj.kronFin (count s) (fun _ ↦ X s))).V i
  | 0, _, _, _ => LinearEquiv.refl K _
  | k + 1, count, X, i => by
      let tailCount : Fin k → ℕ := fun s ↦ count s.succ
      let tailX : Fin k → TensorObj K d := fun s ↦ X s.succ
      let first : Fin (count 0) → TensorObj K d := fun _ ↦ X 0
      let flatTail := recGroupFamily k tailCount tailX
      let Eappend := kronFinRecAppendModeEquiv
        (count 0) (recGroupLength k tailCount) first flatTail i
      let Etail := kronFinRecGroupsModeEquiv k tailCount tailX i
      exact Eappend.trans
        (TensorProduct.congr
          (LinearEquiv.refl K
            ((TensorObj.kronFin (count 0) first).V i)) Etail)

def recGroupWord :
    ∀ {k : ℕ} {count : Fin k → ℕ}
      {index : Fin k → Type u},
      (∀ r, recGroupFamily k count index r) →
        ∀ s, Fin (count s) → index s
  | 0, _, _, _ => fun s ↦ s.elim0
  | _ + 1, _, _, w =>
      Fin.cons (recAppendLeftWord w)
        (recGroupWord (recAppendRightWord w))

noncomputable def recGroupBasisFamily
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (k : ℕ) (count : Fin k → ℕ)
      (X : Fin k → TensorObj K d) (i : Fin d)
      (index : Fin k → Type u),
      (∀ s, Basis (index s) K ((X s).V i)) →
      ∀ r, Basis (recGroupFamily k count index r) K
        ((recGroupFamily k count X r).V i)
  | 0, _, _, _, _, _ => fun r ↦ r.elim0
  | k + 1, count, X, i, index, b =>
      recAppendBasisFamily (count 0)
        (recGroupLength k (fun s ↦ count s.succ))
        (fun _ ↦ X 0)
        (recGroupFamily k (fun s ↦ count s.succ)
          (fun s ↦ X s.succ)) i
        (fun _ ↦ index 0)
        (recGroupFamily k (fun s ↦ count s.succ)
          (fun s ↦ index s.succ))
        (fun _ ↦ b 0)
        (recGroupBasisFamily k (fun s ↦ count s.succ)
          (fun s ↦ X s.succ) i (fun s ↦ index s.succ)
          (fun s ↦ b s.succ))

end MME.TensorObj


