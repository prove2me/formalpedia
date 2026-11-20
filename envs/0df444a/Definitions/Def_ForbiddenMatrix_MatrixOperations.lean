-- Prove2me | Definitions.Def_ForbiddenMatrix_MatrixOperations
-- name    : ForbiddenMatrix_MatrixOperations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:56:47.166741+00:00
-- url     : https://prove2.me/theorems/1e062834-1035-4d06-be91-49add5c28f79
-- title:
--   Matrix Operations
-- statement:
--   Definitions and structural lemmas for Matrix Operations, from Yaël Dillies and the Forbidden Matrix contributors's pinned Forbidden-matrix containment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/MatrixOperations.lean

module
public import Mathlib.Order.OrderDual
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open OrderDual
variable {α β γ δ : Type*}
def L'' : Fin 2 → Fin 2 → Prop :=
  ![
    ![false, true],
    ![true, true]
  ]
def A' : Fin 2 → Fin 1 → Prop :=
  ![![true], ![false]]
def B' : Fin 2 → (Fin 1) → Prop :=
  ![![false], ![true]]
abbrev tranpose (M : α → β → Prop) : β → α → Prop := fun x y ↦ M y x
def rev_all_rows (M : α → β → Prop) : α → βᵒᵈ → Prop := fun i ↦ M i ∘ ofDual
def rot_cw (M : α → β → Prop) : β → αᵒᵈ → Prop := (rev_all_rows ∘ tranpose) M
def rev_all_rows_via_list {n : ℕ} (M : α → Fin n → Prop) : α → Fin n → Prop := fun a i ↦ M a i.rev
def L : Fin 2 → Fin 2 → Prop :=
  ![
    ![true, false],
    ![true, true]
   ]
def L' : Fin 2 → Fin 2 → Prop :=
  ![
    ![true, true],
    ![true, false]
  ]
def X : (Fin 3)ᵒᵈ → Bool := ![true, false, false] ∘ ofDual
def Y : Fin 3 → Bool := ![false, false, true]
def A : Fin 1 → Fin 2 → Prop := ![![true, false]]
def B : Fin 1 → (Fin 2)ᵒᵈ → Prop := ![![true, false]∘ ofDual]
def C : Fin 1 → Fin 2 → Prop := ![![false, true]]
example : (fun i ↦ C i ∘ Fin.revOrderIso ∘ toDual) = fun i ↦ rev_all_rows A i ∘ toDual := by
  ext i j; fin_cases i; fin_cases j <;> simp [rev_all_rows, A, C, Fin.rev]
def a : Fin 2 → Bool := ![true, false]
def c : Fin 2 → Bool := ![false, true]
def b : (Fin 2)ᵒᵈ → Bool := ![false, true] ∘ ofDual
example : a ∘ Fin.revOrderIso = b := by
  ext x
  --have := OrderDual.toDual.surjective x
  --obtain ⟨y, h⟩ :=this
  --rw [← h]
  -- one line version of above
  obtain ⟨y, rfl⟩ := OrderDual.toDual.surjective x
  fin_cases y <;> rfl
example : a ∘ Fin.revOrderIso ∘ toDual = b ∘ toDual := by
  ext x
  fin_cases x <;> rfl
example : A = rev_all_rows_via_list C := by
  ext a b; fin_cases a; fin_cases b <;> simp [A, C, rev_all_rows_via_list]


