-- Prove2me | Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
-- name    : LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:57:08.162844+00:00
-- url     : https://prove2.me/theorems/6b8b5769-a5a7-4e11-8093-55cebf75b021
-- title:
--   CNFOrder
-- statement:
--   Definitions and structural lemmas for CNFOrder, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OrderClosures
open Set
universe u v
section OrdinalConstruction
def cnfExtensionLT (ζ ζ' : Ordinal.{u}) : Prop :=
  ∃ (pre tail : List (Ordinal.{u} × Ordinal.{u})) (β c γ d : Ordinal.{u}),
    Ordinal.CNF Ordinal.omega0 ζ = pre ++ (β, c) :: tail ∧
      Ordinal.CNF Ordinal.omega0 ζ' = pre ++ [(γ, d)] ∧
      ((γ = β ∧ c < d) ∨
        (β < γ ∧
          (pre = [] ∨ ∃ δ e, pre.getLast? = some (δ, e) ∧ γ < δ)))
def cnfExtensionLE (ζ ζ' : Ordinal.{u}) : Prop := ζ = ζ' ∨ cnfExtensionLT ζ ζ'
def CNFStep (pre : List (Ordinal.{u} × Ordinal.{u}))
    (x y : Ordinal.{u} × Ordinal.{u}) : Prop :=
  (y.1 = x.1 ∧ x.2 < y.2) ∨
    (x.1 < y.1 ∧
      (pre = [] ∨ ∃ z, pre.getLast? = some z ∧ y.1 < z.1))
def CNFListLT (l l' : List (Ordinal.{u} × Ordinal.{u})) : Prop :=
  ∃ (pre tail : List (Ordinal.{u} × Ordinal.{u}))
    (x y : Ordinal.{u} × Ordinal.{u}),
    l = pre ++ x :: tail ∧ l' = pre ++ [y] ∧ CNFStep pre x y
noncomputable def cnfValue
    (l : List (Ordinal.{u} × Ordinal.{u})) : Ordinal.{u} :=
  l.foldr (fun p r ↦ Ordinal.omega0 ^ p.1 * p.2 + r) 0
noncomputable def cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u}) :
    List (Ordinal.{u} × Ordinal.{u}) :=
  match l with
  | [] => [(γ, d)]
  | (δ, e) :: tail =>
      if γ < δ then (δ, e) :: cnfAddMonomial tail γ d
      else if γ = δ then [(δ, e + d)] else [(γ, d)]
end OrdinalConstruction
end OrderClosures


