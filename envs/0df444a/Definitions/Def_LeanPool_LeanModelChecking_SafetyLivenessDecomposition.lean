-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking_SafetyLivenessDecomposition
-- name    : LeanPool_LeanModelChecking_SafetyLivenessDecomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:43:18.764147+00:00
-- url     : https://prove2.me/theorems/7a6b1f63-cce0-4c1c-a139-f9d05964a3ea
-- title:
--   Safety Liveness Decomposition
-- statement:
--   Definitions and structural lemmas for Safety Liveness Decomposition, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/SafetyLivenessDecomposition.lean

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Finiteness.Attr
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SafetyLivenessDecomposition
abbrev InfWord T := ℕ → T
abbrev FinWord T := List T
def FinWord.append {T} (a : FinWord T) (b : InfWord T) : InfWord T :=
  fun i =>
    if _ : i < a.length then a[i]
    else b (i - a.length)
def InfWord.slice {T} (w : InfWord T) (k : ℕ) : FinWord T :=
  List.ofFn (fun (i : Fin k) => w i)
abbrev Property T := Set (InfWord T)
def SafetyProp {T} (P : Property T) :=
  ∀ (σ : InfWord T),
  σ ∉ P →
  ∃ (i : ℕ),
  ∀ (β : InfWord T),
  (σ.slice i).append β ∉ P
def LivenessProp {T} (P : Property T) :=
  ∀ (α : FinWord T),
  ∃ (β : InfWord T),
  α.append β ∈ P
section Auxiliary
variable {T : Type u}
end Auxiliary
end SafetyLivenessDecomposition


