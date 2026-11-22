-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
-- name    : LeanPool_DeciSigma1_Satisfiability_Decide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:51:15.811596+00:00
-- url     : https://prove2.me/theorems/363702f6-adf8-4aad-86ef-262fc47aa0a4
-- title:
--   Decide
-- statement:
--   Definitions and structural lemmas for Decide, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_leastShape_sameShape_signedDual
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_signed_flipClosed

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
def lowerAtB (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) : Bool :=
  decide (x ∈ Automata.lowerRun Γ y π)
def upperAtB (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) : Bool :=
  decide (y ∈ Automata.upperRun Γ x π)
def satInfB (Γ : List (LitT n V)) : Bool := !labelClashB Γ
end DeciSigma1.Satisfiability
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
def CycleClash (Γ : List (LitT n V)) : Prop :=
  ∃ π x y, π ≠ [] ∧ LowerAt Γ π x x ∧ Derives Γ x y ∧ UpperAt Γ π y y
namespace PathBounds
end PathBounds
end DeciSigma1.Satisfiability
namespace DeciSigma1.Semantics.FTree
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
def height : FTree n → ℕ
  | .bot | .top => 0
  | .node a => (Finset.univ.sup fun i => (a i).height) + 1
end DeciSigma1.Semantics.FTree
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
end DeciSigma1.Satisfiability
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
end DeciSigma1.Satisfiability
namespace DeciSigma1.Semantics.FTree
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
def truncate : ℕ → Tree n → FTree n
  | 0, t => match t.fn [] with
    | some .bot => .bot
    | some .f => .node fun _ => .top
    | _ => .top
  | d + 1, t =>
    if h : t.fn [] = some .f then
      .node fun i => truncate d (t.branch i h)
    else match t.fn [] with
      | some .bot => .bot
      | _ => .top
end DeciSigma1.Semantics.FTree
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
end DeciSigma1.Satisfiability
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
def cycleClashB (Γ : List (LitT n V)) : Bool :=
  let pairs := derivedPairs Γ
  decide (∃ ρ ∈ Automata.wordsUpTo (α := Fin n) (Fintype.card V * Fintype.card V), ρ ≠ [] ∧
    ∃ x y, lowerAtB Γ ρ x x = true ∧ (x, y) ∈ pairs ∧ upperAtB Γ ρ y y = true)
def Covariant.satFinB (Γ : List (LitT n V)) : Bool := !labelClashB Γ && !cycleClashB Γ
end DeciSigma1.Satisfiability
namespace DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
noncomputable def selectedShape (c : Fin n → Bool) (Γ : List (LitT n V)) :
    (V × Bool) → Semantics.Tree n :=
  select c (leastShape (signed c Γ)) (leastShape_sameShape_signedDual (signed_flipClosed c Γ))
end DeciSigma1.Satisfiability.SignSelection
namespace DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Satisfiability.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
variable [DecidableEq V]
def satFinB (c : Fin n → Bool) (Γ : List (LitT n V)) : Bool := Covariant.satFinB (signed c Γ)
end DeciSigma1.Satisfiability


