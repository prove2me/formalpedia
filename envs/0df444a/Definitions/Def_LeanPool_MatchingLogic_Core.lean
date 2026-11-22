-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Core
-- name    : LeanPool_MatchingLogic_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:13:53.184574+00:00
-- url     : https://prove2.me/theorems/fb4f9863-f3f2-4724-8bc9-0630c4719be7
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Core.lean

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
universe u
structure Signature where
  /-- The type of operation symbols. -/
  Sym : Type
  /-- The number of arguments of each operation symbol. -/
  arity : Sym → Nat
variable (S : Signature) (Var : Type)
inductive Pattern where
  | var : Var → Pattern
  | app : (σ : S.Sym) → (Fin (S.arity σ) → Pattern) → Pattern
  | imp : Pattern → Pattern → Pattern
  | bot : Pattern
  | ex : Var → Pattern → Pattern
namespace Pattern
variable {S Var}
abbrev nt (φ : Pattern S Var) : Pattern S Var := imp φ bot
abbrev tp : Pattern S Var := imp bot bot
abbrev or (φ ψ : Pattern S Var) : Pattern S Var := imp (nt φ) ψ
abbrev and (φ ψ : Pattern S Var) : Pattern S Var := nt (imp φ (nt ψ))
abbrev al (x : Var) (φ : Pattern S Var) : Pattern S Var := nt (ex x (nt φ))
end Pattern
structure Model (S : Signature) where
  /-- The type of points in the model. -/
  carrier : Type
  nonempty : Nonempty carrier
  /-- The set-valued interpretation of each operation symbol. -/
  interp : (σ : S.Sym) → (Fin (S.arity σ) → carrier) → Set carrier
attribute [instance] Model.nonempty
namespace Model
variable {S : Signature}
def app (M : Model S) (σ : S.Sym) (A : Fin (S.arity σ) → Set M.carrier) :
    Set M.carrier :=
  {u | ∃ a : Fin (S.arity σ) → M.carrier, (∀ i, a i ∈ A i) ∧ u ∈ M.interp σ a}
def denote {Var : Type} [DecidableEq Var] (M : Model S) :
    (Var → M.carrier) → Pattern S Var → Set M.carrier
  | ρ, .var x => {ρ x}
  | _, .bot => ∅
  | ρ, .app σ f => M.app σ (fun i => M.denote ρ (f i))
  | ρ, .imp φ ψ => (M.denote ρ φ)ᶜ ∪ M.denote ρ ψ
  | ρ, .ex x φ => ⋃ a : M.carrier, M.denote (Function.update ρ x a) φ
end Model
section Denote
variable {S : Signature} {Var : Type} [DecidableEq Var] (M : Model S)
end Denote
namespace Model
section Reach
variable {S : Signature} (M : Model S)
def Step (u v : M.carrier) : Prop :=
  ∃ (σ : S.Sym) (a : Fin (S.arity σ) → M.carrier) (i : Fin (S.arity σ)),
    u ∈ M.interp σ a ∧ v = a i
def BackwardClosed (C : Set M.carrier) : Prop :=
  ∀ ⦃u⦄, u ∈ C → ∀ ⦃v⦄, M.Step u v → v ∈ C
end Reach
end Model
end MatchingLogic


