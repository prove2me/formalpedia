-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
-- name    : LeanPool_DeciSigma1_Semantics_Classes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:33:37.634815+00:00
-- url     : https://prove2.me/theorems/45df39f4-4bd4-407b-b324-2dfacbc8c879
-- title:
--   Classes
-- statement:
--   Definitions and structural lemmas for Classes, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}
abbrev Language (n : ℕ) := Set (List (Fin n))
def concat (A B : Language n) : Language n := {w | ∃ a ∈ A, ∃ b ∈ B, a ++ b = w}
abbrev residual (L : Language n) (u : List (Fin n)) : Language n := {v | u ++ v ∈ L}
def IsRegular (L : Language n) : Prop := (Set.range (residual L)).Finite
end DeciSigma1.Semantics
namespace DeciSigma1.Semantics.Characterization
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
def domain (t : Tree n) : Set (List (Fin n)) := {π | (t.fn π).isSome}
def subtrees (t : Tree n) : Set (Tree n) := {u | ∃ π, t.subtree π = some u}
end DeciSigma1.Semantics.Characterization


