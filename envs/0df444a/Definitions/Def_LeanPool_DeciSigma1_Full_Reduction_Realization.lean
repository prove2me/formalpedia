-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
-- name    : LeanPool_DeciSigma1_Full_Reduction_Realization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:05:26.325027+00:00
-- url     : https://prove2.me/theorems/250dafd4-11ab-4d6a-98e9-c67c6f982449
-- title:
--   Realization
-- statement:
--   Definitions and structural lemmas for Realization, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
def Event (c : Fin n → Bool) (Γ : List (LitT n V)) (a b : Closure.Config n V) : Prop :=
  ∃ i ≤ a.2.2.length, ∃ j ≤ b.2.2.length,
    (a.2.2.drop i).IsPrefix (b.2.2.drop j) ∧
    (Automata.upperRun (signed c Γ) (a.1, a.2.1) (a.2.2.take i) ∩
      Automata.lowerRun (signed c Γ) (b.1, b.2.1) (b.2.2.take j)).Nonempty
def Collision (c : Fin n → Bool) (Γ : List (LitT n V)) (a b : Closure.Config n V) : Prop :=
  ∃ i ≤ a.2.2.length, ∃ j ≤ b.2.2.length,
    ((a.2.2.drop i).IsPrefix (b.2.2.drop j) ∨
      (b.2.2.drop j).IsPrefix (a.2.2.drop i)) ∧
    (Automata.upperRun (signed c Γ) (a.1, a.2.1) (a.2.2.take i) ∩
      (Automata.upperRun (signed c Γ) (b.1, b.2.1) (b.2.2.take j)).map
        flipEmb).Nonempty
def CrossClash (c : Fin n → Bool) (Γ : List (LitT n V)) (a b : Closure.Config n V) : Prop :=
  ∃ v s w, Reach c Γ a (v, s, w) ∧ Reach c Γ b (v, !s, w)
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
end DeciSigma1.Full.Reduction
namespace DeciSigma1.Full.Reduction
open DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
end DeciSigma1.Full.Reduction
namespace DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
def SeedConsistency (c : Fin n → Bool) (Γ : List (LitT n V))
    (A B : Fin k → Closure.Config n V) : Prop :=
  (∀ i, ¬ HasUnaryObstruction c Γ ((A i).1, (A i).2.1) (A i).2.2 ∧
    ¬ ∃ s t, SelfCollisionEvent c Γ ((A i).1, (A i).2.1) (A i).2.2 s t) ∧
  (∀ i, B i ∉ leastClosure c Γ) ∧
  (∀ j i, ¬ Event c Γ (A j) (B i)) ∧
  (∀ j i, j ≠ i → ¬ Collision c Γ (A j) (A i))
def TerminalRootConditions (c : Fin n → Bool) (Γ : List (LitT n V))
    (A B : Fin k → Closure.Config n V) : Prop :=
  (∀ i, Disjoint
    (Automata.upperRun (signed c Γ) ((A i).1, (A i).2.1) (A i).2.2)
    (forbiddenPredecessors c Γ)) ∧
  (∀ i, B i ∉ leastClosure c Γ ∧ flipC (A i) ∉ leastClosure c Γ) ∧
  (∀ j i, ¬ Event c Γ (A j) (B i) ∧
    ¬ Event c Γ (A j) (flipC (A i)))
def Realizes (c : Fin n → Bool) (Γ : List (LitT n V))
    (A B : Fin k → Closure.Config n V) : Prop :=
  ∃ ρ, SatT c ρ Γ ∧ ∀ i,
    A i ∈ configSet c ρ ∧ B i ∉ configSet c ρ
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
end DeciSigma1.Full.Reduction


