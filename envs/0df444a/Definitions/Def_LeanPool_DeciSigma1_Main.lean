-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Main
-- name    : LeanPool_DeciSigma1_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:20:49.499628+00:00
-- url     : https://prove2.me/theorems/960e173b-4902-4359-ab57-f9de95e7ff97
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1
section Sentences
variable {n : ℕ}
def decideBooleanSentence (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains c) :=
  Full.Logic.decideBooleanSentence c C φ
def decideBooleanSentenceTopFree (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains) :=
  Entailment.Logic.decideBooleanSentence C φ
end Sentences
section Full
variable {n k : ℕ} {V : Type}
abbrev DisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V)) (q : Fin k → V × V) :
    Prop :=
  Full.DisjEntailsIn (fun _ => True) c Γ q
abbrev DisjEntailsReg (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.RegularTop c Γ q
abbrev DisjEntailsFin (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.FiniteTop c Γ q
variable [Fintype V] [DecidableEq V]
def decideDisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntails c Γ q) :=
  Full.decideDisjEntails c Γ q
def decideDisjEntailsReg (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsReg c Γ q) :=
  Full.decideDisjEntailsReg c Γ q
def decideDisjEntailsFin (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsFin c Γ q) :=
  Full.decideDisjEntailsFin c Γ q
end Full
section TopFree
variable {n : ℕ} {V : Type}
abbrev DisjEntailsTopFree {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn (fun _ => True) Γ q
abbrev DisjEntailsTopFreeReg {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsRegularTree Γ q
abbrev DisjEntailsTopFreeFin {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsFiniteTree Γ q
variable [Fintype V] [DecidableEq V] {k : ℕ}
def decideDisjEntailsTopFree (Γ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsTopFree Γ q) :=
  Entailment.decideDisjEntails Γ q
def decideDisjEntailsTopFreeReg (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeReg Γ q) :=
  Entailment.decideDisjEntailsReg Γ q
def decideDisjEntailsTopFreeFin (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeFin Γ q) :=
  Entailment.decideDisjEntailsFin Γ q
end TopFree
def smallHoleBound (σ k N : ℕ) : ℕ := Holes.smallHoleBound σ k N
end DeciSigma1


