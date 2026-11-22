-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Entailment_Decide
-- name    : LeanPool_DeciSigma1_Entailment_Decide
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T15:16:40.039473+00:00
-- url     : https://prove2.me/theorems/b1166274-4307-44c0-aaa2-7d09cf3a30b2
-- title:
--   Decide
-- statement:
--   Definitions and structural lemmas for Decide, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Decide.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
public import Definitions.Def_LeanPool_DeciSigma1_Full_Decide
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_finite_iff_guarded
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_iff_guarded
public import Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_regular_iff
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Entailment
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
def decideOfAllVariables {p : Prop} (r : List V → Prop) (dec : ∀ vs, Decidable (r vs))
    (h : ∀ vs : List V, (∀ v, v ∈ vs) → (p ↔ r vs)) : Decidable p :=
  Quotient.recOnSubsingleton (motive := fun vs : Multiset V => (∀ v, v ∈ vs) → Decidable p)
    Finset.univ.val (fun vs hvs => @decidable_of_iff _ _ (h vs hvs).symm (dec vs))
    Finset.mem_univ_val
def decideDisjEntails (Γ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn (fun _ => True) Γ q) :=
  decideOfAllVariables _
    (fun vs => Full.decideDisjEntails (fun _ => false) (guarded vs Γ) (guardedQueries q))
    (fun _ hvs => disjEntailsIn_iff_guarded hvs Γ q)
def decideDisjEntailsReg (Γ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn IsRegularTree Γ q) :=
  @decidable_of_iff _ _ (disjEntailsIn_regular_iff Γ q).symm (decideDisjEntails Γ q)
def decideDisjEntailsFin (Γ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn IsFiniteTree Γ q) :=
  decideOfAllVariables _
    (fun vs => Full.decideDisjEntailsFin (fun _ => false) (guarded vs Γ) (guardedQueries q))
    (fun _ hvs => disjEntailsIn_finite_iff_guarded hvs Γ q)
end DeciSigma1.Entailment


