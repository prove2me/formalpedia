-- Prove2me | Definitions.Def_LeanPool_Parikh_DFAGrammar
-- name    : LeanPool_Parikh_DFAGrammar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:47:27.982686+00:00
-- url     : https://prove2.me/theorems/224bc18c-ea0f-4477-9a24-87c828537327
-- title:
--   DFAGrammar
-- statement:
--   Definitions and structural lemmas for DFAGrammar, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/DFAGrammar.lean

module
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Prod
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
variable {T : Type*} {σ : Type} [Fintype T] [Fintype σ]
noncomputable abbrev dfaGrammar (M : DFA T σ) : ContextFreeGrammar T := by
  classical
  exact {
    NT := σ
    initial := M.start
    rules := (Finset.univ : Finset (σ × T)).image (fun (q, a) =>
      ⟨q, [.terminal a, .nonterminal (M.step q a)]⟩) ∪
      ((Finset.univ : Finset σ).filter (fun q => q ∈ M.accept)).image (fun q => ⟨q, []⟩)
  }
end Parikh


