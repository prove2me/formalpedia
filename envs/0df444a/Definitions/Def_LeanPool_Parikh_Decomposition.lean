-- Prove2me | Definitions.Def_LeanPool_Parikh_Decomposition
-- name    : LeanPool_Parikh_Decomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:48:45.680606+00:00
-- url     : https://prove2.me/theorems/80b3f9fb-6603-418f-839b-3fa400a79279
-- title:
--   Decomposition
-- statement:
--   Definitions and structural lemmas for Decomposition, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
variable {T : Type*}
@[expose] def Inserts (g : ContextFreeGrammar T) (t C t' : ParseTree T g.NT) : Prop :=
  Complete g t ∧ Complete g t' ∧ ∃ A, Cycle g C A ∧
    ∃ q u, t.subtree q = some u ∧ u.root = .nonterminal A ∧
      t.replaceAt q (C.plug u) = some t'
inductive InsertionSequence (g : ContextFreeGrammar T) :
    ParseTree T g.NT → List (ParseTree T g.NT) → ParseTree T g.NT → Prop where
  | nil (t) : InsertionSequence g t [] t
  | cons {t C next Cs final} (step : Inserts g t C next)
      (rest : InsertionSequence g next Cs final) : InsertionSequence g t (C :: Cs) final
@[expose] def IsBase (g : ContextFreeGrammar T) (B : ParseTree T g.NT) : Prop :=
  Complete g B ∧ B.root = .nonterminal g.initial ∧ B.Simple
@[expose] def IsBoundedCycle (g : ContextFreeGrammar T) (C : ParseTree T g.NT) : Prop :=
  (∃ A, Cycle g C A) ∧ C.height ≤ (activeNonterminals g).card + 1
end Parikh


