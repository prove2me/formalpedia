-- Prove2me | Definitions.Def_LeanPool_Parikh_CompilerTrees
-- name    : LeanPool_Parikh_CompilerTrees
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:52:00.3423+00:00
-- url     : https://prove2.me/theorems/01d217cf-1260-40c8-b300-d3e9b079112d
-- title:
--   Compiler Trees
-- statement:
--   Definitions and structural lemmas for Compiler Trees, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/CompilerTrees.lean

module
public import Definitions.Def_LeanPool_Parikh_CompilerSupport
public import Definitions.Def_LeanPool_Parikh_BoundedEnumeration
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
namespace EncodedGrammar
@[expose] def activeLabels (g : EncodedGrammar) : Finset (Fin (g.extraNonterminalCount + 1)) :=
  {g.initial} ∪ g.rules.toFinset.biUnion (fun r =>
    {r.input} ∪ (r.output.filterMap fun s => match s with
      | .terminal _ => none
      | .nonterminal A => some A).toFinset)
@[expose] def baseTest (g : EncodedGrammar)
    (B : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) : Bool :=
  decide (B.holes = [] ∧ B.root = .nonterminal g.initial) &&
    B.labelPaths.all (fun p => decide p.Nodup)
@[expose] def cycleTest (g : EncodedGrammar)
    (C : ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) : Bool :=
  decide (∃ A, C.holes = [A] ∧ C.root = .nonterminal A ∧ 0 < C.productionSize) &&
    decide (C.height ≤ g.activeLabels.card + 1)
@[expose] def baseTrees (g : EncodedGrammar) :
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :=
  letI := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  ((boundedEnumeration.enumerate g (g.activeLabels.card + 1)).filter g.baseTest).dedup
@[expose] def cycleTrees (g : EncodedGrammar) :
    List (ParseTree (Fin g.terminalCount) (Fin (g.extraNonterminalCount + 1))) :=
  letI := ParseTree.decEq (T := Fin g.terminalCount) (N := Fin (g.extraNonterminalCount + 1))
  ((boundedEnumeration.enumerate g (g.activeLabels.card + 1)).filter g.cycleTest).dedup
end EncodedGrammar
end Parikh


