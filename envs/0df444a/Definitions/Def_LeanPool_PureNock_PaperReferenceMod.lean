-- Prove2me | Definitions.Def_LeanPool_PureNock_PaperReferenceMod
-- name    : LeanPool_PureNock_PaperReferenceMod
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:48.882293+00:00
-- url     : https://prove2.me/theorems/c54f2821-e06e-468f-a0cd-203a29198007
-- title:
--   Paper Reference Mod
-- statement:
--   Definitions and structural lemmas for Paper Reference Mod, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
open Noun
def evalPaperMod (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalPaperMod q fuel subj (.cell b c), evalPaperMod q fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b, evalPaperMod q fuel subj c with
             | some sb, some sc => evalPaperMod q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalPaperMod q fuel subj tail).map wut
    | 4 => (evalPaperMod q fuel subj tail).bind (FieldEmbedding.lusFBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b, evalPaperMod q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalPaperMod q fuel subj b with
             | some (.atom 0) => evalPaperMod q fuel subj c
             | some (.atom 1) => evalPaperMod q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b with
             | some sb => evalPaperMod q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalPaperMod q fuel subj b with
             | some sb => evalPaperMod q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalPaperMod q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalPaperMod q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalPaperMod q fuel subj c, evalPaperMod q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none
def evalPaperModTop (q : Nat) (subj formula : Noun) : Option Noun := evalPaperMod q 100000 subj
  formula
end Nock


