-- Prove2me | Definitions.Def_LeanPool_PureNock_PaperReference
-- name    : LeanPool_PureNock_PaperReference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:28.623928+00:00
-- url     : https://prove2.me/theorems/8ddbb099-e9b5-481d-a257-40be4718e1d7
-- title:
--   Paper Reference
-- statement:
--   Definitions and structural lemmas for Paper Reference, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean

module
public import Definitions.Def_LeanPool_PureNock_Reference
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
open Noun
def evalPaper : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalPaper fuel subj (.cell b c), evalPaper fuel subj d with
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
             match evalPaper fuel subj b, evalPaper fuel subj c with
             | some sb, some sc => evalPaper fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalPaper fuel subj tail).map wut
    | 4 => (evalPaper fuel subj tail).bind lus
    | 5 => match tail with
           | .cell b c =>
             match evalPaper fuel subj b, evalPaper fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalPaper fuel subj b with
             | some (.atom 0) => evalPaper fuel subj c
             | some (.atom 1) => evalPaper fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalPaper fuel subj b with
             | some sb => evalPaper fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalPaper fuel subj b with
             | some sb => evalPaper fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalPaper fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalPaper fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalPaper fuel subj c, evalPaper fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none
end Nock


