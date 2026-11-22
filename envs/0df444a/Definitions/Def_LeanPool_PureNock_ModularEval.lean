-- Prove2me | Definitions.Def_LeanPool_PureNock_ModularEval
-- name    : LeanPool_PureNock_ModularEval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:32.453264+00:00
-- url     : https://prove2.me/theorems/317792ab-55e5-4d4b-8cea-4732ce3ba163
-- title:
--   Modular Eval
-- statement:
--   Definitions and structural lemmas for Modular Eval, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock.FieldEmbedding
open Nock Nock.Noun
def BoundedBy (q : ℕ) : Noun → Prop
  | .atom n   => n < q
  | .cell l r => BoundedBy q l ∧ BoundedBy q r
def lusFBy (q : ℕ) : Noun → Option Noun
  | .atom n   => some (.atom ((n + 1) % q))
  | .cell _ _ => none
def lusGBy (q : ℕ) : Noun → Option Noun
  | .atom n   => if n + 1 < q then some (.atom (n + 1)) else none
  | .cell _ _ => none
def evalFBy (q : ℕ) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalFBy q fuel subj (.cell b c), evalFBy q fuel subj d with
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
             match evalFBy q fuel subj b, evalFBy q fuel subj c with
             | some sb, some sc => evalFBy q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalFBy q fuel subj tail).map wut
    | 4 => (evalFBy q fuel subj tail).bind (lusFBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b, evalFBy q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalFBy q fuel subj b with
             | some (.atom 0) => evalFBy q fuel subj c
             | some (.atom 1) => evalFBy q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b with
             | some sb => evalFBy q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalFBy q fuel subj b with
             | some sb => evalFBy q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalFBy q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalFBy q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalFBy q fuel subj c, evalFBy q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with
            | .cell (.cell _ clue) body =>
              match evalFBy q fuel subj clue with
              | some _ => evalFBy q fuel subj body
              | none => none
            | .cell (.atom _) body => evalFBy q fuel subj body
            | _ => none
    | _ => none
def evalGBy (q : ℕ) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGBy q fuel subj (.cell b c), evalGBy q fuel subj d with
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
             match evalGBy q fuel subj b, evalGBy q fuel subj c with
             | some sb, some sc => evalGBy q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGBy q fuel subj tail).map wut
    | 4 => (evalGBy q fuel subj tail).bind (lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b, evalGBy q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGBy q fuel subj b with
             | some (.atom 0) => evalGBy q fuel subj c
             | some (.atom 1) => evalGBy q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b with
             | some sb => evalGBy q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGBy q fuel subj b with
             | some sb => evalGBy q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalGBy q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalGBy q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalGBy q fuel subj c, evalGBy q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | 11 => match tail with
            | .cell (.cell _ clue) body =>
              match evalGBy q fuel subj clue with
              | some _ => evalGBy q fuel subj body
              | none => none
            | .cell (.atom _) body => evalGBy q fuel subj body
            | _ => none
    | _ => none
end Nock.FieldEmbedding


