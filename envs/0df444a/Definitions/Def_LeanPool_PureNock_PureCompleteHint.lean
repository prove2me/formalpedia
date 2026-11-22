-- Prove2me | Definitions.Def_LeanPool_PureNock_PureCompleteHint
-- name    : LeanPool_PureNock_PureCompleteHint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:00:42.517257+00:00
-- url     : https://prove2.me/theorems/e21a3a3b-e947-4747-a95f-4b6477d51fbe
-- title:
--   Pure Complete Hint
-- statement:
--   Definitions and structural lemmas for Pure Complete Hint, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Verb
open Noun
def ncost : Nat → Noun → Noun → Nat
  | 0, _, _ => 0
  | _ + 1, _, .atom _ => 0
  | f + 1, subj, .cell (.cell b c) d =>
      1 + ncost f subj (.cell b c) + ncost f subj d
  | f + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => 2
    | 1 => 1
    | 2 =>
        match tail with
        | .cell b c =>
            let inner := match evalN f subj b, evalN f subj c with
                         | some sb, some sc => ncost f sb sc
                         | _, _ => 0
            1 + ncost f subj b + ncost f subj c + inner
        | _ => 0
    | 3 => 2 + ncost f subj tail
    | 4 => 2 + ncost f subj tail
    | 5 =>
        match tail with
        | .cell b c => 2 + ncost f subj b + ncost f subj c
        | _ => 0
    | 6 =>
        match tail with
        | .cell b (.cell c d) =>
            let inner := match evalN f subj b with
                         | some (.atom 0) => ncost f subj c
                         | some (.atom 1) => ncost f subj d
                         | _ => 0
            100 + ncost f subj b + inner
        | _ => 0
    | 7 =>
        match tail with
        | .cell b c =>
            let inner := match evalN f subj b with
                         | some sb => ncost f sb c
                         | _ => 0
            1 + ncost f subj b + inner
        | _ => 0
    | 8 =>
        match tail with
        | .cell b c =>
            let inner := match evalN f subj b with
                         | some sb => ncost f (.cell sb subj) c
                         | _ => 0
            1 + ncost f subj b + inner
        | _ => 0
    | 9 =>
        match tail with
        | .cell (.atom ax) c =>
            let inner := match evalN f subj c with
                         | some core =>
                             match Noun.slot ax core with
                             | some arm => ncost f core arm
                             | _ => 0
                         | _ => 0
            20 + ncost f subj c + inner
        | _ => 0
    | 10 =>
        match tail with
        | .cell (.cell (.atom _) c) d => 2 + ncost f subj c + ncost f subj d
        | _ => 0
    | 11 =>
        match tail with
        | .cell (.cell _ clue) body =>
            let inner := match evalN f subj clue with
                         | some _ => ncost f subj body
                         | _ => 0
            50 + ncost f subj clue + inner
        | .cell (.atom _) body => 50 + ncost f subj body
        | _ => 0
    | _ => 0
def vcostN (F : Nat) : Verb → Nat
  | .leaf _ => 0
  | .node a l r =>
      (match a with
       | .star => match den F l, den F r with
                  | some sa, some fo => ncost F sa fo
                  | _, _ => 0
       | .slot => 1
       | .equal => 1
       | .minus => 1
       | .edit => 1
       | .null => 0
       | .wut => 0) + vcostN F l + vcostN F r
end Verb
end Nock


