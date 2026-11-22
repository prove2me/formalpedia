-- Prove2me | Definitions.Def_Comp_Search
-- name    : Comp_Search
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:43:51.456045+00:00
-- url     : https://prove2.me/theorems/729743f5-1746-44c8-b041-0c5074ddc519
-- title:
--   Search
-- statement:
--   Definitions and structural lemmas for Search, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Search.lean

import Definitions.Def_Comp_MatrixGameQ
set_option autoImplicit true
namespace Comp
open Csg
namespace MatrixGameQ
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
def elimStep (rows : List (List ℚ)) : Option (List ℚ × List (List ℚ)) :=
  match rows.findIdx? (fun r => r.headD 0 != 0) with
  | none => none
  | some k =>
    match rows[k]? with
    | none => none
    | some piv =>
      let a := piv.headD 0
      let pivN := piv.map (fun x => x / a)
      let rest := (rows.eraseIdx k).map fun r =>
        let c := r.headD 0
        (List.zipWith (fun x y => x - c * y) r pivN).tail
      some (pivN, rest)
def solveQ : Nat → List (List ℚ) → Option (List ℚ)
  | 0, _ => some []
  | n + 1, rows => do
    let (piv, rest) ← elimStep rows
    let xs ← solveQ n rest
    -- `piv` is `[1, c₁, …, cₙ, b]`: back-substitute `x = b - ∑ cᵢ xᵢ`.
    let coeffs := piv.tail.dropLast
    let b := (piv.getLast?).getD 0
    some ((b - (List.zipWith (fun c x => c * x) coeffs xs).sum) :: xs)
def rowSystem (G : MatrixGameQ I J) (Rs : List I) (Cs : List J) : List (List ℚ) :=
  (Cs.map fun j => (Rs.map fun i => G.A i j) ++ [-1, 0])
    ++ [(Rs.map fun _ => (1 : ℚ)) ++ [0, 1]]
def colSystem (G : MatrixGameQ I J) (Rs : List I) (Cs : List J) : List (List ℚ) :=
  (Rs.map fun i => (Cs.map fun j => G.A i j) ++ [-1, 0])
    ++ [(Cs.map fun _ => (1 : ℚ)) ++ [0, 1]]
def weightOf {α : Type*} [DecidableEq α] (support : List α) (xs : List ℚ) (a : α) : ℚ :=
  match (support.zip xs).find? (fun pr => pr.1 == a) with
  | some pr => pr.2
  | none => 0
def candidateFor (G : MatrixGameQ I J) (Rs : List I) (Cs : List J) :
    Option (ℚ × (I → ℚ) × (J → ℚ)) :=
  if Rs.length != Cs.length then none
  else if Rs.length == 0 then none
  else
    match solveQ (Rs.length + 1) (G.rowSystem Rs Cs),
          solveQ (Cs.length + 1) (G.colSystem Rs Cs) with
    | some sp, some sq =>
      some ((sp.getLast?).getD 0, weightOf Rs sp.dropLast, weightOf Cs sq.dropLast)
    | _, _ => none
def sublistsOf {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: as => let r := sublistsOf as; r ++ r.map (fun t => a :: t)
def supportPairs (Is : List I) (Js : List J) : List (List I × List J) :=
  let css := sublistsOf Js
  (sublistsOf Is).foldr (fun Rs acc =>
    (css.filterMap fun Cs =>
      if Rs.length == Cs.length && Rs.length != 0 then some (Rs, Cs) else none) ++ acc) []
def certOK (G : MatrixGameQ I J) (c : ℚ × (I → ℚ) × (J → ℚ)) : Bool :=
  decide (G.ValueCert c.1 c.2.1 c.2.2)
def findValueCert (G : MatrixGameQ I J) (Is : List I) (Js : List J) :
    Option (ℚ × (I → ℚ) × (J → ℚ)) :=
  ((supportPairs Is Js).filterMap fun pr => G.candidateFor pr.1 pr.2).find? G.certOK
end MatrixGameQ
end Comp


