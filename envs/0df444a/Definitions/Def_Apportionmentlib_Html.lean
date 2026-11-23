-- Prove2me | Definitions.Def_Apportionmentlib_Html
-- name    : Apportionmentlib_Html
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:41:36.31016+00:00
-- url     : https://prove2.me/theorems/d09c0ff5-0b59-4426-b99f-d6533bce0e16
-- title:
--   Html
-- statement:
--   Definitions and structural lemmas for Html, from mdbrnowski/apportionmentlib contributors (see pinned LICENSE and source headers)'s pinned Balinski–Young apportionment impossibility development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Html.lean

module
public meta import Definitions.Def_Apportionmentlib_Basic
public import Definitions.Def_Apportionmentlib_Basic
public import ProofWidgets.Component.HtmlDisplay
set_option autoImplicit false
@[expose] public section
public meta section
open ProofWidgets
open Lean (Json)
namespace Apportionmentlib
def Election.toHtml {n : ℕ} (e : Election n) : Html :=
  let indices := List.range n
  let votesList := e.votes.toList
  let houseSize := e.houseSize
  let total := votesList.sum
  let thStyle := Json.mkObj [
    ("border", Json.str "1px solid"),
    ("padding", Json.str "6px"),
    ("textAlign", Json.str "center")
  ]
  let tdStyle := Json.mkObj [
    ("border", Json.str "1px solid"),
    ("padding", Json.str "6px"),
    ("textAlign", Json.str "center"),
    ("fontFamily", Json.str "monospace")
  ]
  let tableStyle := Json.mkObj [
    ("borderCollapse", Json.str "collapse"),
  ]
  let th (s : String) := Html.element "th" #[("style", thStyle)] #[Html.text s]
  let td (s : String) := Html.element "td" #[("style", tdStyle)] #[Html.text s]
  let row1 := Html.element "tr" #[] <|
    ([th "id"] ++ indices.map (fun i => th (toString i)) ++ [th "Σ"]).toArray
  let row2 := Html.element "tr" #[] <|
    ([th "votes"] ++ votesList.map (fun v => td (toString v)) ++ [td (toString total)]).toArray
  let row3 := Html.element "tr" #[] <|
    ([th "quota"] ++ (List.finRange n).map (fun i => td (formatRat4 (e.quota i))) ++
     [td (toString houseSize.val)]).toArray
  Html.element "table" #[("style", tableStyle)] #[Html.element "tbody" #[] #[row1, row2, row3]]
instance {n : ℕ} : HtmlEval (Election n) where
  eval e := pure e.toHtml
end Apportionmentlib


