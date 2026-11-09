-- Prove2me | Definitions.Def_MatroidOptGame_pairInput
-- name    : MatroidOptGame_pairInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:27.690218+00:00
-- url     : https://prove2.me/theorems/672f9804-62f0-4c23-9a4c-394d0119f092
-- title:
--   Input encoding of a position together with two given sets
-- statement:
--   The machine input for a strategy that is handed two sets $B_1, B_2$ in advance (Lemma 6): integer cell $0$ holds $n$, cells $1, \dots, n$ the weights, cells $n+1, \dots, 2n$ a label for each element $i$ ($1$ if $i \in B_1$, else $2$ if $i \in B_2$, else $0$), cell $2n+1$ the number of moves so far, and the following cells the moves of the history. All other cells are $0$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 6, p.6

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM

namespace MatroidOptGame

/-- The RAM input for a strategy that is given two sets `B₁, B₂` in advance: integer cell `0`
holds `n`, cells `1, …, n` the weights, cells `n + 1, …, 2n` a label for each element `i`
(`1` if `i ∈ B₁`, else `2` if `i ∈ B₂`, else `0`), cell `2n + 1` the length of `h`, and the
following cells the moves of `h`. All other cells are `0`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 6, p.6 ("Given two disjoint bases B1, B2 of M, MIN has an efficient
strategy …"): the two bases are part of the input. -/
def pairInput (n : ℕ) (w : Fin n → ℕ) (B₁ B₂ : Finset (Fin n)) (h : List (Fin n)) :
    LSWNewArcAudit.NewArc.RAMInput where
  integers := fun a =>
    if 0 ≤ a then
      ((((n : ℤ) :: List.ofFn (fun i => (w i : ℤ))) ++
        (List.ofFn (fun i => if i ∈ B₁ then (1 : ℤ) else if i ∈ B₂ then 2 else 0)) ++
        ((h.length : ℤ) :: h.map (fun e => (e.val : ℤ))))[a.toNat]?).getD 0
    else 0
  reals := fun _ => 0

end MatroidOptGame


