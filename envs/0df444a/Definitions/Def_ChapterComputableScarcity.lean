-- Prove2me | Definitions.Def_ChapterComputableScarcity
-- name    : ChapterComputableScarcity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:35:57.628409+00:00
-- url     : https://prove2.me/theorems/f4eb9bc1-c457-47c7-a4e8-de8745212c81
-- title:
--   Chapter ComputableScarcity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterComputableScarcity.lean`): generated def bundle for ChapterComputableScarcity. See BookProof/ChapterComputableScarcity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterComputableScarcity.lean

import Mathlib


/-!
# Chapter "Aligned deep learning as a random sampling method", §4 — almost all
functions are not computable, not even approximately

Source: `book.tex`, chapter *"Aligned deep learning as a random sampling
method"*, §*"4. Why deep neural networks do not overfit"* (line ~9999):

> *"Under reasonable assumptions, almost all functions are not computable not
> even approximately.  Thus, Machine Learning works because the functions we are
> approximating are in fact probability distributions …"*

The self-contained mathematical content of that sentence is a counting /
diagonalization statement about the functions `ℕ → ℕ`:

* there are only **countably many** computable functions, because every
  computable function is described by one of the countably many programs;
* there are **uncountably many** functions, so "almost all" of them (all but a
  countable set) are not computable;
* and this is not repaired by allowing approximations: there is a single
  function that differs from **every** computable function at infinitely many
  arguments, hence no computable function eventually agrees with it.

## Deliverables

* `evalTotal` — the total function computed by a program (a `Nat.Partrec.Code`),
  undefined values being read as `0`;
* `exists_code_of_computable` — every computable `f : ℕ → ℕ` is `evalTotal c` for
  some program `c`;
* `countable_computable` — **countably many computable functions**;
* `exists_infinitely_often_ne` — **diagonalization**: for every sequence `e` of
  functions there is a function differing from each `e k` at infinitely many
  arguments;
* `uncountable_natFun` — there are uncountably many functions `ℕ → ℕ`;
* `exists_differs_infinitely_often_from_all_computable` — **the book's claim**:
  some function differs from *every* computable function at infinitely many
  arguments;
* `exists_not_eventually_eq_computable` — the "not even approximately" form: no
  computable function eventually agrees with that function;
* `exists_not_computable` — in particular non-computable functions exist.
-/

namespace BookProof.ComputableScarcity

open Nat.Partrec

open Classical in
/-- The total function computed by the program `c`: the value of `c` on `n` when
`c` halts on `n`, and `0` otherwise.  Reading the partial function this way loses
no generality here, because a program computing a *total* function halts
everywhere. -/
noncomputable def evalTotal (c : Code) (n : ℕ) : ℕ :=
  if h : (c.eval n).Dom then (c.eval n).get h else 0















end BookProof.ComputableScarcity


