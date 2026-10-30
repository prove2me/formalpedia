-- Prove2me | Definitions.Def_CoffmanMitrani_Job
-- name    : CoffmanMitrani_Job
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:10.345811+00:00
-- url     : https://prove2.me/theorems/9e998186-9975-4d39-99cf-33a0dd194430
-- title:
--   Jobs: class and index within the class
-- statement:
--   A job is identified by a pair $(i,n)$: its class $i$ and its position $n$ in the order of arrivals of class $i$ (the $n$-th arriving job of class $i$).
--
--   **Formalization Note** Classes are indexed $0,\dots,M-1$ (`Fin M`) and the jobs of a class $0,1,2,\dots$; the paper's class $i$ and $n$-th job are the Lean class $i-1$ and job $n-1$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811

import Mathlib

namespace CoffmanMitrani

/-- **Jobs.** A job is identified by its class and its index within the class:
`(i, n)` is the `n`-th arriving job of class `i`.
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: "the nth arriving job of class i".

**Formalization Note.** Both indices are 0-based: the paper's `n`-th arriving job of class `i` is
`(i - 1, n - 1) : Fin M × ℕ`. -/
abbrev Job (M : ℕ) : Type := Fin M × ℕ

end CoffmanMitrani


