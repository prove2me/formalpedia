-- Prove2me | Definitions.Def_TightClock_Supplement_ClockProg
-- name    : TightClock_Supplement_ClockProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:01:04.905075+00:00
-- url     : https://prove2.me/theorems/1a24bfcf-39f7-4c68-a826-8288332dd1bc
-- title:
--   Clock programs: offers, sequencing and while-loops
-- statement:
--   A **clock program** describes an adaptive clock auction for one fixed public seed. It is built from four constructs: return a value; offer a price $p$ to a bidder $i$ and observe whether she accepts; run one program and then a continuation chosen from its result; and a while-loop that repeats a body from a state until the body signals termination with a result. Loops may run for an unbounded number of rounds, as the auctions of §4–§5 do (they raise prices until bidders drop out, with no public bound on values).
--
--   A program reads the answers to its own offers and nothing else, so it never reads the values directly: prices are "a function of the public random seed and the observed acceptance/rejection history". The auctions of this mission are written as clock programs; their meaning as clocks is `ClockProg.toStrategy`.
--
--   **Formalization Note** An inductive type indexed by the result type, with a `Monad` instance so that the auctions can be written in `do`-notation.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, pp.13–14 (PDF pp.16–17)

import Mathlib
import Definitions.Def_TightClock_Strategy

set_option autoImplicit false

namespace TightClock.Supplement

/-- A clock program: the description of an adaptive clock auction (for one fixed public seed) as a
program that offers prices to bidders, observes accept/reject answers, and eventually returns a
value. `offer i p` offers the price `p` to bidder `i` and returns her answer (`true` = accept);
`bind` is sequential composition; `loop body s` iterates `body` from the state `s` until it returns
`Sum.inr b`, and then returns `b` (a `while` loop, possibly unbounded). Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, pp.13–14
(PDF 16–17): prices "may be raised adaptively as a function of the public random seed and the
observed acceptance/rejection history".

**Formalization Note** This is syntax only; its meaning as a `TightClock.Strategy` is
`ClockProg.toStrategy`. A program reads the answers to its own offers and nothing else, so it never
reads the values. The `Monad` instance (`pure`, `bind`) lets the auctions be written in
`do`-notation. -/
inductive ClockProg (n : ℕ) : Type → Type 1
  /-- Return a value without further offers. -/
  | pure {α : Type} (a : α) : ClockProg n α
  /-- Offer the price `p` to bidder `i`; the answer is `true` iff she accepts. -/
  | offer (i : Fin n) (p : ℝ) : ClockProg n Bool
  /-- Run `x`, then the continuation `f` on its result. -/
  | bind {α β : Type} (x : ClockProg n α) (f : α → ClockProg n β) : ClockProg n β
  /-- Iterate `body` from `init` until it returns `Sum.inr b`; then return `b`. -/
  | loop {σ β : Type} (body : σ → ClockProg n (σ ⊕ β)) (init : σ) : ClockProg n β

instance (n : ℕ) : Monad (ClockProg n) where
  pure := ClockProg.pure
  bind := ClockProg.bind

end TightClock.Supplement


