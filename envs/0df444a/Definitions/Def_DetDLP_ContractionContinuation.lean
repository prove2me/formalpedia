-- Prove2me | Definitions.Def_DetDLP_ContractionContinuation
-- name    : DetDLP_ContractionContinuation
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T17:29:40.126269+00:00
-- url     : https://prove2.me/theorems/06820e62-a8fc-4f75-b835-5777d4a7ad9a
-- title:
--   Bounded sequential recursion for the contraction evaluator
-- statement:
--   A local action returns a value or requests evaluation of one child while saving a single continuation. The inductive computation relation records the returned value, the number of local actions and the maximum number of simultaneously suspended frames. On resumption the parent receives the result of its child.
-- source:
--   DetDLP, Lemma 5.2 and Theorem 4.3, sequential evaluation of recursive contraction.

import Mathlib

namespace DetDLP.ContinuationSchedule
inductive Answer where
  | value (v : ℕ)
  | call (save child : ℕ)

/-- The number of stored continuations is charged only to a child call. -/
inductive Computes (F : ℕ → ℕ → Answer) (B : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | value {x y v} : x<B → y<B → v<B → F x y=.value v → Computes F B x y v 1 0
  | call {x y save child childValue v n h m k} :
    x<B → y<B → save<B → F x y=.call save child →
    Computes F B child 0 childValue n h → Computes F B save childValue v m k →
    Computes F B x y v (1+n+m) (max (h+1) k)
end DetDLP.ContinuationSchedule


