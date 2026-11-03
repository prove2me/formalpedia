-- Prove2me | Definitions.Def_FreeOrderEPTAS_Prog
-- name    : FreeOrderEPTAS_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:36.556744+00:00
-- url     : https://prove2.me/theorems/8420cc8d-e771-4796-9af6-f2a9a9f1ab4e
-- title:
--   Instrumented programs and the cost model
-- statement:
--   Programs of this mission live in a monad that carries a probability distribution and five counters: unit operations, oracle queries, LP solves, rounding calls, and the largest instance handed to a subroutine.
--
--   A unit operation is one of $+,-,\times,/$, a comparison, $\lfloor\cdot\rfloor$, $\lceil\cdot\rceil$, $\log$, an array read or write, or one loop dispatch. Combinators: `tick k` charges $k$ units; `opn k a` is a straight-line block of at most $k$ units with result `a`; `foldP` is a loop with one charged dispatch per iteration; `foldProd` is an odometer over a product of lists; `tabP` fills a table; `callOrc` is one oracle query.
--
--   The cost model gives "$t(\epsilon)\cdot\mathrm{poly}(n)$ time" a meaning for an algorithm with a real-valued oracle and an LP subroutine: real arithmetic has unit cost, and the oracle, the LP solver and the rounding are counted calls.
--
--   **Formalization Note** `Prog α` is `StateT Cost PMF α`. Pure Lean computes for free, so the statements of the mission name their programs; an existential over programs would be trivial.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, the reading of "t(ϵ) · poly(n)-time", Theorem 3.1, p.17, with §2.5, p.12

import Mathlib

namespace FreeOrderEPTAS

/-- The counters of the cost model, which reads "t(ϵ) · poly(n) time" (Theorem 3.1, p.17) relative to the oracle, the LP
solver and the rounding: unit operations, oracle queries, LP
solves, rounding calls, and the largest LP or rounding instance handed to a subroutine. -/
structure Cost where
  /-- Unit operations: `+ − × /`, comparisons, `⌊·⌋`, `⌈·⌉`, `log`, array reads and writes, and one
  loop dispatch per iteration. -/
  ops : ℕ
  /-- Calls to `E[max{X_i, v}]`. -/
  oracle : ℕ
  /-- Calls to the LP solver. -/
  lpCalls : ℕ
  /-- Calls to dependent rounding. -/
  rndCalls : ℕ
  /-- The largest instance size passed to the LP solver or to the rounding. -/
  maxSize : ℕ

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0⟩⟩

/-- The total counted cost. -/
def Cost.total (c : Cost) : ℕ := c.ops + c.oracle + c.lpCalls + c.rndCalls

/-- Instrumented randomized programs: a probability distribution over results and final counters.
Randomness enters only through `callRnd`; each draw is independent, being a `PMF` bind. -/
abbrev Prog (α : Type) : Type := StateT Cost PMF α

/-- Charge `k` unit operations. -/
noncomputable def tick (k : ℕ) : Prog Unit :=
  modify fun c => { c with ops := c.ops + k }

/-- A straight-line block of at most `k` unit operations with result `a`. Every computation of a
program happens under a charge at its own site, of this form or inside a loop combinator below. -/
noncomputable def opn {α : Type} (k : ℕ) (a : α) : Prog α := do
  tick k
  pure a

/-- A loop: one charged dispatch per iteration, threading an accumulator. -/
noncomputable def foldP {α β : Type} : List α → (β → α → Prog β) → β → Prog β
  | [], _, b => pure b
  | a :: l, f, b => do
    tick 1
    let b' ← f b a
    foldP l f b'

/-- Nested loops over a product of lists, as an odometer: the body runs once per element of the
product, in lexicographic order, with one charged dispatch per step of each loop. -/
noncomputable def foldProd {α β : Type} : List (List α) → (β → List α → Prog β) → β → Prog β
  | [], f, b => f b []
  | c :: cs, f, b => foldP c (fun b a => foldProd cs (fun b' r => f b' (a :: r)) b) b

/-- Fill a table with `k` entries, in a charged loop (`foldP`), with one charged write per entry. -/
noncomputable def tabP {β : Type} [Inhabited β] {k : ℕ} (f : Fin k → Prog β) : Prog (Fin k → β) := do
  let l ← foldP (List.finRange k) (fun acc a => do
    let v ← f a
    opn 1 (acc ++ [v])) []
  pure fun a => l.getD a.val default

/-- One counted query `E[max{X_j, v}]` of the oracle `o`, the only access a program has to the
laws of the variables. -/
noncomputable def callOrc {n : ℕ} (o : Fin n → ℝ → ℝ) (j : Fin n) (v : ℝ) : Prog ℝ := do
  modify fun c => { c with oracle := c.oracle + 1 }
  pure (o j v)

end FreeOrderEPTAS


