-- Prove2me | Definitions.Def_LearnVsOpt_Prog
-- name    : LearnVsOpt_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:21.086608+00:00
-- url     : https://prove2.me/theorems/ef1d4445-b012-4774-9b92-588468174fc6
-- title:
--   Charged computations on the unit-cost real RAM
-- statement:
--   The cost model behind "runs in time $\mathrm{poly}(T,n_L)$". A deterministic charged computation is a result with the number of unit operations spent on it; these compose by adding the counts. A randomized program is a probability distribution over the pair (result, counter), threaded through the program.
--
--   One unit is charged for each of $+,-,\times,/,\min,\max$, each comparison of two numbers, each array or list cell read or write, each loop dispatch, and each arithmetic operation on a loop bound. One unit is charged for a uniform draw from $\{0,\dots,M-1\}$, and one for a two-point draw. There is no floor, no real-to-integer cast and no oracle.
--
--   **Formalization Note** The paper fixes no machine model; its proof counts iterations and a linear program in $n_L$ variables (p.22). Entries are real numbers, so the unit-cost real RAM is the model on which the statement is defined.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Theorem 6.7, p.21; proof, p.22

import Mathlib

namespace LearnVsOpt

/-- **Deterministic charged computations**: a result together with the number of unit operations spent
on it.

**Formalization Note (cost model).** "Runs in time poly(T, n_L)" (Fikioris, Sivan & Tardos,
arXiv:2611.05580, Theorem 6.7, p.21) is read on the unit-cost real RAM: one unit for each `+ − × /`,
`min`, `max`, comparison of two numbers, array or list cell read or write, one dispatch per loop
iteration, one arithmetic operation on a loop bound. There is no floor, no real-to-integer cast and no
oracle. -/
structure Det (α : Type) where
  /-- The result. -/
  val : α
  /-- The units charged. -/
  cost : ℕ

instance : Monad Det where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- A straight-line block of at most `k` unit operations with result `a`. Every computation of a
program happens under a charge at its own site, of this form or inside a loop below. -/
def opn {α : Type} (k : ℕ) (a : α) : Det α := ⟨a, k⟩

/-- A loop over a list: one charged dispatch per iteration, threading an accumulator. -/
def foldD {α β : Type} : List α → (β → α → Det β) → β → Det β
  | [], _, b => pure b
  | a :: l, f, b => do
    let _ ← opn 1 ()
    let b' ← f b a
    foldD l f b'

/-- The sum of a charged term over a list: one dispatch per element and one addition. -/
def sumD {α : Type} (l : List α) (f : α → Det ℝ) : Det ℝ :=
  foldD l (fun s a => do
    let v ← f a
    opn 1 (s + v)) 0

/-- The list of the results of a charged term over a list: one dispatch per element, one write. -/
def mapD {α β : Type} (l : List α) (f : α → Det β) : Det (List β) :=
  foldD l (fun acc a => do
    let v ← f a
    opn 1 (acc ++ [v])) []

/-- Fill an array of `nL` reals, in a charged loop. -/
def tabD {nL : ℕ} (f : Fin nL → Det ℝ) : Det (Fin nL → ℝ) := do
  let l ← mapD (List.finRange nL) f
  pure fun j => l.getD j.val 0

/-- **Instrumented randomized programs**: a probability distribution over the pair (result, counter).
Randomness enters only through `drawRange` and `drawTwo`, and successive draws are independent, being
`PMF` binds. -/
abbrev Prog (α : Type) : Type := StateT ℕ PMF α

/-- Run a deterministic charged computation inside a program. -/
noncomputable def Det.lift {α : Type} (d : Det α) : Prog α :=
  fun n => PMF.pure (d.val, n + d.cost)

/-- Charge `k` unit operations. -/
noncomputable def charge (k : ℕ) : Prog Unit := fun n => PMF.pure ((), n + k)

/-- One uniform draw from `{0, …, M − 1}`, at cost `1` (the point `0` if `M = 0`). -/
noncomputable def drawRange (M : ℕ) : Prog ℕ := fun n =>
  if h : (Finset.range M).Nonempty then
    (PMF.uniformOfFinset (Finset.range M) h).map (fun m => (m, n + 1))
  else PMF.pure (0, n + 1)

/-- One draw of `a` with probability `Q` and `b` with probability `1 − Q`, at cost `1` (`Q` is clipped
to `[0, 1]`). -/
noncomputable def drawTwo {α : Type} (Q : ℝ) (a b : α) : Prog α := fun n =>
  (PMF.bernoulli (min Q.toNNReal 1) (min_le_right _ _)).map
    (fun h => ((if h then a else b), n + 1))

end LearnVsOpt


