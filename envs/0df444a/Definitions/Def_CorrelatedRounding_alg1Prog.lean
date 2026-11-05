-- Prove2me | Definitions.Def_CorrelatedRounding_alg1Prog
-- name    : CorrelatedRounding_alg1Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:47.630192+00:00
-- url     : https://prove2.me/theorems/0341a46e-7f2f-4111-827c-1138a864c505
-- title:
--   Algorithm 1 as a real-RAM program
-- statement:
--   A program in the tick monad of the published real-RAM cost model. Given the marginals $u$ and a realization $E$, it
--
--   1. computes $y_k=\max_i u_{ki}$ for every $k$ by scanning $u$;
--   2. reads every draw $E_k$ once;
--   3. for every item $i$, scans the FCs, skips those with $u_{ki}=0$, computes $(y_k/u_{ki})E_k$ for the others, and returns the first minimizer.
--
--   Every read of an entry of $u$, every read of a draw, every real comparison and arithmetic operation, and every loop iteration costs one tick or more. The running time of a run is the final tick counter.
--
--   **Formalization Note.** The module also holds the helpers `uAt`, `drawAt`, `rowMaxProg`, `yProg`, `drawProg`, `itemArgMinProg` and `assignProg`. The program uses only `for` loops over `List.finRange` and never reads the counter. The output has type `Fin q → Option (Fin K)` so that no assumption $K\ge1$ is needed to write it.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Algorithm 1, p.10, and proof of Theorem 1, p.11

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_rle
import Definitions.Def_LNTopology_Hermetization_req
import Definitions.Def_LNTopology_Hermetization_rmul
import Definitions.Def_LNTopology_Hermetization_rdiv

open LNTopology.Hermetization

namespace CorrelatedRounding

/-- Ticked read of the entry `u_ki` of the input. -/
noncomputable def uAt {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) (i : Fin q) : StateM ℕ ℝ := do
  tick 1
  pure (u k i)

/-- Ticked read of the draw `E_k` (the sampling cost). -/
noncomputable def drawAt {K : ℕ} (E : Fin K → ℝ) (k : Fin K) : StateM ℕ ℝ := do
  tick 1
  pure (E k)

/-- Step (a) for one FC: scan `u_ki` over `i` and keep the maximum, starting from `0`. -/
noncomputable def rowMaxProg {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) : StateM ℕ ℝ := do
  let mut m : ℝ := 0
  for i in List.finRange q do
    tick 1
    let a ← uAt u k i
    let ge ← rle m a
    if ge then m := a
  pure m

/-- Step (a): the vector `y_k = max_i u_ki`. -/
noncomputable def yProg {q K : ℕ} (u : Fin K → Fin q → ℝ) : StateM ℕ (Fin K → ℝ) := do
  let mut ys : Fin K → ℝ := fun _ => 0
  for k in List.finRange K do
    tick 1
    let m ← rowMaxProg u k
    ys := Function.update ys k m
  pure ys

/-- Step (b): read every draw `E_k` once. -/
noncomputable def drawProg {K : ℕ} (E : Fin K → ℝ) : StateM ℕ (Fin K → ℝ) := do
  let mut es : Fin K → ℝ := fun _ => 0
  for k in List.finRange K do
    tick 1
    let e ← drawAt E k
    es := Function.update es k e
  pure es

/-- Step (c) for one item: scan the FCs, skip those with `u_ki = 0` (clock `∞`), compute
`(y_k / u_ki) E_k` for the others, and keep the first minimum. Returns `none` only for a column of zeros,
which an instance does not have. -/
noncomputable def itemArgMinProg {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q) :
    StateM ℕ (Option (Fin K)) := do
  let mut best : Option (Fin K × ℝ) := none
  for k in List.finRange K do
    tick 1
    let a ← uAt u k i
    let isZero ← req a 0
    if !isZero then
      let r ← rdiv (ys k) a
      let c ← rmul r (es k)
      match best with
      | none => best := some (k, c)
      | some (k₀, b) =>
        let keep ← rle b c
        best := if keep then some (k₀, b) else some (k, c)
  pure (best.map Prod.fst)

/-- Step (c): the assignment of every item. -/
noncomputable def assignProg {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) :
    StateM ℕ (Fin q → Option (Fin K)) := do
  let mut z : Fin q → Option (Fin K) := fun _ => none
  for i in List.finRange q do
    tick 1
    let b ← itemArgMinProg u ys es i
    z := Function.update z i b
  pure z

/-- **Algorithm 1 as a real-RAM program.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4,
Algorithm 1, p.10, and the runtime claim in the proof of Theorem 1, p.11: "The runtime is O(qK) because
taking the arg min over k = 1,…,K for all i = 1,…,q is the bottleneck operation in Algorithm 1."

Given the marginals `u` and a realization `E` of the draws, the program computes `y` from `u`, reads each
draw, and returns for each item the first minimizer of its clocks.

**Formalization Note.** The paper names no machine model, and its inputs are real numbers, so running time
is counted in the real-RAM model of the published `LNTopology.Hermetization.tick`, whose discipline binds
this program. Every read of `u` (`uAt`), every read of a draw (`drawAt`, the cost of sampling one
exponential), every real comparison and operation, and every loop iteration ticks; updates of array-like
state (`Fin K → ℝ`, `Fin q → Option (Fin K)`) are the `O(1)` RAM writes inside one iteration; the only
classical decisions are the ticked primitives; the program never reads the counter. The running time of a
run started at `0` is the final counter. The value `y` is computed, not taken as input, since the input
of the problem is `u`. The output type is `Option` so that no `NeZero K` is needed to state the program. -/
noncomputable def alg1Prog {q K : ℕ} (u : Fin K → Fin q → ℝ) (E : Fin K → ℝ) :
    StateM ℕ (Fin q → Option (Fin K)) := do
  let ys ← yProg u
  let es ← drawProg E
  assignProg u ys es

end CorrelatedRounding


