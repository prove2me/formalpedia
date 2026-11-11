-- Prove2me | Definitions.Def_WeakStrongMSR_Test
-- name    : WeakStrongMSR_Test
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:30:58.034373+00:00
-- url     : https://prove2.me/theorems/f3e1ba41-b2ec-4b3e-8eed-cb7063593540
-- title:
--   One test of a guess $\lambda$, the grid TEST, and the search over guesses (§3.5, Algorithm 5)
-- statement:
--   1. A **test** of the guess $\lambda$ runs sampling, rounding, repair and compression with $h$ of Eq. (20) and the threshold (21). Its outcome is an abort or a solution, together with its strong-query count. It **passes** if it does not abort and the total radius is at most $Ck\lambda$, with $C=3000$.
--   2. With $u,v$ the points $0,1$ and $d_0=d(u,v)$, Eq. (18) sets
--   $$\lambda_-=\frac{d_0}{2Ck\Delta},\qquad \lambda_+=\frac{\Delta d_0}{k}.$$
--   TEST is $\lambda_-,2\lambda_-,4\lambda_-,\dots$ below $\lambda_+$, followed by $\lambda_+$.
--   3. **Algorithm 5.** If $k\ge n$, return radius-zero balls at all points. Otherwise:
--      - if the test at $\lambda_+$ fails, return $B(u,\Delta d_0)$ with all points;
--      - if the test at $\lambda_-$ passes, return its solution;
--      - otherwise binary search on TEST (middle index $\lfloor(i+j)/2\rfloor$) and return the retained solution at the final upper bound.
--
--      The search counts the tests it runs and its strong queries: $2$ for $u,v$, plus those of every test it runs.
--
--   **Formalization Note** The search reads independent outcomes of a test at every grid value. This is the coupling of the proofs of Lemma 3.37 and Theorem 3.35, and it has the same law as running the tests one after another with fresh randomness.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §3, p.6 (PDF 7); §3.5, p.27 (PDF 28), Eqs. (17), (18); Algorithm 5, p.28 (PDF 29); App. A, p.34 (PDF 35)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP
import Definitions.Def_WeakStrongMSR_Sampling
import Definitions.Def_WeakStrongMSR_Rounding
import Definitions.Def_WeakStrongMSR_Repair
import Definitions.Def_WeakStrongMSR_Compress

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# One test of a guess, and the search over guesses (§3.5, Algorithm 5)

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0): §3, p.6 (a test is sampling, rounding, repair and
compression); §3.5, p.27, Eqs. (17), (18): `d₀ = d(u, v)`, `λ₋ = d₀/(2Ck∆)`, `λ₊ = ∆d₀/k`,
`C = 3000`, "TEST consist[s] of λ₋, 2λ₋, 4λ₋, … up to the largest such value below λ₊, together with
the endpoint λ₊"; "declare the test to pass only if the run does not abort and its returned balls
have total radius at most Ckλ"; Algorithm 5, p.28 (lines 1–10); App. A, p.34 (the parameters
(20), (21)).

This module bundles the test outcome, the law of one test, the grid and the law of the search.

**Formalization Note.**
* A test uses `h = hParam c δ n` and the margin `γ = 1/2 − δ` (App. A). Its strong-query count is
  the sum of the counts of its steps, up to an abort.
* `u, v` are the points `0` and `1` (R12); `d₀ = 0` if `n < 2`.
* The grid has `⌈log₂(λ₊/λ₋)⌉` values `λ₋ 2^i` (exactly the `i ≥ 0` with `λ₋ 2^i < λ₊`, when
  `λ₊/λ₋ = 2C∆² > 0`) followed by `λ₊`; index `0` is `λ₋` whenever the grid has a value below `λ₊`
  (always when `∆ ≥ 1`).
* The search reads independent outcomes of a test at every grid value (R13; the coupling of the
  proofs of Lemma 3.37 and Theorem 3.35): it equals the sequential algorithm's law because each
  test uses fresh randomness. The middle value is the grid index `⌊(i + j)/2⌋` (R12).
* The search's outcome records the solution, the number of tests run and the strong queries
  (`2` for `u, v`, plus those of every test run). For `k ≥ n` it returns radius-zero balls at all
  points (slot `v` holds point `v`; spare slots have radius `0`). -/

/-- The outcome of one test: a solution, or `none` for an abort; and its strong queries. -/
structure TestOut (n k : ℕ) where
  /-- The solution, or `none` if the run aborted. -/
  result : Option (Sol n k)
  /-- The strong queries of the run. -/
  queries : ℕ

/-- The law of one test of the guess `λ` (sampling, rounding, repair, compression), with absolute
constant `c`, corruption probability `δ`, LP routine `sel`, offline routine `off`, metric `d` and
weak table `w`. -/
noncomputable def testLaw {n : ℕ} (c : ℕ) (δ : ℝ) (k : ℕ) (lam : ℝ) (sel : LPSelector n)
    (off : OfflineRoutine n k) (d w : Fin n → Fin n → ℝ) : PMF (TestOut n k) :=
  let h := hParam c δ n
  (sampleLaw c k h lam sel d w).bind (fun o =>
    match round c k h lam d o.S.toFinset o.cands with
    | .abort q => PMF.pure ⟨none, o.S.length + q⟩
    | .ok r => (repairLaw c k h (1 / 2 - δ) d w r).map (fun rp =>
        ⟨if rp.aborted then none else some (compress r rp off),
          o.S.length + r.queries + rp.queries⟩))

/-- The joint law of sampling followed by rounding and repair (no compression), used to state
Lemma 3.21: the sampling outcome, and, unless rounding aborted, the rounding output with the repair
outcome. -/
noncomputable def roundRepairLaw {n : ℕ} (c : ℕ) (δ : ℝ) (k : ℕ) (lam : ℝ) (sel : LPSelector n)
    (d w : Fin n → Fin n → ℝ) :
    PMF (SampState n × Option (Σ r : RoundOut n, RepairOut n r.m)) :=
  let h := hParam c δ n
  (sampleLaw c k h lam sel d w).bind (fun o =>
    match round c k h lam d o.S.toFinset o.cands with
    | .abort _ => PMF.pure (o, none)
    | .ok r => (repairLaw c k h (1 / 2 - δ) d w r).map (fun rp => (o, some ⟨r, rp⟩)))

/-- A test of the guess `λ` passes: it did not abort and its total radius is at most
`C k λ = 3000 k λ`. -/
def passes {n k : ℕ} (lam : ℝ) (t : TestOut n k) : Prop :=
  ∃ s, t.result = some s ∧ solCost s.rad ≤ 3000 * k * lam

/-- `d₀ = d(u, v)` for the points `u = 0`, `v = 1` (`0` if `n < 2`). -/
noncomputable def d0 {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  if h : 2 ≤ n then d ⟨0, by omega⟩ ⟨1, by omega⟩ else 0

/-- `λ₋ = d₀ / (2 C k ∆)` with `C = 3000` (Eq. (18)). -/
noncomputable def lamMinus {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (Δ : ℝ) : ℝ :=
  d0 d / (2 * 3000 * k * Δ)

/-- `λ₊ = ∆ d₀ / k` (Eq. (18)). -/
noncomputable def lamPlus {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (Δ : ℝ) : ℝ :=
  Δ * d0 d / k

/-- The grid TEST: `λ₋, 2λ₋, 4λ₋, …` below `λ₊`, then `λ₊`. -/
noncomputable def testGrid {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (Δ : ℝ) : List ℝ :=
  (List.range ⌈Real.logb 2 (lamPlus d k Δ / lamMinus d k Δ)⌉₊).map
    (fun i => lamMinus d k Δ * 2 ^ i) ++ [lamPlus d k Δ]

/-- Binary search on grid indices between `lb` (failed) and `ub` (passed), with fuel: returns the
final upper index and the indices tested, in order. -/
def bsearch (pass : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × List ℕ
  | 0, _, ub => (ub, [])
  | f + 1, lb, ub =>
      if ub ≤ lb + 1 then (ub, []) else
        let mid := (lb + ub) / 2
        let res := if pass mid then bsearch pass f lb mid else bsearch pass f mid ub
        (res.1, mid :: res.2)

/-- The outcome of the search: the solution (`none` only in degenerate cases `n = 0` or `k = 0`),
the number of tests run, and the strong queries. -/
structure GuessOut (n k : ℕ) where
  /-- The returned solution. -/
  sol : Option (Sol n k)
  /-- The number of tests run. -/
  tests : ℕ
  /-- The strong queries. -/
  queries : ℕ

/-- The law of the full algorithm (Algorithm 5) on the inputs `k`, `∆`, with absolute constant `c`,
corruption probability `δ`, LP routine `sel`, offline routine `off`, metric `d` and weak table `w`.
-/
noncomputable def guessLaw {n : ℕ} (c : ℕ) (δ : ℝ) (k : ℕ) (Δ : ℝ) (sel : LPSelector n)
    (off : OfflineRoutine n k) (d w : Fin n → Fin n → ℝ) : PMF (GuessOut n k) :=
  if hk : n ≤ k then
    if hn : 0 < n then
      PMF.pure ⟨some ⟨fun v => ⟨v, by omega⟩,
        fun j => if hj : (j : ℕ) < n then ⟨j, hj⟩ else ⟨0, hn⟩, fun _ => 0⟩, 0, 0⟩
    else PMF.pure ⟨none, 0, 0⟩
  else if hk0 : k = 0 then PMF.pure ⟨none, 0, 0⟩ else
    let grid := testGrid d k Δ
    let N := grid.length - 1
    (seqLaw (grid.map (fun lam => testLaw c δ k lam sel off d w))).map (fun outs =>
      let out : ℕ → TestOut n k := fun i => outs.getD i ⟨none, 0⟩
      let pass : ℕ → Bool := fun i => decide (passes (grid.getD i 0) (out i))
      let q : List ℕ → ℕ := fun is => 2 + (is.map (fun i => (out i).queries)).sum
      let fallback : Sol n k :=
        ⟨fun _ => ⟨0, by omega⟩, fun _ => ⟨0, by omega⟩,
          fun j => if (j : ℕ) = 0 then Δ * d0 d else 0⟩
      if pass N = false then ⟨some fallback, 1, q [N]⟩
      else if pass 0 = true then ⟨(out 0).result, 2, q [N, 0]⟩
      else
        let bs := bsearch pass (N + 1) 0 N
        ⟨(out bs.1).result, 2 + bs.2.length, q ([N, 0] ++ bs.2)⟩)

end WeakStrongMSR


