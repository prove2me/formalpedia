-- Prove2me | Definitions.Def_SingleOrSample_runLaw
-- name    : SingleOrSample_runLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:21.896648+00:00
-- url     : https://prove2.me/theorems/a484f390-5bbd-4726-b455-db59a235d9ab
-- title:
--   The law of Algorithm 2
-- statement:
--   This definition is the randomness of Algorithm 2 for a profile of strategies. Fix $n$ agents and a parameter $k$.
--
--   1. **The loop (lines 11–14).** From the picks so far in the round, stop if $|G|<k(n-t)$. Otherwise the agent's strategy names a bucket $B$, one uniformly random good of $B$ is picked, and $B$ leaves $G$.
--   2. **The round (lines 5–16).** If the strategy selects a good $e$, the round is the special round of $e$; otherwise it is the loop started with no picks.
--   3. **The run.** The law of the history after $j$ rounds starts at the empty history; agent $j$ acts on the history of the first $j$ rounds. After $n$ rounds nothing changes.
--
--   Note that $t$ is frozen within a round, so all buckets of one round have the same size. This is the object whose probabilities the main theorem bounds.
--
--   **Formalization Note** The loop has a fuel parameter so that its recursion is structural. The law at top level uses fuel $m+1$, which a legal strategy never exhausts, since every bucket is nonempty and leaves $G$. The guard $k(n-t)=0$ stops the loop when $t\ge n$, which does not occur on a run with $k>0$.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Algorithm 2, p.12

import Mathlib
import Definitions.Def_SingleOrSample_Strategy

open scoped Classical

namespace SingleOrSample

/-- The `while` loop of Algorithm 2 (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online
Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256
28cd3d7b…, lines 11–14, p.12), as a law on the final list of (bucket, pick) pairs. From the pairs `picks`
so far: stop if `|G| < k(n − t)`; otherwise the strategy names a bucket, one uniformly random item of it
is picked, and the loop continues.

**Formalization Note.** `fuel` makes the recursion structural; the law at top level uses `m + 1`, which
a legal strategy never exhausts, as each bucket is nonempty and leaves `G`. The guard `k(n − t) = 0`
stops the loop off a run (`t ≥ n`, where natural subtraction gives `0`) and is never met on a run with
`0 < k`. An empty bucket, possible only for an illegal strategy, also stops the loop. -/
noncomputable def loopLaw {m : ℕ} (n k : ℕ) (σ : Strategy m) (h : Hist m) :
    ℕ → List (Finset (Fin m) × Fin m) → PMF (List (Finset (Fin m) × Fin m))
  | 0, picks => PMF.pure picks
  | fuel + 1, picks =>
    if k * (n - specialCount h) = 0 ∨ (pending h picks).card < k * (n - specialCount h) then
      PMF.pure picks
    else if hB : (σ.bucket h picks).Nonempty then
      (PMF.uniformOfFinset (σ.bucket h picks) hB).bind fun e =>
        loopLaw n k σ h fuel (picks ++ [(σ.bucket h picks, e)])
    else
      PMF.pure picks

/-- One served round of Algorithm 2 (lines 5–16, p.12): a special round if the strategy selects an item,
and the loop started from no picks, with fuel `m + 1`, otherwise. -/
noncomputable def roundLaw {m : ℕ} (n k : ℕ) (σ : Strategy m) (h : Hist m) : PMF (Round m) :=
  match σ.choose h with
  | some e => PMF.pure (.special e)
  | none => (loopLaw n k σ h (m + 1) []).map Round.sampled

/-- The law of the history after the first `j` rounds of Algorithm 2 (p.12) for the profile `σ`, with the
parameters `n`, `k`. Agent `j` (Lean index, from `0`) acts in the round after `j` served rounds. For
`j ≥ n` the history is unchanged. -/
noncomputable def runLaw {m n : ℕ} (k : ℕ) (σ : Fin n → Strategy m) : ℕ → PMF (Hist m)
  | 0 => PMF.pure []
  | j + 1 => (runLaw k σ j).bind fun h =>
    if hj : j < n then (roundLaw n k (σ ⟨j, hj⟩) h).map (fun r => h ++ [r]) else PMF.pure h

end SingleOrSample


