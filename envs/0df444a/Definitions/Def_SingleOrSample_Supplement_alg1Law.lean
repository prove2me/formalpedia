-- Prove2me | Definitions.Def_SingleOrSample_Supplement_alg1Law
-- name    : SingleOrSample_Supplement_alg1Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:32:00.403798+00:00
-- url     : https://prove2.me/theorems/df74550b-ba3c-48e0-bf66-073b6e470def
-- title:
--   The law of Algorithm 1 (simple static-bucketing allocation)
-- statement:
--   **Algorithm 1** serves agents $i=1,\dots,n$ in order. Let $R_i$ be the goods still unallocated when agent $i$ arrives ($R_1=[m]$). Agent $i$ forms buckets $B_{i1},B_{i2},\dots$ of exactly $3n$ goods each out of $R_i$; with $G$ the goods of $R_i$ not yet put into a bucket, a new bucket is formed and sampled as long as $|G|>3n$. From each such bucket one good is chosen uniformly at random (this is $\mathrm{SwR}(B_{ij},1/(3n))$ on a bucket of size $3n$) and allocated to agent $i$; the remaining $|G|\le3n$ goods form the last bucket $B_{i\ell_i}$, which is not sampled. Then $R_{i+1}=R_i\setminus A_i$. Each bucket may be chosen after the picks from the earlier buckets of the round are revealed.
--
--   Looping while $|G|>3n$ samples exactly $\ell_i-1$ buckets with $\ell_i=\lceil |R_i|/3n\rceil$, which is the bucket count of Definitions 5 and 6. The definition gives the law of the history (all rounds, with their buckets and picks) after the first $j$ agents, given a profile of strategies naming the buckets.
--
--   **Formalization Note** Histories, rounds, the remaining set and the bundles are the published `SingleOrSample.Hist` objects (Algorithm 1 has no special rounds). The loop has fuel $m+1$, never exhausted when every bucket is a nonempty subset of $G$; an empty bucket (possible only off the safe strategies) stops the loop. The published Algorithm 2 law is not reused: its guard $|G|\ge k(n-t)$ samples one more bucket when $3n$ divides $|R_i|$.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Algorithm 1, p.9; Definitions 5–6, pp.9–10; §3.1, p.10 (adaptive buckets)

import Mathlib
import Definitions.Def_SingleOrSample_Strategy

open scoped Classical

namespace SingleOrSample.Supplement

open SingleOrSample

/-- The sampling loop of one round of **Algorithm 1** (Chawla, Huang, Kulkarni, Mehta, Shahkar,
Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, Algorithm 1, lines 4–7, p.9, with `ℓ_i = ⌈|R_i|/3n⌉`
of Definitions 5–6), as a law on the final list of (bucket, pick) pairs. From the pairs `picks` so far,
with `G` the remaining goods minus every bucket formed in this round: stop if `|G| ≤ 3n`; otherwise the
strategy names a bucket `B`, one uniformly random item of `B` is allocated (`SwR(B, 1/(3n))` on a bucket
of size `3n` picks exactly one item), and the loop continues.

**Formalization Note.** Looping while `|G| > 3n` samples exactly `ℓ_i − 1 = ⌈|R_i|/3n⌉ − 1` buckets of
size `3n` and leaves the last bucket `B_{iℓ_i}` (of size in `(0, 3n]`) unallocated, as in Definitions 5
and 6; this differs from Algorithm 2's guard `|G| ≥ k(n − t)`, which samples one more bucket when `3n`
divides `|R_i|`. `fuel` makes the recursion structural; at top level it is `m + 1`, never exhausted when
each bucket is a nonempty subset of `G`. An empty bucket, possible only off the safe strategies, stops
the loop. Buckets may be chosen adaptively from the picks so far (§3.1, p.10). -/
noncomputable def alg1Loop {m : ℕ} (n : ℕ) (σ : Strategy m) (h : Hist m) :
    ℕ → List (Finset (Fin m) × Fin m) → PMF (List (Finset (Fin m) × Fin m))
  | 0, picks => PMF.pure picks
  | fuel + 1, picks =>
    if (pending h picks).card ≤ 3 * n then
      PMF.pure picks
    else if hB : (σ.bucket h picks).Nonempty then
      (PMF.uniformOfFinset (σ.bucket h picks) hB).bind fun e =>
        alg1Loop n σ h fuel (picks ++ [(σ.bucket h picks, e)])
    else
      PMF.pure picks

/-- The law of the history after the first `j` rounds of **Algorithm 1** (p.9) for the profile `σ` of
`n` agents: agent `j` (Lean index, from `0`; the page's agent `j + 1`) runs `alg1Loop` from no picks on
the remaining set `R_{j+1}`, and the round is recorded as `Round.sampled picks`; it is allocated the
picked items. For `j ≥ n` the history is unchanged.

**Formalization Note.** Only `Strategy.bucket` is used; Algorithm 1 has no special rounds. The bundle
of agent `i` is `allocOf h i` and the remaining set is `remaining h`, from the published `Hist`. -/
noncomputable def alg1Law {m n : ℕ} (σ : Fin n → Strategy m) : ℕ → PMF (Hist m)
  | 0 => PMF.pure []
  | j + 1 => (alg1Law σ j).bind fun h =>
    if hj : j < n then
      (alg1Loop n (σ ⟨j, hj⟩) h (m + 1) []).map (fun picks => h ++ [Round.sampled picks])
    else PMF.pure h

end SingleOrSample.Supplement


