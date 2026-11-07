-- Prove2me | Definitions.Def_TTTSampling_alg2
-- name    : TTTSampling_alg2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:57.706785+00:00
-- url     : https://prove2.me/theorems/215d4a86-dc78-4202-b62f-43eebd6d0159
-- title:
--   Algorithm 2 (Tree-structured Rejection Sampling): output law of $(\mathcal T,\mathcal G^{\mathrm{ret}},\text{reads})$
-- statement:
--   **Algorithm 2** takes a node $w\in\Sigma^{\le n}$, a finite class $\mathcal G$, the density-ratio parameter $M\ge1$, the oracle $\hat\mu$ and the parameter $R$ of Assumption 3.1. It runs $M$ independent trials (outer iterations $i=1,\dots,M$, each as in `alg2Trial`) and returns
--
--   1. the multiset $\mathcal T$ of nodes added by the trials (each trial adds at most one);
--   2. the class $\mathcal G^{\mathrm{ret}}$: it starts as $\mathcal G$ (Line 1) and is intersected with each trial's Line-11 restriction;
--   3. the set of nodes at which $\hat\mu$ was read.
--
--   With a cache $Q$ of already obtained values, the number of **new oracle evaluations** of the call is the number of read nodes outside $Q$, per the caching convention of p.18.
--
--   Algorithm 2 is the inner step of Algorithm 3: it extends a partial sequence by rejection sampling from the mean density of the current class, and restricts the class whenever the oracle reveals a large discrepancy (Lemma 3.6).
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Algorithm 2, p.11 (PDF p.13); caching, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_TTTSampling_alg2Trial

open Classical

namespace TTTSampling

/-- The outputs of Algorithm 2 computed from the records of its `M` trials: the multiset `𝒯` of
added nodes (with multiplicity), the class `𝒢^ret` (Line 1 sets `𝒢^ret ← 𝒢`; Line 11 intersects it
with each trial's restriction), and the union of the trials' read sets. -/
noncomputable def alg2Result {α : Type} [Fintype α] [LinearOrder α] {n : ℕ}
    (G : Finset (PMF (Fin n → α))) (L : List (TrialOut α n)) :
    Multiset (List α) × Finset (PMF (Fin n → α)) × Finset (List α) :=
  ((L.filterMap TrialOut.added : Multiset (List α)),
   L.foldl (fun acc tr => match tr.restr with | some H => acc ∩ H | none => acc) G,
   L.foldl (fun acc tr => acc ∪ tr.reads) ∅)

/-- **Algorithm 2 (Tree-structured Rejection Sampling).**

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Algorithm 2, printed
p.11 (PDF p.13). Input: the oracle ratio parameter `R` (Lines 3, 11, 16), the density ratio
parameter `M ≥ 1` (number of trials and threshold), the oracle `µ̂`, a node `w ∈ Σ^{≤n}` and a
class `𝒢 ⊂ ∆(Σⁿ)`. Output law of `(𝒯, 𝒢^ret, reads)`:
* `𝒯` — the multiset of nodes added on Lines 11 and 19 (each trial adds at most one);
* `𝒢^ret` — the returned class (Line 20);
* `reads` — the set of nodes at which `µ̂` is evaluated (caching convention, p.18: a test on
  Lines 6/9 at a node `v` with `|v| < n` reads `µ̂(v)` and all `µ̂(v∘y)`). The number of *new*
  oracle evaluations of a call made with cache `Q` is `(reads \ Q).card`.

The `M` trials are `alg2Trials` (see `trialGo` for each line and the conventions). -/
noncomputable def alg2 {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (w : List α) (G : Finset (PMF (Fin n → α))) :
    PMF (Multiset (List α) × Finset (PMF (Fin n → α)) × Finset (List α)) :=
  (alg2Trials R M μh w G).map (alg2Result G)

end TTTSampling


