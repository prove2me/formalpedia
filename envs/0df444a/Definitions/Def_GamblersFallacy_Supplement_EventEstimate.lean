-- Prove2me | Definitions.Def_GamblersFallacy_Supplement_EventEstimate
-- name    : GamblersFallacy_Supplement_EventEstimate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:12:20.605733+00:00
-- url     : https://prove2.me/theorems/52a996e8-8a56-428d-940e-a30646436d6d
-- title:
--   The event $E_{k\ell}$, its $n$-period estimate $\hat p_{E_{k\ell}}(n)$ and the target probability $P[E_{k\ell}(0)]$
-- statement:
--   In the general Markov chain of §3.1, let $B_n(t)\in\{0,1\}$ indicate an arrival at position $t$, with $B_n(0)=1$. For $k\le\ell$ the event $E_{k\ell}(t)$ is that at least $k$ demands arrive in the $\ell$ periods following a demand arrival at $t$, i.e. among the positions $t+1,\dots,t+\ell$.
--
--   For a horizon $n\ge\ell$, the **$n$-period estimate** of the probability of $E_{k\ell}$ is the fraction of arrivals at the positions $0,\dots,n-\ell$ that are followed by at least $k$ arrivals in the next $\ell$ periods:
--   $$
--   \hat p_{E_{k\ell}}(n)=\frac{\sum_{i=0}^{n-\ell}B_n(i)\,\chi(E_{k\ell}(i))}{\sum_{i=0}^{n-\ell}B_n(i)} .
--   $$
--   Its expectation is $\mathbb E[\hat p_{E_{k\ell}}(n)]$. The target is the true probability $P[\chi(E_{k\ell}(0))=1]$ of at least $k$ arrivals at the positions $1,\dots,\ell$ after the arrival at $0$.
--
--   These are the two sides of Theorem 1. They generalize the arrival-after-arrival frequency $\hat p_1(n)$ ($k=\ell=1$) to streaks and to windows with several arrivals.
--
--   **Formalization Note** The window $\{0,\dots,n-\ell\}$ is `Finset.range (n - ℓ + 1)`. The denominator is at least $1$ because $B_n(0)=1$. The expectation is the finite weighted sum over the $2^n$ arrival patterns under the renewal law. The target is computed under the law of the positions $0,\dots,\ell$, which is the restriction of the law of the positions $0,\dots,n$ for every $n\ge\ell$.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §3.1, p.11 (E_kℓ(t) for k ≤ ℓ ≤ n − t, the target P[χ(E_kℓ(0)) = 1]) and Theorem 1, p.12 (p̂_{E_kℓ}(n))

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate
import Definitions.Def_GamblersFallacy_Supplement_RenewalLaw

namespace GamblersFallacy.Supplement

open GamblersFallacy

/-- The number of arrivals at the positions `a + 1, …, b`. -/
def arrivalsIn {n : ℕ} (ω : Fin n → Bool) (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun s => arrival ω s = true).card

/-- **The `n`-period estimate `p̂_{E_kℓ}(n)` of the event `E_kℓ`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, §3.1, p.11 ("E_kℓ(t) := {at least k demand
arrivals in the next ℓ periods, following a demand arrival at t}", for `k ≤ ℓ ≤ n − t`) and
Theorem 1, p.12:
`p̂_{E_kℓ}(n) = Σ_{i=0}^{n−ℓ} B_n(i) χ(E_kℓ(i)) / Σ_{i=0}^{n−ℓ} B_n(i)`.

The numerator counts the positions `i ∈ {0, …, n − ℓ}` carrying an arrival that is followed by at
least `k` arrivals at the positions `i + 1, …, i + ℓ` (all of them `≤ n`, so observed); the
denominator counts the arrivals at the positions `0, …, n − ℓ`.

**Formalization Note.** The range `{0, …, n − ℓ}` is `Finset.range (n - ℓ + 1)`; the source only
uses `ℓ ≤ n`, where the subtraction does not truncate. The denominator is at least `1` because
`B_n(0) = 1`. -/
noncomputable def eventEstimate (k l : ℕ) {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  (((Finset.range (n - l + 1)).filter fun i =>
      arrival ω i = true ∧ k ≤ arrivalsIn ω i (i + l)).card : ℝ) /
    (((Finset.range (n - l + 1)).filter fun i => arrival ω i = true).card : ℝ)

/-- **`E[p̂_{E_kℓ}(n)]`** (Theorem 1, p.12) under the renewal law of §3.1, as the finite weighted
sum over the `2ⁿ` arrival patterns of the positions `1, …, n`. -/
noncomputable def expectedEventEstimate (L : InterArrivalLaw) (n k l : ℕ) : ℝ :=
  ∑ ω : Fin n → Bool, L.renewalWeight ω * eventEstimate k l ω

/-- **The target probability `P[χ(E_kℓ(0)) = 1]`** (p.11): the probability of at least `k`
arrivals at the positions `1, …, ℓ` following the arrival at `0`, computed from the renewal law
of the positions `0, …, ℓ`.

**Formalization Note.** The law of the positions `0, …, ℓ` is the restriction of the law of the
positions `0, …, n` for every `n ≥ ℓ` (the renewal process does not depend on the horizon), so
this is the probability of `E_kℓ(0)` in every horizon `n ≥ ℓ`. -/
noncomputable def eventProb (L : InterArrivalLaw) (k l : ℕ) : ℝ :=
  ∑ ω : Fin l → Bool, L.renewalWeight ω * (if k ≤ arrivalsIn ω 0 l then 1 else 0)

end GamblersFallacy.Supplement


