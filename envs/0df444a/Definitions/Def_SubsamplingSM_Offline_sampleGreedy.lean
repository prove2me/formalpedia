-- Prove2me | Definitions.Def_SubsamplingSM_Offline_sampleGreedy
-- name    : SubsamplingSM_Offline_sampleGreedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:29.316972+00:00
-- url     : https://prove2.me/theorems/d4f4b440-5d80-49ea-9ace-13f55d2be5a3
-- title:
--   SampleGreedy (Algorithm 1) on a given sample
-- statement:
--   SampleGreedy first draws a random sample $N'\subseteq N$, adding each element independently with probability $q$, and then runs the greedy algorithm on $N'$: starting from $S=\emptyset$, while some $u\in N'$ has $S\cup\{u\}\in\mathcal I$ and $f(u\mid S)>0$, it adds such an element of maximum marginal gain (ties to the earliest element). For a fixed sample $T$, the output is
--   $$\mathrm{SG}(T)=\operatorname{step}_T^{\,n}(\emptyset),\qquad n=|N|.$$
--
--   The random output of SampleGreedy is $\mathrm{SG}(N')$, and the expectations of Theorem 1 are taken over the law of $N'$.
--
--   **Formalization Note** Every effective iteration adds a new element of $T$, so the loop stops after at most $n$ iterations, and $n$ iterations compute its output.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, Algorithm 1, p. 9

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_greedyStep

namespace SubsamplingSM.Offline

/-- **SampleGreedy (Algorithm 1) on a given sample.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, Algorithm 1, p. 9: "Let `N′ ← ∅` and `S ← ∅`. for each `u ∈ N` do with probability
`q` do Add `u` to `N′`. end while there exists `u ∈ N′` such that `S + u ∈ I` and
`f(u | S) > 0` do Let `u ∈ N′` be the element of this kind maximizing `f(u | S)`. Add `u`
to `S`. end return `S`." Ties are broken by the fixed order of p. 10.

`sampleGreedy f I T` is the set returned when the sample is `N′ = T`: the while loop
(`greedyStep`) run from `S = ∅` for `n = |α|` iterations.

**Formalization Note.** Each effective iteration adds a new element of `T`, so the loop stops
after at most `n` iterations, and an iteration after termination changes nothing; `n`
iterations therefore compute the output of the while loop. The random sampling of Lines 1–5 is
the Bernoulli(`q`) law of `T`, which enters through `expectSample`. -/
noncomputable def sampleGreedy {α : Type*} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) : Finset α :=
  (greedyStep f I T)^[Fintype.card α] ∅

end SubsamplingSM.Offline


