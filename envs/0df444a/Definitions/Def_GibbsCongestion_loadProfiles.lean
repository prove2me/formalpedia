-- Prove2me | Definitions.Def_GibbsCongestion_loadProfiles
-- name    : GibbsCongestion_loadProfiles
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:21.573872+00:00
-- url     : https://prove2.me/theorems/34840dc0-10f9-4480-9947-922b60ef1789
-- title:
--   Set $\mathcal L$ of strategy load profiles
-- statement:
--   The set of **strategy load profiles** of $n$ players on the strategy set $\mathcal P$ is
--   $$\mathcal L=\Big\{\alpha\in\mathbb Z_{\ge0}^{\mathcal P}:\ \sum_{p\in\mathcal P}\alpha_p=n\Big\}.$$
--   It indexes the partition $\mathcal P^n=\bigcup_{\alpha\in\mathcal L}\mathcal S(\alpha)$ used in the proof of Theorem 4.4, and is the state space of the projection chain.
--
--   **Formalization Note** The page prints $\mathcal L=\{\alpha\in[q]^n:|\alpha|=n\}$; it is used as the set of non-negative integer vectors indexed by the $q$ paths and summing to $n$, which is what is encoded. Every entry is at most $n$, so $\mathcal L$ is a finite set of vectors with entries in $\{0,\dots,n\}$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4, p.15

import Mathlib

namespace GibbsCongestion

/-- The set of **strategy load profiles** `L = {α ∈ ℤ_{≥0}^P : ∑_p α_p = n}`
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4, p.15).

**Formalization Note** The page prints `L = {α ∈ {1,…,q}ⁿ : |α| = n}`; it is used as the set of
all strategy load profiles (vectors indexed by the `q` paths with non-negative entries summing to
`n`), which is what is encoded here. Every entry of such a vector is at most `n`, so `L` is the
finite set of `α : P → ℕ` with entries in `{0,…,n}` and sum `n`. -/
noncomputable def loadProfiles {E : Type*} [DecidableEq E] (P : Finset (Finset E)) (n : ℕ) : Finset (P → ℕ) :=
  (Fintype.piFinset fun _ : P => Finset.range (n + 1)).filter (fun α => ∑ p, α p = n)

end GibbsCongestion


