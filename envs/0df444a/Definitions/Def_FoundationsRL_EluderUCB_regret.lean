-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_regret
-- name    : FoundationsRL_EluderUCB_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:42.558471+00:00
-- url     : https://prove2.me/theorems/bed2b1ec-1e6b-4c69-8deb-11fb6f864d1d
-- title:
--   (4.3): regret of a decision sequence
-- statement:
--   For a mean reward function $f^\star$ and decisions $\pi^1,\dots,\pi^T$,
--
--   $$
--   \mathrm{Reg}=\sum_{t=1}^T\Bigl(\sup_{\pi\in\Pi}f^\star(\pi)-f^\star(\pi^t)\Bigr).
--   $$
--
--   **Formalization Note** The source writes the comparator as $f^\star(\pi^\star)$ with $\pi^\star=\arg\max_\pi f^\star(\pi)$. The supremum equals it when the maximizer exists and needs no attainment on an arbitrary $\Pi$. The source's expectation over $\pi^t\sim p^t$ is the value at $\pi^t$ for generalized UCB, which plays a point mass. Every use has $f^\star$ with values in $[0,1]$, so the real supremum is the true one.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (4.3), p. 57

import Mathlib

namespace FoundationsRL.EluderUCB

/-- **Regret of a decision sequence.** Foster & Rakhlin, arXiv:2312.16730v1, (4.3), p. 57:
`Reg = ∑_{t=1}^T f⋆(π⋆) - ∑_{t=1}^T E_{πᵗ∼pᵗ}[f⋆(πᵗ)]`, with `π⋆ = argmax_{π ∈ Π} f⋆(π)`.

**Formalization Note.** Rounds are indexed `1, …, T`, as in the source. The comparator `f⋆(π⋆)` is
the supremum `⨆ p, f⋆ p`, which equals `f⋆(π⋆)` when the maximizer exists and needs no attainment
on an arbitrary `Act`; every use has `f⋆` bounded above, so the real supremum is not a junk value.
The expectation over `πᵗ ∼ pᵗ` is the value at `πᵗ` because generalized UCB plays a point mass. -/
noncomputable def regret {Act : Type*} (fstar : Act → ℝ) (T : ℕ) (π : ℕ → Act) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ((⨆ p, fstar p) - fstar (π t))

end FoundationsRL.EluderUCB


