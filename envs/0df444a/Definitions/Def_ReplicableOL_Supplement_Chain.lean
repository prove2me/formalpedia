-- Prove2me | Definitions.Def_ReplicableOL_Supplement_Chain
-- name    : ReplicableOL_Supplement_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:15:14.973575+00:00
-- url     : https://prove2.me/theorems/a23d7138-8994-4463-89c9-7384a02572a0
-- title:
--   DALR chain of powers of $2$
-- statement:
--   A **DALR chain** for a horizon $T$ is a finite sequence of powers of $2$
--
--   $$
--   T=A_0>A_1>\cdots>A_K=:B\ge 1,
--   $$
--
--   each dividing the previous one. The number $K$ is the number of levels, $A_i$ is the spacing of the level-$i$ anchors, and $B=A_K$ is the block length: DALR changes its action only at multiples of $B$.
--
--   **Formalization Note** The lengths are a function $A:\mathbb N\to\mathbb N$ read only on $0,\dots,K$. $B\ge1$ holds because $A_K$ is a power of $2$. The type allows $K=0$; the theorems that use a chain either assume $K\ge2$ or construct the chain.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, p.17

import Mathlib

namespace ReplicableOL.Supplement

/-- **DALR chain of powers of 2.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, p.17. "a chain of powers of 2, T = A_0 > A_1 > ⋯ > A_K =: B ≥ 1, each dividing the previous one."

**Formalization Note.** `A : ℕ → ℕ` is read only on `0, …, K`; its values beyond `K` play no role. `B = A K ≥ 1` holds because `A K` is a power of 2. `K = 0` is allowed by the type (a one-block rule); every theorem of the mission that uses a chain either requires `K ≥ 2` or constructs its chain. -/
structure Chain (T : ℕ) where
  /-- The number of levels `K`. -/
  K : ℕ
  /-- The block lengths `A_0, …, A_K`. -/
  A : ℕ → ℕ
  /-- `A_0 = T`. -/
  A_zero : A 0 = T
  /-- Each `A_i`, `i ≤ K`, is a power of 2. -/
  pow_two : ∀ i ≤ K, ∃ e : ℕ, A i = 2 ^ e
  /-- The chain is strictly decreasing. -/
  strictAnti : ∀ i < K, A (i + 1) < A i
  /-- Each `A_{i+1}` divides `A_i`. -/
  dvd : ∀ i < K, A (i + 1) ∣ A i

end ReplicableOL.Supplement


