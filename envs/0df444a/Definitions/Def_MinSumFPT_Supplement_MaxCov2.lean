-- Prove2me | Definitions.Def_MinSumFPT_Supplement_MaxCov2
-- name    : MinSumFPT_Supplement_MaxCov2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:17:01.224194+00:00
-- url     : https://prove2.me/theorems/af9b0f75-4410-427a-aaf0-e190d13db42d
-- title:
--   Gap 2-maxcoverage instances
-- statement:
--   An instance consists of sets $S_1,\dots,S_n$ over a universe $U=\{1,\dots,m\}$; sets may repeat.
--
--   1. **Completeness case**: there are $i,j\in[n]$ and an equipartition $U=U_1\sqcup U_2$, $|U_1|=|U_2|$, with $U_1\subseteq S_i$ and $U_2\subseteq S_j$.
--   2. **Soundness case** (for a gap $\delta$): for every $i,j\in[n]$,
--   $$
--   |S_i\cup S_j|\le(1-\delta)\,|U|.
--   $$
--
--   In both cases $i=j$ is allowed. These are the two cases Theorem 38 says cannot be distinguished in subquadratic time; they are disjoint as soon as $U$ is nonempty and $\delta>0$, because in the completeness case $S_i\cup S_j=U$.
--
--   **Formalization Note** Indices are 0-based. The integer input is $[n,m]$ followed by the $nm$ membership bits $[u\in S_i]$, row-major in $(i,u)$.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 38, p.45 (completeness and soundness cases)

import Mathlib
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-!
# Gap 2-maxcoverage instances (Theorem 38)

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Theorem 38, p.45: a collection of sets `S_1, …, S_n` over a universe `U`; completeness:
"There are some i, j ∈ [n] and an equipartition of U = U_1 ∪̇ U_2 such that U_1 ⊆ S_i and
U_2 ⊆ S_j"; soundness: "For every i, j ∈ [n] we have |S_i ∪ S_j| ≤ (1 − δ) · |U|."

This module bundles `encodeSets`, `MaxCovYes` and `MaxCovNo`.

**Formalization Note.** The universe is `Fin m`, the sets are `S : Fin n → Finset (Fin m)`
(0-based indices; sets may repeat). `i = j` is allowed in both cases, as printed. An equipartition
is `U = U₁ ⊔ U₁ᶜ` with `|U₁| = |U₁ᶜ|`. The integer input is `[n, m]` followed by the membership bits
`[u ∈ S_i]` (`1`/`0`), row-major in `(i, u)`. -/

/-- The integer encoding `[n, m, bits…]` of a set system. -/
def encodeSets {n m : ℕ} (S : Fin n → Finset (Fin m)) : List ℤ :=
  (n : ℤ) :: (m : ℤ) :: (List.finRange n).flatMap fun i =>
    (List.finRange m).map fun u => if u ∈ S i then 1 else 0

/-- Completeness case: two sets cover the two halves of an equipartition of the universe. -/
def MaxCovYes {n m : ℕ} (S : Fin n → Finset (Fin m)) : Prop :=
  ∃ i j : Fin n, ∃ U₁ : Finset (Fin m), U₁.card = U₁ᶜ.card ∧ U₁ ⊆ S i ∧ U₁ᶜ ⊆ S j

/-- Soundness case: every two sets cover at most a `(1 − δ)` fraction of the universe. -/
def MaxCovNo {n m : ℕ} (δ : ℝ) (S : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j : Fin n, ((S i ∪ S j).card : ℝ) ≤ (1 - δ) * m

end MinSumFPT.Supplement


