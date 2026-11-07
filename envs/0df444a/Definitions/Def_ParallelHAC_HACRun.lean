-- Prove2me | Definitions.Def_ParallelHAC_HACRun
-- name    : ParallelHAC_HACRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:36.20585+00:00
-- url     : https://prove2.me/theorems/77a3f8e3-21f7-4235-90d6-be24621cc0b0
-- title:
--   $c$-approximate HAC run (any tie-breaking)
-- statement:
--   **Hierarchical agglomerative clustering** on a finite point set $P$ with $n=|P|$ and linkage $d$ starts from the singleton clustering $\mathcal C_1=\{\{p\}:p\in P\}$ and performs $n-1$ merges. At step $i=1,\dots,n-1$ it picks two distinct clusters $A_i,B_i\in\mathcal C_i$, removes them and adds $A_i\cup B_i$, giving $\mathcal C_{i+1}$. The run is **$c$-approximate** when every merge satisfies
--   $$d(A_i,B_i)\le c\cdot\min_{C\ne D\in\mathcal C_i} d(C,D).$$
--
--   A HAC run is any such sequence of merges: every admissible choice among pairs within the factor $c$ (every tie-breaking) gives a run. Here $\mathcal C_i$ is the clustering just before the $i$-th merge.
--
--   **Formalization Note** Merges are indexed $1,\dots,n-1$; the clusterings $\mathcal C_i$ are computed from the merge sequence. Values of the merge sequence outside $[1,n-1]$ are never used.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §1 p.1 (PDF p.4); §2.2 p.7 (PDF p.10); §4 p.18 (PDF p.21)

import Mathlib

namespace ParallelHAC

/-!
# c-approximate HAC runs (§1, p.1; §2.2, p.7; §4, p.18)

Source: arXiv:2507.20047 (sha256 a21061c8…).

**Formalization Note.** Merges are indexed from `1` to `n − 1` as in §4 (p.18), with `n = |P|`.
A run is given by its merged pairs `A i, B i`; the clustering `C_i` just before merge `i` is
computed from them, starting from the singleton clustering. The values of `A i, B i` outside
`1 ≤ i ≤ n − 1` are never used. "Regardless of how ties are broken" (p.7) is captured by
quantifying over every `HACRun`.
-/

/-- One HAC merge step: remove `A` and `B` from the clustering `𝒞` and add `A ∪ B` (p.1). -/
def mergeStep {V : Type*} [DecidableEq V] (𝒞 : Finset (Finset V)) (A B : Finset V) :
    Finset (Finset V) :=
  insert (A ∪ B) ((𝒞.erase A).erase B)

/-- The clustering after the first `m` merges of the merge sequence `(A i, B i)_{i ≥ 1}`, starting
from the singleton clustering `{{p} : p ∈ P}` (p.1). -/
def clusteringAfter {V : Type*} [DecidableEq V] (P : Finset V) (A B : ℕ → Finset V) :
    ℕ → Finset (Finset V)
  | 0 => P.image (fun p => ({p} : Finset V))
  | m + 1 => mergeStep (clusteringAfter P A B m) (A (m + 1)) (B (m + 1))

/-- `C_i`, the clustering just before the `i`-th merge (`i ≥ 1`), i.e. after `i − 1` merges
(§4, p.18). -/
def clustering {V : Type*} [DecidableEq V] (P : Finset V) (A B : ℕ → Finset V) (i : ℕ) :
    Finset (Finset V) :=
  clusteringAfter P A B (i - 1)

/-- A **`c`-approximate HAC run** on the point set `P` with linkage `d` (§1, p.1; §2.2, p.7): for
each of the `n − 1` steps `i = 1, …, n − 1` (`n = |P|`) it merges two distinct clusters `A i, B i`
of the current clustering `C_i` whose value satisfies `d(A_i, B_i) ≤ c · min_{C ≠ D ∈ C_i} d(C, D)`.
Any choice among the admissible pairs is allowed (every tie-breaking).
Source: arXiv:2507.20047 (sha256 a21061c8…), p.1, p.7, p.18. -/
structure HACRun {V : Type*} [DecidableEq V] (P : Finset V) (d : Finset V → Finset V → ℝ)
    (c : ℝ) where
  /-- The first cluster of the `i`-th merge. -/
  A : ℕ → Finset V
  /-- The second cluster of the `i`-th merge. -/
  B : ℕ → Finset V
  /-- `A i` is a current cluster. -/
  left_mem : ∀ i, 1 ≤ i → i ≤ P.card - 1 → A i ∈ clustering P A B i
  /-- `B i` is a current cluster. -/
  right_mem : ∀ i, 1 ≤ i → i ≤ P.card - 1 → B i ∈ clustering P A B i
  /-- The two merged clusters are distinct. -/
  left_ne_right : ∀ i, 1 ≤ i → i ≤ P.card - 1 → A i ≠ B i
  /-- The `c`-approximate condition against the closest pair of distinct current clusters. -/
  approx : ∀ i, 1 ≤ i → i ≤ P.card - 1 →
    ∀ C ∈ clustering P A B i, ∀ D ∈ clustering P A B i, C ≠ D → d (A i) (B i) ≤ c * d C D

/-- `C_i` for a run: the clustering just before merge `i` (§4, p.18). -/
def HACRun.C {V : Type*} [DecidableEq V] {P : Finset V} {d : Finset V → Finset V → ℝ} {c : ℝ}
    (R : HACRun P d c) (i : ℕ) : Finset (Finset V) :=
  clustering P R.A R.B i

end ParallelHAC


