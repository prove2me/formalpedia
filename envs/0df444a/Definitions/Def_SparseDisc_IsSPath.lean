-- Prove2me | Definitions.Def_SparseDisc_IsSPath
-- name    : SparseDisc_IsSPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:26.689663+00:00
-- url     : https://prove2.me/theorems/f80b87bc-91de-4ad9-8fc0-ce746ebedf9c
-- title:
--   $s$-path in a subset of the cube
-- statement:
--   An **$s$-path** in $A \subseteq \{\pm1\}^U$ is a sequence $z_0, \dots, z_L$ of points of $A$ with $\operatorname{dist}(z_{i-1}, z_i) \le s$ for all $i$.
--
--   **Formalization Note** The sequence is a map $\mathbb N \to \{\pm1\}^U$ read on $0, \dots, L$; the one-term sequence and steps of length $0$ are allowed. Definition 2.9 assumes $U \ne \emptyset$; Section 8.1 extends the notion to $U = \emptyset$, which is covered.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.9, p.14; Section 8.1, p.29

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- `IsSPath s A z L`: the points `z 0, …, z L` form an **`s`-path in `A`** — all lie in `A` and
consecutive points are at Hamming distance at most `s` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy
Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81),
Definition 2.9, p.14).

**Formalization Note** A sequence `z₀, …, z_L` is a map `ℕ → Cube U` read on `0, …, L`; the
one-term sequence (`L = 0`) is allowed, and steps of length `0` are allowed. Definition 2.9
assumes `U ≠ ∅`; Section 8.1 (p.29) extends it to `U = ∅`, which this definition covers. -/
def IsSPath {U : Type} [Fintype U] (s : ℝ) (A : Set (Cube U)) (z : ℕ → Cube U) (L : ℕ) : Prop :=
  (∀ i ≤ L, z i ∈ A) ∧ ∀ i < L, (hammingDist (z i) (z (i + 1)) : ℝ) ≤ s

end SparseDisc


