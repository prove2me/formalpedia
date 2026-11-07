-- Prove2me | Definitions.Def_RegevRecon_ConfigurationModel
-- name    : RegevRecon_ConfigurationModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:57.344554+00:00
-- url     : https://prove2.me/theorems/8387aad4-c419-4ade-b8c5-5e58910061b0
-- title:
--   The matching construction: edge counts, parallel edges and small sets with no singly incident check
-- statement:
--   The **matching construction** chooses a uniform bijection between the $mk$ edge ends of the $m$ symbols, of degree $k$, and the $nD$ edge ends of the $n$ checks, of degree $D$. This defines the multigraph's edge counts, the event $A$ that it has no parallel edges, its incidence pattern, and the event that some nonempty set of at most $\delta m$ symbols has no check incident to exactly one of its edges. The support of a nonzero codeword is such a set, for every choice of nonzero coefficients.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Proposition 2, pp.15–16

import Mathlib

namespace RegevRecon

open Finset

/-- **The matching construction** of [MPRP26, Sec. 4.1] used in Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Proposition 2, p.15: a
bijection between the `m k` edge ends of the `m` symbols (degree `k`) and the `n D` edge ends of the `n` checks
(degree `D`). It is uniform in the probabilities below. -/
abbrev Matching (m k n D : ℕ) := (Fin m × Fin k) ≃ (Fin n × Fin D)

variable {m k n D : ℕ}

/-- The number of edges between symbol `i` and check `j`. -/
def edgeCount (σ : Matching m k n D) (i : Fin m) (j : Fin n) : ℕ :=
  (univ.filter fun a : Fin k => (σ (i, a)).1 = j).card

/-- The event `A` of p.16: the matched graph has no parallel edges. -/
def NoParallelEdges (σ : Matching m k n D) : Prop := ∀ i j, edgeCount σ i j ≤ 1

/-- The incidence pattern of a matching, the matrix `B̄` when it has no parallel edges. -/
def graphOf (σ : Matching m k n D) : Matrix (Fin m) (Fin n) Bool :=
  fun i j => decide (0 < edgeCount σ i j)

/-- A nonempty set `A` of at most `δ m` symbols such that no check is incident to exactly one of its edges
(p.15: the shape of the support of a nonzero codeword, for every choice of nonzero coefficients). -/
def HasSmallNoSingleCheckSet (δ : ℝ) (σ : Matching m k n D) : Prop :=
  ∃ A : Finset (Fin m), A.Nonempty ∧ (A.card : ℝ) ≤ δ * m ∧ ∀ j, ∑ i ∈ A, edgeCount σ i j ≠ 1

open Classical in
/-- The probability of an event under the uniform matching. -/
noncomputable def matchingProb (E : Matching m k n D → Prop) : ℝ :=
  ((univ.filter E).card : ℝ) / (Fintype.card (Matching m k n D) : ℝ)

end RegevRecon


