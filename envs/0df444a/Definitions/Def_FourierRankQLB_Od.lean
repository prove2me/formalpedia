-- Prove2me | Definitions.Def_FourierRankQLB_Od
-- name    : FourierRankQLB_Od
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:09.438959+00:00
-- url     : https://prove2.me/theorems/8093d292-f957-4622-95de-e458d3a15159
-- title:
--   The orthogonal group $O(d)$ as a compact group with its Borel $\sigma$-algebra
-- statement:
--   The orthogonal group
--   $$
--   O(d)=\{Q\in\mathbb R^{d\times d}: Q^TQ=I\},
--   $$
--   with the subspace topology of the matrices. It is a compact topological group, and it carries its Borel $\sigma$-algebra.
--
--   The hidden matrix of every hard instance ranges over this group.
--
--   **Formalization Note** It is Mathlib's `Matrix.orthogonalGroup (Fin d) ℝ`. The module proves compactness and declares the Borel structure.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §2.1, p.13

import Mathlib

open Matrix

namespace FourierRankQLB

/-- The orthogonal group `O(d) = {Q ∈ ℝ^{d×d} : QᵀQ = I}`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §2.1, p. 13.

**Formalization Note.** This is Mathlib's `Matrix.orthogonalGroup`, a subtype of the matrices with
the subspace topology. The Borel σ-algebra and compactness are supplied here, for the Haar measure
`haarO`. -/
abbrev Od (d : ℕ) : Type := Matrix.orthogonalGroup (Fin d) ℝ

/-- The Borel σ-algebra on `O(d)`. -/
instance instMeasurableSpaceOd (d : ℕ) : MeasurableSpace (Od d) := borel _

instance instBorelSpaceOd (d : ℕ) : BorelSpace (Od d) := ⟨rfl⟩

/-- `O(d)` is compact: it is closed, and its entries are bounded by one. -/
instance instCompactSpaceOd (d : ℕ) : CompactSpace (Od d) := by
  refine isCompact_iff_compactSpace.mp ?_
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin d => Set.pi Set.univ fun _ : Fin d =>
      Metric.closedBall (0 : ℝ) 1 : Set (Matrix (Fin d) (Fin d) ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hc ?_ ?_
  · have : ((Matrix.orthogonalGroup (Fin d) ℝ : Submonoid (Matrix (Fin d) (Fin d) ℝ)) :
        Set (Matrix (Fin d) (Fin d) ℝ)) = {A | A * Aᵀ = 1} := by
      ext A
      exact Matrix.mem_orthogonalGroup_iff (n := Fin d) (R := ℝ)
    rw [this]
    exact isClosed_eq (by fun_prop) continuous_const
  · intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j

end FourierRankQLB


