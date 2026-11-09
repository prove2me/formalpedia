-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank
-- name    : DetSupportRank_DeterminantSupport_PartitionRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:26.855519+00:00
-- url     : https://prove2.me/theorems/a276ba21-1930-442e-99c9-dce72b5f0910
-- title:
--   Partition decompositions and their minimum
-- statement:
--   Let $f\in F[x_{i,j}]$ have $d$ row parts and $m$ variables per part. A length-$r$ partition decomposition is an actual equality
--   $$f=\sum_{k=1}^r g_kh_k,$$
--   where each $g_k$ uses one variable from every row in a nonempty proper subset $S_k$, and each $h_k$ uses one variable from every complementary row. The subsets may vary with $k$. Partition rank is the infimum of the actual lengths in $\mathbb N\cup\{\infty\}$. The empty decomposition represents exactly zero.
--
--   This defines the rank in the target without any rank certificate or assumed bound. Row expansion gives a finite minimum on the source's multilinear domain with at least two rows.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §1, partition rank, p. 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib
import Definitions.Def_SetMultCost_IsSetMultilinearOn

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

/-- The actual row-partition decompositions of §1, p.1; zero has a length-zero decomposition. -/
def HasPartitionDecomposition {K : Type*} [Field K] {d m : ℕ}
    (f : MvPolynomial (Fin d × Fin m) K) (r : ℕ) : Prop :=
  ∃ (S : Fin r → Finset (Fin d))
    (g h : Fin r → MvPolynomial (Fin d × Fin m) K),
    (∀ k, (S k).Nonempty ∧ S k ≠ Finset.univ ∧
      SetMultCost.IsSetMultilinearOn Prod.fst (S k) (g k) ∧
      SetMultCost.IsSetMultilinearOn Prod.fst (Finset.univ \ S k) (h k)) ∧
    f = ∑ k, g k * h k

/-- Minimum length in ℕ∞. The infimum of no lengths is ∞, never the junk value zero. -/
def partitionRank {K : Type*} [Field K] {d m : ℕ}
    (f : MvPolynomial (Fin d × Fin m) K) : ℕ∞ :=
  ⨅ r : {r : ℕ // HasPartitionDecomposition f r}, (r.val : ℕ∞)

end DetSupportRank.DeterminantSupport


