-- Prove2me | Definitions.Def_ParallelHAC_Supplement_centroidLinkage
-- name    : ParallelHAC_Supplement_centroidLinkage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:30:29.680098+00:00
-- url     : https://prove2.me/theorems/17280e74-1d7d-4ddf-9633-c6513ebb4050
-- title:
--   Centroid $\mu(X)$ and centroid linkage $d_{\mathrm{cen}}$
-- statement:
--   For a finite nonempty set $X\subseteq\mathbb R^k$ the **centroid** is
--   $$\mu(X):=\frac1{|X|}\sum_{x\in X}x,$$
--   and the **centroid linkage** of two clusters $A,B\subseteq\mathbb R^k$ is the Euclidean distance between their centroids,
--   $$d_{\mathrm{cen}}(A,B):=\|\mu(A)-\mu(B)\|.$$
--
--   Centroid linkage is one of the two linkage functions the paper shows to be well-behaved (Theorem 1) and the one used in the height lower bound (Theorem 4).
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`. The value at an empty cluster ($\mu(\emptyset)=0$ by Lean's convention $0^{-1}=0$) is never read: every predicate of the mission evaluates linkages at nonempty clusters only.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §1, p.1 (PDF p.4)

import Mathlib

namespace ParallelHAC.Supplement

/-- The **centroid** `μ(X) := Σ_{x∈X} x / |X|` of a finite set `X ⊆ ℝ^k` (§1, p.1).
Source: Bateni et al., *Parallel Hierarchical Agglomerative Clustering in Low Dimensions*,
arXiv:2507.20047 (sha256 a21061c8…), §1, printed p.1 (PDF p.4).

**Formalization Note.** `ℝ^k` is `EuclideanSpace ℝ (Fin k)`. At `X = ∅` the value is `0`
(Lean's `0⁻¹ = 0`); clusters are nonempty, and every predicate of the mission evaluates the
centroid only at nonempty clusters. -/
noncomputable def centroid {k : ℕ} (X : Finset (EuclideanSpace ℝ (Fin k))) :
    EuclideanSpace ℝ (Fin k) :=
  ((X.card : ℝ)⁻¹) • ∑ x ∈ X, x

/-- The **centroid linkage** `d_cen(A, B) := ‖μ(A) − μ(B)‖` on finite subsets of `ℝ^k` (§1, p.1):
the Euclidean distance between the centroids of the two clusters.
Source: arXiv:2507.20047 (sha256 a21061c8…), §1, printed p.1 (PDF p.4).

**Formalization Note.** A function `Finset (EuclideanSpace ℝ (Fin k)) → … → ℝ`, the shape of the
base mission's linkage functions; its value at an empty cluster is never read. -/
noncomputable def centroidLinkage (k : ℕ) (A B : Finset (EuclideanSpace ℝ (Fin k))) : ℝ :=
  ‖centroid A - centroid B‖

end ParallelHAC.Supplement


