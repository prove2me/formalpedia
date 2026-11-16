-- Prove2me | Definitions.Def_ParallelHAC_Supplement_wardLinkage
-- name    : ParallelHAC_Supplement_wardLinkage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:31:06.338145+00:00
-- url     : https://prove2.me/theorems/f3ac6662-e6e2-43ae-9fd3-6ba86ad8aefc
-- title:
--   k-means objective $\Delta(X)$ and Ward's linkage $d_{\mathrm{Ward}}$
-- statement:
--   For a finite set $X\subseteq\mathbb R^k$ let $\Delta(X):=\sum_{x\in X}\|x-\mu(X)\|^2$ be its **k-means objective**, where $\mu$ is the centroid. **Ward's linkage** of two clusters $A,B$ is the increase of the k-means objective caused by merging them when they are disjoint, and is given by the closed formula of footnote 2 otherwise:
--   $$d_{\mathrm{Ward}}(A,B):=\begin{cases}\Delta(A\cup B)-\Delta(A)-\Delta(B), & A\cap B=\emptyset,\\[2pt] \dfrac{|A||B|}{|A|+|B|}\,\|\mu(A)-\mu(B)\|^2, & A\cap B\neq\emptyset.\end{cases}$$
--
--   Ward's linkage is the second linkage the paper shows to be well-behaved (Theorem 2) and the linkage of the CC-hardness result (Theorem 8). The overlapping case is used by weight-stability, which evaluates $d(A\cup B,A)$.
--
--   **Formalization Note** The two cases are the page's; Lemma 42 (p.54) shows the closed formula also holds for disjoint clusters. Values at empty clusters are never read.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §1, p.1 (PDF p.4) and footnote 2; Lemma 42, p.54 (PDF p.57)

import Mathlib
import Definitions.Def_ParallelHAC_Supplement_centroidLinkage

namespace ParallelHAC.Supplement

/-- The **k-means objective** `∆(X) := Σ_{x∈X} ‖x − μ(X)‖²` of a finite set `X ⊆ ℝ^k`
(§1, p.1).
Source: arXiv:2507.20047 (sha256 a21061c8…), §1, printed p.1 (PDF p.4). -/
noncomputable def kmeansCost {k : ℕ} (X : Finset (EuclideanSpace ℝ (Fin k))) : ℝ :=
  ∑ x ∈ X, ‖x - centroid X‖ ^ 2

/-- **Ward's linkage** (§1, p.1 and footnote 2): for disjoint clusters,
`d_Ward(A, B) := ∆(A ∪ B) − ∆(A) − ∆(B)`, the increase of the k-means objective caused by merging
`A` and `B`; for clusters that are not disjoint,
`d_Ward(A, B) := |A||B| / (|A| + |B|) · ‖μ(A) − μ(B)‖²` (footnote 2).
Source: arXiv:2507.20047 (sha256 a21061c8…), §1, printed p.1 (PDF p.4), footnote 2;
Lemma 42, printed p.54 (PDF p.57).

**Formalization Note.** The definition is the page's two-case one. Lemma 42 shows that the
closed formula also holds for disjoint clusters. The overlapping case is read by
weight-stability, `d(A ∪ B, A)`. Values at empty clusters are never read. -/
noncomputable def wardLinkage (k : ℕ) (A B : Finset (EuclideanSpace ℝ (Fin k))) : ℝ :=
  if Disjoint A B then kmeansCost (A ∪ B) - kmeansCost A - kmeansCost B
  else (A.card : ℝ) * B.card / ((A.card : ℝ) + B.card) * ‖centroid A - centroid B‖ ^ 2

end ParallelHAC.Supplement


