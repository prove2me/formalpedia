-- Prove2me | Definitions.Def_RobustKZClust_Main_Proj
-- name    : RobustKZClust_Main_Proj
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:11:35.151674+00:00
-- url     : https://prove2.me/theorems/83643e4e-d499-4d90-a6f4-700aace36c47
-- title:
--   Linear maps G ∈ ℝ^{d̃×d} applied to points and to center sets
-- statement:
--   For a matrix $G\in\mathbb R^{\tilde d\times d}$ and a point $x\in\mathbb R^d$, $Gx\in\mathbb R^{\tilde d}$ is the matrix-vector product. For a finite center set $C\subseteq\mathbb R^d$, $GC=\{Gc: c\in C\}$.
--
--   These are the projected points and center sets of the dimension-reduction lemma (Lemma 3.1), whose guarantee compares $\mathrm{dist}(Gx,GC)$ with $\mathrm{dist}(x,C)$.
--
--   **Formalization Note.** Points are `EuclideanSpace ℝ (Fin d)`; $GC$ is a `Finset` image, so coinciding images are merged, as for a set.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 13, Lemma 3.1 (G_j x, G_j C)

import Mathlib
import Definitions.Def_RobustKZClust_Main_Cost

namespace RobustKZClust.Main

/-! Linear maps `G ∈ ℝ^{d̃×d}` acting on points and center sets (§3, p. 13). -/

/-- The image `Gx ∈ ℝ^{d̃}` of a point `x ∈ ℝ^d` under the matrix `G ∈ ℝ^{d̃×d}`. -/
noncomputable def applyMat {d d' : ℕ} (G : Matrix (Fin d') (Fin d) ℝ) (x : Pt d) : Pt d' :=
  WithLp.toLp 2 (G.mulVec (WithLp.ofLp x))

/-- The image `GC = {Gc : c ∈ C}` of a center set. -/
noncomputable def applyMatSet {d d' : ℕ} (G : Matrix (Fin d') (Fin d) ℝ) (C : Finset (Pt d)) :
    Finset (Pt d') := by
  classical
  exact C.image (applyMat G)

end RobustKZClust.Main


