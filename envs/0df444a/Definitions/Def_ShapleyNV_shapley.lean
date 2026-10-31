-- Prove2me | Definitions.Def_ShapleyNV_shapley
-- name    : ShapleyNV_shapley
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:46.606798+00:00
-- url     : https://prove2.me/theorems/9e94c7c3-1a86-4f6f-91b8-2d8473651962
-- title:
--   Shapley policy $f^*(x) = \min_j \max_k A_{jk}(x)$
-- statement:
--   The Shapley extension of an in-sample policy $\hat f$ is
--
--   $$
--   f(x) := \min_{j \in [K]} \max_{k \in [K]} A_{jk}(x), \qquad x \in \mathcal X,
--   $$
--
--   the upper value $A^+(x)$ of the matrix $(A_{jk}(x))_{jk}$.
--
--   **Formalization Note** Lemma 1 and Appendix A write $\min_k \max_j A_{jk}$; since $A$ is symmetric this is the same function. That it also equals $\max_k \min_j A_{jk}(x)$ is Lemma EC.2.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Theorem 1 (II), p.6; Lemma 1, p.7; A⁺, p.ec1 (PDF 22)

import Mathlib
import Definitions.Def_ShapleyNV_shapleyA

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **The Shapley policy** `f*(x) := min_{j∈[K]} max_{k∈[K]} A_jk(x)` (the upper value `A⁺`).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Theorem 1 (II), p.6; Lemma 1, p.7; `A⁺`, proof of Lemma 1, p.ec1 (PDF 22).

**Formalization Note.** Theorem 1 writes `min_j max_k A_jk`; Lemma 1 and p.ec1 write
`min_k max_j A_jk`. These are the same function because `A_jk = A_kj`. That this equals the lower
value `max_k min_j A_jk(x)` (`shapleyLower`) is Lemma EC.2. -/
noncomputable def shapley {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (x : X) : ℝ :=
  Finset.univ.inf' D.univ_nonempty (fun j => Finset.univ.sup' D.univ_nonempty (fun k => shapleyA D y j k x))

end ShapleyNV


