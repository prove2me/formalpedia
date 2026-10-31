-- Prove2me | Definitions.Def_ShapleyNV_shapleyLower
-- name    : ShapleyNV_shapleyLower
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:43.653557+00:00
-- url     : https://prove2.me/theorems/0fdd5497-7d66-4965-898b-57f41a122eac
-- title:
--   Lower value $\max_k \min_j A_{jk}(x)$
-- statement:
--   The lower value of the matrix $(A_{jk}(x))_{jk}$ is
--
--   $$
--   A^-(x) := \max_{k \in [K]} \min_{j \in [K]} A_{jk}(x).
--   $$
--
--   **Formalization Note** Appendix A writes $\max_k \min_j A_{jk}$ with the roles of the indices as here; by symmetry of $A$ the order of the indices does not matter.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Theorem 1 (II), p.6; A⁻, p.ec1 (PDF 22)

import Mathlib
import Definitions.Def_ShapleyNV_shapleyA

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **The lower value** `max_{k∈[K]} min_{j∈[K]} A_jk(x)` of the matrix `A(x)` (`A⁻`).
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Theorem 1 (II), p.6; `A⁻`, proof of Lemma 1, p.ec1 (PDF 22).

**Formalization Note.** p.ec1 writes `A⁻ = max_k min_j A_jk`, the same function by symmetry of
`A`. -/
noncomputable def shapleyLower {X : Type*} [MetricSpace X] (D : Data X) (y : Fin D.K → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' D.univ_nonempty (fun k => Finset.univ.inf' D.univ_nonempty (fun j => shapleyA D y j k x))

end ShapleyNV


