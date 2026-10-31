-- Prove2me | Definitions.Def_ShapleyNV_zlow
-- name    : ShapleyNV_zlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:52:04.984999+00:00
-- url     : https://prove2.me/theorems/156f7822-e3d3-47d4-bf1d-1f6c6c05cd82
-- title:
--   Lower truncation level $\underline z_k$
-- statement:
--   For $k \in [K]$,
--
--   $$
--   \underline z_k := \min_{(x,z) \in \operatorname{supp} \widehat{\mathbb P}} \big\{ z + \|x - \hat x_k\| \big\},
--   $$
--
--   where $\operatorname{supp}\widehat{\mathbb P} = \{(\hat x_{k'}, \hat z_{k'i})\}$ is the set of observations.
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.3, p.ec4 (PDF 25)

import Mathlib
import Definitions.Def_ShapleyNV_Data

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Lower truncation level** `z̲_k := min_{(x,z) ∈ supp P̂} { z + ‖x − x̂_k‖ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.3, p.ec4 (PDF 25).

**Formalization Note.** `supp P̂` is the finite set of observations `(x̂_k', ẑ_k'i)`, indexed by the
pairs `(k', i)`; the minimum is a finite minimum over that nonempty index set. -/
noncomputable def zlow {X : Type*} [MetricSpace X] (D : Data X) (k : Fin D.K) : ℝ :=
  Finset.univ.inf' D.obs_nonempty
    (fun p : Σ k' : Fin D.K, Fin (D.m k') => (D.zhat p.1 p.2 : ℝ) + dist (D.xhat p.1) (D.xhat k))

end ShapleyNV


