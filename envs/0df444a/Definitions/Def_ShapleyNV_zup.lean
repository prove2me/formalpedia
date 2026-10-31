-- Prove2me | Definitions.Def_ShapleyNV_zup
-- name    : ShapleyNV_zup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:59.729832+00:00
-- url     : https://prove2.me/theorems/10007054-8433-4862-92ce-b86fe86ac6c6
-- title:
--   Upper truncation level $\overline z_k$
-- statement:
--   For $k \in [K]$,
--
--   $$
--   \overline z_k := \max_{(x,z) \in \operatorname{supp} \widehat{\mathbb P}} \big\{ z - \|x - \hat x_k\| \big\}.
--   $$
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.3, p.ec4 (PDF 25)

import Mathlib
import Definitions.Def_ShapleyNV_Data

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Upper truncation level** `z̄_k := max_{(x,z) ∈ supp P̂} { z − ‖x − x̂_k‖ }`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.3, p.ec4 (PDF 25).

**Formalization Note.** As for `zlow`, the maximum is over the observation indices `(k', i)`. -/
noncomputable def zup {X : Type*} [MetricSpace X] (D : Data X) (k : Fin D.K) : ℝ :=
  Finset.univ.sup' D.obs_nonempty
    (fun p : Σ k' : Fin D.K, Fin (D.m k') => (D.zhat p.1 p.2 : ℝ) - dist (D.xhat p.1) (D.xhat k))

end ShapleyNV


