-- Prove2me | Definitions.Def_MaxCompForest_covObj
-- name    : MaxCompForest_covObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:31.097205+00:00
-- url     : https://prove2.me/theorems/6548ffa1-780f-4f5e-981b-cb0f27fa6422
-- title:
--   Covariance objective $W(F)$
-- statement:
--   For a forest $F$, with vertex masses $d$ and feature vectors $\phi_v\in\mathbb R^r$,
--   $$
--   W(F)=\Big(\prod_{C\in\mathcal C(F)}p_Cm_C\Big)\det\Big(I_r+\sum_{C\in\mathcal C(F)}\Sigma_C\Big).
--   $$
--   The empty forest has value one. Writing the determinant this way assembles the score from the components of the forest, which is what the terminal optimizer exploits.
--
--   **Formalization Note** The case $r=0$ is allowed, with the empty determinant equal to $1$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.7), p.16

import Mathlib
import Definitions.Def_MaxCompForest_nontrivialComps
import Definitions.Def_MaxCompForest_compP
import Definitions.Def_MaxCompForest_compMass
import Definitions.Def_MaxCompForest_compSigma
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V]

/-- **The covariance objective**
`W(F) = (∏_{C ∈ C(F)} p_C m_C) · det(I_r + ∑_{C ∈ C(F)} Σ_C)`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.7), p.16.

**Formalization Note.** Stated for arbitrary masses `d` and `r` feature coordinates, `r = 0` allowed
(the empty determinant is `1`). The empty forest has no nontrivial component, so its value is `1`, as
printed (sanity file). In the algorithm the masses are the current degrees (p.16). -/
noncomputable def covObj {r : ℕ} (G : WGraph V E) (d : V → ℝ)
    (φ : V → EuclideanSpace ℝ (Fin r)) (F : Finset E) : ℝ :=
  (∏ C ∈ nontrivialComps G F, compP G F d C * compMass G F d C) *
    Matrix.det (1 + ∑ C ∈ nontrivialComps G F, compSigma G F d φ C)

end MaxCompForest


